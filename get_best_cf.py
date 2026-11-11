#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BlueEyes Cloudflare IP quality selector.

Priority:
1. Strict HKG nodes first (live Cloudflare colo must equal HKG).
2. If fewer than HK_TOP_N HKG nodes survive, fill the remaining slots with
   verified Asian Cloudflare colos, ranked by measured quality.
3. US nodes are selected independently.

All candidates must be in official Cloudflare IPv4 ranges. Region is determined
only by live /cdn-cgi/trace colo, never by feed labels or IP geolocation.
Only TCP/443 is tested, with verified TLS certificates and hostname checks.
Credential-bearing sub.txt is generated only in the runner workspace.
"""

from __future__ import annotations

import base64
import concurrent.futures
import hashlib
import ipaddress
import json
import os
import random
import re
import socket
import ssl
import statistics
import time
import urllib.parse
import uuid as uuid_module
from datetime import datetime, timezone
from pathlib import Path

import requests

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
RESULTS.mkdir(parents=True, exist_ok=True)

PORT = 443
TRACE_HOST = "www.cloudflare.com"
CF_IPV4_URL = "https://www.cloudflare.com/ips-v4"
USER_AGENT = "BlueEyes-Network-Quality-Check/3.0"
SOURCE_TIMEOUT = (5, 12)
MAX_SOURCE_BYTES = 512 * 1024

US_TOP_N = max(1, min(int(os.getenv("US_TOP_N", "25")), 50))
# Total preferred Asia-region slots: HKG first, then other Asian colo fallback.
ASIA_TOTAL_N = max(1, min(int(os.getenv("HK_TOP_N", "20")), 50))

WORKERS = max(1, min(int(os.getenv("CHECK_WORKERS", "3")), 4))
TIMEOUT = max(2.5, min(float(os.getenv("CHECK_TIMEOUT", "4.0")), 8.0))
GLOBAL_LIMIT = max(100, min(int(os.getenv("GLOBAL_DISCOVERY_MAX", "500")), 700))
HK_LIMIT = max(150, min(int(os.getenv("HK_DISCOVERY_MAX", "600")), 800))
GLOBAL_SOURCE_LIMIT = max(50, min(int(os.getenv("GLOBAL_SOURCE_MAX", "300")), 450))
HK_SOURCE_LIMIT = max(50, min(int(os.getenv("HK_SOURCE_MAX", "300")), 450))
US_DEEP_LIMIT = max(20, min(int(os.getenv("US_DEEP_POOL", "80")), 120))
HK_DEEP_LIMIT = max(20, min(int(os.getenv("HK_DEEP_POOL", "140")), 180))
ASIA_DEEP_LIMIT = max(20, min(int(os.getenv("ASIA_DEEP_POOL", "140")), 180))
STABILITY_ROUNDS = max(2, min(int(os.getenv("STABILITY_ROUNDS", "3")), 4))
SAMPLES_PER_CIDR = max(8, min(int(os.getenv("SAMPLES_PER_CIDR", "28")), 48))
MAX_TOTAL_DISCOVERY = 1100

UUID = os.environ.get("U", "").strip()
HOST = os.environ.get("H", "").strip()
WS_PATH = os.environ.get("P", "/").strip() or "/"

GLOBAL_SOURCES = (
    "https://raw.githubusercontent.com/LancelotRar/best-cf-ips/main/best-cf-ip-scanned-top100.txt",
    "https://raw.githubusercontent.com/svip-s/cloudflare_ip/main/best_ips.txt",
    "https://raw.githubusercontent.com/ymyuuu/IPDB/main/BestCF/bestcfv4.txt",
    "https://raw.githubusercontent.com/yuanxiawan/cfipv4db/main/cfip.txt",
)
HK_SOURCES = (
    "https://cleanip.io/api/cf-best-ip?region=HK&count=200&format=txt",
    "https://gist.githubusercontent.com/cber/59724b99f00eac8c32a845e64c49ceed/raw/AS-HK.txt",
)

# Cloudflare colo codes used as an allow-list for Asian fallback. HKG is
# intentionally excluded here and handled as its own higher-priority region.
# Mainland-China colo codes are intentionally not included in this fallback.
ASIA_COLOS = {
    "AMD", "BLR", "BKK", "BWN", "CEB", "CCU", "CGK", "CGP", "CMB",
    "COK", "DAC", "DEL", "DPS", "FUK", "HAN", "HYD", "ICN", "ISB",
    "IXC", "JHB", "KHH", "KHI", "KIX", "KNU", "KTM", "KUL", "KWI",
    "MAA", "MLE", "MNL", "NAG", "NRT", "OKA", "PAT", "PNH", "SGN",
    "SIN", "TPE", "ULN", "VTE", "YOG", "JOG", "MFM",
}
US_COLOS = {
    "ATL", "AUS", "BNA", "BOS", "BUF", "BWI", "CLE", "CLT", "CMH",
    "CVG", "DAL", "DCA", "DEN", "DFW", "DTW", "EWR", "FLL", "GSO",
    "HNL", "IAD", "IAH", "IND", "JAX", "LAS", "LAX", "MCI", "MCO",
    "MDW", "MEM", "MIA", "MKE", "MSP", "MSY", "OAK", "OKC", "OMA",
    "ORD", "PDX", "PHL", "PHX", "PIT", "RDU", "RIC", "SAN", "SAT",
    "SEA", "SFO", "SJC", "SLC", "SMF", "STL", "TPA", "TUL",
}

SESSION = requests.Session()
SESSION.headers.update({"User-Agent": USER_AGENT, "Accept": "text/plain,*/*;q=0.8"})


def log(message: str) -> None:
    print(message, flush=True)


def validate_config() -> None:
    if not UUID or not HOST:
        raise RuntimeError("Required GitHub Secrets U and H must be configured.")
    try:
        parsed = uuid_module.UUID(UUID)
    except (ValueError, AttributeError):
        raise RuntimeError("Secret U must contain a valid UUID.") from None
    if str(parsed) != UUID.lower():
        raise RuntimeError("Secret U must be a canonical UUID.")
    if (len(HOST) > 253 or "://" in HOST or "/" in HOST or ":" in HOST
            or "@" in HOST or any(ch.isspace() for ch in HOST)
            or not re.fullmatch(r"[A-Za-z0-9.-]+", HOST)):
        raise RuntimeError("Secret H must be a hostname only.")
    if not WS_PATH.startswith("/") or "\r" in WS_PATH or "\n" in WS_PATH:
        raise RuntimeError("Secret P must be an absolute WebSocket path.")


def bounded_get(url: str) -> str:
    with SESSION.get(url, timeout=SOURCE_TIMEOUT, stream=True,
                     allow_redirects=False) as response:
        response.raise_for_status()
        chunks, total = [], 0
        for chunk in response.iter_content(16384):
            if chunk:
                total += len(chunk)
                if total > MAX_SOURCE_BYTES:
                    raise ValueError("source too large")
                chunks.append(chunk)
        return b"".join(chunks).decode("utf-8", errors="replace")


def extract_candidates(text: str) -> list[dict]:
    output = []
    for line in text.splitlines():
        # Labels are retained only for candidate ordering; never trusted as region.
        upper = line.upper()
        hint = "HK" if ("HKG" in upper or "HONG KONG" in upper or
                        re.search(r"\bHK\b", upper)) else ""
        for raw in re.findall(r"(?<![\d.])(?:\d{1,3}\.){3}\d{1,3}(?![\d.])", line):
            try:
                ip = ipaddress.IPv4Address(raw)
            except ipaddress.AddressValueError:
                continue
            if ip.is_global:
                output.append({"ip": str(ip), "hint": hint})
    return output


def download_sources(urls: tuple[str, ...], label: str) -> list[dict]:
    rows, ok = [], 0
    for url in urls:
        try:
            rows.extend(extract_candidates(bounded_get(url)))
            ok += 1
        except Exception as exc:
            log(f"[SOURCE] {label}: skipped feed ({type(exc).__name__})")
    log(f"[SOURCE] {label}: {ok}/{len(urls)} feeds; {len(rows)} records")
    return rows


def load_cf_networks() -> list[ipaddress.IPv4Network]:
    networks = []
    for line in bounded_get(CF_IPV4_URL).splitlines():
        try:
            net = ipaddress.ip_network(line.strip(), strict=False)
        except ValueError:
            continue
        if net.version == 4:
            networks.append(net)
    if not networks:
        raise RuntimeError("Could not load official Cloudflare IPv4 ranges.")
    return networks


def in_cf_ranges(ip: str, networks: list[ipaddress.IPv4Network]) -> bool:
    address = ipaddress.IPv4Address(ip)
    return address.is_global and any(address in net for net in networks)


def read_previous(path: Path, networks: list[ipaddress.IPv4Network],
                  hint: str = "") -> list[dict]:
    rows = []
    if not path.exists():
        return rows
    try:
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                ip = str(ipaddress.IPv4Address(line.strip().split(":")[0]))
            except ipaddress.AddressValueError:
                continue
            if in_cf_ranges(ip, networks):
                rows.append({"ip": ip, "hint": hint})
    except OSError:
        pass
    return rows


def weekly_reservoir(networks: list[ipaddress.IPv4Network]) -> list[dict]:
    iso = datetime.now(timezone.utc).isocalendar()
    week = f"{iso.year}-{iso.week:02d}"
    rows = []
    for net in networks:
        usable = int(net.num_addresses) - 2
        if usable <= 0:
            continue
        digest = hashlib.sha256(f"blueeyes:{net}:{week}".encode()).digest()
        rng = random.Random(int.from_bytes(digest[:8], "big"))
        count = min(SAMPLES_PER_CIDR, usable)
        offsets = set()
        while len(offsets) < count:
            offsets.add(rng.randrange(1, usable + 1))
        rows.extend({"ip": str(net.network_address + n), "hint": ""}
                    for n in sorted(offsets))
    return rows


def dedupe(rows: list[dict]) -> list[dict]:
    merged = {}
    for row in rows:
        ip = row["ip"]
        if ip not in merged:
            merged[ip] = dict(row)
        elif row.get("hint") and not merged[ip].get("hint"):
            merged[ip]["hint"] = row["hint"]
    return list(merged.values())


def collect_candidates(networks):
    global_rows = download_sources(GLOBAL_SOURCES, "global")
    hk_rows = download_sources(HK_SOURCES, "HK")
    reservoir = weekly_reservoir(networks)
    global_rows = [x for x in global_rows if in_cf_ranges(x["ip"], networks)][:GLOBAL_SOURCE_LIMIT]
    hk_rows = [x for x in hk_rows if in_cf_ranges(x["ip"], networks)][:HK_SOURCE_LIMIT]
    old_us = read_previous(RESULTS / "us.txt", networks)
    old_hk = read_previous(RESULTS / "hk.txt", networks, "HK")
    old_asia = read_previous(RESULTS / "asia.txt", networks)

    global_pool = dedupe(old_us + old_hk + old_asia + global_rows + reservoir)
    hk_pool = dedupe(old_hk + hk_rows + reservoir)
    global_pool.sort(key=lambda x: 0 if x.get("hint") == "HK" else 1)
    hk_pool.sort(key=lambda x: 0 if x.get("hint") == "HK" else 1)
    global_pool = global_pool[:GLOBAL_LIMIT]
    hk_pool = hk_pool[:HK_LIMIT]

    if len(global_pool) + len(hk_pool) > MAX_TOTAL_DISCOVERY:
        hk_budget = min(len(hk_pool), MAX_TOTAL_DISCOVERY // 2)
        global_pool = global_pool[:MAX_TOTAL_DISCOVERY - hk_budget]
        hk_pool = hk_pool[:hk_budget]
    log(f"[POOL] global={len(global_pool)}; HK-focused={len(hk_pool)}; "
        f"weekly-reservoir={len(reservoir)}")
    return global_pool, hk_pool


def tls_context():
    ctx = ssl.create_default_context()
    ctx.verify_mode = ssl.CERT_REQUIRED
    ctx.check_hostname = True
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    return ctx


def probe(ip: str, sni: str, host: str):
    raw = tls = None
    try:
        time.sleep(random.uniform(0.03, 0.12))
        t0 = time.perf_counter()
        raw = socket.create_connection((ip, PORT), timeout=TIMEOUT)
        tcp_ms = (time.perf_counter() - t0) * 1000
        raw.settimeout(TIMEOUT)
        t1 = time.perf_counter()
        tls = tls_context().wrap_socket(raw, server_hostname=sni)
        raw = None
        tls_ms = (time.perf_counter() - t1) * 1000
        tls.settimeout(TIMEOUT)
        request = (f"GET /cdn-cgi/trace HTTP/1.1\r\nHost: {host}\r\n"
                   f"User-Agent: {USER_AGENT}\r\nAccept: text/plain\r\n"
                   "Connection: close\r\n\r\n")
        t2 = time.perf_counter()
        tls.sendall(request.encode("ascii"))
        first = tls.recv(1)
        if not first:
            return None
        ttfb_ms = (time.perf_counter() - t2) * 1000
        data = bytearray(first)
        while len(data) < 8192:
            chunk = tls.recv(min(2048, 8192 - len(data)))
            if not chunk:
                break
            data.extend(chunk)
            pos = data.find(b"colo=")
            if pos >= 0 and b"\n" in data[pos:]:
                break
        response = bytes(data).decode("utf-8", errors="ignore")
        status_match = re.search(r"HTTP/\d(?:\.\d)?\s+(\d+)", response)
        colo_match = re.search(r"(?im)^colo=([A-Z]{3})\s*$", response)
        status = int(status_match.group(1)) if status_match else 0
        colo = colo_match.group(1).upper() if colo_match else ""
        if not colo:
            ray = re.search(r"(?im)^CF-Ray:\s*[^\r\n]*?-([A-Z]{3})\s*$", response)
            colo = ray.group(1).upper() if ray else ""
        if status != 200 or not colo:
            return None
        return {"ip": ip, "port": PORT, "colo": colo, "status": status,
                "tcp_ms": round(tcp_ms, 2), "tls_ms": round(tls_ms, 2),
                "ttfb_ms": round(ttfb_ms, 2)}
    except (OSError, ssl.SSLError, socket.timeout, ValueError):
        return None
    finally:
        try:
            if tls:
                tls.close()
            elif raw:
                raw.close()
        except OSError:
            pass


def region_for_colo(colo: str) -> str:
    colo = (colo or "").upper()
    if colo == "HKG":
        return "HK"
    if colo in US_COLOS:
        return "US"
    if colo in ASIA_COLOS:
        return "ASIA"
    return ""


def discovery(item):
    result = probe(item["ip"], TRACE_HOST, TRACE_HOST)
    if not result:
        return None
    region = region_for_colo(result["colo"])
    if not region:
        return None
    result["region"] = region
    return result


def probe_pool(items, label):
    if not items:
        log(f"[DISCOVERY] {label}: no candidates")
        return []
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as executor:
        futures = [executor.submit(discovery, x) for x in items]
        for i, future in enumerate(concurrent.futures.as_completed(futures), 1):
            try:
                row = future.result()
                if row:
                    results.append(row)
            except Exception:
                pass
            if i % 50 == 0 or i == len(futures):
                log(f"[DISCOVERY] {label}: {i}/{len(futures)}; verified={len(results)}")
    return results


def latency_key(x):
    return (x.get("ttfb_ms", 1e9), x.get("tls_ms", 1e9), x.get("tcp_ms", 1e9))


def deep_probe(item):
    result = probe(item["ip"], HOST, HOST)
    if not result or region_for_colo(result["colo"]) != item["region"]:
        return None
    result["region"] = item["region"]
    result["score"] = round(result["tcp_ms"] * .20 +
                            result["tls_ms"] * .20 +
                            result["ttfb_ms"] * .60, 2)
    return result


def deep_test(items, region, limit):
    selected = sorted(items, key=latency_key)[:limit]
    if not selected:
        log(f"[DEEP] {region}: no candidates")
        return []
    passed = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as executor:
        futures = [executor.submit(deep_probe, x) for x in selected]
        for i, future in enumerate(concurrent.futures.as_completed(futures), 1):
            try:
                row = future.result()
                if row:
                    passed.append(row)
            except Exception:
                pass
            if i % 20 == 0 or i == len(futures):
                log(f"[DEEP] {region}: {i}/{len(futures)}; passed={len(passed)}")
    return sorted(passed, key=lambda x: x["score"])


def stability_test(item):
    samples = []
    for _ in range(STABILITY_ROUNDS):
        row = probe(item["ip"], HOST, HOST)
        if row and region_for_colo(row["colo"]) == item["region"]:
            samples.append(row)
    if len(samples) < 2:
        return None
    tcp = statistics.median(x["tcp_ms"] for x in samples)
    tls = statistics.median(x["tls_ms"] for x in samples)
    ttfb = statistics.median(x["ttfb_ms"] for x in samples)
    jitter = statistics.pstdev(x["ttfb_ms"] for x in samples)
    final = dict(item)
    final.update({
        "tcp_ms": round(tcp, 2), "tls_ms": round(tls, 2),
        "ttfb_ms": round(ttfb, 2), "jitter_ms": round(jitter, 2),
        "score": round(tcp * .20 + tls * .15 + ttfb * .50 + jitter * .15, 2),
        "success_rounds": len(samples),
    })
    return final


def stability_pool(items, label):
    selected = sorted(items, key=lambda x: x["score"])[:min(50, len(items))]
    output = []
    for i, item in enumerate(selected, 1):
        row = stability_test(item)
        if row:
            output.append(row)
        if i % 5 == 0 or i == len(selected):
            log(f"[STABILITY] {label}: {i}/{len(selected)}; passed={len(output)}")
    return sorted(output, key=lambda x: x["score"])


def make_vless(item, label):
    query = ("encryption=none&security=tls"
             f"&sni={urllib.parse.quote(HOST, safe='')}&type=ws"
             f"&host={urllib.parse.quote(HOST, safe='')}"
             f"&path={urllib.parse.quote(WS_PATH, safe='/')}")
    return (f"vless://{UUID}@{item['ip']}:{PORT}?{query}"
            f"#{urllib.parse.quote(label)}")


def write_results(us, hk, asia_fallback):
    us = us[:US_TOP_N]
    hk = hk[:ASIA_TOTAL_N]
    remaining = max(0, ASIA_TOTAL_N - len(hk))
    asia_fallback = [x for x in asia_fallback if x["ip"] not in {h["ip"] for h in hk}]
    asia_fallback = asia_fallback[:remaining]
    asia_pool = hk + asia_fallback

    (RESULTS / "us.txt").write_text(
        "".join(f"{x['ip']}:{PORT}\n" for x in us), encoding="utf-8")
    # hk.txt remains HKG-only. No Asian fallback is ever mislabeled as Hong Kong.
    (RESULTS / "hk.txt").write_text(
        "".join(f"{x['ip']}:{PORT}\n" for x in hk), encoding="utf-8")
    (RESULTS / "asia.txt").write_text(
        "".join(f"{x['ip']}:{PORT}\n" for x in asia_fallback), encoding="utf-8")
    all_rows = asia_pool + us
    (RESULTS / "best-cf-ips.txt").write_text(
        "".join(f"{x['ip']}:{PORT}\n" for x in all_rows), encoding="utf-8")

    nodes = []
    for i, row in enumerate(hk, 1):
        nodes.append(make_vless(row, f"香港{i:02d}"))
    for i, row in enumerate(asia_fallback, 1):
        nodes.append(make_vless(row, f"亚洲备用-{row['colo']}-{i:02d}"))
    for i, row in enumerate(us, 1):
        nodes.append(make_vless(row, f"美国{i:02d}"))
    encoded = base64.b64encode(("\n".join(nodes) + "\n").encode()).decode("ascii")
    (RESULTS / "sub.txt").write_text(encoded + "\n", encoding="utf-8")

    report = [{
        "ip": x["ip"], "port": PORT, "region": x["region"], "colo": x["colo"],
        "tcp_ms": x["tcp_ms"], "tls_ms": x["tls_ms"],
        "ttfb_ms": x["ttfb_ms"], "jitter_ms": x.get("jitter_ms", 0),
        "score": x["score"],
    } for x in all_rows]
    (RESULTS / "best-cf-ips.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")

    log(f"[FINAL] HKG={len(hk)}; Asia fallback={len(asia_fallback)}; "
        f"Asia total={len(asia_pool)}/{ASIA_TOTAL_N}; US={len(us)}/{US_TOP_N}")
    if len(hk) < ASIA_TOTAL_N:
        log("[INFO] HKG count is below target; remaining slots are filled only "
            "with verified Asian Cloudflare colos.")
    for label, rows in (("HK", hk), ("ASIA", asia_fallback), ("US", us)):
        for i, row in enumerate(rows[:3], 1):
            log(f"[CHECK] {label}{i:02d}: colo={row['colo']} "
                f"tcp={row['tcp_ms']}ms tls={row['tls_ms']}ms "
                f"ttfb={row['ttfb_ms']}ms")


def main():
    validate_config()
    log("[START] BlueEyes HK-priority + Asia-fallback Cloudflare selector")
    log(f"[CONFIG] port=443; workers={WORKERS}; timeout={TIMEOUT}s; "
        f"Asia target={ASIA_TOTAL_N}; US target={US_TOP_N}")
    networks = load_cf_networks()
    global_pool, hk_pool = collect_candidates(networks)

    global_verified = probe_pool(global_pool, "GLOBAL")
    hk_verified = probe_pool(hk_pool, "HK-FOCUSED")
    verified = {x["ip"]: x for x in global_verified}
    verified.update({x["ip"]: x for x in hk_verified})

    hk_candidates = [x for x in verified.values() if x["region"] == "HK"]
    asia_candidates = [x for x in verified.values() if x["region"] == "ASIA"]
    us_candidates = [x for x in verified.values() if x["region"] == "US"]
    log(f"[REGION] verified HKG={len(hk_candidates)} "
        f"ASIA={len(asia_candidates)} US={len(us_candidates)}")

    hk_deep = deep_test(hk_candidates, "HK", HK_DEEP_LIMIT)
    asia_deep = deep_test(asia_candidates, "ASIA", ASIA_DEEP_LIMIT)
    us_deep = deep_test(us_candidates, "US", US_DEEP_LIMIT)
    hk_final = stability_pool(hk_deep, "HKG")
    asia_final = stability_pool(asia_deep, "ASIA")
    us_final = stability_pool(us_deep, "US")

    if not us_final:
        raise RuntimeError("No US nodes passed final verification; old results preserved.")
    if not hk_final and not asia_final:
        raise RuntimeError("No HKG or Asian fallback nodes passed; old results preserved.")
    if len(hk_final) < ASIA_TOTAL_N and len(asia_final) < ASIA_TOTAL_N - len(hk_final):
        log(f"[WARN] Asia pool cannot fully reach target: HKG={len(hk_final)}, "
            f"Asia fallback={len(asia_final)}, target={ASIA_TOTAL_N}.")
    write_results(us_final, hk_final, asia_final)


if __name__ == "__main__":
    main()
