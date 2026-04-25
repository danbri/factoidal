#!/usr/bin/env python3
"""
bench_ukpar_queries.py — UK Parliament SPARQL query benchmark harness.

Discovers every .rq under third_party/data/ukparliament/sparql/{main,detail}/,
POSTs each one to a SPARQL endpoint, and times the wallclock round-trip.

Outputs:
  docs/test-results/ukparliament-bench.csv
  docs/test-results/ukparliament-bench.json

Usage:
  python3 tools/bench_ukpar_queries.py
  python3 tools/bench_ukpar_queries.py --endpoint http://host:port/sparql
  python3 tools/bench_ukpar_queries.py --timeout 30 --health-wait 300

This is pure tooling per CLAUDE.md rules #1, #5, #15 — no semantic logic;
the harness does not interpret SPARQL, it just times HTTP requests and
parses the SPARQL Results JSON envelope from the endpoint.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

# Resolve repo root from this script's location: tools/<this>
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
QUERY_ROOT = REPO_ROOT / "third_party" / "data" / "ukparliament" / "sparql"
OUT_DIR = REPO_ROOT / "docs" / "test-results"
CSV_OUT = OUT_DIR / "ukparliament-bench.csv"
JSON_OUT = OUT_DIR / "ukparliament-bench.json"

DEFAULT_ENDPOINT = "http://100.107.116.70:3030/sparql"
DEFAULT_QUERY_TIMEOUT_S = 60       # per-query cap
DEFAULT_HEALTH_WAIT_S = 300        # 5 min before giving up on endpoint
HEALTH_PROBE_INTERVAL_S = 10
HEALTH_PROBE_QUERY = "ASK {}"


def discover_queries(root: Path) -> list[Path]:
    """All .rq files under root, sorted for determinism."""
    return sorted(p for p in root.rglob("*.rq") if p.is_file())


def post_sparql(endpoint: str, query: str, timeout: float) -> tuple[int, bytes, str]:
    """POST a SPARQL query as application/sparql-query, asking for JSON results.

    Returns (http_status, body_bytes, content_type).
    Raises urllib.error.URLError / socket.timeout on transport failure.
    """
    req = urllib.request.Request(
        endpoint,
        data=query.encode("utf-8"),
        method="POST",
        headers={
            "Content-Type": "application/sparql-query; charset=utf-8",
            "Accept": "application/sparql-results+json, application/json;q=0.9, */*;q=0.1",
            "User-Agent": "factoidal-bench-ukpar/1.0",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        body = resp.read()
        ct = resp.headers.get("Content-Type", "")
        return resp.status, body, ct


def classify_result(body: bytes, content_type: str) -> tuple[str, int | None, bool | None, str | None]:
    """Parse a SPARQL Results body.

    Tries JSON first (sparql-results+json), falls back to a tolerant
    XML-by-regex count if the body looks like SRX. Returns
    (kind, row_count, ask_bool, parse_error). kind in {"select", "ask", "unknown"}.
    """
    if not body:
        return ("unknown", None, None, "empty body")
    text = body.decode("utf-8", errors="replace").lstrip()
    # JSON path
    if text.startswith("{"):
        try:
            doc = json.loads(text)
        except json.JSONDecodeError as e:
            return ("unknown", None, None, f"json decode: {e}")
        if isinstance(doc, dict):
            if "boolean" in doc:
                return ("ask", None, bool(doc["boolean"]), None)
            results = doc.get("results")
            if isinstance(results, dict) and "bindings" in results:
                bindings = results["bindings"]
                if isinstance(bindings, list):
                    return ("select", len(bindings), None, None)
            return ("unknown", None, None, "no boolean / results.bindings")
        return ("unknown", None, None, "json top-level not object")
    # XML / SRX fallback (some endpoints ignore Accept and always send XML)
    if text.startswith("<"):
        import re
        m_bool = re.search(r"<boolean[^>]*>\s*(true|false)\s*</boolean>", text, re.I)
        if m_bool:
            return ("ask", None, m_bool.group(1).lower() == "true", None)
        # Count <result> elements (not <results>)
        rows = len(re.findall(r"<result\b[^>/]*>", text))
        return ("select", rows, None, None)
    return ("unknown", None, None, f"unrecognised body (ct={content_type!r})")


def wait_for_endpoint(endpoint: str, max_wait_s: int) -> tuple[bool, str]:
    """Poll the endpoint with ASK {} until it answers, or we exhaust max_wait_s."""
    deadline = time.monotonic() + max_wait_s
    last_err = "no probes attempted"
    attempt = 0
    while time.monotonic() < deadline:
        attempt += 1
        try:
            status, body, _ct = post_sparql(endpoint, HEALTH_PROBE_QUERY, timeout=10)
            if status == 200:
                kind, _rows, ask_val, perr = classify_result(body, _ct)
                if kind == "ask":
                    return True, f"healthy after {attempt} probe(s); ASK {{}} -> {ask_val}"
                # Non-ASK 200 is still a working endpoint
                return True, f"healthy after {attempt} probe(s); 200 OK ({kind})"
            last_err = f"HTTP {status}"
        except urllib.error.HTTPError as e:
            # An HTTP-level error still means the endpoint is up
            return True, f"healthy after {attempt} probe(s); HTTP {e.code} (endpoint reachable)"
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            last_err = f"{type(e).__name__}: {e}"
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        sleep_for = min(HEALTH_PROBE_INTERVAL_S, max(1.0, remaining))
        time.sleep(sleep_for)
    return False, f"endpoint not reachable after {attempt} probe(s): {last_err}"


def run_one(endpoint: str, qpath: Path, timeout_s: int) -> dict:
    """Run a single query and return a result record."""
    rel = qpath.relative_to(REPO_ROOT)
    query_text = qpath.read_text(encoding="utf-8")
    record: dict = {
        "name": qpath.name,
        "path": str(rel),
        "category": qpath.parent.name,        # main / detail
        "size_bytes": len(query_text.encode("utf-8")),
        "status": None,
        "kind": None,
        "rows": None,
        "ask": None,
        "http_status": None,
        "wallclock_ms": None,
        "error": None,
    }
    t0 = time.perf_counter()
    try:
        http_status, body, ct = post_sparql(endpoint, query_text, timeout=timeout_s)
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        record["wallclock_ms"] = round(elapsed_ms, 2)
        record["http_status"] = http_status
        if http_status != 200:
            record["status"] = "ERROR"
            snippet = body[:400].decode("utf-8", errors="replace").strip()
            record["error"] = f"HTTP {http_status}: {snippet}"
            return record
        kind, rows, ask, perr = classify_result(body, ct)
        record["kind"] = kind
        record["rows"] = rows
        record["ask"] = ask
        if perr is not None:
            record["status"] = "PARSE_ERROR"
            record["error"] = perr
        else:
            record["status"] = "OK"
        return record
    except urllib.error.HTTPError as e:
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        record["wallclock_ms"] = round(elapsed_ms, 2)
        record["http_status"] = e.code
        record["status"] = "ERROR"
        try:
            snippet = e.read()[:400].decode("utf-8", errors="replace").strip()
        except Exception:
            snippet = ""
        record["error"] = f"HTTPError {e.code}: {snippet}"
        return record
    except (TimeoutError, urllib.error.URLError) as e:
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        record["wallclock_ms"] = round(elapsed_ms, 2)
        # urllib raises URLError wrapping socket.timeout when timeout fires
        msg = str(e)
        if "timed out" in msg.lower() or isinstance(e, TimeoutError):
            record["status"] = "TIMEOUT"
        else:
            record["status"] = "ERROR"
        record["error"] = f"{type(e).__name__}: {msg}"
        return record
    except Exception as e:  # noqa: BLE001 — last-resort catch
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        record["wallclock_ms"] = round(elapsed_ms, 2)
        record["status"] = "ERROR"
        record["error"] = f"{type(e).__name__}: {e}"
        return record


def write_outputs(records: list[dict], summary: dict, run_meta: dict) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    # CSV
    fieldnames = [
        "timestamp_utc", "name", "path", "category", "status", "kind",
        "rows", "ask", "http_status", "wallclock_ms", "size_bytes", "error",
    ]
    with CSV_OUT.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        ts = run_meta["timestamp_utc"]
        for r in records:
            row = {k: r.get(k) for k in fieldnames}
            row["timestamp_utc"] = ts
            w.writerow(row)
    # JSON
    payload = {
        "run": run_meta,
        "summary": summary,
        "results": records,
    }
    with JSON_OUT.open("w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=False)
        fh.write("\n")


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--endpoint", default=DEFAULT_ENDPOINT,
                    help=f"SPARQL endpoint URL (default {DEFAULT_ENDPOINT})")
    ap.add_argument("--timeout", type=int, default=DEFAULT_QUERY_TIMEOUT_S,
                    help=f"per-query timeout seconds (default {DEFAULT_QUERY_TIMEOUT_S})")
    ap.add_argument("--health-wait", type=int, default=DEFAULT_HEALTH_WAIT_S,
                    help=f"max seconds to wait for endpoint to come up (default {DEFAULT_HEALTH_WAIT_S})")
    ap.add_argument("--query-root", default=str(QUERY_ROOT),
                    help="root dir to scan for .rq files")
    ap.add_argument("--no-health-check", action="store_true",
                    help="skip the initial endpoint readiness probe")
    args = ap.parse_args(argv)

    query_root = Path(args.query_root).resolve()
    if not query_root.exists():
        print(f"ERROR: query root not found: {query_root}", file=sys.stderr)
        return 2

    queries = discover_queries(query_root)
    if not queries:
        print(f"ERROR: no .rq files under {query_root}", file=sys.stderr)
        return 2

    print(f"# bench_ukpar_queries.py")
    print(f"# endpoint     : {args.endpoint}")
    print(f"# query root   : {query_root}")
    print(f"# query count  : {len(queries)}")
    print(f"# per-q timeout: {args.timeout}s")
    print(f"# health wait  : {args.health_wait}s")

    # Health probe
    if args.no_health_check:
        print("# health-check skipped (--no-health-check)")
        ready, health_msg = True, "skipped"
    else:
        print(f"# probing endpoint readiness ...")
        ready, health_msg = wait_for_endpoint(args.endpoint, args.health_wait)
        print(f"# endpoint    : {health_msg}")

    if not ready:
        print(f"FATAL: endpoint not reachable", file=sys.stderr)
        # Still write a stub JSON so callers know we ran
        run_meta = {
            "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "endpoint": args.endpoint,
            "query_root": str(query_root),
            "query_count": len(queries),
            "per_query_timeout_s": args.timeout,
            "health_wait_s": args.health_wait,
            "endpoint_status": health_msg,
        }
        write_outputs([], {"ok": 0, "error": 0, "timeout": 0, "total_wallclock_ms": 0,
                            "slowest": None, "endpoint_unreachable": True}, run_meta)
        return 3

    # Run each query
    run_started = datetime.now(timezone.utc)
    records: list[dict] = []
    bench_t0 = time.perf_counter()
    for i, qp in enumerate(queries, 1):
        rel = qp.relative_to(REPO_ROOT)
        print(f"[{i:>2}/{len(queries)}] {rel} ...", end="", flush=True)
        rec = run_one(args.endpoint, qp, args.timeout)
        records.append(rec)
        # one-line per-query summary on stdout
        if rec["status"] == "OK":
            if rec["kind"] == "ask":
                print(f" OK  ASK={rec['ask']} ({rec['wallclock_ms']:.1f} ms)")
            else:
                print(f" OK  rows={rec['rows']} ({rec['wallclock_ms']:.1f} ms)")
        elif rec["status"] == "TIMEOUT":
            print(f" TIMEOUT after {rec['wallclock_ms']:.1f} ms")
        else:
            err = (rec.get("error") or "").splitlines()[0][:120]
            print(f" {rec['status']}  {err}")
    total_wallclock_ms = (time.perf_counter() - bench_t0) * 1000.0

    # Summary
    n_ok = sum(1 for r in records if r["status"] == "OK")
    n_err = sum(1 for r in records if r["status"] in ("ERROR", "PARSE_ERROR"))
    n_timeout = sum(1 for r in records if r["status"] == "TIMEOUT")
    slowest = max(records, key=lambda r: r["wallclock_ms"] or 0.0, default=None)

    summary = {
        "ok": n_ok,
        "error": n_err,
        "timeout": n_timeout,
        "total_wallclock_ms": round(total_wallclock_ms, 2),
        "total_wallclock_s": round(total_wallclock_ms / 1000.0, 2),
        "slowest": (
            {
                "name": slowest["name"],
                "path": slowest["path"],
                "wallclock_ms": slowest["wallclock_ms"],
                "rows": slowest["rows"],
                "status": slowest["status"],
            }
            if slowest else None
        ),
    }

    run_meta = {
        "timestamp_utc": run_started.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "endpoint": args.endpoint,
        "query_root": str(query_root),
        "query_count": len(queries),
        "per_query_timeout_s": args.timeout,
        "health_wait_s": args.health_wait,
        "endpoint_status": health_msg,
    }

    write_outputs(records, summary, run_meta)

    print()
    print(f"# {len(records)} queries: {n_ok} OK, {n_err} error, "
          f"{n_timeout} timeout, total wallclock {summary['total_wallclock_s']:.2f} s")
    if slowest is not None:
        print(f"# slowest = {slowest['name']} ({slowest['wallclock_ms']:.1f} ms, "
              f"{slowest['status']}, rows={slowest.get('rows')})")
    print(f"# wrote {CSV_OUT.relative_to(REPO_ROOT)}")
    print(f"# wrote {JSON_OUT.relative_to(REPO_ROOT)}")
    # Exit non-zero only if every query failed
    if n_ok == 0:
        return 4
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
