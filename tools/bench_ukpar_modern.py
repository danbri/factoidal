#!/usr/bin/env python3
"""
bench_ukpar_modern.py — Modernised UK Parliament SPARQL bench.

Sister of bench_ukpar_queries.py. The vendored queries under
third_party/data/ukparliament/sparql/{main,detail}/ target specific
entity IRIs from the live id.parliament.uk service that aren't in our
2019-07-27 N-Quads snapshot, so 22 of 24 return rows=0. This harness
runs the parallel "modernised" set under
tools/sample-queries/ukparliament/{main,detail}/ that has been
re-shaped to match the actual 2019 data and (per query) returns at
least 1 row against the live endpoint.

Outputs:
  docs/test-results/ukparliament-bench-modern.csv
  docs/test-results/ukparliament-bench-modern.json

Same envelope semantics, classify_result, health-probe etc. as
bench_ukpar_queries.py — we re-import those helpers so behaviour stays
in sync.

Usage:
  python3 tools/bench_ukpar_modern.py
  python3 tools/bench_ukpar_modern.py --endpoint http://host:port/sparql
  python3 tools/bench_ukpar_modern.py --timeout 30 --health-wait 60

Pure tooling per CLAUDE.md rules #1, #5, #15 — no semantic logic; the
harness only times HTTP and parses the SPARQL Results JSON envelope.
"""

from __future__ import annotations

import argparse
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# Re-use everything from bench_ukpar_queries.py so we don't drift.
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from bench_ukpar_queries import (  # noqa: E402
    REPO_ROOT,
    DEFAULT_ENDPOINT,
    DEFAULT_QUERY_TIMEOUT_S,
    DEFAULT_HEALTH_WAIT_S,
    discover_queries,
    wait_for_endpoint,
    run_one,
    write_outputs as _orig_write_outputs,
)
import json
import csv

MODERN_QUERY_ROOT = REPO_ROOT / "tools" / "sample-queries" / "ukparliament"
OUT_DIR = REPO_ROOT / "docs" / "test-results"
CSV_OUT = OUT_DIR / "ukparliament-bench-modern.csv"
JSON_OUT = OUT_DIR / "ukparliament-bench-modern.json"


def write_outputs(records: list[dict], summary: dict, run_meta: dict) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
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
    payload = {"run": run_meta, "summary": summary, "results": records}
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
                    help=f"max seconds to wait for endpoint (default {DEFAULT_HEALTH_WAIT_S})")
    ap.add_argument("--query-root", default=str(MODERN_QUERY_ROOT),
                    help="root dir to scan for modernised .rq files")
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

    print(f"# bench_ukpar_modern.py")
    print(f"# endpoint     : {args.endpoint}")
    print(f"# query root   : {query_root}")
    print(f"# query count  : {len(queries)}")
    print(f"# per-q timeout: {args.timeout}s")
    print(f"# health wait  : {args.health_wait}s")

    if args.no_health_check:
        print("# health-check skipped (--no-health-check)")
        ready, health_msg = True, "skipped"
    else:
        print(f"# probing endpoint readiness ...")
        ready, health_msg = wait_for_endpoint(args.endpoint, args.health_wait)
        print(f"# endpoint    : {health_msg}")

    if not ready:
        print(f"FATAL: endpoint not reachable", file=sys.stderr)
        run_meta = {
            "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "endpoint": args.endpoint,
            "query_root": str(query_root),
            "query_count": len(queries),
            "per_query_timeout_s": args.timeout,
            "health_wait_s": args.health_wait,
            "endpoint_status": health_msg,
        }
        write_outputs([], {"ok": 0, "error": 0, "timeout": 0,
                            "rows_gt_zero": 0, "total_wallclock_ms": 0,
                            "slowest": None, "endpoint_unreachable": True},
                       run_meta)
        return 3

    run_started = datetime.now(timezone.utc)
    records: list[dict] = []
    bench_t0 = time.perf_counter()
    for i, qp in enumerate(queries, 1):
        rel = qp.relative_to(REPO_ROOT)
        print(f"[{i:>2}/{len(queries)}] {rel} ...", end="", flush=True)
        rec = run_one(args.endpoint, qp, args.timeout)
        records.append(rec)
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

    n_ok = sum(1 for r in records if r["status"] == "OK")
    n_err = sum(1 for r in records if r["status"] in ("ERROR", "PARSE_ERROR"))
    n_timeout = sum(1 for r in records if r["status"] == "TIMEOUT")
    # New summary metric: how many SELECT queries returned rows>0,
    # plus how many ASK queries returned (any boolean is "answered").
    n_rows_gt0 = sum(
        1 for r in records
        if r["status"] == "OK" and (
            (r["kind"] == "select" and (r.get("rows") or 0) > 0)
            or r["kind"] == "ask"
        )
    )
    avg_wallclock = (
        sum((r["wallclock_ms"] or 0.0) for r in records) / max(len(records), 1)
    )
    slowest = max(records, key=lambda r: r["wallclock_ms"] or 0.0, default=None)

    summary = {
        "ok": n_ok,
        "error": n_err,
        "timeout": n_timeout,
        "rows_gt_zero": n_rows_gt0,
        "total_wallclock_ms": round(total_wallclock_ms, 2),
        "total_wallclock_s": round(total_wallclock_ms / 1000.0, 2),
        "avg_wallclock_ms": round(avg_wallclock, 2),
        "slowest": (
            {
                "name": slowest["name"], "path": slowest["path"],
                "wallclock_ms": slowest["wallclock_ms"],
                "rows": slowest["rows"], "status": slowest["status"],
            } if slowest else None
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
    print(f"# {len(records)} queries: {n_ok} OK ({n_rows_gt0} with rows>0), "
          f"{n_err} error, {n_timeout} timeout; "
          f"avg {summary['avg_wallclock_ms']:.1f} ms, "
          f"total {summary['total_wallclock_s']:.2f} s")
    if slowest is not None:
        print(f"# slowest = {slowest['name']} ({slowest['wallclock_ms']:.1f} ms, "
              f"{slowest['status']}, rows={slowest.get('rows')})")
    print(f"# wrote {CSV_OUT.relative_to(REPO_ROOT)}")
    print(f"# wrote {JSON_OUT.relative_to(REPO_ROOT)}")
    if n_ok == 0:
        return 4
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
