#!/usr/bin/env python3
"""Results-table generator for docs/test-results/competitive-bench.json.

Rerunnable: `python3 tools/bench_competitive_report.py` regenerates the
markdown tables from whatever JSON currently sits at
docs/test-results/competitive-bench.json (or --input), so the
narrative doc (docs/designissues/2026-07-06-competitive-benchmark-
results.md) can quote a table without hand-transcribing numbers.
This script only formats; it does not re-run anything or interpret
results -- see that doc for the "honest read" analysis.
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def fmt_s(x):
    if x is None:
        return "SKIP"
    if x < 1:
        return f"{x * 1000:.0f} ms"
    return f"{x:.2f} s"


def fmt_rss(kb):
    if kb is None:
        return "SKIP"
    return f"{kb / 1024:.0f} MiB"


def load_table(doc):
    rows = doc["load"]
    lines = []
    lines.append("| Engine | Corpus | Wall (median of runs) | Peak RSS (median) | Runs ok | Note |")
    lines.append("|---|---|---:|---:|---:|---|")
    for r in rows:
        # Two schemas coexist here: the 3-run LOAD rows (load_*() helpers
        # in bench_competitive.py, via summarize_load_runs()) carry
        # wall_s_median/peak_rss_kb_median/n_ok/n_runs; the single-run
        # cottas-import row (import_factoidal_cottas(), deliberately not
        # median-of-3 -- see its docstring) carries plain wall_s/
        # peak_rss_kb/n_runs=1 instead. Fall back rather than mislabel a
        # real 129s/1.7GB measurement as SKIP.
        wall = fmt_s(r.get("wall_s_median", r.get("wall_s")))
        rss = fmt_rss(r.get("peak_rss_kb_median", r.get("peak_rss_kb")))
        n_runs = r.get("n_runs", "?")
        n_ok = r.get("n_ok", 1 if r.get("wall_s") is not None else 0)
        ok = f"{n_ok}/{n_runs}"
        note = r.get("method", "") or r.get("note", "")
        timed = " (TIMED OUT)" if r.get("any_timed_out") or r.get("timed_out") else ""
        lines.append(f"| {r['engine']} | {r['corpus']} | {wall}{timed} | {rss} | {ok} | {note} |")
    return "\n".join(lines)


def query_table(doc):
    rows = doc["query_results"]
    lines = []
    lines.append("| Engine | Query | Cold | Warm (median of 3) | Rows | Answer hash |")
    lines.append("|---|---|---:|---:|---:|---|")
    for r in rows:
        cold = fmt_s(r.get("cold_s"))
        warm = fmt_s(r.get("warm_s_median"))
        rowcount = r.get("row_count", "SKIP")
        ahash = r.get("answer_sha256", "-")
        skip = r.get("skip_reason")
        note = f" SKIP: {skip}" if skip else ""
        lines.append(f"| {r['engine']} | {r['query']} | {cold} | {warm} | {rowcount} | {ahash}{note} |")
    return "\n".join(lines)


def agreement_table(doc):
    rows = doc["agreement"]
    lines = []
    lines.append("| Query | Engines compared | Agree? | Mismatching engines |")
    lines.append("|---|---|---|---|")
    for r in rows:
        engines = ", ".join(r.get("engines_compared", []))
        agree = "yes" if r.get("agree") else "**NO -- VOID**"
        mism = ", ".join(r.get("mismatches", [])) or "-"
        lines.append(f"| {r['query']} | {engines} | {agree} | {mism} |")
    return "\n".join(lines)


def engines_table(doc):
    lines = ["| Engine | Available | Version / detail |", "|---|---|---|"]
    for name, info in doc["engines"].items():
        avail = "yes" if info.get("available") else "no"
        detail = info.get("version") or info.get("reason", "")
        lines.append(f"| {name} | {avail} | {detail} |")
    return "\n".join(lines)


def corpora_table(doc):
    lines = ["| Corpus | Path | Bytes |", "|---|---|---:|"]
    for name, info in doc["corpora"].items():
        lines.append(f"| {name} | `{info['path']}` | {info['bytes']:,} |")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default=str(ROOT / "docs/test-results/competitive-bench.json"))
    ap.add_argument("--section", choices=["all", "engines", "corpora", "load", "query", "agreement"], default="all")
    args = ap.parse_args()

    doc = json.loads(Path(args.input).read_text())

    sections = {
        "engines": ("### Engines detected", engines_table),
        "corpora": ("### Corpora", corpora_table),
        "load": ("### LOAD phase", load_table),
        "query": ("### QUERY phase (gene corpus)", query_table),
        "agreement": ("### Cross-engine answer agreement", agreement_table),
    }

    if args.section == "all":
        for _, (title, fn) in sections.items():
            print(title)
            print()
            print(fn(doc))
            print()
    else:
        title, fn = sections[args.section]
        print(title)
        print()
        print(fn(doc))
    return 0


if __name__ == "__main__":
    sys.exit(main())
