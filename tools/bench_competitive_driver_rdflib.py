#!/usr/bin/env python3
"""Driver invoked as its own subprocess by tools/bench_competitive.py.

Same contract as bench_competitive_driver_pyoxigraph.py, backed by
rdflib instead -- the "floor" baseline per the task brief (pure-Python
RDF store, no query planner beyond rdflib's own).
"""
import argparse
import json
import resource
import sys
import time

from rdflib import Graph

FORMAT_BY_EXT = {
    ".ttl": "turtle",
    ".nt": "nt",
    ".nq": "nquads",
    ".trig": "trig",
}


def rows_to_comparable(rows, varnames):
    out = []
    for row in rows:
        rec = {}
        for name in varnames:
            val = row[name] if name in row.labels else None
            rec[name] = None if val is None else str(val)
        out.append(rec)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--queries-json", required=True, help="JSON: {id: sparql}")
    ap.add_argument("--warm-runs", type=int, default=3)
    ap.add_argument("--load-only", action="store_true",
                     help="load the corpus, report load_s/load_peak_rss_kb, run no queries")
    args = ap.parse_args()

    ext = "." + args.corpus.rsplit(".", 1)[-1]
    fmt = FORMAT_BY_EXT.get(ext, "turtle")

    g = Graph()
    t0 = time.perf_counter()
    g.parse(args.corpus, format=fmt)
    load_s = time.perf_counter() - t0
    load_rss_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss

    if args.load_only:
        print(json.dumps({"load_s": load_s, "load_peak_rss_kb": load_rss_kb}))
        return 0

    queries = json.loads(args.queries_json)
    result = {
        "load_s": load_s,
        "load_peak_rss_kb": load_rss_kb,
        "queries": {},
    }

    for qid, sparql in queries.items():
        cold_t0 = time.perf_counter()
        cold_res = g.query(sparql)
        varnames = [str(v) for v in cold_res.vars] if cold_res.vars else []
        cold_rows = rows_to_comparable(list(cold_res), varnames)
        cold_s = time.perf_counter() - cold_t0

        warm_times = []
        for _ in range(args.warm_runs):
            t1 = time.perf_counter()
            list(g.query(sparql))
            warm_times.append(time.perf_counter() - t1)

        result["queries"][qid] = {
            "cold_s": cold_s,
            "warm_s_runs": warm_times,
            "row_count": len(cold_rows),
            "rows": cold_rows,
        }

    result["final_peak_rss_kb"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
