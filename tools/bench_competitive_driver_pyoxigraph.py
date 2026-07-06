#!/usr/bin/env python3
"""Driver invoked as its own subprocess by tools/bench_competitive.py.

Loads one corpus into a pyoxigraph in-memory Store once, then runs
every query in --queries-json cold (1x) + warm (3x), emitting one JSON
document to stdout. Kept as a standalone script (not an in-process
import) so the harness can wrap it in `timeout N` and measure the
whole engine run's wall time / peak RSS the same way it does for the
CLI-based engines.
"""
import argparse
import json
import resource
import sys
import time

import pyoxigraph as ox

FORMAT_BY_EXT = {
    ".ttl": ox.RdfFormat.TURTLE,
    ".nt": ox.RdfFormat.N_TRIPLES,
    ".nq": ox.RdfFormat.N_QUADS,
    ".trig": ox.RdfFormat.TRIG,
}


def rows_to_comparable(solutions):
    """solutions: a pyoxigraph QuerySolutions (iterable of QuerySolution,
    with .variables giving the ordered Variable list -- QuerySolution
    itself has no .variables, so this must be read off the parent)."""
    varnames = [v.value for v in solutions.variables]
    out = []
    for row in solutions:
        rec = {}
        for name in varnames:
            val = row[name]
            # .value gives the bare lexical form for NamedNode/Literal/
            # BlankNode alike (no "<...>" wrapping, no ^^datatype/@lang
            # suffix) -- matched to rdflib's str() and Jena's CSV cells
            # by bench_competitive.py's canonicalize_term as a second
            # line of defense, but already bare here.
            rec[name] = None if val is None else val.value
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
    fmt = FORMAT_BY_EXT.get(ext, ox.RdfFormat.TURTLE)

    store = ox.Store()
    t0 = time.perf_counter()
    with open(args.corpus, "rb") as f:
        store.load(f, format=fmt)
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
        cold_rows = rows_to_comparable(store.query(sparql))
        cold_s = time.perf_counter() - cold_t0

        warm_times = []
        for _ in range(args.warm_runs):
            t1 = time.perf_counter()
            rows_to_comparable(store.query(sparql))
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
