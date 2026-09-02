#!/usr/bin/env python3
"""Same-host pyoxigraph baseline for the gene-corpus competitive queries.

Runs q4_two_pattern_join and q2_bound_predicate_count from
docs/test-results/competitive-bench.json against pyoxigraph (in-memory)
on examples/wikidata/subsets/lifesci-kgx/data/gene.ttl, reporting load
time and warm medians. Purpose: a locally reproducible external baseline
to place next to the Shardborough SBM5 numbers from
tools/blockengine-ibk3-query-benchmark.sh, measured on the SAME machine.

Needs: python3 with pyoxigraph (`pip install pyoxigraph`). The script
refuses to run rather than substitute an engine if pyoxigraph is absent.

First measured 2026-08-31 on the owner's MacBook Air (arm64):
pyoxigraph 0.5.10 load 1.04s (888,949 triples);
q4 join warm median 0.257s (14 rows); q2 COUNT warm median 0.081s.
Same query, same corpus, SBM5 activated generation (OS-warm): 0.08s.
"""
import pathlib
import statistics
import sys
import time

try:
    import pyoxigraph as ox
except ImportError:
    sys.stderr.write("pyoxigraph is not installed; pip install pyoxigraph\n")
    sys.exit(2)

REPO = pathlib.Path(__file__).resolve().parent.parent
GENE = REPO / "examples/wikidata/subsets/lifesci-kgx/data/gene.ttl"
QUERIES = {
    "q4_two_pattern_join": (
        "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
        "SELECT ?s ?o1 ?o2 WHERE { ?s wdt:P684 ?o1 . ?s wdt:P682 ?o2 }"
    ),
    "q2_bound_predicate_count": (
        "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
        "SELECT (COUNT(*) AS ?n) WHERE { ?s wdt:P684 ?o }"
    ),
}


def main() -> int:
    if not GENE.exists():
        sys.stderr.write(f"corpus missing: {GENE}\n")
        return 2
    store = ox.Store()
    started = time.perf_counter()
    store.load(path=str(GENE), format=ox.RdfFormat.TURTLE)
    load_s = time.perf_counter() - started
    print(f"pyoxigraph {ox.__version__} load {load_s:.3f}s triples={len(store)}")
    for name, query in QUERIES.items():
        runs = []
        rows = 0
        for _ in range(5):
            started = time.perf_counter()
            rows = len(list(store.query(query)))
            runs.append(time.perf_counter() - started)
        print(
            f"{name}: rows={rows} warm_median={statistics.median(runs):.4f}s "
            f"runs={[round(r, 4) for r in runs]}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
