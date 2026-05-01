# A correct fast path on the wrong layer

**Status:** lessons-learned note, 2026-05-01
**Trigger:** PR #131 + #132 added a streaming-count-group-by-graph
fast path. Detector matches Q01, dispatcher routes correctly,
W3C clean — and Q01 wall time on the lifesci demo went from 137s to
137s. Identical.

## What happened

Q01: `SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }
GROUP BY ?g ORDER BY DESC(?n)`. The fast path replaces an O(43k row)
materialise-and-aggregate with O(3) `backend_estimate` calls. Per-call
saving: ~50s. Total saving in the eval phase: real. **But the eval
phase isn't where the time was going.**

Profile breakdown (eyeballed; no actual instrumented profile, so the
exact split is approximate):

| Phase | Time |
|---|---:|
| Read 3 .ttl files from disk | < 0.1 s |
| Parse 3 .ttl into rdf_graph | ~ 1 s |
| Build `indexed_dataset_backend` (= 6 bucket maps × N entries × O(N) `bucket_replace_acc`) | **~ 135 s** |
| Eval Q01 streaming-count fast path | ~ 0.1 s |
| Format 3-row table | < 0.001 s |

The fast path saved ~50s of materialise-and-aggregate that would have
cost something on top of the 135s, but the materialise path's eval
cost is amortised against the same indexes that were already built.
Net: the fast path is correct and useful but its expected speedup is
**zero on this corpus** because the dominant cost is upstream.

## The general lesson

**A fast path that delivers no wall-time win on the target query is
still correct — but you should know which layer's cost it eliminates
before you ship it.** Three checks before declaring a perf PR:

1. **Profile first.** If you don't know which layer dominates, you're
   guessing. The bench numbers told us native (137s) was *slower* than
   JS (53s), which is the loud signal that something other than the
   eval shape is going on. (JS doesn't go through `indexed_graph_backend`
   for the same reason — different code path.)
2. **Bound the fast path's possible win.** The maximum speedup is "all
   the work that the fast path replaces." If the displaced work is
   smaller than the rest of the pipeline, the fast path won't move
   wall time. We knew Q01 was a 43k-triple aggregate scan; we didn't
   know the bucket-build was 6× more expensive.
3. **Don't conflate "fires correctly" with "delivers the win."** The
   debug eprintf showed the detector matching Q01 — load-bearing
   evidence the dispatch is correct, NOT that the user-visible
   wall-clock will improve. Verify with timing.

## Bucket build is the real bottleneck

`RDF.Graph.Executable.fst:bucket_map = list (string * list triple)`,
backed by `bucket_replace_acc` doing a linear scan to find or insert
a key. Six such maps (S, P, O, SP, PO, SO) × per-graph. Insert cost
per triple = O(distinct keys so far). Total: O(N²) per index per graph.

For 27k subjects, ~360M list-cell walks. At ~100ns each ≈ 36s. Times
6 indexes ≈ ~135s. Matches.

## Two ways out

1. **In-memory COTTAS encoder** (design note: `in-memory-cottas-encoder.md`).
   Bypass `indexed_graph_backend` entirely; serialise to in-RAM COTTAS
   bytes; reuse the F\*-verified COTTAS read path which already has
   O(1) num_rows in the parquet footer. Same fast path, different byte
   source. PR #133 lands the scaffold; Phase A.5 is the unlock. Best
   for the demo because it gets all the F\*-verified indexing for free.

2. **Replace `bucket_map` with a hash structure.** Whole-file refactor
   in `RDF.Graph.Executable.fst` plus proof updates for everything
   that reasons about it (RDFS closure, OWL-RL closure, model-theory
   equivalence, all `find_*` / `add_triple_to_indexes`). Higher blast
   radius. Better long-term because it helps all queries against
   in-memory data, not just COTTAS-eligible shapes.

For now: option 1 is in flight (PR #133). Option 2 is a separate
larger investigation.

## What we should remember

- **Native isn't always faster than JS.** When native is slower,
  there's a code-path divergence; that's a signal worth chasing
  before declaring native the optimisation target.
- **Fast paths are layer-local.** A correct fast path at the eval
  layer can be entirely shadowed by a slower upstream layer. The
  wall-clock attribution test is harsh but fair.
- **The streaming-count-group detector is still the right shape.**
  When the upstream (in-memory COTTAS encoder OR hash bucket_map)
  lands, the existing fast path will deliver the win automatically.
  PRs #131 + #132 + #133 are the foundation.
