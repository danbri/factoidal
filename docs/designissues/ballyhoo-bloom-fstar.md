# Ballyhoo Bloom in F*

The Bloom sidecar story is no longer only Python/runtime glue.

New module:

- [`Parser.BallyhooBloom.fst`](/home/danbri/working/sandbox/foaf25/codex/factoidal/formal/fstar/Parser.BallyhooBloom.fst)

Current scope:

- F* representation of predicate Bloom filters
- deterministic hash/position generation
- insert
- membership test
- OR-rollup/union for compatible filters

This is intentionally smaller than a full sidecar file parser. The immediate
goal is to make the in-memory Bloom structures and utility logic ours, in F*,
so they can be used alongside HDT-backed stores and later in purely in-memory
corpus/index experiments.

Short-term split:

- Python still generates the current `graph.bloom.pred.json` and
  `graph.bloom.pred.bin` sidecars
- OCaml runtime glue still consumes those sidecars on the HDT path
- F* now owns the Bloom data structure model and core operations

Next obvious extensions:

- fixed-size sidecar byte representation in F*
- sidecar parsing/serialization
- subset/bundle Bloom summaries under corpus TOC areas
- use the same structure for in-memory ephemeral corpus pruning, not only
  on-disk HDT artifacts
