# COTTAS Native Backend Notes

> **Status note (2026-04-19):** `Parquet.Footer.fst` in F\* is the real
> metadata + DeltaLengthByteArray value decoder behind the COTTAS runtime
> glue — audit in
> [`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md). The
> stack is currently not wired into `build-ocaml.sh` on `claude/main`;
> restore/extend plan is
> [`2026-04-19-cottas-parquet-wiring-plan.md`](2026-04-19-cottas-parquet-wiring-plan.md).

This note records the current native-F* direction for a COTTAS-style backend.

## Focus

Unlike plain HDT, COTTAS is attractive because it is dataset-native:

- quads, not just triples
- named graphs as first-class data
- columnar / Parquet-friendly physical structure

For Factoidal this is strategically important because the corpus model is not
one giant undifferentiated graph. We care about:

- many named graphs
- selective dataset assembly
- graph-level pruning
- future analytical and SQL-friendly storage paths

## Native Position

The source of truth should still be ours.

That means:

- do not make `pycottas` the semantic core
- do not let external runtime code define the dataset model for us
- do define the dataset/backend boundary in F*

The current native module for that is:

- [`Parser.BallyhooCOTTAS.fst`](/home/danbri/working/sandbox/foaf25/codex/factoidal/formal/fstar/Parser.BallyhooCOTTAS.fst)

## Current Model

The module captures:

- column summaries
- dictionary summaries
- row-group summaries
- dataset store handle
- named graph store handle
- quad-pattern search / estimate
- graph-name encode / decode

This is enough to treat COTTAS as a real backend target in the architecture,
even though a binary reader is not implemented yet.

## Relationship To HDT / HDTQ

We are **not** dropping HDT or HDTQ.

The likely storage family is now:

- HDT for graph assets
- HDTQ-style dataset-aware compressed structures
- COTTAS-style columnar quad storage
- SQL-backed stores

Those should all live under the same SPARQL/store seam.

## Why COTTAS Matters

Compared with plain HDT-per-graph plus manifest stitching, a COTTAS-like
backend offers a more natural home for:

- quad-native persistence
- large named-graph corpora
- future Parquet / analytical tooling
- SQL-friendly dataset access patterns

That makes it a plausible priority backend for the dataset side of Factoidal.

## Next Steps

1. Verify and extract `Parser.BallyhooCOTTAS.fst`.
2. Add it to the build pipeline.
3. Generalize dataset backend notes so HDTQ and COTTAS are peer native targets.
4. Later, decide whether to parse Parquet/container metadata directly in F* or
   to define a narrower intermediate columnar quad format first.
