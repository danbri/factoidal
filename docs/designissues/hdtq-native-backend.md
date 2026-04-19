# HDTQ Native Backend Notes

> **Status note (2026-04-19):** as of this audit, no F\* binary reader exists
> for HDT or HDTQ — the modules fix the interface only. See
> [`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md) for what
> is and isn't in F\* today.

This note records the current native-F* direction for HDTQ-style quad storage.

## Why

Plain HDT is a good fit for read-mostly RDF graphs, but it is not a natural
home for dataset semantics when named graphs matter.

For Factoidal, named graphs are not a cosmetic feature. They are units of:

- storage
- provenance
- corpus selection
- query routing
- trust / policy

So the dataset backend should not depend on pretending quads are an afterthought.

## Current Direction

The new module:

- [`Parser.BallyhooHDTQ.fst`](/home/danbri/working/sandbox/foaf25/codex/factoidal/formal/fstar/Parser.BallyhooHDTQ.fst)

defines the native F* representation for an HDTQ-style backend.

It does **not** yet implement a binary reader. What it does fix is the intended
semantic boundary:

- dataset store handle
- graph dictionary summary
- quad-info summary
- graph-name encoding / decoding
- quad-pattern search and estimate
- named-graph candidate selection

This keeps the SPARQL dataset semantics in F* while leaving the eventual
physical implementation open.

## Data Model

The current model reflects the broad HDTQ picture:

- HDT-like shared term dictionary and triple structures
- graph dictionary for named graph identities
- quad information layer

Two annotation modes are represented:

- `HQ_AnnotatedGraphs`
- `HQ_AnnotatedTriples`

Those are enough to capture the key design fork without forcing a specific
on-disk layout yet.

## Why This Matters

This lets us target dataset-native backends without immediately deciding that:

- plain per-graph HDT is the only answer
- Parquet-style quad batches are the only answer
- SQL is the only answer

Instead, the SPARQL layer can ask for:

- quad-pattern search
- graph-name encoding / decoding
- graph-level pruning

and later bind that to:

- native HDTQ-style files
- Parquet-like dataset artifacts
- SQL-backed dataset stores

## Immediate Constraints

- No external HDTQ engine becomes the semantic source of truth.
- No claim is made yet that the binary format is implemented.
- The main goal tonight is to make HDTQ a real native target in the F* design,
  not another vague future note.

## Next Steps

1. Verify and extract `Parser.BallyhooHDTQ.fst`.
2. Add it to the build pipeline next to `Parser.BallyhooHDT.fst`.
3. Extend the dataset backend note so HDTQ, Parquet-like, and SQL backends all
   sit under the same seam.
4. Later, choose a smallest useful binary subset to parse directly in F*:
   likely container/header plus graph dictionary metadata first.
