# Deterministic heterogeneous Shardborough fixture (2026-09-01)

The rung-1 heterogeneity fixture assigned in
[the Tuesday OKRs](20260901-blockengine-tuesday-okrs.md) item 3: one
small, checked-in, hand-written corpus plus a profiler and a
self-asserting end-to-end cycle. Everything below is measured output,
not intention.

## Files

- `formal/lean4/Harness/TestData/heterogeneous-fixture.ttl` — the
  corpus. Hand-written, no generator, 2,503 bytes,
  sha256 `c8988a56a4355c3354123901ba99c6cfbb0d798e513f6160146c6122357be0c1`.
- `tools/corpus-profile.sh` — profiler for any RDF file: bytes,
  SHA-256, parser-measured statement count, predicate histogram,
  object-kind histogram, literal datatype and language histograms.
  Parsing is `l4factoidal parse --out nquads`; the shell only counts
  engine-emitted fields (no hand-rolled RDF parsing).
- `tools/blockengine-heterogeneous-fixture-smoke.sh` — the asserted
  cycle: profile → pack (SBM6/IBK3) → activate → queries → durable
  INSERT/DELETE → compact → activate → re-query → fresh-epoch update.

## Measured profile

44 statements (parser-measured; `l4factoidal parse`). Predicate skew:
`ex:note` 17, `ex:name` 12, `ex:knows` 6, `ex:age` 5, `ex:homepage` 3,
`rare:seenAt` 1. Objects: 33 literals, 10 IRIs, 1 blank node.
Datatypes: `xsd:integer` 5, `xsd:decimal` 2, `xsd:double`,
`xsd:dateTime`, `xsd:date`, `xsd:boolean` 1 each. Language tags:
`@en` 4, `@fr` 2, `@es`, `@en-gb`, `@de` 1 each (the engine
canonically lowercases language tags on parse, so `@en-GB` in the
source is stored and queried as `@en-gb`; both spellings match).

## What the cycle asserts (all green, 2026-09-01)

- Skew: `COUNT` over the dominant predicate = 17; the rare one = 1.
- Language-tagged object lookups: `"Alicia"@es` → exactly `ex:alice`;
  `"Bob"@en` and `"Bob"@en-GB` are distinct terms, one row each.
- Term-identity sentinel: `"1"^^xsd:integer` selects only `ex:alice`
  and `"01"^^xsd:integer` only `ex:bob` — equal values, distinct
  terms; BGP object matching must stay term-level
  (`shardborough-storage-spec.md` §8 caveat, exercised).
- Shared-term join: `?a ex:knows ?b . ?b ex:knows ?c` = 6 rows.
- Object-bound IRI lookup through a shared term (`ex:hub`).
- Absent lookups: unknown subject, unknown literal (`@tlh`), unknown
  predicate — all empty/false, none an error.
- Durable update: INSERT + DELETE visible before compaction
  (name count 12 = 12 + Grace − Carol).
- Compaction folds the delta exactly:
  `base-triples=44 delta-batches=2 compacted-triples=44`; activation
  replaces `CURRENT`; all pre-compaction answers reproduce through
  the new generation; a post-compaction update lands in the fresh
  epoch and is visible.

## Reproduce

```sh
tools/corpus-profile.sh formal/lean4/Harness/TestData/heterogeneous-fixture.ttl
tools/blockengine-heterogeneous-fixture-smoke.sh
```

Both exit 0; the smoke prints
`blockengine-heterogeneous-fixture-smoke=pass`. Requires the Lean
CLIs built (`lake build l4block-shard-pack l4block-shard-activate
l4block-delta-log l4block-shard-compact l4block-id-v3-query
l4factoidal` from `formal/lean4/`).
