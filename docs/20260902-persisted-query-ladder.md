# Persisted query ladder — 2026-09-02

Owner goal, 2026-09-02, verbatim: "Performant standards-compliant formally
verifiable e2e RDF/SPARQL MVP, showing snappy searches against increasingly
large dataset converted to Shardborough formed rdf indexed data."

This note is the measurement record for that goal on the persisted path
(`l4block-shard-pack` → `l4block-shard-activate` → `l4block-id-v3-query`,
see [`skills/shardborough-storage`](../skills/shardborough-storage/SKILL.md)).
Every number is a single cold run on one laptop (Apple M-series, macOS,
`formal/lean4` native build) unless a column says otherwise; timings are
wall-clock for the whole process, including manifest read, Merkle
verification, decoding and result printing. Rows are counted by the CLI.

## Rung 2: gene.ttl, 888,949 triples

| Step | Result |
| --- | --- |
| Source | `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`, 17,363,312 bytes |
| Pack (`ibk3`) | 13 blocks, 105.8 s while a WASM build competed for CPU (2026-08-31 baseline: 72 s on the IBK2 publisher) |
| Generation on disk | 50 MB (blocks, PTD1 dictionaries, SRI2/OLI2/TLI1 sidecars, Merkle leaves) |
| Largest predicate | P684, 759,263 rows across five blocks (36,056 / 180,667 / 251,148 / 256,698 / 34,694) |

### Query workload

The six competitive-bench queries (`docs/test-results/competitive-bench.json`)
plus a bounded scan and an object-bound lookup.

| # | Query shape | Rows | Before (17:30) | After planner fixes (19:40) | Open mode after |
| --- | --- | --- | --- | --- | --- |
| q1 | `COUNT(*)` over everything | 1 | 12.5 s | 6.3 s (quiet machine; same path) | full manifest, 13 blocks |
| q2 | `COUNT` of P684 (759,263 rows) | 1 | 1.95 s | 1.28 s (same path) | per-predicate count |
| q3 | subject point lookup, unbound predicate: `wd:Q100085837 ?p ?o` | 3 | 10.0 s | **0.23 s** | TLI1/SRI2 subject point, 13 entries |
| q4 | two-pattern join P684/P682 | 14 | 0.17 s | 0.11 s | SRI2/TLI1 subject join |
| q5 | `GROUP BY ?p` with counts | 6 | 2.4 s | 1.55 s (same path) | per-predicate counts |
| q6 | `?s P1057 ?o1 . OPTIONAL { ?s P688 ?o2 } FILTER(isIRI(?o1))` | 25,083 | 31.8 s | **17.6 s** | 2 blocks; LeftJoin on the reference evaluator |
| s1 | `?s P684 ?o LIMIT 10` | 10 | 0.66 s | 0.03 s | bounded prefix scan |
| o1 | `?s P682 wd:Q14860489` | 0 | 0.05 s | 0.01 s | OLI2 object scan |

The "before" column was measured while a WASM build competed for CPU; the
two columns are therefore comparable only where the open mode changed (q3,
q6). Every query returns the same row count and the same preview rows in
both columns. q3's bytes read fell from 24.9 MB to 0.24 MB logical; q6's
from 24.9 MB to 2.7 MB.

Reference points from the same store: the plain join `?s P1057 ?o1 . ?s P688 ?o2`
returns 9,117 rows in 2.4 s through the subject-join path (4 shards,
3.0 MB read); `?s P1057 ?o1` alone returns 25,058 rows in 0.54 s.

### Diagnoses

- **q3, q6: planning, not engine.** Both fall to the full-manifest path.
  For q3 the harness had no selective path for an unbound predicate, although
  every block carries a TLI1 term index and SRI2 subject postings that the
  join path already uses. For q6 the constant-predicate collector
  (`ShardManifest.nativeConstantPredicates?`) refused OPTIONAL, so the
  planner read all 13 blocks (24.9 MB) and evaluated over 888,949 triples;
  the same two predicates as a plain join read 4 shards.
- **q1, and every full-manifest read: Merkle verification in pure Lean.**
  The profile of q3 before the fix is dominated by `BlockMerkle.nextLevel`,
  `Crypto.sha256`, `processBlocks256` and `sha256CompressBlock`: SHA-256 in
  pure Lean at roughly 5 MB/s over 25 MB, before any decoding. HACL*'s
  SHA-256 is already vendored and linked for the Ed25519 family
  (`third_party/hacl/src/Hacl_Hash_SHA2.c`, native and WASM), so a host-side
  hasher realised by HACL* is available under the crypto policy; the pure
  Lean `sha256` stays the specification because build-time `#guard`s run in
  the interpreter, which cannot call an extern.
- **The evaluator's physical plan has no OPTIONAL arm.** Once q6 reads only
  its two predicates, the LeftJoin still runs on the reference evaluator over
  the fragment. A native LeftJoin arm with its refinement proof is the next
  engine-side step (`L4Factoidal/SPARQL/StoreDataset.lean`).

## Status

- Planner fixes for q3 and q6: landed (commit 82d2f530e; the "after" column
  above). The worker that measured them also found, through
  `tools/w3c-persisted-census.sh`, that FILTER NOT EXISTS answered zero rows
  in the WASM and CLI query path since the morning's backend routing change;
  fixed the same day with pins in `native-smoke.sh`, `StoreDataset.lean` and
  `tests/hub/l4_exists_regression_test.mjs`. Census after the fix: 535
  executed, 0 refused (out of 535 eligible), the recorded 2026-09-01 numbers.
- HACL* SHA-256 hasher for the host verification path: landed. The pure
  Lean `sha256` stays the specification; the host passes a HACL*-backed
  `Hasher` into the Merkle and artifact functions, and `lake exe l4vc-probe`
  checks the two agree on the FIPS vectors, the block boundaries and a 1 MiB
  buffer (13 pass, 0 fail), as a required CI step. Measured on the gene
  store, single runs, hasher the only difference:

  | Operation | Pure Lean hasher | HACL* hasher |
  | --- | --- | --- |
  | `COUNT(*)` over the whole store (full-manifest read) | 7.49 s | 3.94 s |
  | `l4block-shard-activate` of the 25 MB generation | 52.95 s | 13.81 s |
  | `l4block-shard-pack chromosome.ttl` | 1.01 s | 0.72 s |

  Block bytes are unchanged (the chromosome block keeps sha256 01484578…).
  What remains in a full read is decoding and index building, not hashing.
- LeftJoin physical arm with refinement proof: queued.
- Rung 3 (UK Parliament TriG, 347 MB, named graphs): blocked on the
  quad-aware layout (spec section 10, gate 4); the packer reads Turtle only.
