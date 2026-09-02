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

## Rung 2.5: the whole life-science extract, 1,290,077 triples

All twelve Turtle files of `examples/wikidata/subsets/lifesci-kgx/data/`
concatenated (31,603,120 bytes), through the same path, measured 22:25 with
nothing else running.

| Step | Result |
| --- | --- |
| Pack (`ibk3`) | 52 blocks over 26 predicates, 35.8 s (36,000 triples/s) |
| Activate | 50,744,391 logical bytes verified, 45.5 s |
| Generation on disk | 103 MB |

| # | Query shape | Time | Path |
| --- | --- | --- | --- |
| q1 | `COUNT(*)` over everything | 10.3 s | full read of 52 blocks (50.7 MB) |
| q3 | subject point lookup, unbound predicate | 0.20 s | TLI1/SRI2 probe of all 52 blocks |
| q4 | two-pattern join P684/P682 | 0.05 s | subject join, 6 shards |
| q5 | `GROUP BY ?p` with counts | 0.66 s | per-predicate counts, 52 blocks |
| q6 | OPTIONAL + FILTER | 0.36 s | 2 predicates, 6 shards, hash LeftJoin |
| s1 | `?s P684 ?o LIMIT 10` | 0.02 s | bounded prefix scan |

The selective paths scale with the number of blocks probed (q3: 13 to 52
blocks, 0.12 s to 0.20 s), not with the triple count. The two costs that
scale with bytes are activation (one full verification and index
recomputation per generation, 45 s for 51 MB) and the whole-store count.

## Rung 3: the UK Parliament dump, 3,143,406 triples

`third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig`, 346,861,556
bytes, 5,325,830 lines, one unlabelled graph block (the TriG default graph).
Converted to Turtle by dropping the two brace lines; packed with the same
command as the rungs above. The content is dominated by e-petition signature
counts (four predicates hold 2.2 million of the 3.1 million triples); the
procedure-browser vocabulary the sample queries use is almost absent (29
`:name` triples, 405 typed entities), so the sample queries answer zero or
few rows, correctly: the F* engine's recorded bench shows no rows for the
same queries.

| Step | Result |
| --- | --- |
| Pack (`ibk3`) | 309 blocks over 232 predicates, 6,134 s (512 triples/s; 70× slower per triple than rung 2.5) |
| Activate | 356,214,197 logical bytes verified, 4,554 s (78 KB/s) |
| Generation on disk | 716 MB |

| Query (`third_party/data/ukparliament/sparql/main/`) | Time | Rows | Path |
| --- | --- | --- | --- |
| enabling-legislation listing (5 OPTIONALs) | 0.05 s | 0 | 1 shard, 8 predicates named |
| enabling-legislation first-letter counts (BIND, GROUP BY) | 1,125 s | 0 | full manifest, 309 blocks |
| legislatures, organisations, procedures, step collections, steps by type (6 queries) | 0.03 to 0.05 s | 0 or 1 | 1 to 2 shards |
| work packages current, count (MINUS with a property path) | 85 s | 1 | full manifest |
| work packages current, listing | 43 s | 0 | full manifest |

What this rung teaches:

- **Answers stay correct at 3 million triples**; the selective paths stay
  at tens of milliseconds even when a query names eight predicates.
- **Pack and activation are the bottleneck, and something in them is
  superlinear** in the number of predicates or blocks: rung 2.5 packed
  36,000 triples/s over 26 predicates, this rung 512 triples/s over 232.
  Activation at 78 KB/s is far below the HACL* hashing rate, so the cost is
  in index recomputation. Both need a profile before any design change.
- **The constant-predicate collector refuses BIND and property paths**, so
  two queries read all 309 blocks (356 MB) and evaluate on the reference
  path. BIND with a backend-local expression and a sequence or alternative
  path whose steps are constant IRIs are both collectable by the same
  argument the collector already relies on.

Findings from the first, failed attempt (2026-09-02, late):

- The first pack failed after 867 s with `Turtle parse error at 202943268:
  expected object`. Cause: the TriG-to-Turtle conversion used BSD `awk`,
  which stopped at about 203 MB on the 3.9 MB polygon line and truncated
  the file; the error position is the cut-off last statement. Not a parser
  defect. The conversion was redone in Python and the full pack repeated.
- The reference Turtle parser (`parseTurtle`, behind `l4factoidal parse` and
  the WASM `datasetOpen` Turtle path) is quadratic: 2,514 triples 0.38 s,
  5,012 triples 1.51 s, 10,012 triples 6.16 s. Two token readers compute
  their fuel as the length of the remaining character list once per token
  (`readTurtleString`, `readNumericLiteral`); the whitespace skipper had the
  same pattern removed earlier. The packer's chunked path bounds each chunk,
  which is why packing still runs at about 4 MB/s. FIXED 2026-09-02 late:
  the literal loops take the constant `literalFuel` (2^32) and the old
  per-token forms are kept as `readTurtleStringSpec` /
  `readNumericLiteralSpec`; `Syntax/TurtleFuelTheorems.lean` proves the
  loops fuel-independent above the remaining length and the constant-fuel
  readers equal to the specification forms for every input shorter than
  2^32 characters (axioms: propext, Classical.choice, Quot.sound only).
  After: 5,019 lines (2,734 triples) 0.30 s, 10,019 lines 0.37 s, 20,019
  lines 0.74 s — linear. Gates: W3C RDF 1.1 Turtle 313 pass and TriG 356
  pass, RDF 1.2 Turtle syntax 67 / eval 29, TriG syntax 35 / eval 25, all
  0 fail; native-smoke 63 pass (out of 63).
- The dump has a 3,875,112-character line (a `geosparql:wktLiteral` polygon)
  and 223 sibling polygon literals in one statement group. That group alone
  parses in 1.4 s and packs correctly, but the pack takes 57 s for 224
  triples: multi-megabyte literals go through the term codec, the PTD1
  pages, the TLI1 keys and the Merkle leaves several times each. A
  per-term size limit or a separate large-literal store is a design
  question for the corpus ladder, not a correctness problem.
- `l4block-shard-pack` on an empty input produced an empty generation that
  activated (recorded in the `shardborough-storage` skill).

### Where the 6,134 s went (2026-09-02, late): the statement scanner

Method. A size ladder of UK Parliament slices with no literal over 10 KB
(the first such literal is at line 1,702,684 of 5,360,986), each packed
and activated on an idle machine with the Turtle-fixed binary:

| Lines | Triples | Blocks | Pack | Activate | Pack per triple |
| --- | --- | --- | --- | --- | --- |
| 20,019 | 10,305 | 18 | 0.40 s | 0.46 s | 38 µs |
| 40,019 | 20,305 | 18 | 0.74 s | 0.87 s | 37 µs |
| 80,019 | 40,305 | 22 | 1.39 s | 1.59 s | 34 µs |
| 160,019 | 92,265 | 30 | 2.85 s | 3.22 s | 31 µs |
| 320,019 | 370,355 | 47 | 12.75 s | 15.87 s | 34 µs |

Linear in triples, and the block count (18 to 47) does not show. The gene
store on the same idle machine: 888,949 triples, 13 blocks, pack 11.5 s,
activate 13.4 s (13 µs per triple). So neither predicate count nor block
count explains the full dump's 1,950 µs per triple.

The remaining candidate was the region of large literals: 345 lines over
100 KB, 105 MB of the 341 MB file, all inside lines 1,702,684 to
1,706,891. Cut as one 134 MB Turtle file (4,211 lines, 3,560 triples), it
packed in 334 s with the committed binary — 100 s more than the whole
linear ladder above put together.

Cause. `Syntax/TurtleStatementScan.lean` decides at every line end in
normal mode whether the current candidate is a no-dot directive
(`PREFIX`, `BASE`, `VERSION`), and did so by reversing the whole
accumulated candidate (`dropWs currentRev.reverse`) to read its first
word. That is O(lines × characters) per statement group: the polygon group
has 4,211 lines and 134 MB, about 280 G list steps.

Fix. `StatementScan` now carries `head`, the first seven characters after
leading whitespace, maintained per character by `pushHead`; the directive
test reads it. The old form is kept as `directiveHeadSpec`, and
`Syntax/TurtleStatementScanTheorems.lean` proves `head = directiveHeadSpec
currentRev` for every run of the scanner from `init` (axioms: propext,
Classical.choice, Quot.sound only).

After, same region: pack 81 s, activate 109 s (both with another pack
running on the machine; re-measure idle). The remaining 81 s is the
reference parse (31 s for this file: 19 s user, 9 s system reading 134 MB
as a character list) plus the term codec, PTD1 pages, TLI1 keys and
Merkle leaves over 105 MB of literal bytes; the activate is four full
decodes per block (`ShardActivate.verify*` each decode the primary again)
over the same bytes. Those are the next two items for this rung, with the
large-literal policy question above.

Gates for the scanner change: all 378 artifacts of the 320,019-line slice
byte-identical between the old and new scanner; W3C RDF 1.1 Turtle 313 and
TriG 356, RDF 1.2 Turtle 67 + 29 and TriG 35 + 25, all 0 fail;
native-smoke 63 pass (out of 63); lake build 922 jobs. The scanner is used
only by `Harness/PredicateShardPack.lean`, so the WASM mirrors are
unchanged.

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
- LeftJoin physical arm with refinement proof: landed. `SPARQL.hashLeftJoin`
  buckets the right side once on the shared always-bound variables, and
  `hashLeftJoin_eq_leftJoin` (`SPARQL/IndexedEvalRefinement.lean`) proves it
  equal to the nested-loop `leftJoin` as a list, rows and order; the
  reference evaluator's OPTIONAL arm and a new backend arm (conditions in
  `Expr.backendLocal`) both use it, and the backend join arm now uses
  `hashJoin` (licensed by `hashJoin_eq_join`). Guards compare the backend
  runner with the reference on extending, unmatched and rejected OPTIONALs.

### Milestone table, 2026-09-02 evening

Single cold runs on the same store, everything of the day landed; a WASM
build was competing for CPU during these runs, so the quiet numbers are a
little lower (q1 measures 3.94 s quiet).

| # | Query shape | Rows | Morning | Evening | Path |
| --- | --- | --- | --- | --- | --- |
| q1 | `COUNT(*)` over everything | 1 | 12.5 s | 7.5 s (3.9 s quiet) | full read, 13 blocks, HACL* Merkle verification |
| q2 | `COUNT` of P684 (759,263 rows) | 1 | 1.95 s | 1.3 s | per-predicate count |
| q3 | subject point lookup, unbound predicate | 3 | 10.0 s | 0.12 s | TLI1/SRI2 subject point |
| q4 | two-pattern join P684/P682 | 14 | 0.17 s | 0.07 s | SRI2/TLI1 subject join, hash join |
| q5 | `GROUP BY ?p` with counts | 6 | 2.4 s | 0.62 s | per-predicate counts |
| q6 | `?s P1057 ?o1 . OPTIONAL { ?s P688 ?o2 } FILTER(isIRI(?o1))` | 25,083 | 31.8 s | 0.86 s | 2 blocks, hash LeftJoin on the backend arm |
| s1 | `?s P684 ?o LIMIT 10` | 10 | 0.66 s | 0.03 s | bounded prefix scan |
| o1 | `?s P682 wd:Q14860489` | 0 | 0.05 s | 0.01 s | OLI2 object scan |

Every row count and preview is unchanged from the morning. What backs the
numbers: the codecs' round-trip theorems (spec section 10.1), the hash
join and hash LeftJoin equalities, the backend-arm theorems, the encoder
admission equal to the decoder's, and the HACL* SHA-256 differential probe
in CI. What remains outside a theorem: the planner's choice of blocks
(argued in docstrings, checked by the census and the row-count comparisons)
and the extern hasher's agreement with the specification (checked by the
probe).
- Rung 3 (UK Parliament TriG, 347 MB, named graphs): blocked on the
  quad-aware layout (spec section 10, gate 4); the packer reads Turtle only.
