# Repository review — 2026-08-31

Snapshot: commit `e5c7ac954` ("fsync durable delta log appends"), branch
`claude/main`, reviewed 2026-08-31 06:00–08:00 UTC+1. The tree moved
during the review: three delta-log commits landed between 06:30 and
06:41 while it ran. Findings are pinned to `e5c7ac954` unless dated
otherwise. Method notes are inline; every score is labelled.

Scope requested: completeness, integrity, performance, standards
compatibility, architecture, Lean usage — with attention to the
Shardborough persistent storage layer. Cross-checked against the Codex
update gist of 2026-08-31.

## Result summary

- 🔴→✅ **The Lean library at the reviewed commit did not build.**
  `lake build` failed in
  `formal/lean4/L4Factoidal/Syntax/TurtleTheorems.lean:299`. Commit
  `f83dc599f` ("Parse Turtle incrementally across decoded chunks",
  2026-08-31 02:26) changed `maxUnderscoreRun` to a state-machine form.
  The theorem `maxUnderscoreRun_ge_best` still unfolded the old
  definition; its proof failed and elaborated to `sorryAx`.
  **Repaired at 07:06 by `009f2ab53`** with a new
  `UnderscoreRun.longest_le_feedChars` lemma; re-verified after that
  commit — the module builds.
- 🔴→✅ **No CI gate built the Lean tree** at the reviewed commit. No
  workflow ran `lake` or `elan`, so the no-sorry policy for the
  intended full-scope engine was enforced only by local builds. That
  is how the broken proof reached the shared branch. **Commit
  `009f2ab53` added `.github/workflows/verify-lean4.yml`** (a
  `lake build` gate); its first green run on GitHub Actions has not
  been observed yet.
- 🔴 **The F\* W3C SPARQL comparator is lenient.**
  `bin/w3c-runner/w3c_runner.ml:744,751` checks that each expected
  binding is present in the actual row. It does not reject extra
  bindings. At least six named evaluator bugs pass as green (detail in
  § Standards). "631 pass, 0 fail (out of 631)" is a manifest-gate
  result, not an exact-bindings result.
- ⚠️ **Shardborough has one real correctness theorem and many
  spot-checks.** `mergeOnRead_matches_applyEntries` (the UPDATE
  overlay) is fully proved. The wire formats IBK1, IBK2, PTD1,
  SBM0/1/2 carry zero theorems; their "canonical bytes" claim rests on
  a few `#guard` fixtures.
- ⚠️ **No W3C conformance test exercises the disk-backed query path.**
  All SPARQL conformance, in both trees, runs against the in-memory
  engine only.
- ⚠️ **PostgreSQL persistence is a smoke script, not an adapter.**
  There is no PostgreSQL client code in Lean. Four bash scripts round-
  trip bytes through `bytea` using `pg_read_binary_file()`. TiKV does
  not exist yet.
- 📊 Where the Lean engine is measured, it matches the F\* tree on the
  RDF 1.1/1.2 and SPARQL 1.1 suites and is behind on OWL 2, ShEx,
  rdf-semantics, and RIF Core (numbers in § Standards).
- 🧹 `.git` is 19.6 GiB. 899 of 5,141 commits are automated artifact
  commits. The repo root carries stale untracked material, including
  two full nested clones under `tmp-codex/`.

## 1. Integrity

### 1.1 Build state

`lake build` in `formal/lean4` fails at HEAD:

- `L4Factoidal/Syntax/TurtleTheorems.lean:299` — `omega` cannot close
  the goal; `:303` — `split` fails. The axiom audit at line 325 prints
  `maxUnderscoreRun_ge_best depends on axioms: [sorryAx]`.
- Cause: `f83dc599f` refactored `maxUnderscoreRun`
  (`L4Factoidal/Syntax/Turtle.lean:166-172`) into
  `UnderscoreRun.feedChars` without repairing the theorem. The theorem
  file was not touched by that commit.
- Update, 07:06: commit `009f2ab53` repaired the proof (new lemma
  `UnderscoreRun.longest_le_feedChars`, stated over the streaming
  state machine) and added `.github/workflows/verify-lean4.yml`.
  Re-verified after that commit: the module builds.
- The grep-level policy still holds: zero literal `sorry`, zero user
  `axiom`, zero `native_decide`, zero `unsafe`, zero `panic!` in
  `L4Factoidal/`, `Harness/`, `Wasm/`, `Bench/` (verified by direct
  grep, not by file headers). The `sorryAx` enters through the failed
  elaboration, not through source text.
- A trap seen during this review: `lake build ... | tail` returns the
  pipe's exit code, so the failure printed "exited with code 0".
  Anti-pattern #14 applies to build invocations too.

### 1.2 Shardborough proof coverage

Proved (kernel-checked theorems):

- `Storage/BlockMvp.lean:63-96` — `scan_eq_evalTP`,
  `scanBound_eq_tripleMatchesBound`: the in-memory block scan equals
  the SPARQL spec evaluator.
- `Storage/BlockWireV0.lean:100-112` — conditional form: IF bytes
  decode to `block` THEN the byte-level scan equals `evalTP` over
  `block.denotes`. There is no `decode (encode x) = some x` round-trip
  theorem for BLK0.
- `RDF/StoreDeltaMerge.lean:299-315` —
  `mergeOnRead_matches_applyEntries`: reading base plus delta through
  `mergeOnRead` agrees triple-for-triple with re-applying the
  `DeltaEntry` list, for any pattern bound, across
  add/remove/clear/drop/create. This is the load-bearing result behind
  the durable-UPDATE overlay, and it is real.

Not proved:

- `IndexedBlock`, `IndexedBlockWireV1`, `IndexedBlockWireV2`,
  `PredicateBlocks`, `PagedTermDictionary`, `ShardManifest`,
  `ChunkedArtifact`, `DeltaLog` contain zero `theorem` declarations.
  Correctness rests on `#guard` fixtures, typically one 3-triple,
  2-predicate example (`IndexedBlockWireV2Tests.lean:14-52`).
- "Canonical byte representation" here means deterministic bytes for
  one fixed in-memory value. No determinism or round-trip theorem
  backs it for any format after BLK0.
- `Storage/Bytes.lean:17-18` states "Round-trip theorems are proved
  rather than assumed". The file contains zero theorems, and its own
  body (lines 47-60) lists the round-trips as open obligations. The
  header is false as written.

### 1.3 Shardborough integrity mechanisms

- `BlockArtifact.verify` is `claimedDigest == sha256 bytes` — whole-
  artifact identity only. Signature/key trust is explicitly out of
  scope for this layer.
- `BlockMerkle` uses domain-separated leaf/node hashing with sibling
  proofs. Verification soundness is `#guard`-checked on one 3-chunk
  fixture, not proved.
- Gap: `ShardManifest.artifactValidFor`
  (`Storage/ShardManifest.lean:86-92`) validates the whole-file
  SHA-256 and the Merkle root independently. Nothing checks that the
  two commit to the same bytes. The full-open path checks only
  SHA-256; the partial-read path checks only the Merkle root. A hand-
  crafted manifest with a mismatched pair passes admission. The
  reference packer cannot produce one, but no proof or runtime check
  prevents it. This becomes a requirement on whatever signs manifests.
- Epoch guard is dead code: `shouldReplay`
  (`Storage/DeltaLog.lean:130-146`) is never called outside its test;
  `foldDeltaBatches` replays every batch unconditionally;
  `Harness/DeltaLogTool.lean` hardcodes epoch `0` on append. No
  compaction exists yet, so no double-apply can occur today, but the
  epoch plumbing must be threaded through the read and write paths
  when compaction lands — it does not already work.
- Crash durability: `appendSyncRaw` (landed `e5c7ac954`) fsyncs file
  data with an EINTR-safe write loop. It does not fsync the directory
  and there is no create-then-rename pattern, so a brand-new
  `deltas.dlog` can still be lost on some filesystems. The code
  comment states this; the gap is open and known.
- `partial def` in the block engine violates the totality rule in
  `skills/blockengine/SKILL.md`: `Storage/DeltaLog.lean:118`
  (`replay`) and `:418` (`replayDeltaBatches`). Both recurse on
  strictly decreasing byte-list length; a total rewrite is mechanical.
  `Harness/PredicateShardPack.lean:38,110` carries two more
  (IO-driven, more defensible).

## 2. Standards compatibility

### 2.1 F\* engine (docs/test-results/latest.json, run 2026-08-31 05:13 UTC)

All labelled "N pass, M fail (out of T)":

| Area | Score |
|---|---|
| SPARQL 1.1 (query, update, protocol, GSP, service, results) | 631 pass, 0 fail (out of 631) |
| RDF 1.1 six syntaxes + rdf-mt | 1030 pass, 0 fail, 1 unsupported (out of 1031) |
| RDF 1.2 syntax/eval | 242 pass, 0 fail (out of 242) |
| RDF 1.2 canonicalization | 82 pass, 0 fail (out of 82) |
| RDF 1.2 entailment (rdf-semantics) | 41 pass, 3 fail, 3 skip (out of 47) |
| SPARQL 1.2 | 254 pass, 0 fail (out of 254) |
| RDFC-1.0 | 86 pass, 0 fail (out of 86) |
| SHACL core / SPARQL constraints | 98 pass, 0 fail (out of 98) / 22 pass, 0 fail (out of 22) |
| ShEx | 1182 pass, 0 fail (out of 1182) |
| JSON-LD (toRdf/expand/compact/flatten/fromRdf) | 467/385/245/58/53 pass, 0 fail each |
| CSVW (csv2rdf/csv2json/validation) | 270, 270, 281 pass; 0, 0, 1 fail |
| RIF Core | 46 pass, 0 fail, 4 skip (out of 50) |

Caveats on this record:

- The comparator leniency (see Result summary). Known bugs it masks,
  from `docs/designissues/2026-08-22-lean4-w3c-harness.md`: `STRDT()`
  on typed literals, `CONCAT()` on non-strings, `IF()` with a
  division-by-zero condition, `STRBEFORE()`/`STRAFTER()` argument
  compatibility, cast failures on `xsd:boolean`/`xsd:integer`/
  `xsd:decimal` — all bind a variable that must stay unbound per
  SPARQL 1.1 §17.4/§17.5, and all score PASS. Also: SERVICE SILENT on
  an unreachable endpoint returns 0 rows instead of one empty
  solution; `UUID()` repeats across two BINDs in one query.
- `latest.json` `totals` omit the four large OWL 2 DL catalogs
  (positive/negative entailment, consistency, semantics-direct,
  together ≈930 test units). Their last measurement,
  `docs/web/conformance/owl2.md`: ≈1887 pass, ≈51 fail (out of ≈1938),
  measured 2026-07-30 — 32 days stale.
- `qudt_integrity`: 0 pass, 0 fail, 29 skip (out of 29) — a fully
  timed-out suite occupying a dashboard row (disclosed in
  `docs/designissues/2026-07-10-qudt-scoping.md`).
- `skills/test-suites/SKILL.md:171-172` still says the ShEx, CSVW, VC,
  DID, RML suites are "not yet wired". They are wired and green. Stale
  claim; obsolescence-sweep candidate.

### 2.2 Lean engine

The Lean runner `lake exe l4w3c` prints the same score grammar, but no
Lean number reaches `docs/test-results/`. All Lean scores are hand-
transcribed prose in `formal/lean4/README.md` and `PORT_NOTES.md`,
with no regeneration mechanism and no CI. Latest full measurement
2026-08-25 (`PORT_NOTES.md:13790-13798`):

- Parity with F\*: SPARQL 1.1 631 pass, 0 fail (out of 631). RDF 1.1
  and RDF 1.2 suites 1355 pass, 0 fail (out of 1355). RDFC-1.0 86
  pass, 0 fail (out of 86). SHACL core 98 pass, 0 fail (out of 98);
  SHACL SPARQL 22 pass, 0 fail (out of 22). SPARQL entailment regimes
  70 pass, 0 fail (out of 70). Protocol 34, GSP 19, service
  description 3, all 0 fail.
- Behind F\*:
  - OWL 2: Lean 1060 pass, 354 fail, 41 unsupported (out of 1457) vs
    F\* ≈1887 pass, ≈51 fail (out of ≈1938). The widest gap.
  - ShEx: Lean 1075 pass, 104 fail (out of 1179 decided) vs F\* 1182
    pass, 0 fail (out of 1182).
  - RDF 1.2 rdf-semantics: Lean 19 pass, 11 fail, 17 unsupported (out
    of 47) vs F\* 41 pass, 3 fail, 3 skip (out of 47).
  - RIF Core standalone: Lean 24 pass, 2 fail (out of 26 decided, 20
    not decided/attempted) vs F\* 46 pass, 0 fail, 4 skip (out of 50).
  - RML-Core: Lean 60 pass, 0 fail (out of 60) vs F\* 76 pass, 0 fail
    (out of 76) — narrower manifest, not a correctness gap.
- `formal/lean4/README.md` carries three contradictory entries for the
  same SPARQL score (lines 50, 52, 53: 601/0, 545/0, 631/0) and two
  contradictory SHACL-SPARQL entries (lines 51, 54). Only the last is
  current. A scraper or a reader can pick the wrong one.
- `docs/claude-rules/current-state.md` contains no Lean content at
  all. The project's standing state document does not know the
  intended full-scope engine exists.

### 2.3 Differential oracle

`lake exe l4diff` runs (dataset, query) pairs through the committed
F\* binary and the Lean evaluator. Last tally (2026-08-22): 712 agree,
18 disagree, 6 fstar-error, 0 lean-error, 395 skipped (out of 1131,
including 500 generated cases). Of the sparql11 manifest it covers 236
of 631 entries (≈37%): UPDATE, Protocol, GSP, syntax-only, entailment-
regime and SERVICE entries are all skipped. The shared comparator
(`Harness/Compare.lean`) is a clause-for-clause port of the F\*
comparator, so it inherits the same leniencies rather than checking
them.

### 2.4 Conformance coverage of Shardborough

None. `l4w3c` and `l4diff` build in-memory `Dataset` values from
manifest fixtures. No conformance path constructs a `DatasetBackend`
over IBK2/SBM2 artifacts. The disk-backed path is exercised only by
one-shot CLIs (`l4block-*`) with hand-typed queries and by the smoke
scripts in `tools/`. A regression specific to the on-disk backend,
the delta overlay, or manifest resolution is invisible to every
conformance suite in the repository.

## 3. Performance

- Shardborough gene gate (`docs/20260831-ibk2-gene-ingest-gate.md`,
  reproducible via `tools/blockengine-gene-shard-benchmark.sh`):
  888,949-triple `gene.ttl` packed to 13 SBM2 blocks in 72 s
  (≈12.4k triples/s) by the native reference packer. A `LIMIT 5`
  query on predicate P1057 reads 959,508 logical bytes with the
  Merkle-verified prefix path vs 1,586,092 for the unbounded scan.
  The Codex gist's "~1.59 MiB to ~0.96 MiB" matches these numbers
  with MB/MiB units mixed; the measured figures are the doc's.
  All numbers are the local-file/`pread` path. No PostgreSQL-backed
  run of this benchmark exists.
- The remaining dominant cost is confirmed and measured: the whole
  per-block term dictionary must be read before any row. The PTD1
  paged-dictionary probe projects 12,121 bytes (641 planning + 11,480
  one page) vs materializing the 894,584-byte dictionary — a
  dictionary-only projection; PTD1 is a prototype not yet embedded in
  any live block format.
- Concrete defect: the storage wire-format decoders convert
  `ByteArray` to `List UInt8` and recurse with `List.drop`/`List.take`
  (`Storage/IndexedBlockWireV2.lean:70-71,129,189,368` and the same
  pattern in 10 further files including `IndexedBlockWireV1.lean`,
  `BlockWireV0.lean`, `ShardManifest.lean`, `BlockMerkle.lean`,
  `PagedTermDictionary.lean`). `List.drop k` is O(k), so decoding n
  rows is O(n²), and `sliceBytes` re-materializes the byte list per
  call inside `scanBoundRange`. The Cottas/HDT layer already uses
  `Array`-backed readers and avoids this. This is the first place to
  spend performance effort in the block engine.
- The only Lean benchmark file, `Bench/SparqlJoinBench.lean`, runs
  under the interpreter; its absolute numbers are not comparable to
  native or wasm. The proved hash-join twin
  (`SPARQL/IndexedEvalRefinement.lean`, `evalBgpIdx_eq_evalBgp`) is
  the right pattern: fast path proved equal to spec path.
- F\* side baselines stand as documented (Turtle ≈104k triples/s;
  QUDT closure 87.1 s / 1.2 GB RSS; known superlinear `dump-nq` /
  `canonicalize` blowups; RDF/XML stack overflow above ~10k triples —
  `docs/claude-rules/performance.md`).
- Codex's own assessment in the gist — useful evidence, nowhere near
  state-of-the-art database performance — is accurate.

## 4. Architecture

- The layering matches `skills/blockengine/SKILL.md`: SPARQL semantics
  → `BackendReadOps { search, estimate, predicatePresent }` as the
  single dispatch seam (`SPARQL/StoreBackend.lean`, with the
  `backendSearch_via_caps` theorems) → pure block/byte modules →
  host adapters. Host I/O crosses the boundary in exactly two places:
  the C FFI (`ffi/block_pread.c`: `pread`, and the new fsync append)
  and plain `IO.FS` calls confined to `Harness/`.
- PushIR does not exist yet. TiKV does not exist. PostgreSQL is four
  bash scripts (`tools/blockengine-postgres-*.sh`) proving a lossless
  `bytea` round-trip via `pg_read_binary_file()` — a superuser-only,
  local-dev ingestion route, flagged as such in the scripts. Any
  summary calling PostgreSQL persistence "landed" should be read as
  "byte round-trip demonstrated", not "adapter implemented".
- Format sprawl is real but staged: BLK0 → IBK1 → IBK2, SBM0/1/2,
  PTD1, delta-log framings (DLE1/DLB1/DLOG/CEP1), served by 21
  `lean_exe` targets. IBK1 is not dead: it is what the original
  PostgreSQL smoke persists. Two formats currently satisfy the
  persistence gate in parallel. Decide which single format the
  adapters will persist before writing a real adapter.
- The UPDATE slice is conservatively designed: unsupported update
  forms are refused, never silently dropped; a non-empty delta
  disables the base-only LIMIT prefix shortcut (a tombstone could
  remove an early match); the merge is covered by the proved theorem.
  Verified end-to-end by hand during this review: INSERT DATA appended
  through `l4block-delta-log` is visible to
  `l4block-shard-merkle-query`.
- Known scope limits, correctly documented in
  `docs/20260831-durable-sparql-update-slice.md`: default graph only,
  no blank-node freshness for INSERT DATA (rejected), no compaction,
  WHERE-dependent forms refused.

## 5. Lean usage

- Toolchain `leanprover/lean4:v4.33.1`, zero external Lake packages
  (`lake-manifest.json` empty; `Std.HashMap` comes from the toolchain).
  Vendored native code is HACL\* C only, behind the tree's two
  `@[extern]` families: `Crypto/Ed25519.lean` (library) and
  `Harness/PosixRangeIO.lean` (harness). The
  `skills/factoidal-lean-basics` claim of "exactly one extern family"
  is true of the library only; add the qualifier.
- 2,884 theorems and 6,740 `#guard`s re-check on every `lake build`
  because the default library imports the whole namespace. There is no
  `lake test`; W3C probes are ~45 separate executables invoked by
  hand. A thin test driver that runs the smoke scripts plus a probe
  subset would make "did the whole net run" a single command.
- `partial def` backlog: 213 in the library (ShEx 50, XPath 44, OWL
  37, XSLT 27, RIF 15, others smaller), tracked in
  <https://github.com/danbri/factoidal/issues/617>; 2 new ones in
  Storage (§1.3). Highest-value target: `ShEx/Satisfies.lean:39-45`
  already contains a correct prose termination argument (visited
  (label,node) pairs bounded by |labels|×|nodes|); encoding it as a
  measure unlocks proofs over the ShEx checker.
- Proof style where it exists is sound: structural induction for the
  storage refinements; `Std.HashMap` lemma work for the hash-join
  equality; bounded witness search with a soundness proof for graph
  isomorphism; per-file `#print axioms` audits.
- Wasm surface: `Wasm/Ops/{Canon,Handles,Parse,Query,Reason,Support}`
  carry zero `#guard`s; only the two smoke scripts cover them, and
  those need a built binary and an explicit invocation.
- Documentation density in the Lean tree is high and specific: modules
  cite the exact W3C section they implement, and non-obvious decisions
  are recorded with the failure that motivated them.

## 6. Completeness

- Port coverage, module-presence method (`tools/lean-port-gap.py`;
  presence is not depth, per `skills/counting-coverage/SKILL.md`):
  220 F\* modules; 202 have a Lean counterpart by name/alias; 18 do
  not. Of the 18: 1 is engine code to port (`Parquet.Footer`, 3,373
  lines), 4 are proofs about F\*-internal representations, 13 are
  F\*-only machinery absent by design.
- Spot-checks by reading files (not names): SPARQL Protocol, RDFC-1.0
  canonicalization and COTTAS layer-1 are genuine ports with named
  deviations; in RDFC the Lean side is more verified than F\* (pure
  Lean SHA-2 replaces the F\* `assume val` hashes).
- Reverse direction: the whole Shardborough subsystem is Lean-only
  with no F\* twin. Consistent with the 2026-08-29 direction (Lean is
  the full-scope target), but note the F\* tree no longer tracks the
  storage frontier.
- The Codex gist is accurate on scope with two corrections: the
  read-only limitation is partially stale (the durable INSERT
  DATA/DELETE DATA/CLEAR/DROP/CREATE slice landed 2026-08-31
  06:30–06:41), and "PostgreSQL bytea storage" overstates a smoke
  script (§4).

## 7. Hygiene

- `.git` is 19.62 GiB (`git count-objects -vH`). 478 commits match
  "shadow build artifacts" and 421 match "generated docs artifacts" —
  899 of 5,141 total (≈17.5%), firing every 10–20 minutes at times.
  335 commits touch the ~17 MB `bin/linux-x86_64/factoidal` binary,
  which does not delta-compress. Iron rule #9 (commit binaries) plus
  this cadence is what produced 20 GiB. Owner decision, 2026-08-31:
  this is accepted for now — the project is migrating to a
  split-repository layout, factoidal-builds (artifacts) vs
  factoidal-core (source), which removes artifact churn from the
  source repository's history.
- Untracked material at root to disposition: `tmp-codex/` (two full
  nested clones of the whole repo), `formal/RDF.Graph.Executable.fst`
  and its byte-identical copy `formal/RDF.Graph.Executable.fst 2`
  (4,152-line pre-stratification orphans dated 27 May; the tracked
  module in `formal/fstar/` is 616 lines), `old-factoidal-sparql-client.js`,
  `status-sat30.txt` (pasted transcript from another agent session),
  `blockgo.txt`, `data/` (1.3 MB), `bin/graphflow/` (self-described
  spike; see next bullet).
- `bin/graphflow/README.md` documents a real, currently unfixed parser
  bug: `bin/npm-entry/entry_jsoo.ml` `parse_text_to_dataset` swallows
  parser errors and reports `{"ok":true,"count":0}` for rejected
  input. No tracked issue references it. It deserves one.
- Tracked junk: `.DS_Store`, `fix-quad-build.log`, `merged-build.log`,
  `.claude-runs-*-compile.log`, `tinc_time.txt` (contents: a shell
  error message).
- Work tracking: the 20 dated block-engine worknotes under `docs/` are
  the de facto tracker; the only issue cited is
  <https://github.com/danbri/factoidal/issues/466>. This conflicts
  with the repo's own rule that GitHub issues are the durable work
  record. The Shardborough workstream needs its own issue (or set),
  linked from <https://github.com/danbri/factoidal/issues/404>.

## 8. Recommended order of work

1. ✅ Done (`009f2ab53`, 07:06): `maxUnderscoreRun_ge_best` repaired
   via the monotone `feedChars` lemma. HEAD builds again.
2. ✅ Partly done (`009f2ab53`): `.github/workflows/verify-lean4.yml`
   now gates `lake build` (re-checking all 2,884 theorems and 6,740
   guards). Still open: confirm its first green run on GitHub
   Actions, and extend with `l4w3c` score regeneration into
   `docs/test-results/` (Lean rows next to F\* rows). Owner note,
   2026-08-31: CI arrangements are migrating to a split-repository
   layout (factoidal-builds vs factoidal-core), so wire new gates
   with that destination in mind.
3. 🔴 Tighten `w3c_runner.ml` row matching to equal-domain rows and
   re-run the SPARQL suites in both trees. Expect some published
   631/0 numbers to drop. That is a measurement correction, not a
   regression; fix the exposed evaluator bugs after.
4. ⚠️ Storage proofs, in order of leverage: `decode (encode b) = some b`
   for IBK2; the two `Bytes.lean` round-trips (and fix that file's
   header now); a determinism statement for SBM2. Then extend the
   `BlockWireV0`-style conditional scan theorem to IBK2.
5. ⚠️ Run W3C SPARQL conformance through the disk path: give `l4w3c` a
   mode that packs each test's fixtures into IBK2/SBM2 in a temp
   directory and evaluates through `DatasetBackend`. This closes the
   conformance blind spot for Shardborough and turns the suite into a
   regression net for the storage frontier.
6. Replace the `List UInt8` decoder idiom with `ByteArray`-native
   offset slicing in the 11 affected files before the next scale-up
   benchmark; re-run the gene gate after.
7. Wire the epoch guard through `foldDeltaBatches` and
   `DeltaLogTool` before building compaction; add the SHA-256/Merkle
   pair cross-check at manifest admission; totalize the two
   `DeltaLog` `partial def`s.
8. 🧹 Hygiene pass: remove or relocate the root strays, delete the
   tracked junk files, add `.gitignore` entries (artifact-commit
   churn is resolved by the planned factoidal-builds/factoidal-core
   split — owner, 2026-08-31), file the `entry_jsoo.ml` parse-error-swallowing
   bug, deduplicate the contradictory `formal/lean4/README.md`
   entries, and give `docs/claude-rules/current-state.md` a Lean
   section or a pointer to `PORT_NOTES.md`.
