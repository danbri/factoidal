# Fresh-eyes repository review — 2026-09-02

Snapshot: commit `2f1ad89f5` (2026-09-01 22:19), branch `claude/main`,
plus the uncommitted `queryIBK3BlockSet` prototype in `formal/lean4/Wasm/`.
Second full review after
[the 2026-08-31 review](20260831-repo-review.md); scope requested by the
owner: docs, `formal/` (Lean 4 first), and `skills/`. Method: full
`lake build` at tip, direct grep-verified counts, CI run history, and
three read-only review passes (docs, Lean code, skills) whose claims were
spot-checked before use — one agent claim was wrong and is corrected in
§2.4. Every score is labelled; every count names its method.

## Result summary

- ✅ **Integrity is good.** `lake build` at tip: 897 jobs, no failure.
  `verify-lean4.yml` passed its last two runs. Zero `sorry`, user
  `axiom`, `native_decide`, `unsafe`, `panic!` in `L4Factoidal/`,
  `Harness/`, `Wasm/` (anchored grep). `L4Factoidal/Storage`,
  `SPARQL`, `RDF` carry zero `partial def`.
- ⚠️ **The newest storage code is the least verified.** The three
  modules the current manifest (SBM6) depends on — `SubjectRowIndexWireV2`,
  `TermLocalIndex`, `TermLocalIndexWire` — have zero theorems and no
  separate test file; their assurance is in-module `#guard`s (7, 6, 8)
  plus activation's cross-artifact equality checks. No format after
  `BlockWireV0` has a `decode (encode x) = some x` theorem.
- ⚠️ **Copy-paste and idiom debt in `Storage/`.** Eight private copies
  of the same byte helpers; two spellings of `fitsU32`; every wire
  decoder still materializes the whole artifact as `List UInt8`
  although a zero-copy `Cursor` already exists in `IndexedBlockWireV2`.
- ⚠️ **Docs are voluminous and largely unreachable.** 46 dated
  worknotes; ~34 are linked from nowhere but each other; `docs/index.md`
  links none. Perhaps 10–12 carry unique load-bearing content.
  `docs/claude-rules/current-state.md` still has zero mentions of Lean or
  Shardborough. Several findings from the 08-31 review are still open.
- 🔴 **The `blockengine` skill is not loaded.** `.claude/skills/` has 36
  symlinks for 38 skills: `blockengine` (the skill CLAUDE.md sends
  contributors to for Shardborough) and `lean4-performance` are
  unlinked. Six other skills are stale in ways that mislead.
- 🧹 F\* tree idle since 2026-08-27 (consistent with its
  lineage/oracle role); CI green. CLAUDE.md's "~148 `assume val`s" does
  not match a fresh count (81 top-level declarations in
  `formal/fstar/*.fst`) — re-measure by the audit's method.

## 1. Integrity

- Build: `lake build` (from `formal/lean4/`) — 897 jobs, success, with
  the uncommitted WASM prototype included.
- CI: `verify-lean4.yml` success at `144bff3d8` and `6866c9ea3`;
  `verify-fstar.yml` and `w3c-tests.yml` success on their latest runs.
- Policy sweep (anchored regex, docstring mentions excluded): 0 of each
  banned construct tree-wide.
- `partial def`: **211** real declarations in `L4Factoidal/` (a broad
  grep says 221; the extra 10 are backtick mentions in docstrings —
  issue [#617](https://github.com/danbri/factoidal/issues/617) should
  count with `grep -rE '^\s*(private\s+)?partial def '`). By directory:
  ShEx 50, XPath 44, OWL 37, XSLT 27, RIF 15, Math 11, Geo 6, MathML 5,
  Testing 4, GRDDL 3, XForms/CSVW/JSONSchema 2 each, HTTP/Schematron/XSD
  1 each; Storage/SPARQL/RDF/Cottas/HDT/SHACL/JSON-LD/VC 0. `Harness/`:
  16, of which two (`PredicateShardPack.lean:72,197`) sit in the storage
  ingest pipeline — storage debt filed under Harness. `Wasm/`: 0.

## 2. Lean 4 code (`formal/lean4`)

### 2.1 Duplication

Byte-identical private helpers, one copy per file:
`byteArrayOfList`/`listOfByteArray` in 8 files (`ShardManifest:25`,
`IndexedBlockWireV1:39`, `V2:70`, `V3:83`, `PagedTermDictionary:46`,
`SubjectRowIndexWire:31`, `BlockWireV0:39`, `TermLocalIndexWire:45`;
`SubjectRowIndexWireV2:47` renamed `listOf`); `fitsU32` in 6 files with
two spellings (`n < 4294967296` vs `n < UInt32.size`); `readU32At?` in 3;
`takeExact` in 2; two lexicographic byte comparators (`lessBytes`,
`lessKey`) with different recursion styles; `at?` reimplementing
`xs[i]?`. `Storage/Bytes.lean` is the module these belong in and none of
the copies import it for them.

### 2.2 Idioms

Every `decode`/`decode?` entry point converts the whole artifact to
`List UInt8` first: `BlockWireV0:65`, `IndexedBlockWireV1:75`,
`IndexedBlockWireV2:329,453`, `IndexedBlockWireV3:122,314`,
`PagedTermDictionary:244`, `ShardManifest:498`. `IndexedBlockWireV2:78-110`
already defines a zero-copy `Cursor` (`u8`, `u32le`, `bytesOfLength`)
and uses it for segment decoding — the same file's top-level `decode`
does not. `BlockMerkle.lean:15` concatenates via `List` round-trip on
every leaf and node hash. No O(n²) drop/take chains remain (the 08-31
finding was fixed); what remains is constant-factor allocation of the
entire artifact per read, which is the memory the WASM bridge's caps
exist to protect.

### 2.3 Format-version sprawl

`ShardManifest.lean` decodes wire versions 0–6 with three byte-identical
arms. No live writer (`ShardPublish`, `PredicateShardPack`,
`IndexedBlockV3Convert`) emits versions 0, 1, 3, 4, or 5 — only 2 and 6;
the others exist as decode arms for intermediate states nothing ever
persisted outside fixtures. `BlockWireV0` and its four harness front
doors (`l4block-mvp/-pack/-file-query/-corpus`) are called by no
`tools/*.sh` script; only two dated docs mention them. `lakefile.lean`
has 62 `lean_exe` targets, 29 storage-related. `SubjectRowIndexWire`
(SRI1) is legitimately live (older generations must stay readable).
Under the standing "no users — prefer the right structure" ruling,
versions 0/1/3/4/5 and the V0 pipeline are quarantine or delete
candidates pending a check for persisted fixtures.

### 2.4 Proof-vs-guard balance (corrected)

Grep of `^theorem` and `^#guard` per module (tests siblings noted):

| Module | theorems | `#guard` | separate tests | round-trip theorem |
|---|---|---|---|---|
| `Bytes` | 12 | 0 | — | LE32 only |
| `DeltaLog` (+Tests) | 17 | 16 | yes | yes (CEP1, DLB1 framing) |
| `BlockMvp` | 6 | 4 | — | scan = spec |
| `IndexedBlockWireV2` (+Tests) | 5 | 8 | yes | no |
| `BlockWireV0` (+Tests) | 2 | 6 | yes | guard only |
| `IndexedBlockWireV3` (+Tests) | 0 | 13 (in Tests) | yes | no |
| `PagedTermDictionary` | 0 | 10 | no | no |
| `SubjectRowIndexWireV2` | 0 | 7 | no | no |
| `TermLocalIndexWire` | 0 | 8 | no | no |
| `TermLocalIndex` | 0 | 6 | no | — |

Correction to the review pass: an agent reported the last three as
"zero guards, untested"; they have in-module guards (7/6/8) and are
additionally checked at activation by content-equality against the
IBK3 they index. What is true: zero theorems, no separate test files,
and they are the modules the live SBM6 write path depends on.
`Storage/Bytes.lean:17-19` still claims "Round-trip theorems are proved
rather than assumed" while lines 49-63 list the VByte and `Section`
round-trips as open — flagged 08-31, unchanged.

### 2.5 Harness boundary leakage

- Layout strings: `ShardManifest.layoutConsistent` is the library's
  single source of truth, yet `Harness/ShardActivate.lean:27-57`
  re-declares eleven layout literals plus its own `isIbk3Layout`, and
  `IndexedBlockV3MerkleScan.lean:19-22` and `IndexedBlockV3Query.lean:41-45`
  each carry their own subset. Four places to edit per new layout, no
  compiler help.
- Epoch policy: `Harness/CompactedEpoch.lean:43-52` (`nextWriteEpoch`,
  `foldedThrough`) encodes the no-double-replay invariant as pure
  functions with zero theorems and zero guards, while the byte framing
  of the same concept is proved in `L4Factoidal/Storage/DeltaLog.lean`.
  The policy belongs beside `EpochMarker`, with its monotonicity proved.

### 2.6 Naming and docstrings

`decode` (returns `Option`) in five modules vs `decode?` in four —
unpredictable per format. `structure Prefix` means five unrelated
headers (`IndexedBlockWireV2:40`, `V3:39`, `PagedTermDictionary:30`,
`SubjectRowIndexWireV2:24`, `TermLocalIndexWire:32`). Stale headers:
`IndexedBlock.lean:8-9` ("byte format belongs to the later canonical-codec
gate") and `SubjectRowIndex.lean:8-9` ("a later IBK successor must
encode this") both describe as future what sibling files already do.

### 2.7 WASM prototype (uncommitted)

`Wasm/Ops/Block.lean` `queryIBK3BlockSet`: caps on bytes and rows are
checked after each artifact is fully hex-decoded and admitted — the
work they are meant to bound. Reviewed in detail in the Codex sync file
(2026-09-02 09:05); recommendation was land as `…Preview` after moving
the size check before decode.

## 3. Documentation

### 3.1 Entry points

`README.md:91-131` and `docs/index.md:14-15` link the spec; good. The
worknote series is not indexed anywhere: of 46 dated notes, 12 are
linked from README/spec/skills, `docs/index.md` links none, and ~34 are
reachable only by `ls`. Three notes in the same dated slot are
unrelated to Shardborough (`20260831-xmpp-mix-pilot.md`,
`-foafmixer-pilot.md`, `-podman-machine-audit.md`).

### 3.2 Contradictions and stale claims (with status)

- `formal/lean4/README.md:50-54` — three contradictory SPARQL scores
  (601/0/30, 545/0/86, 631/0) and two SHACL-SPARQL entries under
  duplicated item numbers. Flagged 08-31; **still unfixed**.
- `docs/claude-rules/current-state.md` — "Last refreshed 2026-08-12",
  zero mentions of Lean, Shardborough, blockengine, IBK. A reader would
  conclude the repo has one storage engine. Flagged 08-31; **still
  unfixed**.
- `skills/test-suites/SKILL.md:171-172` — ShEx/CSVW/VC/DID/RML "not yet
  wired"; the same file reports their green scores at lines 102-103.
  Flagged 08-31; **still unfixed**.
- `skills/blockengine/SKILL.md:36` — "Current boundary" pinned at commit
  `73209342c`, names IBK1 as frontier, 7 of 29 `l4block-*` CLIs.
- `docs/20260831-repo-review.md:255` said 888,949-triple `gene.ttl` as
  889,949 — my error, corrected 2026-09-02.
- Two same-day notes disagree on epoch-guard status (`20260831-repo-review`
  says dead code at `e5c7ac954`; `20260831-epoch-safe-compaction` says
  landed) — both true at their commits, but the date-only naming
  convention cannot order them. Worknotes need a commit pin in the
  first line.

### 3.3 Terminology and prose rules

Reserved terms are well kept: "W3C disk gate" appears only where it is
retired; "pure" is used as effect-free; the census doc refuses to call
535/535 a suite result. Anti-pattern 26 violations (banned adjectives)
in eight places, e.g. `20260831-gene-shard-scale-baseline.md:34`
("Important measured limit"), `20260830-segmented-ibk-design.md:45`
("an honest result"), `20260901-persisted-sparql-language-index-safety.md:422`
("critical bucket-safety"), `20260901-blockengine-tuesday-okrs.md:112`
("not yet honest to call"). No aphorism/metaphor hits.

### 3.4 Sprawl

Of 46 notes: format-specific notes fully absorbed by the spec's §6
(`blockwirev0`, `indexedblockwirev1`, `ibk2-bytearray-slicing`,
`paged-term-dictionary`, `tli1-term-local-index`,
`sri2-paged-subject-index`, `native-range-slicing`,
`packed-ibk2-selective-reader`, `ibk3-migration-publisher`); same-topic
duplicates (`epoch-safe-compaction` vs `agent-coordination`);
`persisted-sparql-language-index-safety.md` is five notes in one file.
Unique and load-bearing: `20260829-blockengine-baseline`,
`20260831-repo-review`, `20260901-blockengine-tuesday-okrs`,
`-heterogeneous-fixture`, `-persisted-executability-census`,
`-ibk3-wasm-worker-demo`, `-corpus-ladder-catalogue`, the spec.

## 4. Skills

- 🔴 Not symlinked into `.claude/skills/`: `blockengine`,
  `lean4-performance` (the latter also absent from CLAUDE.md's list).
  The harness never auto-loads either.
- Stale: `test-suites:171-172` (above); `factoidal-lean-basics:38,131-133`
  "exactly ONE `@[extern]` family" — `Harness/PosixRangeIO.lean` is a
  second (`l4_block_pread`, `l4_delta_log_append_sync_at_size`,
  `l4_atomic_replace_file_sync`, `extern_lib libl4blockhost`);
  `blockengine` boundary section (above); `disk-storage-format` answers
  "how is data stored on disk" for COTTAS only, no Shardborough pointer;
  `repo-tour` (2026-07-20) has no `formal/lean4/` entry and opens with
  "the product is the F\* spec, everything else is plumbing";
  `using-factoidal` has no `l4block-*` entry.
- Coverage gaps, no skill at all: the Shardborough lifecycle CLIs (pack
  → activate → query → update → compact; 29 binaries, 7 named anywhere);
  the corpus ladder; the persisted census; the Codex/Fable sync-file
  protocol and the "Codex mediates all commits" rule — both live and
  in daily use, recorded nowhere in the repo, only in session goal text;
  `verify-lean4.yml` (absent from `test-suites`'s CI table).
- Score labelling: one bare ratio,
  `node-crypto-haclstar-vc-wasm-build:139` ("181/0").
- Frontmatter: all 38 valid; no missing paths beyond CI-generated
  artifacts not present locally.

## 5. F\* tree

Last substantive change 2026-08-27; `verify-fstar` and `w3c-tests`
green. 220 modules, 81 top-level `assume val` declarations by
`grep -h '^assume val'` — CLAUDE.md rule 3 says "~148"; whichever method
the boundary audit used, the number in CLAUDE.md is currently
unverified and should be regenerated by a script, not hand-carried.

## 6. Process observations

1. Findings addressed to Codex in the sync file were fixed within hours
   (every 08-31/09-01 code finding). Findings written only in review
   docs (README duplicate scores, current-state.md, test-suites line,
   Bytes.lean header) are still open two days later. The repo's own
   rule — GitHub issues are the durable work record — is the fix: each
   open finding below should become an issue, not a paragraph.
2. Velocity produced 46 worknotes in four days with no index and no
   supersession marks. A one-file index with a status column
   (current / absorbed-by-spec / historical) costs an hour and would
   change how a new reader experiences the project.
3. This session's harness injected commit-attribution instructions that
   contradict CLAUDE.md iron rule 13. The repository rule governs (it
   says so explicitly); no commits were made by this session.

## 7. Ranked fixes

| # | Fix | Where | Effort | Status (2026-09-02 evening) |
|---|---|---|---| --- |
| 1 | Symlink `blockengine` and `lean4-performance` into `.claude/skills/`; add `lean4-performance` to CLAUDE.md | `.claude/skills/`, `CLAUDE.md` | small | done, 0ab177b50 |
| 2 | Delete the three contradictory score entries; keep the 631/0 line | `formal/lean4/README.md:50-54` | small | done, 0ab177b50 |
| 3 | Add `#guard` decode∘encode round trips, then theorems, for `SubjectRowIndexWireV2`, `TermLocalIndexWire`, `PagedTermDictionary`, `IndexedBlockWireV3` | `L4Factoidal/Storage/` | small / medium | theorems landed for PTD1 and IBK3 (a75054870, c11dd3ed3; encoders enforce admission); SRI2/TLI1 in progress |
| 4 | Move byte helpers into `Bytes.lean`; one `fitsU32`; delete 8+ copies | `L4Factoidal/Storage/*` | medium | open |
| 5 | Promote `Cursor` to `Bytes.lean`; retire whole-artifact `List` copies at every decode entry | 8 decoders | large | open |
| 6 | Single source for layout strings: call `layoutConsistent`, delete 11+ Harness literals | `Harness/ShardActivate.lean:27-57` and two siblings | medium | open |
| 7 | Move `nextWriteEpoch`/`foldedThrough` into `DeltaLog.lean`; prove monotonicity | `Harness/CompactedEpoch.lean:43-52` | small / medium | open |
| 8 | Quarantine or delete manifest versions 0/1/3/4/5 arms and the V0 pipeline after a fixture check | `ShardManifest.lean`, `lakefile.lean:159-163` | small (owner call) | open |
| 9 | Fix `Bytes.lean` header; rename `decode`→`decode?` uniformly; rename the five `Prefix`s to `Header` with format prefix | `Storage/` | small | headers done, 0ab177b50; decode/decode? and Prefix/Header renames open |
| 10 | Refresh six stale skills; write `shardborough-storage` skill (lifecycle CLIs, format registry, corpus ladder, census); document the sync-file protocol and mediated-shipping rule in-repo | `skills/`, `CLAUDE.md` | medium | open |
| 11 | Worknote index with status column; pin each note to a commit; move the three non-Shardborough notes out of the series | `docs/` | small | done, 0ab177b50 (docs/worknotes-index.md) |
| 12 | Give `current-state.md` a Lean section or a pointer; regenerate CLAUDE.md's `assume val` count by script | `docs/claude-rules/`, `CLAUDE.md` | small | open |
