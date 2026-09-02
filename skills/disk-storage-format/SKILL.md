---
name: disk-storage-format
description: How Factoidal stores RDF data on disk — the COTTAS/Parquet base file, its 11 sidecars, the durable-UPDATE delta log, the compacted-epoch marker, and the symlink-current versioning layout. Use when asked how data is stored on disk, when adding a new on-disk companion file, when a magic-number/framing question comes up (DLE1/DLB1/DLOG/CEP1/COTD/COTP/COTO/COPO/COTS), when running import/query/compact/serve against a COTTAS store, or when auditing rule #11 status for the storage layer.
---

# Disk storage format

**Scope note (2026-09-02).** This skill describes the F\* tree's COTTAS
store. The Lean 4 tree's persisted store, the Shardborough family (IBK3,
PTD1, SRI2/OLI2, TLI1, SBM6, DLOG, CURRENT), is documented in
[`skills/shardborough-storage`](../shardborough-storage/SKILL.md) and
specified in `docs/shardborough-storage-spec.md`; the Lean tree is the
intended full-scope target (CLAUDE.md, 2026-08-29), so read that first for
new storage work.

Factoidal's on-disk RDF store is a **read-optimized Parquet base file**
(COTTAS format) plus a growing set of **companion files**: eager
sidecars that make bound-term queries fast without decoding the whole
column, and — since the 2026-07-06 durable-UPDATE work — an **append-only
delta log** and a **compacted-epoch marker** that make the store
read-write without breaking the base file's write-once assumption. This
skill is the map of what exists on disk, in what byte format, owned by
which F\* module, and how to drive the whole lifecycle from the CLI.

Companion reading: `perf-benchmarking` skill (query latency numbers for
this layer), `ocaml-boundary` skill (rule #11 taxonomy this skill
applies throughout), `build-and-test` skill (building the binaries used
below).

## 1. Store anatomy — what exists on disk after import

A single COTTAS "chunk" (one logical dataset/named-graph-set) lives in
a directory tree. Pre-durable-UPDATE (import only, no writes yet):

```
<corpus_root>/<chunk_name>/v1/
  data.cottas              the Parquet base file (§2)
  data.nq                  normalised N-Quads the base was built from
  data.factbin             an OCaml-glue fact-count/summary sidecar
  source-info.ttl          provenance metadata
  summary.json             import summary (quad/graph counts)
  data.cs-clustered.nq     present only if --row-order cs was used
  cs-cluster-stats.log     present only if --row-order cs was used
  data.cottas.s.dict       )
  data.cottas.s.presence   )
  data.cottas.p.dict       )  the 11 eager sidecars, present only if
  data.cottas.p.presence   )  --build-sidecars was passed at import
  data.cottas.o.dict       )  (verified directly, this session — see
  data.cottas.o.presence   )  §5). All eleven or none: the import script
  data.cottas.g.dict       )  either writes the full set or leaves the
  data.cottas.g.presence   )  store without eager sidecars (lazy build
  data.cottas.p.offsets    )  at first server-open then applies).
  data.cottas.po.presence  )
  data.cottas.s.offsets    )  per-subject contiguous global row-range
                           )  index (§1.1), 2026-07-13
```

After the first `factoidal compact` (durable-UPDATE stage 4), the
layout grows a **store-level** delta log (sibling to the chunk, not
inside any version dir) and a **version-level** symlink indirection:

```
<corpus_root>/<chunk_name>/
  v1/                      the original import (unchanged, still
                            directly queryable at its own path)
  v2/, v3/, ...             one full artifact SET per compaction —
                            data.cottas + all 11 sidecars + this
                            version's OWN data.compacted-epoch (§1.2),
                            written to a FRESH directory name, never
                            mutating an existing version in place
  current -> vN             a SYMLINK, the live pointer. Flipped by one
                            atomic_rename syscall (issue #282's
                            atomic_rename primitive) so the whole
                            artifact set becomes visible together —
                            no window where `current` names a partially-
                            written version.
  data.deltalog             the append-only delta log (§3) — a
                            STORE-level file, outside every version
                            dir, because the same logical append
                            stream survives across many compactions
```

Point `--data-cottas` at `<chunk_dir>/current/data.cottas` for the
crash-safe live view; any numbered version dir remains directly
queryable and untouched by later compactions. This directory-layout
decision (symlink indirection, not an in-place directory rename) is
disclosed in the banner above `run_compact` in
`bin/factoidal-cli/factoidal_cli.ml:768-841` — POSIX `rename(2)` cannot
atomically swap a whole non-empty directory onto another, so the
"atomic swap" property is bought at the symlink layer instead.

### 1.1 Byte-level pointers — which F\* module owns which file, which magic

| File | Owning F\* module | Magic (LE u32) | Checksum/CRC |
|---|---|---|---|
| `data.cottas` (read path) | `Parquet.Footer.fst` (footer/row-group/column decode) | n/a — Parquet's own `PAR1` magic | Parquet's own page CRCs, unused by our reader |
| `data.cottas` (native write path, in-flight — §5.1) | `RDF.CottasStore.BaseWriter.fst` | n/a — writes a spec-conformant Parquet file | n/a |
| `<name>.dict` | `RDF.CottasStore.DictWriter.fst` / read side `RDF.CottasStore.OnDiskIndex.fst` | `0x44544f43` ('COTD') | none — magic+version header only |
| `<name>.presence` | `RDF.CottasStore.PresenceBitmap.fst` / `OnDiskIndex.fst` | `0x50544f43` ('COTP') | none |
| `.p.offsets` | `RDF.Store.Columnar.OffsetIndex.fst` | `0x4f544f43` ('COTO') | none |
| `.po.presence` | `RDF.CottasStore.CompoundPresenceBitmap.fst` | `0x4f504f43` ('COPO') | none |
| `.s.offsets` | `RDF.CottasStore.SubjectOffsetsWriter.fst` (write) / `RDF.Store.Columnar.SubjectOffsetIndex.fst` (read) | `0x53544f43` ('COTS') | none |
| `data.deltalog` — per-entry framing | `RDF.Store.Columnar.DeltaLog.fst` §5 | `0x31454C44` ('DLE1') | additive mod-2^32 `simple_checksum` over the payload |
| `data.deltalog` — per-batch framing | `RDF.Store.Columnar.DeltaLog.fst` §7 | `0x31424C44` ('DLB1') | `simple_checksum` over the batch body |
| `data.deltalog` — log-file header | `RDF.Store.Columnar.DeltaLog.fst` §9 | `0x474F4C44` ('DLOG') | none (the header carries no payload to check) |
| `data.compacted-epoch` | `RDF.Store.Columnar.DeltaLog.fst` §13 | `0x31504543` ('CEP1') | `simple_checksum` over the 8-byte epoch value |

Note the asymmetry: the **sidecars** (dict/presence/offsets/compound-po)
validate with magic+version only — no checksum field — while the
**delta-log family** (entry/batch/log/epoch-marker) all carry the same
additive `simple_checksum`, because that family exists specifically to
detect a torn write after a crash (§3), a concern the write-once
sidecars don't have. The additive checksum is explicitly **not**
cryptographic (`RDF.Store.Columnar.DeltaLog.fst`'s own module banner) —
it exists only so `parse_delta_entry`/`parse_delta_batch` can reject a
corrupted/truncated record without decoding it. A separate,
cryptographic hash-witness check (SHA-256 via the already-wired
`Fstar_pure_hashes.sha256`, io-verification-doc pattern) is layered on
top at the test-driver level, comparing `expected_digest_bytes`
(§11 of `DeltaLog.fst`) against a real on-disk read-back — it is not a
field inside the file format itself.

### 1.2 The compacted-epoch marker in full

`data.compacted-epoch` (one per version dir, `RDF.Store.Columnar.
DeltaLog.fst` §13) is a single `nat` (a u64 body) meaning "every delta
batch with `db_epoch <= this value` is already folded into this base
and MUST be skipped on replay." This is the crash-recovery idempotence
guard for the window between a compaction's base-rename and its
delta-log truncation (§3.3 step 5 of the design doc). The **sharp edge**
disclosed in the module banner: a writer appending a new batch after a
compaction recorded epoch CE must stamp its own `db_epoch` as `CE+1` or
higher, or the batch is silently treated as already-folded and ignored
at merge time. This fails safe (never double-applies a write) but is a
real footgun for any future writer path that doesn't thread the epoch
correctly — check `read_compacted_epoch`/`read_compacted_epoch_opt` in
`bin/factoidal-cli/factoidal_cli.ml:254-268` for the reference pattern.

## 2. The COTTAS base — Parquet subset, precisely

Full contract: `docs/cottas-format-v1.md`. Summary, with the traps:

- **Container:** Apache Parquet, ZSTD-compressed column chunks (codec id
  6). Exactly four required `BYTE_ARRAY`/`STRING` columns, in this
  order: `s`, `p`, `o`, `g`. One row = one quad; the default graph is
  the literal ASCII sentinel `DEFAULT` in column `g` (not empty string,
  not NULL — a true sentinel because `DEFAULT` isn't a valid IRI token).
- **Row groups:** DuckDB's default of **122,880 rows/group**. A v1
  reader MUST iterate every row group (an earlier reader gap that only
  decoded row group 0 is documented as closed in
  `docs/cottas-format-v1.md` §10, but re-check before trusting an old
  build). **Do not lower this** without re-measuring: shrinking to
  20,000 rows/group (44 groups on the 888,949-quad gene corpus)
  regressed a bound-predicate query by ~24x before a footer-offset-table
  fix, and even after that F\* fix (2026-07-06,
  `probe_parquet_row_group_offset_table` in `Parquet.Footer.fst`) a
  44-group build still runs ~4x slower than an 8-group build of the
  same content — the per-row-group cost is bounded now, not eliminated
  (`docs/designissues/2026-07-05-disk-backed-db-perf-review.md` §5
  item 3, "characterised and partially fixed").
- **Encodings actually read/written:** `DELTA_LENGTH_BYTE_ARRAY` (DLBA,
  Parquet encoding id 6) and `RLE_DICTIONARY` (id 8, paired with a
  PLAIN-encoded dictionary page). DuckDB/pycottas do **not** emit a
  uniform encoding — `g` and low-cardinality `p` columns default to
  RLE_DICTIONARY, `s`/`o` are adaptive (DLBA in row group 0, sometimes
  RLE_DICTIONARY in later groups on the same file). The all-DLBA
  parliament fixture is the **exception**, not the rule; a reader that
  only handles DLBA fails or silently mis-decodes (§2.1's bloom-filter
  trap below) on the common case.
- **Definition levels:** every column is declared Parquet `OPTIONAL`
  (SQL `NOT NULL` does not propagate to Parquet `REQUIRED` in
  DuckDB/pycottas output), so every data page opens with a
  definition-level section (4-byte LE length + RLE levels) even though
  no cell is ever actually null. A decoder that assumes `REQUIRED`
  columns and skips this section will misread the first bytes of every
  page as data.

### 2.1 The bloom-filter / field-11 trap (warning, historical but re-checkable)

DuckDB writes a bloom filter by default. A since-fixed F\* bug read
Thrift field 14 (`bloom_filter_offset`) instead of field 11
(`dictionary_page_offset`) when locating a column's dictionary page —
the offset "looked valid" (both are legitimate byte offsets into the
file) but pointed at bloom-filter bytes, so every dictionary decode
either hard-failed or, worse, returned a spuriously empty `Some []`
instead of a loud `None` — a **silent wrong answer** (`COUNT(*) = 0`
instead of the true count) on a file that opened without error. Fixed
2026-07-05 in `Parquet.Footer.fst` (three distinct defects, see
`docs/designissues/2026-07-05-disk-backed-db-perf-review.md` §"item 1,
DONE"); regression-pinned in
`tests/unit/parquet_rle_dictionary_multi_row_group.ml`. The lesson
generalises: **any Parquet-adjacent format change should be checked
against a default-encoded (RLE_DICTIONARY, bloom-filter-present) file,
not just the all-DLBA parliament fixture** — the fixture that "works"
is the unrepresentative one.

### 2.2 Compatibility claims and their verification

`docs/cottas-format-v1.md` claims `.cottas` files are readable by
`duckdb.sql("SELECT * FROM parquet_scan('data.cottas')")` (they are
plain, spec-conformant Parquet — pycottas/DuckDB write them, so
round-tripping through DuckDB again is definitionally true for the
producer side). This session **did not** re-run a DuckDB `parquet_scan`
round-trip check on a freshly-built store — that verification (or a
regression test making it durable) is a documented gap, not a claim
already backed by a fresh measurement here. What **is** independently
verified this session (§5): `factoidal --data-cottas` reads a fresh
`corpus_pipeline.py`-built store correctly for both `producer` and `cs`
row order, with and without eager sidecars.

## 3. The delta log — durable-UPDATE stages 1-4 (landed)

Design doc: `docs/designissues/2026-07-06-durable-update-design.md`.
F\*: `formal/fstar/RDF.Store.Columnar.DeltaLog.fst` (framing + the five
I/O `assume val`s) and `RDF.Store.Columnar.DeltaMerge.fst` (pure
merge-on-read, no I/O). Landed via four commits (`git log --oneline
--grep 'Durable UPDATE'` from `origin/claude/main`):

1. **Stage 1** (`868a20b`) — `delta_entry`/`delta_batch` byte format,
   `Tot`, no I/O yet. Proved: `lemma_delta_entry_roundtrip` — any bytes
   `serialize_delta_entry` produces, followed by arbitrary trailing
   log bytes, parse back to exactly that entry and the untouched tail.
2. **Stage 2** (`1f27320`) — the five `ML`-effect I/O primitives
   (`delta_log_append`, `delta_log_fsync`, `delta_log_read_all`,
   `atomic_rename`, `fsync_dir`), realised in
   `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/282_delta_log_io.sh`
   under **issue #282**. Crash-kill harness: **270 kills, 270 clean
   recoveries** (a process `SIGKILL`ed mid-append always leaves a log
   that replays to exactly the pre-crash committed prefix — a torn tail
   batch is rejected by the checksum/magic check and `parse_log_batches`
   simply stops there, per its own "accept a prefix, never a torn
   entry" contract).
3. **Stage 3** (`5e8399a`) — `RDF.Store.Columnar.DeltaMerge.fst`'s
   `fold_delta_batches`/`merge_on_read`, wired into
   `SPARQL11.Store.fst`'s backend so a query sees `base ⊕ delta`. Proved:
   `lemma_merge_on_read_matches_apply_entries` — querying a reference
   graph with the same entries applied directly agrees, triple for
   triple, with `merge_on_read` composed over base + replayed delta —
   for the `delta_entry` vocabulary (ADD/REMOVE/CLEAR/DROP on one
   graph). The full `update_op`/`apply_update_ops` generalization is an
   explicitly-named, NOT-yet-proved residual (empirically pinned by
   `tests/local/durable_update_stage3.sh` instead — three ways: CLI-
   over-delta-log, in-memory `apply_update`, and crash-recovered-prefix
   consistency). **Re-run this session** (isolated worktree at HEAD,
   see §4's opening note for why): **15 pass, 0 fail (of 15)**, including its own kill-mid-append
   harness — **25 clean recoveries, 0 torn states, 0 unexpected
   failures (of 25 iterations)**.
4. **Stage 4** (`5afad04`) — compaction (`factoidal compact`, §4 below).
   **Re-run this session**: **29 pass, 0 fail (of 29)**, including the
   kill-mid-compaction harness — **25 clean recoveries, 0 torn states,
   0 unexpected failures (of 25 iterations); 11 iterations observed the
   pre-compaction state, 14 observed the post-compaction state** —
   every kill left `current` either fully absent (pre-compaction state
   intact) or fully present and valid (post-compaction state), never a
   third state. The script also drives a second compaction cycle
   (append at `epoch=1` after the first compaction reports
   `compacted_through_epoch=0`) confirming layering continues
   correctly across repeated compactions, not just once.

### 3.1 Framing (entry / batch / log)

Little-endian throughout, all magic+version+length+checksum framed
(§1.1's table has the exact magics):

```
delta_entry  (§5 of DeltaLog.fst):
  [ magic 'DLE1' u32 ][ version u32 ][ length u32 ]
  [ tag byte + constructor fields, length bytes ]
  [ simple_checksum(payload) u32 ]

delta_batch  (§7):
  [ magic 'DLB1' u32 ][ version u32 ][ length u32 ]
  [ db_seq u64 ][ db_epoch u64 ][ op_count u32 ][ ops: N delta_entries back to back ]
  [ simple_checksum(body) u32 ]

log file  (§9):
  [ magic 'DLOG' u32 ][ version u32 ]
  [ batch_0 ][ batch_1 ] ...   -- parse_log_batches decodes a PREFIX of
                                  whole, checksum-valid batches and stops
                                  (no error) at the first byte that
                                  doesn't start a complete frame
```

The five `delta_entry` constructors: `DE_Add`, `DE_Remove` (both carry a
triple + `option iri` graph), `DE_Clear`/`DE_Drop`/`DE_Create` (graph
management). Term encoding is a **deliberate divergence** from N-Quads
text: a length-prefixed binary encoding (tag byte + u32-length-prefixed
UTF-8), not the existing `nq_term_to_string` — parsing N-Quads-escaped
text back would need a full unescaping lexer inside this module, which
the module's own banner calls out as an intentional escape-hatch
decision, not silent drift.

### 3.2 Crash-safety, measured

- **270 kills / 270 clean recoveries** on the raw append path (stage 2's
  own dedicated `delta_log_crash_harness.sh`, design-doc-cited).
- **25 kills / 25 clean recoveries, 0 torn states** on mid-append
  (stage 3's own kill harness) — re-run this session, same result.
- **25 kills / 25 clean recoveries, 0 torn states, both sides observed
  (11 pre-compaction, 14 post-compaction)** on mid-compaction (stage
  4's kill harness) — re-run this session, same result: every observed
  post-kill state was exactly the pre- or exactly the post-compaction
  tuple, confirmed by re-querying five different facts (an added row,
  a removed-anchor row, an added-events row, an emptied-graph check, an
  untouched-graph check) after each kill.
- The checksum is what makes recovery detectable rather than silently
  wrong: a `SIGKILL` mid-append leaves a tail whose length/checksum/magic
  don't line up, so `parse_delta_entry`/`parse_delta_batch` return
  `None` for that tail and the reader simply stops one batch earlier —
  never decodes garbage as a spurious valid entry.

### 3.3 Epoch guard semantics — the writers-must-stamp-above-epoch sharp edge

Repeated here because it's the single easiest way to silently lose a
write: after compaction records `data.compacted-epoch = N`, any new
batch appended to the (now-truncated) log **must** carry `db_epoch >
N`. `filter_batches_since_epoch` (`DeltaLog.fst` §14) keeps a batch iff
`db_epoch > threshold`; a batch stamped at or below the current
compacted epoch is treated as already-folded and silently dropped from
every future read — not an error, not a crash, just invisible. This is
the safe failure direction (never double-applies a write) but it is
real data loss from the caller's point of view if the epoch isn't
threaded correctly. `bin/factoidal-cli/factoidal_cli.ml`'s
`read_compacted_epoch`/`read_compacted_epoch_opt` (lines 254-268) is
the reference "read the current threshold before writing" pattern any
new writer must follow.

## 4. Lifecycle commands (verified against the committed binary this session)

All commands below were run this session against
`bin/linux-x86_64/factoidal` **as committed at HEAD (`0d3542b`,
"Artifacts for the stage-4 landing")**, in an isolated `git worktree`
(not the shared working tree — a sibling session had `factoidal_http.ml`,
`RDF.CottasStore.BaseWriter.fst`, and several `.fst`/`.ml` files
uncommitted mid-edit at the time; per this task's own brief and the
`workflow-gotchas-debugging` skill's subagent-worktree-leakage lesson,
verification here never touched or depended on that in-flight state).
`.cmx`/`.cmi`/`.o` build artifacts are **not** committed (only `.ml`
sources and the final linked `bin/<platform>/*` binaries are, per Iron
Rule #9) — reproducing the `factoidal compact`/delta-log commands from
a clean checkout requires `cd formal/fstar && ./build-ocaml.sh compile`
first (safe to run in a separate worktree; the build lock is
per-worktree, see `build-and-test` skill).

### Import (two paths)

**Current, landed path** — `tools/corpus_pipeline.py` shells out to
`pycottas.rdf2cottas` (DuckDB-backed):

```bash
python3 tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input sample.nq --corpus-root ./corpus \
  --dataset-name demo --chunk-name demo
# -> ./corpus/demo/v1/data.cottas + data.nq + data.factbin +
#    source-info.ttl + summary.json

# with CS clustering + all 10 eager sidecars:
python3 tools/corpus_pipeline.py materialize-nq-cottas-corpus \
  --input sample.nq --corpus-root ./corpus2 \
  --dataset-name demo --chunk-name demo \
  --row-order cs --build-sidecars
```

Verified in an earlier session on `tests/local/data/cottas_sample.nq`
(5 quads, 2 named graphs): both invocations ran clean (`verified=True`,
`quads=5`, `graphs=2`); the second printed `sidecars_built=['.s.dict',
'.s.presence', '.p.dict', '.p.presence', '.o.dict', '.o.presence',
'.g.dict', '.g.presence', '.p.offsets', '.po.presence']` — the 10
sidecars that existed at that time, all present. `COTTAS_SIDECAR_
SUFFIXES` (`tools/corpus_pipeline.py`) grew an 11th entry, `.s.offsets`,
2026-07-13 (§1.1) — not re-verified against this exact fixture in this
pass, but the mechanism is identical: `build_cottas_sidecars_eager`
shells out to `factoidal query --explain`, which calls
`Cottas_companion_boot.prewarm_via_companions`, which now also calls
`Cottas_subject_offset_idx.ensure_subject_offsets_built` (chained after
the existing lamed3 + compound-po hooks). `factoidal cottas-import`
(the CLI subcommand) is a thin `execvp` wrapper around the exact same
script (`bin/factoidal-cli/factoidal_cli.ml`'s `exec_corpus_pipeline`)
— no independent logic to verify there.

**Native path (LANDED and CLI-wired — stale-claim corrected
2026-07-13):** `formal/fstar/RDF.CottasStore.BaseWriter.fst` is a
from-scratch F\* Parquet writer — `serialize_cottas_v2` — and IS wired
into the CLI: `factoidal import` and `factoidal compact
--native-writer` call it directly (`bin/factoidal-cli/factoidal_cli.ml`
~line 1300), removing Python from the store-creation path. An earlier
revision of this section claimed "no CLI subcommand wires it in yet";
that was true when written and false since the import/compact landing —
exactly the drift the obsolescence-sweep skill exists to catch.
Disclosed design deltas from the pycottas-produced files this skill
otherwise describes: the codec is **UNCOMPRESSED, not ZSTD** (paired
with the `Parquet.Footer.fst` UNCOMPRESSED decode branch). "Wired in"
and "emits compressed bytes" are independent facts: native output
measures ~13.90 B/quad vs pycottas/DuckDB's zstd ~1.14-1.17 B/quad
(~12x), so pycottas remains the small-file import path until a zstd
encoder lands — tracked in the storage next-phase list
(`docs/designissues/2026-07-11-ondisk-indexes-query-optimization-deep-dive.md`).

### Query with `--delta-log`

```bash
factoidal --data-cottas current/data.cottas --delta-log data.deltalog \
  -e 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'
```

Verified this session: a plain `--data-cottas` query (no delta) against
the freshly-built 5-quad/2-graph fixture returned the correct count (4
default-graph triples via the `GRAPH ?g` pattern — matches the fixture's
own graph split). `--delta-log PATH` **requires the file to already
exist** (an F\*-side `delta_log_read_all` on a missing path raises
`Unix.Unix_error(ENOENT, "open", path)` — confirmed directly this
session); a store's delta log must be initialized (a header-only write)
before the first `--delta-log`-flagged query, not created on first
query. Once a store has been compacted, `--data-cottas
<version_dir>/data.cottas` alone (no `--delta-log`) still epoch-filters
correctly against that version's own `data.compacted-epoch` — the CLI
reads it via `read_compacted_epoch_opt` before composing any delta
(`factoidal_cli.ml:284-303`).

### Update

There is **no standalone `factoidal update` CLI verb** as of this
session. Two ways a delta batch actually gets appended today:

1. **Test/dev harness:** `bin/delta-log-probe/probe.ml` — a
   consumer-side driver (rule #11: lives in `bin/<consumer>/`, not the
   verified library) with `init`/`append`/`verify`/`hashcheck`/
   `scenario-write` modes, calling the F\*-extracted
   `RDF_Store_Columnar_DeltaLog` functions directly. This is what
   `tests/local/durable_update_stage3.sh` and
   `tests/local/durable_update_stage4_compaction.sh` build and drive —
   treat those two scripts as executable documentation for the exact
   append/query/compact sequence a real writer needs to follow.
2. **HTTP wiring (`--rw`/`POST /update`, in-flight, uncommitted this
   session):** `bin/factoidal-http/factoidal_http.ml` carries
   "Durable-UPDATE stage 8" comments and a `--rw`/`--delta-log` flag
   pair (`--rw` requires `--delta-log`; rejects with 403 if
   `--read-only`) that fsyncs an update's delta batch before returning
   the HTTP response. This was **modified in the working tree, not
   committed**, at the time this skill was written — confirm with
   `git log --oneline --grep 'stage 8' -- bin/factoidal-http/factoidal_http.ml`
   before citing `POST /update` as a landed, durable path.

The F\*-side translator that would make a real SPARQL Update request
into delta entries, `update_ops_to_delta_entries`
(`RDF.Store.Columnar.DeltaMerge.fst` §7), is landed and handles ground
`INSERT DATA`/`DELETE DATA`/`CLEAR`/`DROP`/`CREATE` — it returns `None`
(whole request rejected, not partially applied) for
`DELETE/INSERT WHERE`, `COPY`/`MOVE`/`ADD`, `LOAD`, or
`CLEAR`/`DROP ... NAMED|ALL` (multi-graph fan-out this per-request
translator can't resolve without dataset-level graph lookup). The GSP
(Graph Store Protocol) translators in §8 of the same file (`gsp_put`/
`gsp_post`/`gsp_delete_to_delta_entries`) translate completely, no
residual — PUT is `DE_Clear` + N `DE_Add`s, POST is N `DE_Add`s, DELETE
is one `DE_Clear`.

### Compact

```bash
factoidal compact --data-cottas <chunk_dir>/v1/data.cottas \
  --delta-log <chunk_dir_or_elsewhere>/data.deltalog \
  [--python PATH] [--parser NAME] [--index PERM]
```

Verified this session (`tests/local/durable_update_stage4_compaction.sh`,
run against an isolated worktree checkout of HEAD — see §4's opening
note for why a separate worktree, not the shared tree): **29 pass, 0 fail (of 29)**.
The script's own transcript, reproduced because it is the exact
sequence any operator needs: build a 5-quad/2-graph store → append one
delta batch (carol added, an anchor triple removed, an events-graph
add, a docs-graph clear) → `compact-invocation` succeeds and
`compact-reports-epoch (epoch=0)` → `compact-current-symlink-live`
(`current` resolves and is queryable) → `compact-sidecars-eager-built`
(the new version's 10 sidecars exist) → the new base alone AND the new
base plus the now-truncated log both reproduce the exact
pre-compaction merged view (10 checks, all pass) → a second batch
appended at `epoch=1` shows Dave added, the compacted content still
present, and — critically — invisible without the (now non-empty
again) log, confirming the delta/base split still works post-compaction.

Mechanically: folds the delta log into a fresh `.cottas` base by
materializing `base ⊕ delta` through the SAME F\*-verified read path a
query would use (`SPARQL11_Store.cottas_with_delta_dataset_backend` →
`materialize_dataset_backend` → `RDF_Canonical.canonical_nquads`), then
re-runs the **existing, unmodified** `corpus_pipeline.py` import
pipeline against that N-Quads text (rule #15: no new store-writing
logic), writes `data.compacted-epoch` inside the new version dir, fsyncs
every file plus the directory, then does the `current -> vN` symlink
flip via one `atomic_rename` call, then truncates the delta log
(temp-write + fsync + rename + fsync_dir, same shape as the base
swap). Old versions (`v1/`, `v2/`, ...) are never mutated in place —
each compaction writes to a fresh, never-yet-referenced directory name.

### Serve

```bash
factoidal serve --data-cottas <chunk_dir>/current/data.cottas \
  --delta-log <chunk_dir>/data.deltalog [--rw] [--read-only] --port 3030
```

`--rw` needs `--delta-log` (checked eagerly at startup,
`factoidal_http.ml:588-592`); `--read-only` gates `POST /update` with
403. As noted above, the `--rw` HTTP write path itself was uncommitted
working-tree state this session — verify its landed status before
depending on it; the read side (`--delta-log` composing reads without
`--rw`) is the stage-3/stage-8-read-side path already exercised by the
stage 3/4 test scripts.

## 5. Verified vs glue (rule #11)

| Layer | Status |
|---|---|
| `data.cottas` read path (footer, row-group nav, DLBA/RLE_DICTIONARY decode) | F\*-verified (`Parquet.Footer.fst`, ~2,200 lines) |
| `data.cottas` write path (pycottas/DuckDB) | third-party, not F\* — out of scope for rule #11 (it's not our code); `RDF.CottasStore.BaseWriter.fst` is the in-flight native replacement |
| dict/presence/offsets/compound-po sidecars | F\*-verified byte layout (`DictWriter`/`PresenceBitmap`/`OffsetIndex`/`CompoundPresenceBitmap` `.fst` modules); `assume val` I/O only for the mmap/read primitives |
| delta-log framing + merge-on-read | F\*-verified, `Tot` (`DeltaLog.fst` sections 1-11 + 13-14, `DeltaMerge.fst` entirely) |
| delta-log I/O (append/fsync/read/rename/fsync_dir) | **Issue #282** — five `assume val`s, rule-#11(a)-acceptable pure I/O, realised in `minimal_regrettable_glue_code_each_with_an_open_issue/282_delta_log_io.sh` |
| compaction orchestration (`factoidal compact`) | consumer tool (`bin/factoidal-cli/factoidal_cli.ml`), not verified-library code — it only sequences already-verified F\* calls + the existing import pipeline; no new byte-layout decisions live there |
| the 928-line `cottas_ondisk_runtime.sh` fast-path override | still a standing rule-#11 violation (VIOLATION-SEM), but as of 2026-07-06 the **production SPARQL query path no longer calls it** — `RDF.Store.Capabilities.Cottas.fst`'s `sc_solve`/`sc_estimate`/etc. were rewired to F\* `_tok` entry points (`9750eb7`/`9c3d160`). The patch can't be deleted yet because three non-production consumers (a `tests/unit` baseline, the `cottas-ondisk-smoketest` binary, `factoidal-explain`) still call the id-based entry points. See `fstar-ocaml-boundary-audit.md` (2026-07-06 ratchet audit, authoritative), issue #118/#254. |

**Standing qualifier** (Iron Rule #11, until the boundary audit + recovery
Phase 9 land): "parser and algebra spec verified in F\*; on-disk backend
has unverified OCaml-side optimization layers being migrated back to
F\*." The durable-UPDATE work (delta log, merge-on-read, compaction
orchestration) does **not** add to that debt — it is the first
durability-I/O surface in the codebase and is built entirely inside the
rule-#11 taxonomy (five `assume val`s total, issue #282, no shadow
semantic logic). The debt this qualifier refers to is the pre-existing
COTTAS-on-disk *read* fast path, not this durable-UPDATE layer.

## 6. Browser/JS in-memory bytes store (npm entry points)

`docs/designissues/2026-07-06-inmemory-bytes-store.md` stage 5: the
native `--data-cottas-mem FILE` flag (§4 above) has a browser/JS
equivalent in the npm-entry ABI (`bin/npm-entry/entry_jsoo.ml`, built
into both `factoidal-npm-entry.js` (js_of_ocaml) and
`factoidal-npm-entry.wasm.js` (wasm_of_ocaml) — no new `assume val`,
no F* change; `register_memory_buffer` and `cottas_ondisk_open` already
treat a synthetic handle exactly like a real path):

- `openCottas(bytes)` — registers a whole `.cottas` artifact's bytes
  (hex string / `Uint8Array` / `ArrayBuffer`/`Buffer`) under a
  synthetic handle and opens it read-only. Returns an opaque handle
  string; `{ok:false}` on a bad/truncated footer rather than throwing.
- `queryCottas(handle, sparql)` — SELECT/ASK/CONSTRUCT via the same
  `SPARQL11_Store` backend-executor path (`cottas_ondisk_dataset_
  backend` / `run_select_query_backend_dataset` / `run_ask_query_
  backend_dataset`) the native `--data-cottas`/`--data-cottas-mem` CLI
  query path uses — rows decode lazily, no heap materialization except
  for CONSTRUCT (`materialize_dataset_backend`, same cost as the
  native CLI's CONSTRUCT-over-COTTAS path). No entailment option, no
  `--delta-log`/write overlay (read-only); DESCRIBE is unsupported.
- `closeCottas(handle)` — drops the handle from this entry point's own
  registry only; does NOT evict the underlying `__mim2_file_bytes_
  cache` (no eviction API exists — a page opening many short-lived
  stores still grows that cache for the tab's lifetime).
- `toCottas(nquads)` — the write half: sorts + serializes a dataset via
  the pure `Tot` `RDF.CottasStore.BaseWriter.serialize_cottas_v2`, the
  SAME writer `factoidal compact --native-writer`/`factoidal import`
  call natively, so a browser-produced `.cottas` round-trips into
  `openCottas` (and into the native CLI) byte-for-byte. No sidecars are
  built (sidecars are an on-disk-file optimization; a buffer handle has
  no sidecar files).

npm surface: `index.js`/`wasm.js` (`openCottas`/`queryCottas`/
`closeCottas`/`toCottas`, Dataset-shaped results, gated via
`capabilities().cottasBytesStore`), `fn.js` (`fn.openCottas(bytes)`
returns `{handle, query(sparql), close()}`; `fn.toCottas(ds)`), and
`browser.js` (raw-ABI wrappers of the same four calls). `browser-wasm.js`
does not yet load the npm-entry ABI at all (a pre-existing gap, not
introduced by this — it only drives the CLI bundle's `query()`).
Tests: `npm/factoidal/test/cottas-bytes-store.test.js` (js) and
`cottas-bytes-store-wasm.test.js` (wasm), against the committed fixture
`tests/unit/fixtures/store_capabilities_sample.cottas`.

## 7. Pointers

- [`docs/designissues/2026-07-06-durable-update-design.md`](../../docs/designissues/2026-07-06-durable-update-design.md)
  — the design doc this whole delta-log section follows (architecture
  options considered, the staged implementation plan, six open
  decisions for the owner).
- [`docs/designissues/2026-07-05-disk-backed-db-perf-review.md`](../../docs/designissues/2026-07-05-disk-backed-db-perf-review.md)
  — the COTTAS format inventory, every row-group/encoding/sidecar
  measurement in §2 above, and the bloom-filter/row-group-offset-table
  fix history.
- [`docs/cottas-format-v1.md`](../../docs/cottas-format-v1.md) — the
  frozen v1 Parquet-subset contract (§2's source of truth).
- `formal/fstar/RDF.Store.Columnar.DeltaLog.fst`,
  `formal/fstar/RDF.Store.Columnar.DeltaMerge.fst` — read these directly
  for the exact framing/proof structure; both are heavily commented.
- `bin/factoidal-cli/factoidal_cli.ml` — `run_compact` and its banner
  (search "Durable-UPDATE stage 4") for the compaction orchestration
  and crash-safety argument in full prose.
- `tests/local/durable_update_stage3.sh`,
  `tests/local/durable_update_stage4_compaction.sh` — executable
  documentation for the append/query/compact/kill sequences; run them
  directly rather than hand-rolling the probe build recipe.
- `ocaml-boundary` skill — the rule #11 taxonomy this skill's §5 applies.
- `perf-benchmarking` skill — query latency numbers for this layer
  (row-group-size regressions, CS-clustering wins/losses, the
  quadratic-footer-walk fix).
- `build-and-test` skill — building `bin/linux-x86_64/factoidal` from
  source; needed to reproduce any command in §4 from a clean checkout.
