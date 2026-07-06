# Durable SPARQL 1.1 UPDATE over the read-optimized COTTAS store

**Status:** design doc, no code. Territory: this file only. Read but
did not edit
[`2026-07-05-disk-backed-db-perf-review.md`](2026-07-05-disk-backed-db-perf-review.md)
(current architecture + measurements — owned by a sibling session),
[`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
(planner family + boundary rules), and
[`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
(the characteristic-set clustering and content-addressing research
that motivates §3.4 below).

## 0. What already works, and what does not (read directly from the tree)

This corrects an assumption in the tasking brief. **SPARQL 1.1 UPDATE
semantics are not a gap.** `SPARQL11.Algebra.fst:5733`'s
`apply_update : rdf_dataset -> sparql_update -> rdf_dataset` is a
verified, total F\* function that already implements INSERT DATA,
DELETE DATA, DELETE/INSERT WHERE, LOAD (rejected defensively at the
HTTP layer via `SPARQL.Update.Analysis.fst`'s `update_has_load`, not
because the algebra can't run it), CLEAR, and full graph management
(ADD/COPY/MOVE/CREATE/DROP). The W3C SPARQL 1.1 Update conformance
suite is vendored under
[`third_party/testing/w3c/sparql/sparql11/`](../../third_party/testing/w3c/sparql/sparql11/)
across 14 manifests (`add`, `basic-update`, `clear`, `copy`, `delete`,
`delete-data`, `delete-insert`, `delete-where`, `drop`, `move`,
`syntax-update-1`, `syntax-update-2`, `update-silent`,
`http-rdf-update`), totaling **176 test cases**, and
[`docs/claude-rules/current-state.md`](../claude-rules/current-state.md):451-484
records all 176 passing (100%) as part of the 631-test SPARQL suite —
this is measured, current state, not a target. `bin/w3c-runner/w3c_runner.ml`
drives `UpdateEvaluationTest`, `PositiveUpdateSyntaxTest11`,
`NegativeUpdateSyntaxTest11`, and a stateful `http-rdf-update` sequence
(the "Gimel2" suite-level shared store, `w3c_runner.ml:1883-1914`) that
exercises PUT/POST/DELETE against the SPARQL 1.1 Graph Store HTTP
Protocol across a manifest run.

**What is missing is durability, full stop.** `apply_update` operates
on `rdf_dataset = { ds_default : rdf_graph; ds_named : list named_graph }`
where `rdf_graph = list triple` — a plain in-memory value
(`formal/fstar/RDF.Graph.Executable.fst:142-170`). It never touches
`graph_backend` (`SPARQL11.Store.fst:23-34`, the `GB_List | GB_Indexed
| GB_HDT | GB_COTTAS | GB_CottasOnDisk | GB_Union` variant type the
*read* path routes through) and nothing about it is written to disk.
The perf-review doc's §1.5 finding stands: `.cottas` files are
write-once, produced by `pycottas`; there is no F\*-side COTTAS writer;
issue #100's Phase 4 ("Persistence layer for INSERT/DELETE",
`RDF.Persistent.fst`, on-disk term dictionary, `pwrite`) is unstarted.
A grep of every `.fst` file in the tree for `assume val.*fsync`,
`assume val.*rename`, `assume val.*pwrite`, or `assume val.*openfile`
returns nothing — there is currently **zero** durability-I/O surface
in the codebase to build on; this design proposes the first one.

The task, precisely stated: give the already-correct in-memory UPDATE
semantics a durable on-disk backing that (a) preserves the base
COTTAS read path's measured performance, (b) survives a crash mid-write
without torn state, and (c) lets concurrent readers keep answering
queries while a writer is in flight — without touching
`RDF.Persistent.fst`-the-module's job of being a from-scratch page
format (issue #100 Phase 4 as originally scoped assumed a brand-new
on-disk store; this design instead layers a delta on top of the
COTTAS store that already exists and already serves parliament-scale
reads).

## 1. Requirements

1. **Full SPARQL 1.1 Update**, reusing the existing, already-passing
   `apply_update` algebra: INSERT DATA, DELETE DATA, DELETE/INSERT
   WHERE (the WHERE clause reads through whatever `graph_backend` is
   live, base + delta composed — see §4.1), LOAD (subject to the
   existing HTTP-layer rejection policy, unchanged by this design),
   CLEAR, and graph management (ADD/COPY/MOVE/CREATE/DROP GRAPH).
   This design does not touch the algebra; it gives its *output* (a
   new `rdf_dataset` value, or more precisely the *diff* between the
   pre- and post-update dataset) somewhere durable to go.
2. **Durability.** A crash at any point during an update — mid-write,
   mid-fsync, mid-rename, process killed, machine power-cut — must
   leave the store in exactly the pre-update state or exactly the
   post-update state on the next open. No partially-applied update is
   ever observable. This is the standard "no torn writes" bar every
   engine in issue #100's own list (Jena TDB, RDF4J native, Oxigraph)
   meets via write-ahead logging or copy-on-write; §2 evaluates which
   fits this codebase's Parquet-based read path.
3. **Read performance stays at the measured COTTAS numbers for the
   base, plus a bounded delta penalty.** The perf-review's §2.e cited
   baselines (Lamed3 offset index, the CS-clustering query
   measurements, the post-#118-partial-fix row-group-offset-table
   numbers) are the floor for querying the base file unchanged by an
   empty delta; a non-empty delta may cost more, but the cost must be
   a function of *delta size*, not corpus size — otherwise durable
   UPDATE re-creates the exact O(store) pathology §2.c of the perf
   review already measured and flagged as the #100 acceptance
   criterion still unmet.
4. **Concurrent readers during update.** A reader that opened the
   store before an update completes must see a consistent snapshot
   (either fully pre- or fully post-update, per requirement 2) and
   must not be blocked waiting for the writer, beyond the ordinary cost
   of picking up a new delta-log tail on its next open or poll. This
   design does not attempt in-transaction reads of an update's own
   half-applied effects (SPARQL 1.1 does not require multi-statement
   transaction visibility rules beyond one Update request's own
   atomicity, which requirement 2 already covers).
5. **Corpus scale the design must serve.** The two corpora with real
   measurements in this repo: the 3,143,406-quad UK Parliament COTTAS
   store (cited, not in this sandbox) and the 888,949-quad Wikidata
   gene fixture (measured directly, this session's sibling doc). Design
   choices below are sized against both, not against a synthetic
   "web-scale" target this project has no measurements for.

## 2. Architecture options

### 2.a Base `.cottas` + append-only N-Quads delta log + periodic compaction

A `.cottas` file stays exactly as pycottas writes it today: immutable,
Parquet, write-once. Updates append **delta entries** (adds and
tombstoned removes) to a separate append-only log file
(`data.delta.log`, one file per store, format specified in F\* — §3.1).
Reads compose base ∪ delta-adds − delta-removes (§4.1). Periodically
(size threshold, or an explicit `factoidal compact` invocation), the
delta is folded into a fresh `.cottas` base via the existing
pycottas/`corpus_pipeline.py` writer, the eager sidecars are rebuilt
against the new base (§4.3), and the delta log is truncated.

**Fit against the measurements.** The base file's read path is
untouched — the CS-clustering and row-group-offset-table wins measured
2026-07-05/06 (perf-review §5 items 1-3) carry over unchanged for any
query the delta doesn't touch. The delta itself is small relative to
the corpus between compactions (an UPDATE workload that grows the
delta to base-file size before compacting has chosen too infrequent a
compaction schedule, not a flaw in the architecture). Durability is
the well-understood write-ahead-log pattern: append the delta entry,
fsync, and only then is the update considered committed (§3.3). This
is the same shape OSTRICH (cited in the shapes-canon doc, JWS 2019)
uses for RDF archive versioning — an immutable base snapshot plus
aggregated changesets — except OSTRICH's changesets are themselves
indexed; this design's delta starts as a flat append log and gains
structure only if merge-on-read cost demands it (Open decision 3).

**Cost.** Point lookups and BGP evaluation against a bound term must
check the delta in addition to the base — a hash-set membership test
per delta entry touching the same term positions, bounded by delta
size, not base size (requirement 3). Compaction is a full
`corpus_pipeline.py` rebuild, which the perf-review already measured
at 32.3 s / 1.7 GiB peak RSS for 888,949 quads (§2.a of that doc) —
acceptable as a background/maintenance operation, not acceptable if it
had to run synchronously per update.

### 2.b LSM-style: multiple sorted delta layers with merge-on-read

Instead of one flat append log, deltas accumulate as a sequence of
immutable sorted runs (like an LSM tree's L0/L1/... levels), each run
itself a small `.cottas`-shaped Parquet file, periodically merged into
larger runs. This is the RocksDB/LevelDB recipe Oxigraph's own storage
layer is built on (cited, unverified, in the shapes-canon doc — GitHub
was unreachable that session; treat as **[memory]** here too).

**Fit against the measurements.** This buys write throughput under
sustained update load (each run is written once, sequentially, no
read-modify-write) and gives every delta layer the same columnar
prune machinery (presence bitmaps, offset index) the base already has,
which a flat N-Quads append log does not — a query against a
multi-run delta stack still benefits from Yod6/Tet3-style pruning per
run. The cost is real engineering weight this project does not have
today: a merge policy (when does L0 merge into L1?), a read path that
unions an unbounded number of runs instead of one delta file plus one
base, and — the sharper problem — **every layer needs the same
RLE_DICTIONARY-and-multi-row-group correctness the base reader only
just got right on 2026-07-05** (perf-review §2.b: three distinct F\*
defects, fixed the same day this design's sibling doc was measured).
Standing up N more Parquet-shaped readers before the one-reader case
is fully hardened and regression-pinned against every producer
encoding is exactly the kind of scope creep issue #118's own phasing
guidance warns against.

### 2.c Copy-on-write: new `.cottas` per update batch

Every update (or every batch of updates up to some size/time window)
triggers a full rebuild of a new `.cottas` file from base + all
pending changes, atomically swapped in via rename. This is the
simplest option to reason about — no delta format, no merge-on-read
logic, the read path is *always* the unmodified base reader against
whatever the current file is — and it trivially satisfies requirement
2 (rename is atomic on POSIX filesystems within one directory) and
requirement 4 (a reader that opened the old file keeps reading it
until it closes; a new reader picks up the new file).

**Fit against the measurements.** It fails requirement 3 outright at
either measured scale. The perf-review's own numbers: rebuilding the
888,949-quad gene corpus costs 32.3 s wall / 1.7 GiB peak RSS per
build (§2.a); at parliament's 3.14M quads, extrapolating linearly,
a single-triple INSERT DATA would cost on the order of two minutes and
several GiB of RAM to durably commit. This is not "a bounded delta
penalty" — it is O(corpus size) per update, the exact pathology
requirement 3 rules out. Copy-on-write is the right answer for
**batch** loads (a `LOAD` of a large external document, or a
scheduled bulk refresh) where the cost is naturally amortized over
many triples, but wrong as the *only* mechanism for interactive
single-statement UPDATE.

### 2.d Recommendation: 2.a, with 2.c as the compaction step and 2.b deferred

**Base `.cottas` + append-only delta log + periodic compaction (2.a),
where compaction *is* a copy-on-write rebuild (2.c) run in the
background on a schedule, not per update.** This is not a compromise
between the three options — 2.c is a subroutine of 2.a, and 2.b is
2.a's natural evolution *if* the flat delta log's merge-on-read cost
turns out not to be boundable in practice (Open decision 3 names the
measurement that would trigger it). Reasoning tied to the corpus
scales this project actually has numbers for:

- At gene scale (888,949 quads, the only scale measured this
  sandbox), a compaction costs ~32 s / ~1.7 GiB — fine as an
  occasional background op, unusable per-update.
- At parliament scale (3.14M quads, cited), the same argument holds
  with a larger constant; the delta-log path is what keeps the
  *interactive* update cost independent of corpus size at both
  scales, which is the property 2.c alone cannot offer and 2.b offers
  at a much higher implementation cost than this project's current
  columnar-reader maturity (§2.b above) justifies taking on first.
- The delta log's own size is bounded by the compaction schedule, not
  by corpus size, so requirement 3's "bounded delta penalty" is a
  policy knob (compact every N entries or every T minutes), not an
  open research question.

## 3. The F\*/glue split (rule #11)

### 3.1 Delta-log byte format — specified in F\*

A `delta_entry` is one of: an added quad, a tombstoned (removed) quad,
or a graph-management marker (CLEAR/DROP/CREATE target). The format
lives in F\* per rule #11 and the hash-witness pattern from
[`2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md):

```fstar
module RDF.Store.Columnar.DeltaLog

// One durable log entry. request_salt threads the same per-request
// uniqueness discipline apply_insert_data/apply_delete_data already
// use (SPARQL11.Algebra.fst:4946-5007) so two updates in the same
// process never collide on a generated identifier.
noeq type delta_entry =
  | DE_Add    : quad:triple -> graph:option iri -> delta_entry
  | DE_Remove : quad:triple -> graph:option iri -> delta_entry
  | DE_Clear  : graph:option iri -> delta_entry   // None = default graph
  | DE_Drop   : graph:iri -> delta_entry
  | DE_Create : graph:iri -> delta_entry

// One committed batch: the ops belonging to one SPARQL Update request,
// plus a monotonic sequence number (the log's total order) and a
// commit epoch (§3.3's fsync/rename protocol reads this back on
// crash-recovery replay).
noeq type delta_batch = {
  db_seq   : nat;
  db_epoch : nat;
  db_ops   : list delta_entry;
}

val serialize_delta_entry : delta_entry -> Tot (list FStar.UInt8.t)
val parse_delta_entry     : list FStar.UInt8.t -> Tot (option delta_entry)
val serialize_parse_roundtrip
  (e : delta_entry) :
  Lemma (parse_delta_entry (serialize_delta_entry e) == Some e)

val serialize_delta_batch : delta_batch -> Tot (list FStar.UInt8.t)
val parse_delta_batch     : list FStar.UInt8.t -> Tot (option delta_batch)

// The hash-witness pair from the io-verification doc.
val expected_digest : delta_batch -> Tot sha256_digest
let expected_digest b = sha256 (serialize_delta_batch b)
```

This is a small format (five constructors, no nested variable-length
structures beyond a `list u8` term encoding already specified by the
existing N-Quads/Turtle term serializers this codebase has) — well
inside the plain `serialize : data -> Tot (list u8)` shape rule #11
prefers, not the large-buffer Option-B pattern from
[`2026-05-09-large-writer-byte-format-options.md`](2026-05-09-large-writer-byte-format-options.md)
(that pattern exists for payloads where per-byte F\* list construction
is itself the bottleneck — a delta log entry is a handful of terms,
not a 12 MB offset table). If sustained update throughput later shows
the naive `list u8` construction is the bottleneck, revisit with the
same `FStar.Seq`/array-shape move issue #118 is already making for
the read path, not before.

### 3.2 Merge-on-read semantics — a pure F\* function the evaluator consumes

The composed view a query sees is `base ⊕ delta`: base triples, minus
every quad tombstoned by a `DE_Remove` at or before the read's
snapshot sequence number, plus every quad added by a `DE_Add`,
respecting `DE_Clear`/`DE_Drop`/`DE_Create` as whole-graph resets. This
is a pure function over already-decoded values — it does not itself
decide *how* the base is read (that stays `RDF.CottasStore.fst`'s
`cottas_ondisk_search` unchanged):

```fstar
module RDF.Store.Columnar.DeltaMerge

// Applied once, at store-open time (or on demand for a long-lived
// server that polls for new committed batches — §4.2), producing a
// resolved index the graph_backend's search functions consult.
val fold_delta_batches
  (batches : list delta_batch)   // in commit order
  : Tot delta_resolved            // added-set, tombstone-set, per-graph resets

// The actual read-time composition. Mirrors backend_search's shape
// (SPARQL11.Store.fst:103) so a GB_CottasOnDisk-with-delta variant
// slots into the existing match, not a parallel code path.
val merge_on_read
  (base_results : list triple)   // what cottas_ondisk_search already returns
  (delta : delta_resolved)
  (b : triple_pattern_bound)
  : Tot (list triple)
let merge_on_read base_results delta b =
  let survivors = filter_tombstoned base_results delta in
  let additions = filter_matching_bound (delta_added_triples delta) b in
  survivors @ additions

// Correctness obligation: querying base ⊕ delta after replaying
// delta_batches gives the same answer as applying apply_update_ops
// (SPARQL11.Algebra.fst:5716) directly to the in-memory rdf_dataset
// that base ⊕ delta represents. This is the semantic bridge between
// the existing 176/176-passing update algebra and the new durable
// path — without it, durability and correctness are two unrelated
// claims.
val lemma_merge_on_read_matches_apply_update
  (ds : rdf_dataset) (ops : list update_op) (b : triple_pattern_bound) :
  Lemma (
    let ds' = apply_update_ops ds ops in
    let batches = update_ops_to_delta_batches ops in
    mem_triples_matching b (dataset_search ds' b) ==
    mem_triples_matching b (merge_on_read (cottas_ondisk_search_pure ds b)
                                            (fold_delta_batches batches) b)
  )
```

`GB_CottasOnDisk` (`SPARQL11.Store.fst:33`) gains an optional delta
field (`cottas_ondisk_store -> cottas_ondisk_graph_scope -> option
delta_resolved -> graph_backend`, or a sibling constructor
`GB_CottasOnDiskWithDelta` if KaRaMeL's monomorphisation prefers
avoiding an `option` payload on a variant already carrying two other
fields — an implementation-stage decision, not a semantic one).
`backend_search`/`backend_search_limited`/`backend_estimate`
(`SPARQL11.Store.fst:103,167,197`) each grow one new match arm that
calls `merge_on_read`; no existing arm changes.

### 3.3 fsync/rename atomicity protocol — the OCaml I/O boundary

This is where rule #11's "pure I/O, no decisions" line is drawn. The
protocol itself (what gets fsynced, in what order, before what rename)
is a fixed sequence this doc specifies in prose; F\* owns the byte
layout being written (§3.1) and the decision of *what* to write
(§3.2); OCaml owns only the syscalls:

```fstar
// All ML-effect, all pure I/O per rule #11(a). No branching on
// delta_batch contents beyond "write these bytes then fsync."
assume val delta_log_append  : path:string -> bytes:list FStar.UInt8.t -> ML unit
assume val delta_log_fsync   : path:string -> ML unit
assume val delta_log_read_all: path:string -> ML (list FStar.UInt8.t)
assume val atomic_rename     : from_path:string -> to_path:string -> ML unit
assume val fsync_dir         : path:string -> ML unit   // durability of the rename itself
```

Commit sequence for one Update request (already-applied
`apply_update_ops` output turned into a `delta_batch` by
`update_ops_to_delta_batches`, §3.2):

1. `serialize_delta_batch` the batch (F\*, pure).
2. `delta_log_append` the bytes to `data.delta.log.tmp` — never the
   live `data.delta.log` directly (crash during append must not
   corrupt already-committed entries).

   Actually: appends go to the live log directly (POSIX `O_APPEND`
   writes are atomic for writes below `PIPE_BUF`/filesystem block
   size, and a corrupted *tail* entry — a partial write followed by
   crash — is detectable and truncatable at next-open replay, exactly
   like a WAL's own recovery story; a `.tmp`-then-rename dance is
   unnecessary for *append*, only for the base-file swap in step 5).
3. `delta_log_fsync` — this is the commit point. Before this returns,
   the update is not durable and must not be reported as succeeded to
   the SPARQL Update client (HTTP 204/200 per the Protocol spec).
4. After fsync returns, the update is durable; a concurrent reader
   that re-opens the store (or polls, §4.2) sees it.
5. **Compaction only** (not per-update): write a new `.cottas` +
   sidecars to a temp path, fsync every file, `atomic_rename` the temp
   base over the live path, `fsync_dir` the containing directory (the
   rename itself needs a directory fsync to be durable on most
   POSIX filesystems — a detail every WAL implementation gets bitten
   by if skipped), then truncate `data.delta.log` (itself: write
   empty-log bytes to a temp path, fsync, rename over the live log,
   fsync the directory again). Crash between "new base renamed in" and
   "delta log truncated" is safe and idempotent: on next open, the
   store finds the new base plus a delta log that still contains the
   entries already folded into that base — replaying already-applied
   entries a second time must be a no-op, which is why `DE_Add`/
   `DE_Remove` are set-like operations (idempotent by construction) and
   why `db_epoch` exists: a batch whose epoch is at or below the base
   file's own recorded "compacted through epoch N" marker (a small
   header field in the `.cottas` sidecar, or a companion `data.compacted-epoch`
   file, format also specified in F\*) is skipped on replay rather
   than re-applied.

This protocol is five `assume val`s, all pure-I/O per the taxonomy
table in the io-verification doc — no candidate for migration, same
tier as the existing `map_file`/clock/ZSTD-decompress realisations
already accepted at `experimental_ocaml_glue/parquet_footer_runtime.sh`.

### 3.4 RDFC-1.0 canonical snapshots and content-addressing

A compaction's output base file is a natural point to also compute
and record a canonical hash, connecting this design to the
content-addressing work already landing in
[`2026-07-05-graphs-api-design.md`](2026-07-05-graphs-api-design.md)
(the `urn:rdfc:sha256:<hex>` naming scheme, §2.1 of that doc) and the
E3 experiment in the shapes-canon storage doc (§5). Concretely:

- **Snapshot identity = canonical hash of the post-compaction dataset**
  (per-graph, via `RDF.Canonical.fst`'s existing `canonicalize_to_nquads`,
  HFDQ-only — decline to hash on an HFDQ tie exactly as the shapes-canon
  doc's E3 already specifies, rather than emit a wrong hash). A
  compacted base named/tagged by its own canonical hash gives:
  - **Verifiable replication.** A replica (or a backup) can be checked
    byte-for-byte against the hash without re-deriving it from the
    live store — the same round-trip-witness property §3.1's
    `expected_digest` gives delta batches, one level up the stack.
  - **Dedup across compactions.** If an update batch's net effect on
    a given named graph is empty (e.g. an INSERT immediately followed
    by an equivalent DELETE before the next compaction), the
    post-compaction canonical hash for that graph is unchanged from
    the pre-update one, and the compactor can skip rewriting that
    graph's rows entirely — the same "skip unchanged graphs" win the
    shapes-canon doc's E3 already proposes for the read-only ingest
    pipeline, now available on the write path too.
  - **Query-result cache soundness.** `(base canonical hash, delta
    log sequence number, query text)` is a sound cache key across the
    delta boundary — the base hash covers everything compaction has
    folded in, the sequence number covers everything since.
- **What it does not buy, honestly.** Canonical hashing is a
  compaction-time (i.e. infrequent, background) cost, not a per-update
  cost — computing an RDFC-1.0 hash on every single INSERT DATA would
  reintroduce an O(graph size) cost per update, exactly what §1's
  requirement 3 rules out. This design proposes computing it **only**
  at compaction boundaries, as an optional sidecar
  (`graph.c14n.sha256`, per the shapes-canon E3 experiment plan),
  never as part of the hot commit path in §3.3.

## 4. Interaction with today's components

### 4.1 The streaming fast path — must it see deltas? Yes.

The perf-review's item 4 (`SPARQL.Plan.Streamable.streamable_shape`,
landed 2026-07-05) answers `COUNT(*)`/`ASK`/named-graph-wildcard
`COUNT` queries by folding once over the parse stream, never
materializing the graph — a mechanism that today only applies to
Turtle/N-Quads *file parsing*, not to a `GB_CottasOnDisk` store (the
fast path's fold entry points are `Parser.Turtle.fold_turtle_triples`
etc., not a store-backed iterator). Once a store carries a delta, this
fast path — and any future streaming store-scan — must be defined as
a **composed iterator**: `stream_step` folds over base rows exactly as
today, and for each base row consults the delta's tombstone set before
counting it, then folds a final pass over the delta's addition set
(bounded by delta size, not base size, so it doesn't undermine the
44.1 MiB / 6.6 s bound the perf review measured). Concretely:

```fstar
val stream_step_with_delta
  (delta : delta_resolved)
  (acc : stream_acc)
  (t : triple)
  : Tot stream_acc
let stream_step_with_delta delta acc t =
  if triple_tombstoned delta t then acc else stream_step acc t

val stream_finish_with_delta
  (delta : delta_resolved)
  (acc : stream_acc)
  : Tot stream_acc
let stream_finish_with_delta delta acc =
  List.Tot.fold_left stream_step acc (delta_added_triples delta)
```

This keeps the existing `stream_step`/`streamable_shape` machinery
untouched (rule #13: never hand-edit the fast path's extracted logic)
and adds one new fold stage. An empty delta (the common case between
updates) must be provably a no-op — `stream_step_with_delta
delta_empty = stream_step` — so the fast path's measured numbers hold
exactly when there is nothing to compose against.

### 4.2 Offset-table / sidecars — which caches does a delta invalidate?

None of the base file's sidecars (per-column presence bitmaps, the
compound (p,o) bitmap, the Lamed3 offset index, the row-group-offset
table from the 2026-07-06 fix) are invalidated by a delta — they
describe the immutable base file and stay valid until the *next
compaction*, at which point they are rebuilt against the new base
exactly as `build_cottas_sidecars_eager` already does today (perf-review
§5 item 3). This is a direct consequence of choosing option 2.a: the
base file's sidecars are a base-file concern, the delta is a wholly
separate structure, and the "which caches invalidate on write" question
that plagues in-place-mutated stores (every index touched by a write
must be updated transactionally) does not arise here. What *is* new:
a small in-memory (or, at larger delta sizes, its own tiny companion
file — Open decision 2) index over the delta itself, so a bound-term
query doesn't linearly scan every uncompacted delta entry; at the
scale a delta realistically reaches between compactions (thousands to
low tens of thousands of entries, not millions), a plain per-term hash
set is adequate and does not need bitmap/offset-index machinery of its
own.

### 4.3 Eager-sidecar import — compaction re-runs it, unchanged

Compaction's output is, mechanically, exactly what
`corpus_pipeline.py materialize-nq-cottas-corpus --build-sidecars`
already produces for a fresh import (perf-review §5 item 3, including
the `--row-order cs` characteristic-set clustering if that policy is
in force for the corpus). No new sidecar-writer code is needed;
compaction's F\*/OCaml boundary is "run the existing eager-sidecar
import against base-rows ⊕ delta-rows as the new producer input,"
which is the same `write_cottas_clustered` + `build_cottas_sidecars_eager`
pair already committed, called from a new orchestration point (the
compactor) rather than from the CLI's import command. This also means
the 2026-07-06 `COTD`-magic fix and the row-group-offset-table fix
apply to every compacted base exactly as they apply to a fresh import
— no separate correctness story for "sidecars built via compaction" vs.
"sidecars built via `cottas-import`."

### 4.4 The planner's access paths — delta size as a stats input

`SPARQL.Plan.Estimate.fst` (recovery-plan §"Mapping the disaster onto
real names", retiring Mem5) already estimates cardinality from the
base's presence bitmaps; once a delta exists, its estimate must add
the delta's own matching-entry count (cheap — the delta's small
per-term hash set from §4.2 gives an exact count, not an estimate,
for the delta's contribution) so that BGP reordering doesn't
systematically under- or over-estimate selectivity for a
recently-updated pattern. This is a small additive term in an existing
function, not a new planner subsystem — but it does mean the planner's
`Capabilities` record (`RDF.Store.Capabilities.fst` in the recovery
plan) needs one more optional field, `delta_stats : option (tp_bound
-> nat)`, alongside the existing `estimate`/`count` capabilities, so a
store with no delta (the common case just after compaction) pays
nothing extra.

## 5. Staged implementation plan

Each stage is independently landable and independently testable. The
W3C SPARQL 1.1 Update suite (176 tests, §0) is **already at 100%
against the in-memory backend** — it is the regression floor every
stage below must not move, not a suite this plan needs to "get
running." A new suite this plan does need is a **durability harness**:
kill-and-recover tests that are not part of any W3C manifest (crash
recovery is implementation-defined, not a spec conformance concern) —
scoped explicitly in Stage 3/4 below rather than folded into the W3C
count.

| Stage | Deliverable | Acceptance test | Depends on |
|---|---|---|---|
| 1 | `RDF.Store.Columnar.DeltaLog.fst`: `delta_entry`/`delta_batch` types, `serialize`/`parse`/roundtrip lemma (§3.1). No I/O yet. | F\* verifies (z3 4.13.3, no `--lax`); `serialize_parse_roundtrip` proven for all five constructors; unit test round-trips 100+ generated entries through the F\*-extracted OCaml functions in-process (no disk yet). | none |
| 2 | `assume val` realisations (§3.3): `delta_log_append`/`_fsync`/`_read_all`, `atomic_rename`, `fsync_dir`. Hash-witness CI test per the io-verification pattern. | `expected_digest batch = sha256(read_bytes(path))` after a real append+fsync+read-back cycle, on-disk, this sandbox. | Stage 1 |
| 3 | `RDF.Store.Columnar.DeltaMerge.fst`: `fold_delta_batches`, `merge_on_read`, `lemma_merge_on_read_matches_apply_update` (§3.2). Wire one new `GB_CottasOnDisk`-with-delta match arm into `backend_search`/`_limited`/`_estimate` (`SPARQL11.Store.fst`). | The 176-test W3C Update suite, redirected to run its `UpdateEvaluationTest` cases against a `GB_CottasOnDisk`-backed dataset instead of (or alongside) the current `GB_List` in-memory dataset, still scores 176/176. New durability-specific harness (not W3C): apply the delta-log-recorded effect of every `UpdateEvaluationTest` case, kill the process (`SIGKILL`, not a clean exit) after the fsync point but before any subsequent operation, re-open, confirm the post-update state matches the manifest's expected `mf:result` graph exactly (no torn state) — one crash-point test per manifest category is the minimum bar, not one crash-point total. | Stages 1, 2 |
| 4 | Compaction: fold delta into a fresh `.cottas` base via the existing `corpus_pipeline.py` writer + eager sidecars (§4.3); `atomic_rename` swap; delta-log truncation with the `db_epoch` skip-on-replay guard (§3.3 step 5). | Kill-mid-compaction harness: crash after new-base-rename, before delta-truncate-rename — re-open must show the new base with an intact (not double-applied) delta replay. Kill before new-base-rename — re-open must show the old base, delta untouched. Both must reproduce the exact pre- or post-compaction row count and query results, never a mix. Regression: `tests/local/cottas_row_order_regressions.sh` and `cottas_corpus_regressions.sh` (existing, unchanged-path suites) still pass. | Stage 3 |
| 5 | Streaming fast path composed iterator (§4.1): `stream_step_with_delta`/`stream_finish_with_delta`. | `tests/local/streamable_fastpath_regressions.sh` (existing, 13 checks) re-run against a store with a non-empty delta added at each of the 13 query shapes; `delta_empty` case must reproduce the exact byte-identical output the existing suite already pins. | Stage 3 |
| 6 | Planner delta-stats input (§4.4): `Capabilities.delta_stats` field + `SPARQL.Plan.Estimate.fst` consult. | Estimate-error test (same methodology as shapes-canon E2): predicted vs. true cardinality on a handful of hand-built delta scenarios (pure addition, pure removal, mixed), labelled per scenario; no wall-time claim without its own measurement per the perf-benchmarking skill. | Stage 3 (does not depend on Stage 4/5) |
| 7 | RDFC-1.0 canonical-hash sidecar at compaction boundaries (§3.4), reusing the shapes-canon E3 plan's `.c14n.sha256` writer, decline-to-hash on HFDQ ties. | rdf-canon suite unchanged (62 pass, 23 fail, 1 skip of 86 — HNDQ gap, not this design's concern); new check: canonical hash of a compacted base's default graph matches an independently-computed `factoidal graphs hash` (or equivalent CLI, per the graphs-API design) run against the same rows read via the ordinary N-Quads dump path. | Stage 4; the graphs-API content-addressing slice (`2026-07-05-graphs-api-design.md`) for the CLI surface it reuses |
| 8 | HTTP/Protocol wiring: `factoidal-http`'s Update endpoint commits through the new path instead of mutating an in-process `rdf_dataset` and discarding it on restart (the implicit current behavior — no test today distinguishes "update applied in-memory" from "update durably committed" because nothing restarts mid-suite). Concurrent-reader test (§1 requirement 4): a second connection querying during an in-flight update sees pre- or post-, never partial. | New harness: two HTTP clients, one issuing a slow multi-op Update, one polling `SELECT` throughout — every observed result must be a strict pre/post snapshot; the existing `http-rdf-update` W3C manifest's Gimel2 shared-store sequence (19/19) still passes unchanged (it does not itself exercise concurrency, only sequential state). | Stages 3-7 |
| 9 | Parliament-scale validation (blocked on corpus access, per the perf-review's own caveat). Re-run the delta-penalty measurement (requirement 3) at 3.14M quads: empty-delta query times must match the cited baselines; a delta of realistic size (hundreds to low thousands of entries) must show delta-penalty overhead as a small, bounded addition, not a multiplier on corpus size. | Numeric comparison table, same format as the perf-review's own tables, run against the real ukparliament COTTAS artifact once reachable. | Stage 8 |

Stages 1-3 are the semantic core (byte format, I/O, merge) and are the
minimum for "durable UPDATE exists at all." Stages 4-7 make it
practical at scale (compaction, streaming-path parity, planner
awareness, content-addressed snapshots). Stage 8 closes the loop to
the actual HTTP-facing product. Stage 9 is the honesty check this
project's own culture demands before claiming the parliament number —
every measurement in the perf-review doc that could be checked in this
sandbox was; the ones that needed the real corpus were labeled cited,
not measured, and this plan inherits that discipline.

## 6. Open decisions for the owner

1. **Compaction trigger policy.** Size threshold (delta log reaches N
   bytes/entries), time threshold (compact every T minutes), or
   explicit-only (`factoidal compact`, no automatic trigger)? This
   design assumes a policy exists but does not fix one — it directly
   controls the "bounded delta penalty" constant in requirement 3 and
   the read-vs-write tradeoff at each corpus scale. Recommend starting
   explicit-only (simplest, no background-thread lifecycle to reason
   about) and adding a size-threshold auto-trigger once Stage 4's
   kill-mid-compaction harness is green and trusted.
2. **Delta-log index structure once delta size grows** (§4.2). This
   design assumes a plain per-term hash set is adequate between
   compactions. If the compaction policy above lands looser than
   expected (large deltas persisting a long time), the hash set's
   linear-in-delta-size cost could itself become the "must be a
   function of delta size, not corpus size, but must still be *fast*"
   pressure point — at which point the delta earns its own small
   presence-bitmap-style sidecar, converging toward option 2.b's LSM
   shape one layer at a time rather than adopting it wholesale up
   front. Decide the threshold empirically (measure delta-scan cost
   at realistic delta sizes) rather than pre-building indexing
   machinery for a delta size this project has no measurements
   motivating yet.
3. **Whether option 2.b (LSM multi-layer) is ever worth it.** §2.b's
   objection is sequencing (the base reader's own multi-row-group
   correctness only just got fixed, 2026-07-05), not a permanent
   rejection. Revisit once Stage 4-9 are landed and, if sustained
   high-throughput update workloads appear as a real requirement (not
   hypothesized here), re-open this as its own design doc rather than
   folding LSM complexity into this plan's Stage count.
4. **Concurrent-writer semantics.** This design specifies one writer
   at a time implicitly (the fsync/rename protocol in §3.3 has no
   provision for two processes appending to the same delta log
   concurrently — the perf-review's own §3.6/§1.4 already flags
   "process-global Hashtbl handles hit from multiple HTTP threads
   without Mutexes" as a latent bug in the existing read path). Decide
   whether a single-writer-process assumption (an advisory lock file,
   or simply documenting "one `factoidal serve` process owns writes")
   is acceptable for the near term, or whether Stage 8's HTTP wiring
   needs an explicit writer-serialization mechanism before it ships.
5. **LOAD's durability story.** LOAD is currently rejected at the HTTP
   sandbox layer (`SPARQL.Update.Analysis.fst`'s `update_has_load`)
   for reasons unrelated to durability (external HTTP fetch is outside
   the F\* runtime's purview). Once a durable path exists, does LOAD
   get re-enabled for non-sandboxed (CLI-driven, trusted-input)
   contexts, treating a large LOAD as a batch INSERT that should
   probably go through the copy-on-write compaction path directly
   (§2.c) rather than through the per-triple delta log? This is a
   product decision (is LOAD a "many small INSERT DATA ops" or "one
   bulk rebuild"), not something this doc's architecture forces either
   way.
6. **How `db_epoch`/compacted-epoch tracking is exposed to operators.**
   §3.3's crash-recovery correctness depends on a base file recording
   "compacted through epoch N" somewhere durable. Is that a new
   companion file (`data.compacted-epoch`, one more small format to
   spec and hash-witness per §3.1's pattern) or a header field folded
   into an existing sidecar? Either works; pick one before Stage 4
   rather than during it, since it changes what "the new base" means
   in the kill-mid-compaction test's assertions.
