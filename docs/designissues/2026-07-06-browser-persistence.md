# Browser-side persistence for durable SPARQL UPDATE (issue #282)

**Owner question (verbatim):** "How will db running clientside in hub
store data persistently?"

**Answer this doc designs and partially ships:** the same three pure
F\* byte formats the native on-disk delta log already uses — the
`delta_batch` framing (`RDF.Store.Columnar.DeltaLog.fst`, magic +
version + length + checksum, proved round-trip), the merge-on-read
composition (`RDF.Store.Columnar.DeltaMerge.fst`'s `apply_entries_ref`
/ `delta_batches_named_graphs`), and the SPARQL-Update-to-delta-entries
translator (`update_ops_to_delta_entries`) — plus a **browser**
realisation of the five I/O primitives, backed by IndexedDB rather
than `Unix.openfile`/`fsync`/`rename`. Scope: design + a commit-sized
working prototype (§4-5). Compaction, OPFS, and the actual hub demo
page are named and staged (§3, §6) but not built here.

## 0. What already exists (read directly from the tree, not assumed)

This corrects an assumption the original design doc
([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md))
carried as a staged plan: by the time this doc was written, stages
1-4+8 of that plan were **already landed**, natively:

- `RDF.Store.Columnar.DeltaLog.fst` (1280 lines): `delta_entry` (5
  constructors), `delta_batch`, framed serialize/parse with a
  non-cryptographic checksum, a log-file format (`DLOG` header +
  batches), a compacted-epoch companion-file format (`CEP1`), and the
  five `ML` I/O `assume val`s (`delta_log_append`/`_fsync`/`_read_all`,
  `atomic_rename`, `fsync_dir`), realised in
  [`minimal_regrettable_glue_code_each_with_an_open_issue/282_delta_log_io.sh`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/282_delta_log_io.sh)
  with plain `Unix` syscalls (this doc's own issue number, #282, names
  that patch).
- `RDF.Store.Columnar.DeltaMerge.fst` (903 lines): `delta_resolved`,
  `fold_delta_batches`, `merge_on_read`, `apply_entries_ref` (the
  reference merge a plain `rdf_graph` composes against), and
  `update_ops_to_delta_entries` (`op_to_delta_entries` per-op,
  `request_salt`-threaded for INSERT DATA's bnode-uniqueness
  discipline) — translating a parsed `SPARQL11_Algebra.update_op` list
  into `delta_entry list`, `None` for anything it can't yet express
  (`DELETE/INSERT WHERE`, `COPY`, `MOVE`, `ADD`).
- `bin/factoidal-cli/factoidal_cli.ml`'s `--delta-log PATH` (query-time
  merge-on-read) and `compact` subcommand (fold delta into a fresh
  `.cottas` base).
- `bin/factoidal-http/factoidal_http.ml`'s `--rw --delta-log PATH`:
  `POST /update` translates via `update_ops_to_delta_entries`, commits
  through `commit_delta_entries` (append + fsync), and 501s rather than
  silently falling back to in-memory-only apply when the op isn't yet
  translatable (rule #26 — no misleading success).
- `bin/delta-log-probe/probe.ml`: the crash-kill harness driver
  (`tests/local/delta_log_crash_harness.sh`, not read in full here but
  named by probe.ml's own header) — same shape this doc's browser
  torn-write test borrows (§5.3).

**What does not exist before this doc:** any of it running where
there is no `Unix.openfile` — a browser tab. `RDF.Store.Columnar.
DeltaLog` is already compiled into the `js_of_ocaml` bundle (it's in
`build-ocaml.sh`'s `FSTAR_MODULES` array, used by both `w3c_runner.js`
and `factoidal.js`), but the module's only `ML` surface — the five
`assume val`s — resolves, in the JS build, to whatever `js_of_ocaml`'s
`Unix` shim does with `Unix.openfile`/`Unix.fsync`/`Unix.rename`
against its **pseudo-filesystem** (`MlFakeDevice`, the same fake FS
`jsoo_fs_tmp` populates for `runFactoidalCli()`'s CLI-argv-driven
calls — see `npm/factoidal/browser.js`'s own header comment). That
pseudo-FS is **in-memory and reset on every bundle eval** — it is not
backed by IndexedDB, OPFS, or anything that survives a page reload.
Calling the native `delta_log_append`/`_read_all` realisation from a
browser tab would silently "work" (no crash) and silently **not
persist across a reload** — exactly the kind of misleading success
rule #26 exists to catch. This doc does not attempt to redirect the
native realisation's `Unix` calls into browser storage (that would
mean forking `js_of_ocaml`'s `Unix` shim, a much larger and more
fragile undertaking than the alternative below); instead §4 adds a
**second, parallel set of entry points** that call only the `Tot`
(pure) F\* functions — `serialize_delta_batch`/`parse_delta_batch`/
`apply_entries_ref`/`update_ops_to_delta_entries` — and hands the
resulting bytes to genuinely-persistent browser storage via ordinary
JS glue, never touching the native `assume val` realisation at all.

## 1. The v1 architecture decision: IndexedDB, not OPFS — and why

### 1.1 What OPFS actually offers, read against the spec, not assumed

The Origin Private File System (OPFS) is the browser storage layer
that reads most like "a real filesystem" — `FileSystemFileHandle`s
support:

- **Async writes**, available on the main thread:
  `handle.createWritable()` returns a `FileSystemWritableFileStream`;
  `write()`/`close()` are `Promise`-based. Per spec, the stream stages
  writes and **only swaps them into the visible file atomically when
  `close()` resolves** — the closest browser analogue to the native
  design's temp-file-then-rename step (§3.3 of the durable-update
  design doc). The gotcha that matters for a log file specifically:
  `createWritable()` **truncates the file to zero length immediately
  on open** unless called with `{ keepExistingData: true }` — an
  append-only log opened the naive way would lose everything written
  before the current session on the very first `createWritable()`
  call. Getting append semantics right needs `keepExistingData: true`
  plus a manual `stream.seek(currentSize)` before writing, and even
  then the *durability* boundary is `close()`, not each individual
  `write()` — several small `delta_log_append`-shaped calls sharing
  one still-open stream are not each independently durable the way the
  native design's per-append `O_APPEND` + explicit `fsync` boundary is
  (§3.3 step 2's "appends go to the live log directly ... a corrupted
  *tail* entry is detectable and truncatable" reasoning assumes each
  append can crash independently; the async-writable-stream model
  instead makes one **whole open-to-close session** the atomic/durable
  unit).
- **Sync access handles**, `handle.createSyncAccessHandle()` — true
  synchronous `read`/`write`/`flush`/`close`, no `Promise` overhead,
  the API that could make an *append-then-fsync-per-call* protocol
  read almost identically to the native `Unix` realisation
  (`accessHandle.flush()` is the direct analogue of `Unix.fsync`).
  **This API is worker-only** by spec and in every shipping
  implementation checked against (Chromium, Firefox, WebKit all gate
  `createSyncAccessHandle` to a dedicated worker context) — calling it
  from the main thread throws. This is the load-bearing constraint for
  this decision.

### 1.2 The js_of_ocaml threading constraint, stated precisely

`js_of_ocaml` compiles OCaml's single-threaded runtime to a single
JS execution context; there is no shared-memory thread pool the way
native OCaml has none either. "Running the engine in a worker" in
jsoo terms does not mean "spawn a green thread" — it means **a wholly
separate JS execution context**: a real `Worker` object, with its own
instantiation of the `js_of_ocaml` bundle (a second `factoidal.js`/
`factoidal-npm-entry.js` eval, or a worker-specific bundle), reachable
from the main thread only via `postMessage`. Every query, update, and
delta-log operation would need to cross that `postMessage` boundary —
serializing the request, awaiting a response — which is a bigger
architectural move than "add IndexedDB calls to the existing
entry_jsoo.ml ABI": it means the hub's `mountCell()` convention
(`docs/_includes/hub.njk`, synchronous-feeling `await`s against a
main-thread-loaded bundle) would need a worker-RPC layer that does not
exist today, for every cell that touches the engine, not just the
persistence-using ones. `js_of_ocaml`'s own async story
(`js_of_ocaml-lwt`) maps `Lwt.t` promises to JS `Promise`s inside
**one** execution context; it does not grant a main-thread bundle
access to a worker's synchronous OPFS handle — Lwt concurrency and
worker isolation are orthogonal, and conflating them here would be the
kind of unearned architectural claim this project's own culture
(rule #26) explicitly disallows.

### 1.3 Decision: IndexedDB for v1, OPFS-via-worker named as the v2 track

**v1 (this doc, §4-5, shipped): IndexedDB**, called from the main
thread, no worker required. Every write is one `objectStore.put()`
inside a `readwrite` transaction; every read is a cursor walk. This is
fully async (`Promise`-wrapped `IDBRequest`s), works in every browser
`js_of_ocaml`/hub cells already target, and needs zero change to the
threading model hub cells run under today.

**What v1 gives up, stated plainly, against the native fsync/rename
protocol (§3.3 of the durable-update design doc):**

- **Durability strength is whatever the browser's IndexedDB
  implementation guarantees, not a `fsync(2)` call this code controls —
  and this is not a hypothetical caveat, it is Chrome's actual shipped
  default.** IndexedDB's `durability` transaction option
  (`'default' | 'strict' | 'relaxed'`): under `'strict'`, `oncomplete`
  does not fire until the OS has actually flushed the write; under
  `'relaxed'`, `oncomplete` can fire once the change reaches the OS
  write buffer, "typically flushed every couple seconds" (Chrome's own
  developer-blog phrasing). **Chrome changed its own default from
  `'strict'` to `'relaxed'` starting at Chrome 121**, matching
  Firefox/Safari's prior behavior, explicitly to buy throughput (cited
  real-world speedups of 3-30×). This is the exact gap between "commit
  means durable" (the native design's fsync-gated step 3) and "commit
  means queued" — silently inheriting a browser's default would make
  this whole design's durability claim quietly weaker than stated, so
  `deltaLogAppend` (§4.2) passes `{ durability: 'strict' }` explicitly
  on every write transaction rather than accepting whatever the
  browser's own default currently is. Even with `'strict'` requested,
  this is a configuration choice honored by someone else's storage
  engine — not a guarantee this codebase can independently verify the
  way it can verify its own `Unix.fsync` call actually happened.
- **No atomic multi-file rename primitive is needed — and IndexedDB's
  own transaction model is arguably *better* here.** The native
  design's compaction step (§3.3 step 5) needs `atomic_rename` +
  `fsync_dir` specifically because POSIX has no native multi-file
  transaction — swapping in a new base *and* truncating the delta log
  atomically requires the rename trick. IndexedDB transactions are
  natively atomic across multiple object-store operations: a
  compaction commit (§3 below) can delete every old delta record and
  insert the new compacted-base record **in one transaction**, with no
  rename-equivalent needed at all — a point in IndexedDB's favor, not
  just a fallback's consolation prize.
- **No OPFS-grade random-access editing.** IndexedDB is a
  key/value/record store; there is no "seek and overwrite bytes 40-44
  of an existing large blob" operation the way an OPFS access handle
  offers. This does not matter for the append-only delta log (every
  write is a brand-new record) but would matter if a future stage
  wanted the *compacted base* itself (the `.cottas` + sidecars,
  megabytes) to live byte-addressably in browser storage rather than
  as one opaque blob record — an OPFS question, deferred to v2.

**v2 (named, not built): OPFS via a dedicated worker.** Once (or if) a
worker-RPC layer exists for the engine generally, `createSyncAccessHandle`
gives every one of the native design's I/O primitives a near-literal
browser analogue (`write` → `write`, `flush` → `fsync`, `close` →
implicit visibility) with better throughput than IndexedDB's
per-record transaction overhead, and OPFS's `FileSystemDirectoryHandle`
supports `move()` (an actual rename-shaped primitive) for the
compaction swap. This is the natural next step *if* sustained update
throughput in a browser tab is ever a real requirement — not
hypothesized further here, per this project's own discipline of not
pre-building for an unmeasured need.

## 2. Tab-close/crash guarantees — mapped to the browser

Every guarantee the native kill-harness (`bin/delta-log-probe/
probe.ml`, `tests/local/delta_log_crash_harness.sh`) tests has a
browser equivalent, with one gap called out plainly rather than
glossed over:

| Native guarantee | Browser equivalent | Note |
|---|---|---|
| `SIGKILL` mid-`O_APPEND` write leaves a torn tail, detected by checksum on next open | Tab crash / OS force-quit mid-`IDBTransaction` | IndexedDB transactions are atomic by spec — there is **no torn-write case from ordinary browser use** the way a torn `write()` syscall exists natively. §5.3's torn-write test therefore cannot reproduce a *real* browser failure mode; it directly pokes the store to prove the **checksum framing itself** still rejects a corrupted record if one ever got there by any means (a future OPFS worker path, a buggy migration, manual devtools tampering) — same defense-in-depth reasoning, weaker "how would this ever happen" story. |
| Crash after `fsync` returns = durable; before = not | Crash after `transaction.oncomplete` fires = durable (subject to §1.3's `durability` caveat); before = not observed on reload | Matches structurally; the browser's flush guarantee is opaque instead of a syscall this code invoked directly. |
| Crash mid-compaction (`atomic_rename` not yet called) = old base + full delta log, safe | Crash mid-compaction transaction (not committed) = old delta records + no new compacted record, safe | IndexedDB's native multi-op transaction atomicity (§1.3) makes this *simpler* than the native two-rename dance, not harder. |
| Process restart re-reads the log from disk, replays merge-on-read | Page reload re-opens the IndexedDB database (survives the reload, the tab close, and the browser restart) and replays merge-on-read | This is the literal claim §5.2's smoke test proves end-to-end. |
| Machine power-cut | Browser/OS crash, or OS power-cut with the browser's own storage backend (also disk-backed) | Same ultimate backing store (disk) one layer down; this design does not get to inspect or control that layer's own fsync discipline, same caveat as `durability` above. |
| **No equivalent natively — a new failure mode** | **Storage eviction wipes the whole origin's data at once** | See §3 below — this has no native analogue at all; a torn-write checksum does not protect against it, because there is no partial state to detect, only total absence. |

## 3. Quota and eviction — what happens to the durability claim

Browsers classify most storage (IndexedDB, OPFS, Cache API) as
**"best-effort"** by default: under device storage pressure, the
browser may evict an *entire origin's* data to reclaim space, using an
LRU-ish policy across origins (least-recently-used origin evicted
first), with no partial-eviction story — it is not equivalent to a
crash mid-write (which leaves a torn tail a checksum can detect); it
is the **entire durable log and every prior compacted base
disappearing atomically, with no local signal that it happened** until
the next `IDBDatabase.open()` finds an empty/nonexistent database.

- **`navigator.storage.persist()`** requests **"persistent"** storage
  mode, which (where granted) exempts the origin from the
  eviction-under-pressure story. Grant heuristics are
  browser-specific and outside this codebase's control — some browsers
  auto-grant based on site-engagement heuristics (bookmarked, added to
  home screen, high interaction), others prompt the user explicitly.
  **This design recommends the browser-side persistence layer call
  `navigator.storage.persist()` on first use and surface its boolean
  result to the caller** (not yet wired into the §4 prototype — named
  named here as a gap, not silently assumed) so a page embedding
  this can tell its own user "your data is/isn't protected from
  eviction" rather than silently discovering the answer only after
  loss.
- **`navigator.storage.persist()` granted is still not "guaranteed
  forever."** A user clearing site data/cookies/history in browser
  settings removes persistent storage too — `persist()` defends
  against automatic eviction *under storage pressure*, not against a
  human deliberately clearing data, which is a real and available
  browser UI action with no equivalent "are you sure, this deletes a
  durable database" gate the way deleting a real on-disk file usually
  does have (a file manager's own delete confirmation, at least).
- **Quota is finite and origin-shared.** `navigator.storage.estimate()`
  returns `{usage, quota}`; a delta log growing without the
  compaction step (§3.3 of the durable-update design, "fold into a
  fresh base, truncate the log") competes for the SAME quota as every
  other IndexedDB/OPFS/Cache consumer on the origin. This is the
  browser-side argument for taking compaction *more* seriously than
  the native "explicit-only, simplest" recommendation (durable-update
  design doc's Open decision 1) — an uncompacted browser log has a
  harder quota ceiling than an uncompacted server-side log sitting on
  a multi-TB disk.
- **What survives this, stated plainly:** the checksum/framing machinery
  (§0) protects against **partial corruption** (a torn write, a
  truncated blob) — it says nothing about, and cannot say anything
  about, **total loss via eviction**. A durability claim built on this
  design should say "survives reloads and browser restarts, **as long
  as the browser has not evicted the origin's storage**" — never
  "survives forever," and never silently drop the caveat (rule #26).

## 4. The prototype (this commit)

### 4.1 New F\*-backed ABI in `bin/npm-entry/entry_jsoo.ml`

Two new exports on `factoidalNpmEntry` (full ABI doc in that file's
header comment):

```
factoidalNpmEntry.deltaBatchToHex(sparqlUpdate, seq, epoch)
  -> {"ok":true,"hex":"...","opCount":N} | {"ok":false,"error":"..."}

factoidalNpmEntry.deltaMergeApplyBrowser(nquads, hexBlobsNewlineJoined)
  -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
```

`deltaBatchToHex` parses a SPARQL Update (`SPARQL11_Parser.
parse_sparql_update`), translates its ops via the **already-verified,
already-native** `RDF_Store_Columnar_DeltaMerge.update_ops_to_delta_entries`
(INSERT DATA / DELETE DATA / CLEAR / DROP / CREATE only — the same
subset the native `--rw` commit path accepts, rejecting
anything else rather than silently no-op'ing, rule #26), builds a
`delta_batch` (`db_seq`/`db_epoch` from the caller, so the *browser*
owns log-ordering bookkeeping — an IndexedDB key, not a server
sequence counter), and serializes it via
`RDF_Store_Columnar_DeltaLog.serialize_delta_batch` — the exact same
checksummed, self-framed byte format the native on-disk log uses,
proved round-trip-correct in `RDF.Store.Columnar.DeltaLog.fst` §8.
`deltaMergeApplyBrowser` is the read-back half: parse each hex blob
independently (`parse_delta_batch`; a blob that fails to parse is
**skipped**, never partially decoded — the per-record analogue of the
native log's "accept a prefix, never a torn entry" contract), then
merge onto the base dataset via `apply_entries_ref` per graph
(`delta_batches_named_graphs` discovers CREATE-only graphs with no
base rows of their own).

**Wire encoding: hex, not `RDF_Bytes.bytes_to_string`.** `RDF_Bytes.
bytes` is `int list` (`FStar.Char.char` extracts to a plain OCaml
`int`, 0-255); the existing `bytes_to_string`/`bytes_of_string`
round-trip through `BatUTF8` (`FStar_String.ml`), which raises
`BatUChar.Out_of_range` on an arbitrary byte ≥ 128 that doesn't happen
to start a valid UTF-8 sequence — `bin/delta-log-probe/probe.ml`'s own
header comment documents hitting exactly this while building the
native crash harness, and works around it there by slicing the raw
`int list` instead of the string form. This ABI sidesteps the question
entirely: `hex_of_bytes`/`bytes_of_hex` (new, in `entry_jsoo.ml`, ~15
lines) convert directly between the `int list` and a hex string,
which is unambiguous JSON-embeddable text regardless of byte value.
This is ABI wire-transport encoding at a `bin/<consumer>` boundary
(rule #11 scopes byte-**layout** decisions to F\*, not ABI transport
encoding at a consumer entry point — the same category as this file's
pre-existing `jstr`/JSON-escaping helpers).

Per rule #11: no RDF/SPARQL semantics live in the new OCaml — every
byte assembled or interpreted goes through the already-verified F\*
functions named above; the OCaml only hex-encodes/decodes, loops over
graph names, and builds the JSON envelope.

### 4.2 New browser-side storage glue in `npm/factoidal/browser.js`

`deltaLogOpen`/`deltaLogAppend`/`deltaLogReadAllHex`/`deltaLogMerge`
(plus a test-only `_deltaLogCorruptLastForTest`), all backed by one
IndexedDB object store (`deltaBatches`, keyPath `seq`). `deltaLogAppend`:

1. Computes the next `seq` as `store.count()` (single-writer-tab
   assumption, same shape the native design's Open decision 4 accepts
   for the near term — one `factoidal serve` process there, one
   browser tab here).
2. Calls `factoidalNpmEntry.deltaBatchToHex` (loaded once via the
   existing `loadNpmEntry()` — no new bundle-loading machinery) to get
   the hex blob.
3. `put()`s `{seq, epoch, hex}` in one `readwrite` transaction, and
   resolves only on `transaction.oncomplete` — the commit point
   (§1.3/§2's durability boundary).

`deltaLogMerge` reads every record back (`getAll()`, sorted by `seq`
client-side since IndexedDB's `keyPath` ordering is already numeric-key
order but this makes the contract explicit rather than relying on
implicit cursor order), joins the hex blobs with `\n`, and calls
`deltaMergeApplyBrowser` once. This function makes **zero** calls into
the native `assume val` realisation (§0) — it is a wholly separate
path from `runFactoidalCli()`'s `jsoo_fs_tmp` pseudo-FS.

### 4.3 What was NOT built (named, not silently skipped)

- **Compaction.** No browser-side "fold the log into a fresh
  compacted-base record" exists yet. At prototype scale (a handful of
  small updates) this is not yet a quota problem (§3); the natural
  home for it, once built, is one IndexedDB transaction that deletes
  every existing `deltaBatches` record and inserts a single
  `compactedBase` record holding the merged N-Quads text (or, once a
  native browser writer exists, a COTTAS blob) — the "IndexedDB's
  transaction model beats the rename trick" point from §1.3.
- **`navigator.storage.persist()` wiring.** Named as a gap in
  §3 — the prototype does not request persistent storage or surface
  the grant result.
- **The hub demo page itself.** Per the task brief: this doc's
  deliverable is the mechanism + proof (§5), not the post. A future
  hub post (`docs/web/hub/`) can drive `deltaLogAppend`/`deltaLogMerge`
  from an `observable-js` cell using the same ABI this prototype
  exposes.
- **OPFS/worker path.** Named in §1.3 as the v2 track, not attempted.

## 5. The proof: `tests/web-demos/browser_persistence_smoke.sh`

Headless-Chromium harness (Playwright), same pattern as
`tests/web-demos/hub_posts_smoke.sh`: serves a small static page over
`python3 -m http.server`, drives real browser navigation (not just
in-page JS state), and asserts on `page.evaluate()` results.

1. **Reload-survival (the persistence claim, real navigation).** Load
   the page; parse a small fixture dataset; run two SPARQL Updates
   (`INSERT DATA`, then a `DELETE DATA` + a `CREATE`+`INSERT DATA` into
   a new named graph) through `deltaLogAppend`; confirm `deltaLogMerge`
   reproduces the expected merged graph **in the same page load**
   first (sanity), then call `page.reload()` — an actual browser
   navigation event, not a SPA route change — and confirm
   `deltaLogMerge` against the SAME `dbName` reproduces the **identical**
   merged graph after the reload, proving the data survived the
   navigation (IndexedDB, unlike an in-page JS variable or the jsoo
   pseudo-FS, is not reset by a reload).
2. **Torn-write recovery.** After the reload-survival pass, call
   `_deltaLogCorruptLastForTest` to truncate the most recently written
   record's hex blob, then re-run `deltaLogMerge`: assert the result
   equals the merge **excluding** the corrupted batch's ops (the
   "clean prefix survives, corrupt entry never appears" contract
   `parse_delta_batch`'s checksum enforces), and assert none of the
   corrupted batch's triples appear anywhere in the output (never a
   partially-decoded garbage entry).

Both assertions are driven against the REAL `factoidal-npm-entry.js`
bundle (rebuilt for this task to include the two new exports — see the
task report for the rebuild command) and REAL `IndexedDB`, inside REAL
headless Chromium — not a mock.

## 6. Staging beyond this commit

| Stage | Deliverable | Depends on |
|---|---|---|
| Next | `navigator.storage.persist()` call + surfaced grant result in `deltaLogOpen()` | none |
| Next | Browser-side compaction (single-transaction record collapse, §4.3) | none |
| Later | Hub demo post exercising `deltaLogAppend`/`deltaLogMerge` from an `observable-js` cell | this prototype |
| Later | `DELETE/INSERT WHERE` translation once the native `update_ops_to_delta_entries` gains it (tracked against the native durable-update design doc, not duplicated here) | native-side work, not browser-side |
| v2 | OPFS-via-dedicated-worker path (§1.3) | a general worker-RPC layer for the engine, not scoped to this doc |
| v2 | Real UK-Parliament-scale browser measurement (the in-memory-bytes-store doc's §2.4 "kicker" — COTTAS bytes in a tab), composed with this delta-log layer once both exist | `2026-07-06-inmemory-bytes-store.md`'s stage 5 |

## Sources consulted (§1.1, §1.3's durability claim)

- [MDN: `FileSystemFileHandle.createSyncAccessHandle()`](https://developer.mozilla.org/en-US/docs/Web/API/FileSystemFileHandle/createSyncAccessHandle) — worker-only restriction.
- [MDN: Origin private file system](https://developer.mozilla.org/en-US/docs/Web/API/File_System_API/Origin_private_file_system) — `createWritable()` vs. sync access handle semantics.
- [Chrome for Developers: "A change to the default durability mode in IndexedDB"](https://developer.chrome.com/blog/indexeddb-durability-mode-now-defaults-to-relaxed) — the Chrome 121 `strict` → `relaxed` default change, cited verbatim in §1.3.
