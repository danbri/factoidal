# Unified store-capability seam — one interface for every RDF backend

**Status:** design doc, no code. Territory: this file only. Sibling
sessions are active in
[`formal/fstar/RDF.Store.Columnar.DeltaLog.fst`](../../formal/fstar/RDF.Store.Columnar.DeltaLog.fst),
[`formal/fstar/RDF.CottasStore.fst`](../../formal/fstar/RDF.CottasStore.fst),
and the HDT container modules; this doc reads them and proposes the
seam that lets their work land behind one interface, but edits none of
them.

Read first and not edited:
[`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
(the planner module family + the storage-abstraction-map table this
doc realises),
[`2026-07-05-disk-backed-db-perf-review.md`](2026-07-05-disk-backed-db-perf-review.md)
(current architecture + this week's measured landings),
[`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
(the COTTAS + delta-log read-write view),
[`2026-07-06-hdt-program-plan.md`](2026-07-06-hdt-program-plan.md)
(HDT read-only, whose stage 4 explicitly targets a shared access-path
seam), and
[`2026-07-05-foundational-core-refactor.md`](2026-07-05-foundational-core-refactor.md)
(the module-split steps this doc reconciles against, §5.7 below).

## 0. The goal, and why a seam

The owner goal is "a verified performant read-write RDF/SPARQL database
with efficient on-disk indices and an architecture that maximises
commonalities across all backends." Today the codebase has three real
backends and two more arriving, and the evaluator reaches each of them
by matching on a constructor tag. Every capability the planner needs —
solve, count, estimate, presence-probe, decode-failure — is a separate
function that re-lists all backend constructors. Adding a backend means
editing every one of those functions. The durable-UPDATE design and the
HDT plan each add a backend; landing them the current way multiplies the
per-backend match arms rather than reducing them.

This doc specifies the single typed capability seam the planner and
evaluator consult instead. It is the concrete F\* realisation of the
storage-abstraction-map table in the recovery plan
([`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
§"Storage abstraction map") — that table names the capabilities; this
doc gives them a record type, shows each of the three backends
realising it from entry points that already exist, and shows
COTTAS+delta as a composition rather than a new variant.

## 1. Audit of today's per-backend seams

Every place the read/plan path branches on backend identity, with
file:line. The count at the bottom is the baseline this design reduces.

### 1.1 The backend tag and its dispatch family (`SPARQL11.Store.fst`)

The tag is `graph_backend`, six constructors,
[`SPARQL11.Store.fst:23-34`](../../formal/fstar/SPARQL11.Store.fst):

```
GB_List | GB_Indexed | GB_HDT | GB_COTTAS | GB_CottasOnDisk | GB_Union
```

Six functions each `match gb with` over those constructors, one arm per
backend:

| Dispatch function | Location | Arms | What each backend supplies |
|---|---|---|---|
| `backend_search` | [:103](../../formal/fstar/SPARQL11.Store.fst) | 6 | `store_search` / `ig_search` / `hdt_search_triples` / `cottas_search` / `cottas_ondisk_search` / union |
| `backend_search_limited` | [:167](../../formal/fstar/SPARQL11.Store.fst) | 3 (COTTAS-on-disk, union, wildcard) | LIMIT pushdown for on-disk; `list_take_n` truncation for the rest ([:185-188](../../formal/fstar/SPARQL11.Store.fst)) |
| `backend_estimate` | [:197](../../formal/fstar/SPARQL11.Store.fst) | 6 | `store_estimate` / `ig_estimate` / `hdt_estimate` / `cottas_estimate` / `cottas_ondisk_estimate` / union |
| `backend_count_exact` | [:229](../../formal/fstar/SPARQL11.Store.fst) | 3 (COTTAS-on-disk, union, wildcard→`backend_estimate`) | exact count where estimate approximates |
| `backend_predicate_present` | [:246](../../formal/fstar/SPARQL11.Store.fst) | 6 | presence probe per backend |
| `backend_decode_failure` | [:290](../../formal/fstar/SPARQL11.Store.fst) | 3 (COTTAS-on-disk, union, wildcard→`false`) | issue #269 empty-vs-unreadable distinction |

Each of the six has a `GB_Union` recursion twin that exists only to walk
the union list: `union_backend_search_acc`
([:94](../../formal/fstar/SPARQL11.Store.fst)),
`union_backend_search_limited_acc`
([:152](../../formal/fstar/SPARQL11.Store.fst)),
`union_backend_estimate` ([:190](../../formal/fstar/SPARQL11.Store.fst)),
`union_backend_count_exact` ([:222](../../formal/fstar/SPARQL11.Store.fst)),
`union_backend_predicate_present`
([:238](../../formal/fstar/SPARQL11.Store.fst)),
`union_backend_decode_failure`
([:283](../../formal/fstar/SPARQL11.Store.fst)).

That is **6 dispatch functions + 6 union twins = 12 functions in the
tag-dispatch family**. A new backend adds an arm to each of the six
dispatchers; the twins are the seam paying for `GB_Union` being a
constructor rather than a caller-side list of the interface.

Constructor sites that build these tags: `indexed_graph_backend`
([:53](../../formal/fstar/SPARQL11.Store.fst)),
`indexed_dataset_backend` ([:56](../../formal/fstar/SPARQL11.Store.fst)),
`cottas_ondisk_dataset_backend`
([:75](../../formal/fstar/SPARQL11.Store.fst)).

### 1.2 Two parallel streaming-shape detectors

The COUNT(\*)/ASK fast-path shape recognizer exists **twice**, by
deliberate duplication (not sharing):

- Post-backend, "Aleph6" family in `SPARQL11.Store.fst`:
  `extract_single_tp_bgp` ([:428](../../formal/fstar/SPARQL11.Store.fst)),
  `detect_count_star_select` ([:437](../../formal/fstar/SPARQL11.Store.fst)),
  `detect_streaming_count_star` ([:455](../../formal/fstar/SPARQL11.Store.fst)),
  `detect_streaming_count_group_by_graph`
  ([:499](../../formal/fstar/SPARQL11.Store.fst)). These run after a
  `graph_backend` exists and answer through `backend_count_exact`
  ([:802](../../formal/fstar/SPARQL11.Store.fst),
  [:875](../../formal/fstar/SPARQL11.Store.fst)).
- Pre-backend, in
  [`SPARQL.Plan.Streamable.fst`](../../formal/fstar/SPARQL.Plan.Streamable.fst):
  `extract_single_tp_bgp` ([:123](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `detect_count_star_select` ([:131](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `common_modifiers_ok` ([:158](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `detect_count_default` ([:169](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `detect_count_any_named_graph` ([:192](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `detect_ask_default` ([:224](../../formal/fstar/SPARQL.Plan.Streamable.fst)),
  `streamable_shape` ([:244](../../formal/fstar/SPARQL.Plan.Streamable.fst)).

The `SPARQL.Plan.Streamable` banner states the duplication explicitly:
its `extract_single_tp_bgp` is "duplicated (not imported) so this
module stays below `SPARQL11.Store` in the dependency order"
([:118-122](../../formal/fstar/SPARQL.Plan.Streamable.fst)), and its
`detect_count_star_select` "Mirrors
`SPARQL11.Store.detect_count_star_select`"
([:130](../../formal/fstar/SPARQL.Plan.Streamable.fst)). Two copies of
the same shape logic exist because one runs before any store exists
(off the parse stream) and one after — the seam is what forces the
split.

### 1.3 The CLI fast-path dispatch (`bin/factoidal-cli/factoidal_cli.ml`)

Three sites branch on backend identity:

- The streaming fast-path gate
  ([:1286-1291](../../bin/factoidal-cli/factoidal_cli.ml)): takes the
  `SPARQL.Plan.Streamable.streamable_shape` path only when
  `data_cottas_files = []`, `named_graphs = []`, `entail_regime = ""`,
  and there is at least one plain `--data` file — i.e. gated off for
  every store-backed input.
- `use_backend_exec`
  ([:1460-1465](../../bin/factoidal-cli/factoidal_cli.ml)): selects the
  `SPARQL11_Store` backend executor for SELECT/ASK when entailment is
  the identity.
- COTTAS open + `build_dataset_backend`
  ([:1473-1479](../../bin/factoidal-cli/factoidal_cli.ml)): maps
  `--data-cottas FILE`s to `cottas_ondisk_dataset_backend` via
  `open_cottas_ondisk_store`
  ([:239-253](../../bin/factoidal-cli/factoidal_cli.ml)).

### 1.4 The jsoo entry point (`bin/npm-entry/entry_jsoo.ml`)

One path: `SPARQL11_Store.run_select_query_backend_dataset`
([:396](../../bin/npm-entry/entry_jsoo.ml)) applied to the in-memory
`dsb ()` only. The browser build has no `--data-cottas`/`--data-hdt`
surface at all (no Unix mmap; see §6.2), so the jsoo path is a single
in-memory backend today. This is a constraint the seam must respect,
not a branch to eliminate.

### 1.5 The COTTAS-on-disk direct entry points (`RDF.CottasStore.fst`)

The nine functions the `GB_CottasOnDisk` arms call, which the seam maps
onto: `cottas_ondisk_search`
([:1394](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_search_limited`
([:1626](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_estimate`
([:1661](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_count_exact`
([:1763](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_predicate_present`
([:232](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_build_bound_qp_opt`
([:1833](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_rows_to_triples`
([:1913](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_has_decode_failure`
([:1378](../../formal/fstar/RDF.CottasStore.fst)),
`cottas_ondisk_named_graphs`
([:249](../../formal/fstar/RDF.CottasStore.fst)). These are the
already-verified public surface the COTTAS `store_caps` instance (§3.2)
wires; the seam adds no new COTTAS logic.

### 1.6 Baseline count

- **12 tag-dispatch functions** in `SPARQL11.Store.fst` (6 dispatchers,
  each with a `GB_Union` recursion twin — §1.1).
- **2 parallel streaming-shape detector families**, ~11 functions,
  deliberately duplicated across `SPARQL11.Store` and
  `SPARQL.Plan.Streamable` (§1.2).
- **3 CLI backend-identity branch sites** (§1.3) plus **1 jsoo path**
  (§1.4).

Cost of adding a backend today: a new arm in each of the 6 dispatchers
(the 6 twins ride along because they recurse `GB_Union` over the same
interface), so **6 edit sites in `SPARQL11.Store.fst` per backend**,
before the CLI wiring. The durable-UPDATE design's `GB_CottasOnDisk`
+delta and the HDT plan's stage-4 backend are two such backends in
flight; landing each the current way is 6 more arms apiece across the
dispatch family, and the durable design says as much — it grows
"one new match arm" in `backend_search`/`_limited`/`_estimate`
([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
§3.2). The seam reduces "add a backend" to "construct one `store_caps`
record"; adding a backend then touches **zero** dispatch functions.

## 2. The interface

A backend is a record of the capability functions it already has, plus
a small flags block the planner reads to decide policy without knowing
the backend's identity. This is the record-of-functions encoding the
recovery plan already committed to for KaRaMeL compatibility
([`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
Open decision 1: "record-of-functions, with each `Capabilities`
instance constructed at top level; no polymorphism over
`Capabilities`"). The signature sketch (does not need to verify yet):

```fstar
module RDF.Store.Capabilities

// triple, subject, rdf_term, wf_iri, triple_pattern_bound.
// These AST/term types live in SPARQL11.Algebra.fst today
// (triple_pattern_bound at SPARQL11.Algebra.fst:132) and move to
// SPARQL.Terms under foundational-core-refactor step 4 (§5.7). The
// capability record depends on that lean tier, NOT on the evaluator,
// so RDF.Store.Capabilities sits BELOW SPARQL11.Store in the DAG —
// exactly where SPARQL.Plan.Streamable already sits (its banner,
// SPARQL.Plan.Streamable.fst:118-122).
open SPARQL.Terms
module DL = RDF.Store.Columnar.DeltaLog   // delta_entry / delta_batch (already in-tree)

// --------------------------------------------------------------------
// Advertised capability flags. The planner/evaluator reads THESE
// instead of matching on a backend tag. Each answers a policy question
// the six tag-dispatchers answer by construction today.
// --------------------------------------------------------------------
noeq type store_caps_flags = {
  // Can this store hold named graphs, or only a default graph? A single
  // HDT 1.0 file is triples-only (hdt-program-plan "Out of scope");
  // COTTAS carries a graph column (cottas-format-v1 §6).
  scf_supports_named_graphs : bool;

  // Does this store have a durable write path (§2 write seam below)?
  // In-memory and COTTAS+delta: yes. HDT and a bare COTTAS base: no.
  scf_supports_update       : bool;

  // Can it answer a bounded COUNT(*)/ASK without materialising rows?
  // Governs whether streamable_shape's plan is dispatched here.
  scf_streaming_shapes      : bool;

  // Is sc_estimate exact, or a join-order hint that may approximate?
  // GB_List/GB_Indexed: exact (backend_count_exact wildcard falls back
  // to backend_estimate, SPARQL11.Store.fst:236). GB_CottasOnDisk: not
  // exact (bounds-present branch approximates, SPARQL11.Store.fst:217).
  scf_estimate_is_exact     : bool;

  // Can it distinguish "genuinely empty" from "column I could not
  // decode" (issue #269)? Only the columnar on-disk reader can.
  scf_can_report_decode_fail : bool;
}

// --------------------------------------------------------------------
// The READ seam. Every backend realises it. Each field is the entry
// point that backend ALREADY has (cited in §3); the record is the one
// indirection that replaces `match gb with`.
// --------------------------------------------------------------------
noeq type store_caps = {
  sc_flags : store_caps_flags;

  // Streaming pattern solve: bounds in, matched triples out. The result
  // is the backend's own already-decoded triples; the evaluator never
  // sees rows/cells/dictionary ids. Realises backend_search's arm
  // (SPARQL11.Store.fst:103).
  sc_solve : triple_pattern_bound -> Tot (list triple);

  // LIMIT-pushdown solve. A backend with real pushdown overrides
  // (COTTAS on-disk, RDF.CottasStore.fst:1626); the default realisation
  // is `fun b n -> list_take_n n (sc_solve b)`, exactly the current
  // non-disk wildcard (SPARQL11.Store.fst:185-188).
  sc_solve_limited : triple_pattern_bound -> nat -> Tot (list triple);

  // Join-order estimate; MAY approximate iff scf_estimate_is_exact=false.
  // Realises backend_estimate (SPARQL11.Store.fst:197).
  sc_estimate : triple_pattern_bound -> Tot nat;

  // Exact count for result-producing callers (COUNT(*), per-graph
  // GROUP BY). Realises backend_count_exact (SPARQL11.Store.fst:229);
  // the in-memory default IS sc_estimate.
  sc_count_exact : triple_pattern_bound -> Tot nat;

  // Predicate-presence short-circuit (Bloom/dictionary probe). Realises
  // backend_predicate_present (SPARQL11.Store.fst:246).
  sc_predicate_present : wf_iri -> Tot bool;

  // Did a read touch a column this reader could not decode? Only a
  // columnar reader returns true; the default is `fun () -> false`,
  // the current non-disk wildcard (SPARQL11.Store.fst:296). Realises
  // backend_decode_failure (SPARQL11.Store.fst:290).
  sc_decode_failure : unit -> Tot bool;
}

// --------------------------------------------------------------------
// The WRITE seam. ONLY a read-write backend constructs this. A
// read-only backend advertises scf_supports_update=false and carries
// None (§2, "must not force in-memory to pay COTTAS's costs and vice
// versa"): a read-only store never allocates a delta log, and the
// in-memory store never runs the fsync/rename protocol.
// --------------------------------------------------------------------
noeq type store_write_caps = {
  // Apply one committed SPARQL Update request's ops and return the
  // post-update READ seam. For COTTAS+delta this appends+fsyncs a
  // DL.delta_batch and returns base ⊕ delta (durable-update §3.3/§4.1);
  // for the in-memory store it rebuilds the indexed_graph. ML because
  // durability is I/O; the byte layout it writes is F* (DL.serialize_*).
  swc_apply_delta : list DL.delta_entry -> ML store_caps;

  // Optional planner input: exact count of delta entries matching a
  // bound (durable-update §4.4). None just after compaction (empty
  // delta), so a store with no delta pays nothing.
  swc_delta_stats : option (triple_pattern_bound -> Tot nat);
}

// A store is its read seam plus, iff read-write, its write seam.
noeq type store = {
  st_read  : store_caps;
  st_write : option store_write_caps;   // Some ⟺ sc_flags.scf_supports_update
}
```

The record contains exactly the six read operations the six
tag-dispatchers supply today, one flags block replacing the policy the
dispatchers encode by their arm structure, and an optional write seam
carried only by read-write backends. Nothing in the read record forces
a backend to build machinery it does not have: the in-memory instance's
`sc_decode_failure` is a constant `false` and its `sc_estimate_is_exact`
is `true`, so it never runs COTTAS's decode-failure tracking or exact
recount; the COTTAS instance's read fields are the on-disk walkers and
it never builds an `indexed_graph`. That asymmetry is preserved because
each field is whatever the backend already computes, not a shared
implementation both must fit.

`GB_Union` stops being a backend constructor and becomes a caller-side
combinator over a `list store_caps` — `union_caps : list store_caps ->
store_caps` building one `store_caps` whose `sc_solve` concatenates the
members' (the tail-recursive accumulator shape at
[`SPARQL11.Store.fst:94-101`](../../formal/fstar/SPARQL11.Store.fst)
moves into that one combinator). The six `union_*` twins collapse into
that single function.

## 3. How each backend realises the seam

### 3.1 In-memory via `RDF.Indexed`

The lowest capability set — the "bottom row only" of the recovery
plan's abstraction-map table. Its read seam:

- `sc_solve` = `ig_search` over the `indexed_graph`
  ([`SPARQL11.Store.fst:107-108`](../../formal/fstar/SPARQL11.Store.fst)),
  which dispatches to the bucket indexes
  `find_objects_indexed`/`find_subjects_indexed`
  ([`RDF.Indexed.fsti:180-198`](../../formal/fstar/RDF.Indexed.fsti)).
- `sc_solve_limited` = the default `list_take_n n (sc_solve b)` (no
  pushdown; in-memory search is already resident).
- `sc_estimate` = `sc_count_exact` = `ig_estimate`
  ([`SPARQL11.Store.fst:201-202`](../../formal/fstar/SPARQL11.Store.fst));
  `scf_estimate_is_exact = true`.
- `sc_predicate_present` = the `bp = Some pred` estimate `> 0` shape
  ([`SPARQL11.Store.fst:255-260`](../../formal/fstar/SPARQL11.Store.fst)).
- `sc_decode_failure` = `fun () -> false`;
  `scf_can_report_decode_fail = false`.
- Flags: named graphs yes (a dataset is a default `indexed_graph` plus
  named ones, `indexed_dataset_backend`,
  [`SPARQL11.Store.fst:56-64`](../../formal/fstar/SPARQL11.Store.fst)),
  streaming shapes yes, update yes (rebuild the `indexed_graph` via
  `build_indexed`, [`RDF.Indexed.fsti:267`](../../formal/fstar/RDF.Indexed.fsti)).

### 3.2 COTTAS read via `RDF.CottasStore`

The columnar on-disk backend, the top capability set. Its read seam
maps one-to-one onto the already-verified entry points from §1.5:

| Field | Realisation |
|---|---|
| `sc_solve` | `cottas_ondisk_search` composed with `cottas_ondisk_rows_to_triples`, guarded by `cottas_ondisk_build_bound_qp_opt` (the current `GB_CottasOnDisk` arm, [`SPARQL11.Store.fst:114-126`](../../formal/fstar/SPARQL11.Store.fst)) |
| `sc_solve_limited` | `cottas_ondisk_search_limited` ([`RDF.CottasStore.fst:1626`](../../formal/fstar/RDF.CottasStore.fst)) — real LIMIT pushdown, the override |
| `sc_estimate` | `cottas_ondisk_estimate` ([`:1661`](../../formal/fstar/RDF.CottasStore.fst)); `scf_estimate_is_exact = false` |
| `sc_count_exact` | `cottas_ondisk_count_exact` ([`:1763`](../../formal/fstar/RDF.CottasStore.fst)) |
| `sc_predicate_present` | `cottas_ondisk_predicate_present` ([`:232`](../../formal/fstar/RDF.CottasStore.fst)) |
| `sc_decode_failure` | `cottas_ondisk_has_decode_failure` ([`:1378`](../../formal/fstar/RDF.CottasStore.fst)); `scf_can_report_decode_fail = true` |

The access-path selectivity work — the row-group-offset table, the
compound-(p,o) prune, the offset index — stays inside those functions,
below the seam. `SPARQL.Plan.AccessPath.choose_access_path`
([`SPARQL.Plan.AccessPath.fst:127`](../../formal/fstar/SPARQL.Plan.AccessPath.fst))
and the offset-table threading
([`RDF.CottasStore.fst:1411`](../../formal/fstar/RDF.CottasStore.fst))
are COTTAS-internal; the seam exposes only `sc_solve`, so a future
Parquet-v2 or a reordered clustering changes the realisation without
touching the interface or any other backend. Named-graph dispatch is
one `store` per scope via `cottas_ondisk_named_graphs`
([`:249`](../../formal/fstar/RDF.CottasStore.fst)) with `COS_DefaultOnly`
/ `COS_NamedGraph` scopes (issue #267,
[`SPARQL11.Store.fst:75-84`](../../formal/fstar/SPARQL11.Store.fst)).

The bare COTTAS base carries `st_write = None` (`scf_supports_update =
false`): a read-only Parquet file, unchanged from how pycottas writes
it ([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
§2.a).

### 3.3 COTTAS + delta as a composition — the elegance

The read-write COTTAS view is **not a new backend**. It is the COTTAS
read seam of §3.2 with a delta overlay applied above it, producing
another `store_caps`:

```fstar
// overlay : base read seam + resolved delta = a new read seam of the
// SAME type. This is where the durable-update design's merge_on_read
// lives (2026-07-06-durable-update-design.md §3.2). It is a pure
// function over already-decoded triples — it does not know or change
// how the base reads.
val overlay : store_caps -> RDF.Store.Columnar.DeltaMerge.delta_resolved -> Tot store_caps
let overlay base delta = {
  base with
    sc_solve         = (fun b -> merge_on_read (base.sc_solve b) delta b);
    sc_solve_limited = (fun b n -> list_take_n n (merge_on_read (base.sc_solve b) delta b));
    sc_estimate      = (fun b -> base.sc_estimate b + delta_matching_count delta b);
    sc_count_exact   = (fun b -> base.sc_count_exact b
                                 - tombstoned_count delta (base.sc_solve b)
                                 + delta_added_count delta b);
    // sc_predicate_present, sc_decode_failure: base's, OR the delta's
    // per-term set (durable-update §4.2/§4.4).
    sc_flags = { base.sc_flags with scf_supports_update = true };
}
```

The read-write store is then `{ st_read = overlay cottas_base delta;
st_write = Some { swc_apply_delta = append_fsync_delta_batch; ... } }`.
The durable-UPDATE design already writes `merge_on_read` as "a pure
function over already-decoded values — it does not itself decide *how*
the base is read"
([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
§3.2); the seam is what makes that sentence structural. Base capability
plus delta overlay equals the same interface, so the evaluator does not
learn a delta exists. The streaming fast path composes the same way —
`stream_step_with_delta`
([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
§4.1) is `overlay` applied to the streaming iterator instead of the
solve function, and an empty delta is provably the identity, so the
measured base-file numbers hold when there is nothing to compose
against.

The durable design's own §3.2 hedges between "a `GB_CottasOnDisk` with
an optional delta field" and "a sibling constructor
`GB_CottasOnDiskWithDelta`." The seam retires that question: neither —
`overlay` is a function `store_caps -> delta -> store_caps`, so there
is no new constructor and no optional field on an existing one.

### 3.4 HDT read-only — stage 4 lands as a `store_caps`

The HDT plan's stage 4 already targets "the store-capability surface
the F\* planner already consumes"
([`2026-07-06-hdt-program-plan.md`](2026-07-06-hdt-program-plan.md)
stage 4) and names `SPARQL.Plan.AccessPath`'s typed `access_path` ADT as
the pattern to follow. Under this seam, stage 4's deliverable is exactly
"construct the HDT `store_caps`":

- `sc_solve` = HDT BitmapTriples navigation from stage 3 (`subject_slice`
  / `(s,p)_slice` / scan fallback,
  [`2026-07-06-hdt-program-plan.md`](2026-07-06-hdt-program-plan.md)
  stage 3), replacing the 10 `assume val`s in
  [`Parser.BallyhooHDT.fst`](../../formal/fstar/Parser.BallyhooHDT.fst)
  and deleting `ballyhoo_hdt_runtime.sh` (555 lines, closing #253).
- `sc_solve_limited` = default truncation (HDT has no separate pushdown
  path in stage 4; a bound-S select-jump answers fast already).
- `sc_estimate` / `sc_count_exact` = rank/select counts;
  `scf_estimate_is_exact` can be `true` (the bitmap gives exact slice
  lengths).
- `sc_predicate_present` = a predicate-section dictionary probe (the
  front-coded `pfc_locate` from stage 2).
- `sc_decode_failure` = `fun () -> false` (CRC-validated at parse;
  `scf_can_report_decode_fail = false`).
- Flags: `scf_supports_named_graphs = false` (HDT 1.0 triples only),
  `scf_supports_update = false` (read-only; `st_write = None`).

The HDT plan's Open decision 1 — generalise `access_path` vs an
HDT-shaped sibling ADT — is answered by the seam at the boundary but not
below it: the two backends share the `store_caps` interface (one
`sc_solve` signature), while each keeps its own internal access-path ADT
(COTTAS's offset-jump shape, HDT's select-jump shape). The seam does not
force `SPARQL.Plan.AccessPath.access_path` to grow HDT arms; it lets HDT
keep a private planner and expose only `sc_solve`. That matches the HDT
plan's own lean ("sibling-then-unify").

### 3.5 What lives once, above the seam

Everything that is backend-agnostic moves above the seam and is written
a single time:

- **The streaming fast path.** `SPARQL.Plan.Streamable.streamable_shape`
  ([`SPARQL.Plan.Streamable.fst:244`](../../formal/fstar/SPARQL.Plan.Streamable.fst))
  produces a `stream_plan`; a store that advertises
  `scf_streaming_shapes` answers it through `sc_count_exact` /
  `sc_predicate_present`. The two parallel detector families (§1.2)
  collapse to one: `streamable_shape` becomes the single recognizer, and
  the Aleph6 `detect_streaming_*` functions in `SPARQL11.Store` call it
  instead of re-deriving the shape (§4).
- **GRAPH semantics.** The issue #267 dataset rules — default graph is
  `DEFAULT`-sentinel rows, each named graph a scoped store
  ([`SPARQL11.Store.fst:66-84`](../../formal/fstar/SPARQL11.Store.fst))
  — become one `dataset = { ds_default : store; ds_named : list (iri *
  store) }` built once over the seam, not re-encoded per backend.
- **Entailment closure application.** RDFS/OWL-RL closure runs over the
  materialised graph before store construction (the CLI gates the
  backend executor on `entail_regime = ""`,
  [`factoidal_cli.ml:1460-1465`](../../bin/factoidal-cli/factoidal_cli.ml));
  it is a graph transform above every backend, unchanged.
- **Result formatting.** JSON/CSV/table rendering already consumes
  `solution_sequence` and is byte-identical across paths by construction
  ([`SPARQL.Plan.Streamable.fst:52-57`](../../formal/fstar/SPARQL.Plan.Streamable.fst));
  it sits above the seam untouched.

## 4. What dies

- **The six `GB_Union` recursion twins** (§1.1): `union_backend_search_acc`,
  `union_backend_search_limited_acc`, `union_backend_estimate`,
  `union_backend_count_exact`, `union_backend_predicate_present`,
  `union_backend_decode_failure`. They collapse into one `union_caps :
  list store_caps -> store_caps` combinator.
- **The six-arm structure of the six dispatchers.** `backend_search`,
  `backend_search_limited`, `backend_estimate`, `backend_count_exact`,
  `backend_predicate_present`, `backend_decode_failure` stop matching on
  a tag; each becomes a field projection `sc.sc_solve b` etc. The
  functions may survive as one-line forwarders during migration (§5),
  then retire.
- **The `graph_backend` constructor set as a dispatch axis.** The tag
  ([`SPARQL11.Store.fst:23-34`](../../formal/fstar/SPARQL11.Store.fst))
  is replaced by `store`; `GB_COTTAS` (the in-memory COTTAS path the
  estimate comment already calls "the dead in-memory GB_COTTAS path,"
  [`RDF.CottasStore.fst:1681`](../../formal/fstar/RDF.CottasStore.fst))
  can be dropped rather than ported.
- **One of the two streaming-shape detector families** (§1.2). The
  `SPARQL.Plan.Streamable` recognizer is kept (it is already below the
  store in the DAG); `SPARQL11.Store`'s `detect_streaming_count_star` /
  `detect_streaming_count_group_by_graph` become callers of it, not a
  second copy.
- **The optional-delta-field / sibling-constructor question** in the
  durable-UPDATE design (§3.3 above): superseded by `overlay`.

## 5. Migration stages

Each stage is commit-sized and keeps every suite at its floor: SPARQL
631 pass / 0 fail, RDF 1031 pass / 0 fail,
[`tests/unit/run-all.sh`](../../tests/unit/run-all.sh) all files pass
(28-29 depending on tree state), and the local COTTAS regression suites
([`tests/local/cottas_row_order_regressions.sh`](../../tests/local/cottas_row_order_regressions.sh),
[`tests/local/cottas_corpus_regressions.sh`](../../tests/local/cottas_corpus_regressions.sh),
[`tests/local/streamable_fastpath_regressions.sh`](../../tests/local/streamable_fastpath_regressions.sh))
green. The sequence is written to interleave with the durable-UPDATE
stages and the HDT stages rather than block them.

| Stage | Deliverable | Keeps green by | Depends on / reconciles with |
|---|---|---|---|
| **U1** | `RDF.Store.Capabilities.fst`: `store_caps_flags`, `store_caps`, `store_write_caps`, `store`, `union_caps`. Types + the in-memory and COTTAS `store_caps` builders (§3.1/3.2). No caller rewired yet. | New module verifies standalone (z3 4.13.3, no `--lax`); nothing else changes, so all suites unmoved. | Foundational-core-refactor **step 4** must land first (or the record imports `SPARQL11.Algebra` transitionally) — see §5.7. |
| **U2** | Rewrite the six `SPARQL11.Store` dispatchers as one-line forwarders that build a `store_caps` from the existing `graph_backend` and project the field. `graph_backend` stays as a constructor set for now; `union_*` twins fold into `union_caps`. | Behaviour byte-identical (forwarders call the same underlying functions); full SPARQL + RDF suites re-run. | U1. Independent of durable/HDT work. |
| **U3** | Fold the two streaming detectors into one: `SPARQL11.Store.detect_streaming_*` call `SPARQL.Plan.Streamable.streamable_shape` instead of re-deriving the shape (§3.5). | `streamable_fastpath_regressions.sh` diffs fast-path vs materialise output on the same fixtures; must stay byte-identical. | U2. |
| **U4** | Replace `graph_backend`/`dataset_backend` with `store`/`dataset` at the type level; delete the tag and the dead `GB_COTTAS` in-memory path (§4). CLI + jsoo call sites move to `store`. | Full battery once; jsoo node/wasm parity run (§6.2). CLI's three branch sites (§1.3) reduce to "build the `dataset` of `store`s." | U2, U3. |
| **D-overlay** | `overlay : store_caps -> delta_resolved -> store_caps` (§3.3), realising the durable design's `merge_on_read` as a seam composition. Wires the COTTAS+delta read-write `store`. | The durable design's own Stage 3 acceptance: the 176-test W3C Update suite against a COTTAS+delta `store` stays 176/176; crash-recovery harness per that doc. | **Absorbs durable-UPDATE design Stage 3's** "wire one new `GB_CottasOnDisk`-with-delta match arm" — under the seam there is no new arm, only `overlay` + `st_write`. Lands after U2 (needs `store_caps`), in parallel with the durable design's Stages 1-2 (byte format, I/O), which are seam-independent. |
| **H-caps** | HDT `store_caps` builder (§3.4), consumed by HDT plan stage 4. | HDT stage-4 backend-parity regression (SELECT over `--data-hdt` equals the same query over the `.nt` in-memory). | **Absorbs HDT plan stage 4's** "wire HDT pattern resolution into the store-capability surface" — the surface is `store_caps`. Lands after U1; independent of D-overlay. |
| **U5** | Delete the six dispatcher forwarders; call sites project `sc_solve`/`sc_estimate`/etc. directly. Retire `SPARQL.Plan.AccessPath`'s tag-shaped assumptions if any remain COTTAS-internal (they do not — it is already below the seam, §3.2). | Full battery; the seam is now the only path. | U4, D-overlay, H-caps all landed (so no tag consumer remains). |

Stages U1-U5 are the seam itself; D-overlay and H-caps are the two
in-flight backends landing through it rather than as new tag arms. The
durable design's Stages 4-9 (compaction, planner delta-stats, HTTP
wiring, parliament validation) and the HDT stages 5 (optimized
rank/select) are unaffected — they operate below or beside the seam and
do not touch `store_caps`.

### 5.7 Reconciliation with foundational-core-refactor steps 4 and 7

Foundational-core-refactor **step 4** is the `SPARQL.Terms` split:
extract the SPARQL AST types (including `triple_pattern_bound`,
[`SPARQL11.Algebra.fst:132`](../../formal/fstar/SPARQL11.Algebra.fst))
out of `SPARQL11.Algebra.fst` into a new `SPARQL.Terms.fst`, leaving the
evaluator behind
([`2026-07-05-foundational-core-refactor.md`](2026-07-05-foundational-core-refactor.md)
step 4 row). **Step 7** deletes the `RDF.Graph.Executable` re-export
shim, converting every dependent's `open` line (pure `open`-line
hygiene, no logic).

Decision: **this architecture does not supersede step 4 — it depends on
it, and absorbs the store-tier reorganization that steps 4/7 would
otherwise sweep through.** Concretely:

- **Step 4 stays and lands first (or transitionally).** The
  `store_caps` record's `sc_solve`/`sc_estimate`/`sc_count_exact` all
  take `triple_pattern_bound`, which is an AST/term type, not an
  evaluator symbol. It belongs in step 4's `SPARQL.Terms` tier. Having
  `RDF.Store.Capabilities` import `SPARQL.Terms` (not
  `SPARQL11.Algebra`) keeps the store seam **below** the evaluator in
  the module DAG — the same position `SPARQL.Plan.Streamable` already
  holds and defends by duplicating `extract_single_tp_bgp` rather than
  importing it upward
  ([`SPARQL.Plan.Streamable.fst:118-122`](../../formal/fstar/SPARQL.Plan.Streamable.fst)).
  So stage U1 is sequenced after step 4; if step 4 slips, U1 imports
  `SPARQL11.Algebra` transitionally and moves the import to
  `SPARQL.Terms` when step 4 lands (a one-line `open` change, exactly
  the kind step 7 is designed to make mechanical).
- **This doc absorbs the `SPARQL11.Store` share of steps 4/7.** Steps
  4 and 7 are AST/`open`-hygiene concerns; neither restructures the
  backend dispatch. But both would pass through `SPARQL11.Store.fst` as
  a dependent needing `open`-line edits, and step 4's gate warns it is
  "the step most likely to touch a real evaluator call site by accident"
  ([`2026-07-05-foundational-core-refactor.md`](2026-07-05-foundational-core-refactor.md)
  step 4 row). The seam shrinks `SPARQL11.Store` from 12 dispatch
  functions (§1.1) to a handful of field projections before step 7
  reaches it, so step 7's mechanical `open`-line pass touches far less
  surface. The reorganization of the store's per-backend match arms is
  owned by **this** doc, not steps 4/7 — those two keep their AST/hygiene
  scope and do not need to reason about backend dispatch at all.

Net: step 4 is a prerequisite and remains valid as written; step 7
remains valid and gets easier; the backend-dispatch restructuring is
this doc's territory, sequenced as U1-U5 above.

## 6. Risks

### 6.1 Extraction: a record of closures is closure-heavy in OCaml, hostile to KaRaMeL

`store_caps` is a record whose fields are functions. In OCaml/JS
extraction each field is a closure; each `sc.sc_solve b` is an indirect
call. For the OCaml native and js_of_ocaml targets this is one
indirection per pattern solve — negligible against a row-group walk —
and matches how the recovery plan already decided to encode capabilities
([`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
Open decision 1). The trap is elsewhere and the fstar-module-style
extraction notes name it: F\*-verified `Tot` is not OCaml totality, and
higher-order `Tot` values extract to real closures that KaRaMeL's C
backend does not accept as first-class. Two mitigations, both already in
the recovery plan's grain: (a) construct every `store_caps` instance at
top level, no polymorphism over the record, so KaRaMeL can monomorphise
(recovery Open decision 1, restated); (b) for the C/wasm-via-C pilot,
the seam is defunctionalized — the C build links each backend's
`sc_solve` directly rather than through a stored function pointer, so
the record-of-closures is an OCaml/JS convenience the C target lowers
away. Neither the in-memory hot path nor the COTTAS row-group walk gains
per-row closure allocation: the closures are per-`store`, built once at
open time, not per-solve. This must be measured before U5 (the
perf-benchmarking discipline: no speed claim without its own
measurement); the guard is that U2's forwarders are byte-behaviour
identical, so any regression is a pure indirection cost, isolable.

### 6.2 The wasm/js build keeps Unix-dependent backends out

The COTTAS on-disk and HDT backends depend on `mmap`/file-range reads
realised as `assume val`s; the browser build has no Unix file surface.
`build-ocaml.sh` already excludes the HDT runtime from the JS/wasm build
for exactly this reason, and the jsoo entry point carries only the
in-memory backend (§1.4). The seam does not change this: a `store` whose
read fields call the file-range `assume val`s is simply never
constructed in the jsoo build, and `entry_jsoo.ml` builds only the
in-memory `store`. The HDT plan notes HDT is the better *future* browser
backend (range-request friendly, no zstd,
[`2026-07-06-hdt-program-plan.md`](2026-07-06-hdt-program-plan.md)
"The wasm/js story") — that becomes true when the range-read `assume
val` is realised for `fetch`/`ArrayBuffer`, and the seam is what lets
that land as one new `store_caps` builder without touching the
evaluator. Risk: if `RDF.Store.Capabilities` is placed in the JS/wasm
module list but transitively pulls a Unix-only backend's builder, the
link breaks. Mitigation: the record type and the in-memory builder are
Unix-free; the COTTAS/HDT builders live in their own modules
(`RDF.CottasStore`, HDT container modules), already excluded from the
browser build. U4's acceptance includes a node + wasm parity run
(test-suites cross-runtime discipline).

### 6.3 Rule #11 boundary

The seam introduces no new `assume val`. `swc_apply_delta` is `ML`
because durability is I/O, but the bytes it writes are F\*
(`RDF.Store.Columnar.DeltaLog.serialize_*`, already in-tree) and the
five fsync/rename `assume val`s are the durable-UPDATE design's, all
pure-I/O per the taxonomy
([`2026-07-06-durable-update-design.md`](2026-07-06-durable-update-design.md)
§3.3). No capability decision moves into OCaml: the flags
(`scf_estimate_is_exact`, `scf_supports_update`, etc.) are F\* values on
the record, read by F\* planner code, so the "which backend can do what"
decision that today lives in the arm structure of six F\* dispatchers
stays in F\* — it does not leak into a hand-written OCaml shim. The
`union_caps` combinator, the `overlay` composition, and the streaming
fold are all `Tot` F\* functions. The consumer tools (CLI, jsoo, HTTP)
call the seam; they remain outside the verified boundary per rule #11,
unchanged in kind from today.

## 7. Open decisions for the owner

1. **`store` as a record vs. keeping `graph_backend` as a thin newtype
   over `store_caps`.** U4 replaces the tag; an alternative is to keep
   `graph_backend` as a one-constructor wrapper for source
   compatibility. Recommend the full replacement (U4) — the tag's only
   remaining purpose after U2 is the dead `GB_COTTAS` path, which §4
   drops.
2. **Whether `union_caps` should also be a `store` combinator or stay
   at `store_caps`.** A union of read-write stores has no obvious write
   semantics (which member does an INSERT target?). Recommend
   `union_caps` build a read-only `store_caps` (`st_write = None`);
   unions are a read-side federation, and a writable federated store is
   a separate design if it is ever wanted.
3. **`scf_streaming_shapes` granularity.** One flag today; a store might
   support streaming COUNT but not streaming ASK. Recommend one flag
   until a backend needs the split (all three current backends either
   support both or neither).
