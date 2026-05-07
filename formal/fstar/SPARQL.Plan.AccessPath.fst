module SPARQL.Plan.AccessPath

// Access-path chooser for the COTTAS / columnar query planner.
//
// Recovery plan Phase 6 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Names the F* home for the access-path decision
// that retires codename "Lamed3" alongside its companion module
// `RDF.Store.Columnar.OffsetIndex.fst` (which owns the `.p.offsets`
// file format + reader).
//
// Old shape (the one this module displaces): the decision "if the
// predicate is bound and the offsets companion is present, jump
// directly to the row positions; otherwise fall through to the full
// predicate-column decode" was made inside the OCaml dispatcher
// `Cottas_ondisk_runtime.search_fast` injected by
// experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh
// (later retired in the Yod7 audit, with the offsets writer kept).
// The OCaml side both *built* the bytes and *picked* whether to use
// them; per CLAUDE.md rule #11 the latter is a backend correctness
// decision and belongs in F*.
//
// New shape (this module): a pure F* function from "what's bound" +
// "what capabilities does this store advertise" to a typed
// `access_path` value. The store's reader implementation consumes
// the typed value and dispatches accordingly.
//
// What this module owns:
//   - `access_path` ADT — the typed plan output (full scan vs offset
//     jump vs empty short-circuit).
//   - `choose_access_path` — the decision function: given a bound
//     predicate (+ optional bound subject + optional bound object)
//     and the offset-index handle, returns the cheapest legal
//     access-path for one row group.
//   - `choose_access_path_for_pattern` — caller-shaped wrapper that
//     takes a `pattern_bound_ids` record (the `SPARQL.Plan.Pruning`
//     shape) and picks the access-path per rg.
//   - Lemmas: identity-when-no-offset-index, equivalence under empty
//     cell, soundness sketch deferring to OffsetIndex.
//
// What it deliberately does NOT own:
//   - The actual prune predicate (`SPARQL.Plan.Pruning.fst`).
//   - The cardinality estimate (`SPARQL.Plan.Estimate.fst`).
//   - The companion-file I/O (`RDF.Store.Columnar.OffsetIndex.fst` +
//     `RDF.CottasStore.OnDiskIndex.fst`).
//   - The COTTAS-specific token-id resolution (still in
//     `RDF.CottasStore.fst` until Phase 6's wiring follow-up).
//
// Wiring status: this module is the named F* home; it does not yet
// re-route `RDF.CottasStore.cottas_ondisk_search`'s LIMIT path
// through `choose_access_path`. That swap is a follow-up commit on
// the same recovery branch once the F* extraction toolchain version
// drift is resolved (the same drift that left
// `SPARQL.Plan.Pruning` and `SPARQL.Plan.Estimate` un-wired in
// PR #215 / Phase 4). Phase 6's deliverable is the named-API home +
// the spec — semantics are byte-identical to what the OCaml
// `Cottas_offset_idx.row_positions_for` shim produces today.

module OI  = RDF.Store.Columnar.OffsetIndex
module PR  = SPARQL.Plan.Pruning

// ---------------------------------------------------------------------------
// Access-path shapes.
//
// Three regimes the planner produces for a single (rg, pattern) pair:
//
//   - `AP_Skip` — the rg cannot match the pattern. Caller does
//     nothing for this rg. Sources of `AP_Skip`:
//       (a) prune predicate ruled it out (Pruning module),
//       (b) offset-index says zero rows for the bound predicate
//           (`CD_Empty` from OffsetIndex.row_positions_for_opt).
//
//   - `AP_OffsetJump cv` — read only the row positions in `cv`'s
//     slice of the data section (`cv.cv_count` u32 row indices
//     starting at `cv.cv_start`); decode subject + object cells at
//     just those positions. Strictly cheaper than full decode when
//     the bound predicate is rare in this rg.
//
//   - `AP_FullScan` — the planner has no offset-index info (either
//     the predicate is unbound or the companion file is absent).
//     Caller decodes the predicate column for the whole rg, filters
//     by bound predicate (if any), then decodes subject + object at
//     the surviving positions. The pre-Lamed3 baseline path.
// ---------------------------------------------------------------------------

type access_path =
  | AP_Skip       : access_path
  | AP_OffsetJump : OI.cell_view -> access_path
  | AP_FullScan   : access_path

// Equality on `access_path` for tests / lemmas. Pure boolean.
let access_path_eq (a b : access_path) : Tot bool =
  match a, b with
  | AP_Skip, AP_Skip               -> true
  | AP_FullScan, AP_FullScan       -> true
  | AP_OffsetJump cv1, AP_OffsetJump cv2 ->
    cv1.OI.cv_start = cv2.OI.cv_start &&
    cv1.OI.cv_count = cv2.OI.cv_count
  | _, _ -> false

// ---------------------------------------------------------------------------
// choose_access_path — per-rg decision.
//
// Inputs:
//   - `oh_offsets`   : the offset-index handle (option). None means
//                     the companion file isn't open — we have no
//                     offset-index info for any rg.
//   - `rg`           : the row-group index.
//   - `bound_pred_id`: the resolved predicate token-id when the
//                     pattern's predicate is bound; None when the
//                     predicate is a variable.
//
// Output: the `access_path` for this rg.
//
// Decision table:
//
//   bound_pred_id | oh_offsets | OffsetIndex result | access_path
//   --------------|------------|--------------------|------------
//   None          | *          | -                  | AP_FullScan
//   Some _        | None       | -                  | AP_FullScan
//   Some p        | Some h     | CD_NoInfo          | AP_FullScan
//   Some p        | Some h     | CD_Empty           | AP_Skip
//   Some p        | Some h     | CD_Use cv          | AP_OffsetJump cv
//
// Pure F*; no I/O beyond what `OI.row_positions_for_opt` delegates.
// ---------------------------------------------------------------------------

let choose_access_path
  (oh_offsets : option OI.offset_handle)
  (rg : nat)
  (bound_pred_id : option nat)
  : Tot access_path =
  match OI.row_positions_for_opt oh_offsets rg bound_pred_id with
  | OI.CD_NoInfo   -> AP_FullScan
  | OI.CD_Empty    -> AP_Skip
  | OI.CD_Use cv   -> AP_OffsetJump cv

// ---------------------------------------------------------------------------
// choose_access_path_for_pattern — caller-shaped wrapper.
//
// Takes the bundled `pattern_bound_ids` record from
// `SPARQL.Plan.Pruning` and projects out the bound-predicate field.
// The subject + object bounds are not consulted here; they're
// relevant for the *prune* decision (already made before the
// access-path picker is called) and for the post-jump filter at
// each row position (handled inside the COTTAS reader).
// ---------------------------------------------------------------------------

let choose_access_path_for_pattern
  (oh_offsets : option OI.offset_handle)
  (rg : nat)
  (bounds : PR.pattern_bound_ids)
  : Tot access_path =
  choose_access_path oh_offsets rg bounds.PR.pbi_p

// ---------------------------------------------------------------------------
// Filter a candidate-rg list down to a list of (rg, access_path)
// pairs. Mirrors `Pruning.filter_candidates_by_prune` in shape.
// Callers feed in the post-prune candidate list and get back per-rg
// access-path decisions. Order is preserved.
//
// `AP_Skip` results are KEPT in the output list (they're meaningful:
// "we know this rg has zero matches for this pattern, so the
// estimate for this rg is exactly 0"). Callers that want the
// physical execution list should filter out `AP_Skip` separately.
// ---------------------------------------------------------------------------

let rec choose_access_paths_for_rgs
  (oh_offsets : option OI.offset_handle)
  (candidates : list nat)
  (bounds : PR.pattern_bound_ids)
  : Tot (list (nat * access_path)) (decreases candidates) =
  match candidates with
  | [] -> []
  | rg :: rest ->
    let ap = choose_access_path_for_pattern oh_offsets rg bounds in
    (rg, ap) :: choose_access_paths_for_rgs oh_offsets rest bounds

// Drop the `AP_Skip` entries from a list of (rg, access_path) pairs.
// The execution layer wants the rgs it actually has to read; the
// estimate layer wants the full list (including skips, which
// contribute 0 rows).
let rec drop_skips
  (xs : list (nat * access_path))
  : Tot (list (nat * access_path)) (decreases xs) =
  match xs with
  | [] -> []
  | (rg, ap) :: tl ->
    (match ap with
     | AP_Skip -> drop_skips tl
     | _       -> (rg, ap) :: drop_skips tl)

// ---------------------------------------------------------------------------
// Properties.
// ---------------------------------------------------------------------------

// When the offset-index companion is not open, every rg gets the
// full-scan access path. This is the "no offset-jump optimisation
// available" baseline behaviour that the OCaml runtime exhibited
// before Lamed3 landed.
let choose_access_path_no_handle_is_full_scan
  (rg : nat) (bound_pred_id : option nat)
  : Lemma
    (ensures choose_access_path None rg bound_pred_id == AP_FullScan)
  = ()

// When the predicate is unbound, every rg gets the full-scan access
// path — the offset-index is keyed by predicate so we have nothing
// to look up.
let choose_access_path_unbound_pred_is_full_scan
  (oh_offsets : option OI.offset_handle) (rg : nat)
  : Lemma
    (ensures choose_access_path oh_offsets rg None == AP_FullScan)
  = ()

// When the bounds record carries no bound predicate, the
// pattern-shaped chooser collapses to the full-scan path. Mirrors
// the previous lemma but consumes the `pattern_bound_ids` record so
// callers using the bundled shape get a directly-applicable lemma.
let choose_access_path_for_pattern_unbound_pred_is_full_scan
  (oh_offsets : option OI.offset_handle) (rg : nat)
  (bounds : PR.pattern_bound_ids)
  : Lemma
    (requires bounds.PR.pbi_p == None)
    (ensures
      choose_access_path_for_pattern oh_offsets rg bounds == AP_FullScan)
  = ()

// `drop_skips` is the identity when no input cell is `AP_Skip`. The
// list-fold structure makes this provable by induction; F* discharges
// it from the definitional unfolding for empty input, and we expose
// the "all not skip -> identity" shape as a recursive lemma for any
// callers that need it.
let rec drop_skips_identity_when_no_skips
  (xs : list (nat * access_path))
  : Lemma
    (requires
      forall (rg:nat) (ap:access_path).
        FStar.List.Tot.memP (rg, ap) xs ==> ~(ap == AP_Skip))
    (ensures drop_skips xs == xs)
    (decreases xs)
  =
  match xs with
  | [] -> ()
  | _ :: tl -> drop_skips_identity_when_no_skips tl

// Soundness sketch: if `choose_access_path` returns `AP_Skip`, the
// rg has no row whose predicate equals the bound predicate. This
// follows from `OI.row_positions_for_count_sound`: the chooser
// returns `AP_Skip` only when `OI.row_positions_for_opt` produced
// `CD_Empty`, which by construction came from `cv.cv_count = 0`,
// which by the OffsetIndex soundness lemma implies the spec-side
// ground-truth list of matching rows is empty.
//
// We do NOT re-state a separate executable lemma here (the
// OffsetIndex one is sufficient); the call site can invoke
// `OI.row_positions_for_count_sound` when it needs the formal
// guarantee.
