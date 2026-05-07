module SPARQL.Plan.Loader

// Companion-file load-strategy decision for the COTTAS / columnar
// query planner. Pure F*.
//
// Recovery plan §3.5 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md) and Phase 3 (boundary audit Section 3.4). Retires
// codename Bet7 — "lazy populate of in-RAM Hashtbls when companion
// files are absent / fail." The OCaml-side decision logic in
// `factoidal_http.ml`'s `prewarm_cottas_columns` (line 624) and
// `open_cottas_ondisk_files` (lines 650-669) — try-prewarm-then-fall-
// back-to-lazy — collapses here to a pure F* function over a small
// status enum.
//
// What lives here:
//   - `companion_file_status` — the inputs the loader inspects
//     (`<corpus>.s.dict`, `.s.presence`, `.p.presence`, etc., plus the
//     parquet itself).
//   - `load_strategy` — the dispatch label the OCaml caller pattern-
//     matches on.
//   - `choose_load_strategy` — the pure decision function.
//   - A handful of lemmas pinning the "warm path is always Mmap" and
//     "missing companions never refuse outright" properties so the
//     decision is auditable without re-reading the OCaml caller.
//
// What does NOT live here:
//   - Actual mmap / build / file-stat I/O. Those are in
//     `RDF.CottasStore.OnDiskIndex` (mmap reader) +
//     `RDF.CottasStore` (`cottas_ondisk_open` assume-val) +
//     `RDF.CottasInMem` (in-RAM builder). This module is the policy;
//     the consumer in `factoidal_http.ml` is the mechanism.
//   - The Hashtbl-population side of Bet7 (`ensure_*_loaded` in
//     `experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh`). Those
//     stay where they are pending Phase 6 (offset-index migration);
//     they become the OCaml realisation of `LS_InRamFallback` and
//     emit `[bet7-trace]` lines verbatim. This module only decides
//     WHEN to invoke them.
//
// Per CLAUDE.md rule #11: pure F*, no new `assume val`s. The
// `companion_file_status` is constructed by the caller from
// `Sys.file_exists` / mmap probe / footer-magic checks; that
// classification is rule-#11(a) acceptable I/O glue.
//
// Wiring status: the API surface IS the final shape. The active call
// site in `factoidal_http.ml:650` (open_cottas_ondisk_files) and the
// glue patch `experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh`
// will be updated in a thin follow-up PR to consume
// `choose_load_strategy`. Per the Phase 4 Pruning/Estimate precedent,
// committing the F* spec ahead of the wiring keeps the violator
// retirement on the recovery-plan timeline; the wiring is a
// build-system gap, not a spec gap.
//
// `[bet7-trace]` log signature: the OCaml realisation MUST preserve
// the existing log line shape verbatim — external observers grep for
// `[bet7-trace]`. The exact strings are:
//
//   "[bet7-trace] build_handle path=<P> (lazy open: defer all 4 columns)"
//   "[bet7-trace] ensure_subjects_loaded: lazy populate path=<P>"
//   "[bet7-trace] ensure_subjects_loaded: <N> distinct subjects"
//   "[bet7-trace] ensure_objects_loaded: lazy populate path=<P>"
//   "[bet7-trace] ensure_objects_loaded: <N> distinct objects"
//   "[bet7-trace] ensure_predicates_loaded: lazy populate path=<P>"
//   "[bet7-trace] ensure_predicates_loaded: <N> distinct predicates"
//   "[bet7-trace] ensure_graphs_loaded: lazy populate path=<P>"
//   "[bet7-trace] ensure_graphs_loaded: <N> distinct graphs"
//
// Plus the `[bet7-WARN]` warn variants on token-parse failure. These
// are printed by the OCaml realisation that backs `LS_InRamFallback`,
// not by this module — F*-extracted code does not emit log lines.

// ---------------------------------------------------------------------------
// Companion-file status. The OCaml caller inspects the four companion
// files associated with a COTTAS artifact and reports back which of
// these four states they're collectively in. The classification is
// coarse-grained on purpose: the loader only needs enough information
// to choose between mmap, in-RAM-build, and refuse.
//
// `CFS_Present`     — every required companion exists, magic + schema
//                     version match the readers in
//                     `RDF.CottasStore.OnDiskIndex.fst`. Mmap path.
// `CFS_Missing`     — at least one required companion is absent (e.g.
//                     a fresh corpus that has not had companions
//                     built yet). The caller can either build the
//                     companions on the fly or fall back to in-RAM
//                     dictionaries. Bet7's historical answer is the
//                     latter.
// `CFS_Corrupt`     — a companion exists but its bytes do not parse
//                     (truncated file, wrong magic). Treat as missing
//                     for fall-back purposes; a separate logging path
//                     surfaces the corruption.
// `CFS_StaleSchema` — a companion exists, parses, but its schema
//                     version pre-dates the current reader's
//                     expectations. Same fall-back as Missing /
//                     Corrupt; a future companion-rebuild step will
//                     replace it.
// ---------------------------------------------------------------------------

type companion_file_status =
  | CFS_Present
  | CFS_Missing
  | CFS_Corrupt
  | CFS_StaleSchema

// ---------------------------------------------------------------------------
// Load strategy. The dispatch label the OCaml caller matches on.
//
// `LS_Mmap`           — open the companion files via the F*-verified
//                       mmap reader in `RDF.CottasStore.OnDiskIndex.fst`.
//                       Hashtbls populated from mmap'd bytes; cold-
//                       start ~2 s on the parliament corpus.
// `LS_InRamFallback`  — Bet7's historical path. The Hashtbls start
//                       empty; per-column `ensure_*_loaded` callbacks
//                       populate them on first lookup, decoding from
//                       the parquet directly. Emits `[bet7-trace]`
//                       lines as documented above.
// `LS_Refuse`         — refuse to open the corpus. Reserved for
//                       failure modes the loader cannot recover from;
//                       not currently emitted by `choose_load_strategy`
//                       below (the Bet7-era policy is "always fall
//                       back rather than refuse"), but reserved as a
//                       label so callers can pattern-match
//                       exhaustively and a future stricter policy
//                       can flip on it without a type change.
// ---------------------------------------------------------------------------

type load_strategy =
  | LS_Mmap
  | LS_InRamFallback
  | LS_Refuse

// ---------------------------------------------------------------------------
// choose_load_strategy — the pure decision function.
//
// Mirrors the existing Bet7 policy: companions present -> mmap; any
// other status -> in-RAM fallback. We never refuse; the caller's
// open-failure path handles "the parquet itself is broken" separately.
//
// Argument order is the obvious one: status in, strategy out.
// ---------------------------------------------------------------------------

let choose_load_strategy (s : companion_file_status) : Tot load_strategy =
  match s with
  | CFS_Present     -> LS_Mmap
  | CFS_Missing     -> LS_InRamFallback
  | CFS_Corrupt     -> LS_InRamFallback
  | CFS_StaleSchema -> LS_InRamFallback

// ---------------------------------------------------------------------------
// Properties.
// ---------------------------------------------------------------------------

// Warm path: companions present implies mmap. This is the property
// the daemon-boot prewarm relies on — the second + later opens of a
// corpus that was built once must take the fast path.
let choose_load_strategy_present_is_mmap ()
  : Lemma (ensures choose_load_strategy CFS_Present == LS_Mmap)
  = ()

// Bet7-policy invariant: any status other than Present takes the
// in-RAM fallback. Documents that the current policy never refuses.
// If a future PR introduces an `LS_Refuse` arm, this lemma is the
// place that flags the change for review.
let choose_load_strategy_non_present_is_in_ram
  (s : companion_file_status)
  : Lemma (requires s =!= CFS_Present)
          (ensures  choose_load_strategy s == LS_InRamFallback)
  = match s with
    | CFS_Missing     -> ()
    | CFS_Corrupt     -> ()
    | CFS_StaleSchema -> ()

// `choose_load_strategy` never returns `LS_Refuse` under the current
// policy. Stated as a property so the OCaml caller's pattern match
// can rely on the refuse arm being dead code (and a static check can
// flag it as unreachable). When a future stricter policy fires
// `LS_Refuse`, this lemma fails and the caller gets a verification
// error pointing here.
let choose_load_strategy_never_refuses
  (s : companion_file_status)
  : Lemma (ensures choose_load_strategy s =!= LS_Refuse)
  = match s with
    | CFS_Present     -> ()
    | CFS_Missing     -> ()
    | CFS_Corrupt     -> ()
    | CFS_StaleSchema -> ()

// ---------------------------------------------------------------------------
// Convenience: classify_outcome. Some callers want a boolean "is this
// the fast path?" without unpacking the strategy. Useful in metrics +
// trace lines that bucket cold vs warm opens.
// ---------------------------------------------------------------------------

let is_warm_path (st : load_strategy) : Tot bool =
  match st with
  | LS_Mmap -> true
  | LS_InRamFallback -> false
  | LS_Refuse -> false

let is_cold_path (st : load_strategy) : Tot bool =
  match st with
  | LS_Mmap -> false
  | LS_InRamFallback -> true
  | LS_Refuse -> false

// Sanity: Mmap is warm, InRamFallback is cold, exactly one of the two
// non-refusal arms is warm.
let warm_xor_cold_for_non_refuse (st : load_strategy)
  : Lemma (requires st =!= LS_Refuse)
          (ensures  is_warm_path st <> is_cold_path st)
  = match st with
    | LS_Mmap          -> ()
    | LS_InRamFallback -> ()

// Sanity: a Present status produces a warm path.
let present_is_warm_path ()
  : Lemma (ensures is_warm_path (choose_load_strategy CFS_Present))
  = ()
