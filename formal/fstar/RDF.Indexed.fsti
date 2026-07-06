module RDF.Indexed

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.3/§3.3 step 3 (bucket-map plumbing) and step 6 (RDF-specific
// glue folded in once step 5 dissolved a cyclic-dependency blocker).
// Full history in RDF.Indexed.fst's banner. Every value below is a
// *transparent* `let` (not an abstract `val`) — see RDF.Vocabulary
// .fsti's banner (§2.9) for why.
// This module is mechanism-heavy by nature (it IS an acceleration
// structure): the generic bucket-map preamble is mechanical throughout
// and stays before the `indexed_graph` concept only because F*
// transparent `let`s can't forward-reference it (fstar-module-style
// skill's reading-order note).

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple

(** ==================================================================== *)
(** Preamble: generic bucket-map mechanics (skip on first read — the    *)
(** concept, `indexed_graph`, starts below at the next divider). No     *)
(** RDF-specific content; a plain association-list multimap.            *)
(** ==================================================================== *)

/// A generic "bucket map": an association list from string keys to
/// lists of elements of type `a`. Used as the storage layer for
/// `RDF.Graph.Executable`'s `indexed_graph` acceleration structure
/// (predicate/subject/object/sp/po/so buckets over `triple`), but has
/// no RDF-specific content itself.
let bucket_map (a:Type) = list (string * list a)

/// First-match lookup; absent key returns the empty list. Total,
/// structural recursion on the map.
let rec bucket_lookup (#a:Type) (m : bucket_map a) (k : string)
  : Tot (list a) (decreases m) =
  match m with
  | [] -> []
  | (k', v) :: rest -> if k = k' then v else bucket_lookup rest k

/// Tail-recursive accumulator form (mirrors the pre-move code's
/// issue-#119 stack-safety fix: a straight-recursive shape blew JS's
/// ~10K stack at lifesci-scale ingest because each frame wraps the
/// recursive result in a fresh cons).
let rec bucket_replace_acc (#a:Type)
  (acc : bucket_map a) (m : bucket_map a) (k : string) (v : list a)
  : Tot (bucket_map a) (decreases m) =
  match m with
  | [] -> List.Tot.rev_acc acc [(k, v)]
  | (k', v') :: rest ->
    if k = k' then List.Tot.rev_acc acc ((k, v) :: rest)
    else bucket_replace_acc ((k', v') :: acc) rest k v

/// Replace-or-add for a key: keeps a single binding per key (mirrors
/// OCaml's `Hashtbl.replace`).
let bucket_replace (#a:Type) (m : bucket_map a) (k : string) (v : list a)
  : Tot (bucket_map a) =
  bucket_replace_acc [] m k v

/// Push a single element onto the bucket for `k` (cons-to-front).
let bucket_push (#a:Type) (m : bucket_map a) (k : string) (t : a)
  : Tot (bucket_map a) =
  bucket_replace m k (t :: bucket_lookup m k)

/// Comparator for `List.Tot.sortWith`, generic over `key_of`.
/// Elements with no key for this bucket (`None`) sort first; the
/// grouping pass below filters them out.
///
/// 2026-07-06 (GROUP BY / index-build linear-constant perf investigation,
/// docs/designissues/2026-07-06-competitive-benchmark-results.md): this
/// comparator used to be handed DIRECTLY to `List.Tot.sortWith` together
/// with `key_of`, so it recomputed `key_of t1`/`key_of t2` on EVERY
/// comparison the sort performed — O(N log N) key computations per
/// bucket, not O(N). For `sp_key`/`po_key_opt`/`so_key_opt` each
/// recomputation is itself a `String.concat` (allocating a fresh
/// composite string), so the *N log N factor multiplied an allocating
/// string-concat*: profiled with `valgrind --tool=callgrind` on a
/// 51,696-triple/100k-line subset of `gene.ttl` (isolating the GROUP BY
/// query's cost against an otherwise-identical `COUNT(*)`-only query
/// evaluated over the same data — the only code this differential can
/// attribute to is whatever the GROUP BY path exercises that COUNT(*)
/// does not): `String.unsafe_blits` (1.08B instructions of the 6.3B-
/// instruction differential, ~17%), `String.concat` (0.30B),
/// `caml_blit_string`/`caml_alloc_string`/`__memcpy_avx_unaligned_erms`
/// (a further ~1.5B combined), plus knock-on GC pressure from the
/// allocation churn (`do_some_marking`/`caml_oldify_one`/`sweep_slice`/
/// `bf_allocate`, ~0.9B combined) — all traced to `build_indexed`
/// (`graph_to_store` in `SPARQL11.Algebra.fst` calls it unconditionally
/// for every non-streaming-fast-path query) building its 6 bucket maps
/// (`ig_pred`/`ig_subj`/`ig_obj`/`ig_sp`/`ig_po`/`ig_so`) via
/// `build_bucket`, each a full `List.Tot.sortWith` over the whole graph.
/// This function is unchanged; `build_bucket` below now decorates each
/// element with its key ONCE before sorting (a standard
/// decorate-sort-undecorate / Schwartzian transform) instead of calling
/// this comparator's `key_of` per element per comparison.
let cmp_by_key (#a:Type) (key_of : a -> option string) (t1 t2 : a) : int =
  match key_of t1, key_of t2 with
  | None, None       -> 0
  | None, Some _     -> -1
  | Some _, None     -> 1
  | Some k1, Some k2 -> String.compare k1 k2

/// Comparator over PRE-COMPUTED `(key, elem)` pairs — same ordering as
/// `cmp_by_key` (None-first, then `String.compare` on the key), but
/// reads the already-computed key instead of calling `key_of` again.
/// Because `key_of` is a pure/deterministic (`Tot`) function, this
/// comparator decides every pair exactly as `cmp_by_key key_of` would
/// have, so `build_bucket`'s sorted order (and hence its grouping) is
/// unchanged — only the number of `key_of` calls drops, from O(N log N)
/// to exactly N.
let cmp_by_decorated_key (#a:Type) (p1 p2 : (option string * a)) : int =
  match fst p1, fst p2 with
  | None, None       -> 0
  | None, Some _     -> -1
  | Some _, None     -> 1
  | Some k1, Some k2 -> String.compare k1 k2

/// Walk a key-sorted list of PRE-COMPUTED `(key, elem)` pairs,
/// collapsing each run of same-key elements into one `(key, elements)`
/// binding. Tail-rec via reversed accumulator; `bucket_map` lookup
/// doesn't depend on bucket order so this doesn't bother to reverse at
/// the end. Same shape as the old `group_sorted_aux` (kept below,
/// unused by `build_bucket` now but left as the reference definition
/// `cmp_by_key`/decorate-free callers could still use), just reading
/// each element's key from the pair instead of calling `key_of` again.
let rec group_sorted_decorated_aux (#a:Type)
    (ts : list (option string * a))
    (cur_key : option string) (cur_bucket : list a)
    (acc : bucket_map a)
  : Tot (bucket_map a) (decreases ts) =
  match ts with
  | [] ->
    (match cur_key with
     | Some k -> (k, cur_bucket) :: acc
     | None   -> acc)
  | (k, t) :: rest ->
    (match k with
     | None -> group_sorted_decorated_aux rest cur_key cur_bucket acc
     | Some kk ->
       (match cur_key with
        | Some k0 ->
          if kk = k0 then
            group_sorted_decorated_aux rest cur_key (t :: cur_bucket) acc
          else
            group_sorted_decorated_aux rest (Some kk) [t] ((k0, cur_bucket) :: acc)
        | None ->
          group_sorted_decorated_aux rest (Some kk) [t] acc))

/// Walk a key-sorted list, collapsing each run of same-key elements
/// into one `(key, elements)` binding. Tail-rec via reversed
/// accumulator; `bucket_map` lookup doesn't depend on bucket order so
/// this doesn't bother to reverse at the end.
///
/// No longer called by `build_bucket` (see `group_sorted_decorated_aux`
/// above) — kept as the reference, decoration-free definition since it
/// documents the grouping algorithm most directly and nothing else in
/// this file depends on removing it.
let rec group_sorted_aux (#a:Type)
    (key_of : a -> option string)
    (ts : list a)
    (cur_key : option string) (cur_bucket : list a)
    (acc : bucket_map a)
  : Tot (bucket_map a) (decreases ts) =
  match ts with
  | [] ->
    (match cur_key with
     | Some k -> (k, cur_bucket) :: acc
     | None   -> acc)
  | t :: rest ->
    (match key_of t with
     | None -> group_sorted_aux key_of rest cur_key cur_bucket acc
     | Some k ->
       (match cur_key with
        | Some k0 ->
          if k = k0 then
            group_sorted_aux key_of rest cur_key (t :: cur_bucket) acc
          else
            group_sorted_aux key_of rest (Some k) [t] ((k0, cur_bucket) :: acc)
        | None ->
          group_sorted_aux key_of rest (Some k) [t] acc))

/// Build a bucket map from a flat list in one pass: sort by key
/// (elements with no key for this bucket sort first and are dropped),
/// then collapse each run of same-key elements into one binding.
/// O(N log N) — see `RDF.Graph.Executable.fst`'s `build_indexed`
/// banner (issue #259) for why this replaced an O(N*K) per-insert
/// build.
///
/// 2026-07-06: decorate-sort-undecorate — `key_of` is now called
/// exactly once per element (the `List.Tot.map` below) instead of once
/// per comparison inside the sort (see `cmp_by_key`'s banner above for
/// the profiling evidence). The sort itself is still O(N log N)
/// comparisons, but each comparison is now a cheap `String.compare` (or
/// `option` short-circuit) over an already-built string, not a fresh
/// `String.concat` allocation.
let build_bucket (#a:Type) (key_of : a -> option string) (ts : list a)
  : Tot (bucket_map a) =
  let decorated = List.Tot.map (fun (t : a) -> (key_of t, t)) ts in
  let sorted = List.Tot.sortWith cmp_by_decorated_key decorated in
  group_sorted_decorated_aux sorted None [] []

(** ==================================================================== *)
(** Concept: `indexed_graph` — a multi-index acceleration structure     *)
(** over `list triple` (RDF 1.1 Concepts §3, "a set of triples", plus   *)
(** per-key bucket indexes for O(log n) lookup instead of O(n) scan).   *)
(** Folded in at step 6 (see module banner) — was blocked on step 5.    *)
(** The operations below are the point of this module, so they stay    *)
(** with the concept rather than in a separate appendix; the key-      *)
(** encoding one-liners (`subject_to_key`/`sp_key`/etc.) and the        *)
(** `build_indexed` extractor helpers (`bucket_key_*`) are the only     *)
(** purely mechanical parts, each 1-3 lines — flagged inline below.     *)
(** ==================================================================== *)

(* 2026-07-06 (lazy per-bucket index construction -- the residual flagged
   by the decorate-sort-undecorate commit's own banner above: gene.ttl's
   888,949-triple GROUP BY ?p spent ~11.5s of its ~11.5s total inside
   `build_indexed` building all 6 sorted bucket maps, of which the
   all-unbound BGP `?s ?p ?o` reads NONE -- `ig_search` on that pattern
   never calls a single `bucket_lookup`). `bucket_needs` records which of
   the 6 buckets a caller actually wants built; `build_indexed_selective`
   below builds only those, leaving the rest `[]`. This is SAFE regardless
   of how (im)precise a caller's `bucket_needs` is: `SPARQL11.Algebra
   .ig_search`'s last step is always `triple_matches_bound b pool`, which
   re-checks every candidate against the ACTUAL runtime-bound
   `triple_pattern_bound` -- a bucket that was never built simply isn't
   offered as a narrowing candidate (see `ig_built`-gated reads in
   `ig_search`), so the search falls back to `ig_triples` (the
   always-present full list) for that one lookup. Wrong `bucket_needs`
   can only make a query slower (an O(n) scan instead of an O(log n)
   bucket read), never wrong -- so the query-shape pre-pass that computes
   `bucket_needs` (`SPARQL11.Algebra.bucket_needs_of_pattern`) is free to
   over-approximate. `build_indexed` (unchanged name/signature) is now
   `build_indexed_selective all_bucket_needs` -- full build, byte-identical
   to before this change -- so SHACL/OWL/RDFS closure and any other caller
   that doesn't know its own query shape keeps building every bucket. *)
type bucket_needs = {
  bn_pred : bool;
  bn_subj : bool;
  bn_obj  : bool;
  bn_sp   : bool;
  bn_po   : bool;
  bn_so   : bool;
}

let all_bucket_needs : bucket_needs =
  { bn_pred = true; bn_subj = true; bn_obj = true; bn_sp = true; bn_po = true; bn_so = true }

let no_bucket_needs : bucket_needs =
  { bn_pred = false; bn_subj = false; bn_obj = false; bn_sp = false; bn_po = false; bn_so = false }

(* Union of two needs sets -- used to combine the needs computed for the
   default graph across every triple pattern the query's algebra can
   reach (RDF.Indexed has no dependency on the algebra's pattern types,
   so the combinator lives here; the per-pattern analysis lives in
   `SPARQL11.Algebra.bucket_needs_of_pattern`). *)
let bucket_needs_or (a b : bucket_needs) : bucket_needs = {
  bn_pred = a.bn_pred || b.bn_pred;
  bn_subj = a.bn_subj || b.bn_subj;
  bn_obj  = a.bn_obj  || b.bn_obj;
  bn_sp   = a.bn_sp   || b.bn_sp;
  bn_po   = a.bn_po   || b.bn_po;
  bn_so   = a.bn_so   || b.bn_so;
}

noeq type indexed_graph = {
  ig_triples : list triple;     (* preserves source-of-truth order semantics *)
  ig_pred    : bucket_map triple;       (* keyed by predicate IRI string *)
  ig_subj    : bucket_map triple;       (* keyed by subject_to_key *)
  ig_obj     : bucket_map triple;       (* keyed by term_to_key_opt; literals omitted *)
  (* Phase 1 compound indexes (#100). Composite keys use ASCII unit
     separator U+001F, which is forbidden in IRIs (RFC 3987) and never
     appears in our blank-node keys. Literals (term_to_key_opt = None)
     are not indexed; same rationale as ig_obj. *)
  ig_sp      : bucket_map triple;       (* keyed by sp_key   : subj_key ^ "\x1f" ^ pred_iri *)
  ig_po      : bucket_map triple;       (* keyed by po_key   : pred_iri ^ "\x1f" ^ obj_key  *)
  ig_so      : bucket_map triple;       (* keyed by so_key   : subj_key ^ "\x1f" ^ obj_key  *)
  (* Which of the 6 buckets above were actually built by whoever
     constructed this record -- see the `bucket_needs` banner above.
     `build_indexed` sets every flag true (full build). A bucket whose
     flag is `false` is `[]` *by construction, not because it happens to
     have no matches* -- readers MUST check the flag (see `ig_search`'s
     `ig_built`-gated candidates) before trusting an empty bucket_lookup
     as "no matches." *)
  ig_built   : bucket_needs;
}

(* Canonical key for a subject. Total. *)
let subject_to_key (s : subject) : string =
  match s with
  | S_IRI i   -> String.concat "" ["I_"; i]
  | S_BNode b -> String.concat "" ["B_"; b]

(* Canonical key for an rdf_term, or None for literals. We do NOT index
   on literals because they would require datatype/lang-tag normalisation
   and rarely appear as a join axis in real BGPs. Object-literal patterns
   fall through to whichever bound component (predicate or subject) is
   indexable, or to the full triple list if neither is. *)
let term_to_key_opt (o : rdf_term) : option string =
  match o with
  | T_IRI i     -> Some (String.concat "" ["I_"; i])
  | T_BNode b   -> Some (String.concat "" ["B_"; b])
  | T_Literal _ -> None

(* Composite key separator: ASCII Unit Separator (U+001F). Forbidden in
   IRIs by RFC 3987, never appears in our subject/object keys (which are
   "I_..."/"B_..."), so concatenation is unambiguous. *)
let unit_sep : string = "\x1f"

let sp_key (s : subject) (p : wf_iri) : string =
  String.concat "" [subject_to_key s; unit_sep; p]

let po_key_opt (p : wf_iri) (o : rdf_term) : option string =
  match term_to_key_opt o with
  | Some k -> Some (String.concat "" [p; unit_sep; k])
  | None   -> None

let so_key_opt (s : subject) (o : rdf_term) : option string =
  match term_to_key_opt o with
  | Some k -> Some (String.concat "" [subject_to_key s; unit_sep; k])
  | None   -> None

(* #259 followup / OWL-RL Commit A (2026-05-13).
   Index-backed (s, p, ?) lookup. Bucket: ig_sp.
   Same return contract as find_objects: list of objects, no dedup.
   Replaces O(N) linear scans inside the closure rules' outer fold;
   per-rule cost drops from O(N^2) to O(log P + |result|). *)
let find_objects_indexed (ig : indexed_graph) (subj : subject) (pred : wf_iri)
  : Tot (list rdf_term) =
  let bucket = bucket_lookup ig.ig_sp (sp_key subj pred) in
  List.Tot.map (fun (t : triple) -> t.o) bucket

(* Index-backed (?, p, o) lookup. Uses ig_po when o is non-literal
   (the common case in closure rules); falls back to ig_pred + filter
   when o is a literal (rare in OWL/RDFS schema axioms). *)
let find_subjects_indexed (ig : indexed_graph) (pred : wf_iri) (obj : rdf_term)
  : Tot (list subject) =
  let bucket =
    match po_key_opt pred obj with
    | Some k -> bucket_lookup ig.ig_po k
    | None ->
      List.Tot.filter
        (fun (t : triple) -> rdf_term_eq t.o obj)
        (bucket_lookup ig.ig_pred pred)
  in
  List.Tot.map (fun (t : triple) -> t.s) bucket

(* Single-step index update for one triple. *)
let add_triple_to_indexes (ig : indexed_graph) (t : triple) : indexed_graph =
  let new_pred = bucket_push ig.ig_pred t.p t in
  let new_subj = bucket_push ig.ig_subj (subject_to_key t.s) t in
  let new_obj  = match term_to_key_opt t.o with
    | Some k -> bucket_push ig.ig_obj k t
    | None -> ig.ig_obj in
  let new_sp   = bucket_push ig.ig_sp (sp_key t.s t.p) t in
  let new_po   = match po_key_opt t.p t.o with
    | Some k -> bucket_push ig.ig_po k t
    | None -> ig.ig_po in
  let new_so   = match so_key_opt t.s t.o with
    | Some k -> bucket_push ig.ig_so k t
    | None -> ig.ig_so in
  {
    ig_triples = t :: ig.ig_triples;
    ig_pred = new_pred;
    ig_subj = new_subj;
    ig_obj = new_obj;
    ig_sp = new_sp;
    ig_po = new_po;
    ig_so = new_so;
    ig_built = ig.ig_built;    (* incremental update: leaves whichever buckets
                                  the input `ig` already had (un)built alone *)
  }

(* Build the index from a flat triple list. Linear in the input length;
   each insert is bucket-replace which is linear in the current bucket-map
   size. Total cost O(N * K) where K is the number of distinct keys —
   acceptable for one-shot load. A hashtable swap reduces this to O(N).

   #259 fix (2026-05-11): for any N×K product that gets large enough to
   matter (the lifesci demo's 27K-triple disease.ttl, K ≈ 5K-20K distinct
   subjects/sp-pairs/etc., 270M+ list-walks per bucket) the cumulative
   build cost dominates even `SELECT * LIMIT 1`. Switch to a sort-and-group
   pass per bucket: `List.Tot.sortWith` is O(N log N), then a single
   linear walk collapses adjacent same-key entries into one binding.
   Net: O(N log N) per bucket × 6 buckets = ~6 N log N total.
   Preserves the "one binding per key" invariant the lookup paths rely on. *)
let rec build_indexed_aux (g : list triple) (acc : indexed_graph)
  : Tot indexed_graph (decreases g) =
  match g with
  | [] -> acc
  | t :: rest -> build_indexed_aux rest (add_triple_to_indexes acc t)

(* Mechanical: per-bucket key extractors used only by `build_indexed`
   below, one line each. Each returns `None` for triples that
   shouldn't appear in that bucket (e.g. ig_obj omits literal-keyed
   triples because term_to_key_opt returns None on literals). *)
let bucket_key_pred (t : triple) : option string = Some t.p
let bucket_key_subj (t : triple) : option string = Some (subject_to_key t.s)
let bucket_key_obj  (t : triple) : option string = term_to_key_opt t.o
let bucket_key_sp   (t : triple) : option string = Some (sp_key t.s t.p)
let bucket_key_po   (t : triple) : option string = po_key_opt t.p t.o
let bucket_key_so   (t : triple) : option string = so_key_opt t.s t.o

let empty_indexed : indexed_graph = {
  ig_triples = [];
  ig_pred = [];
  ig_subj = [];
  ig_obj = [];
  ig_sp = [];
  ig_po = [];
  ig_so = [];
  ig_built = all_bucket_needs;
}

(* Build the index from a flat triple list, but only the buckets
   `needs` flags on -- the rest are left `[]` and marked unbuilt in
   `ig_built` (see the `bucket_needs` banner above `indexed_graph` for
   why this is safe regardless of `needs`'s precision). Takes a plain
   `list triple` (not `RDF.Graph.rdf_graph`, which is a transparent
   alias for exactly this type) — see the module banner for why: this
   keeps RDF.Indexed's dependency on RDF.Graph at zero. *)
let build_indexed_selective (needs : bucket_needs) (g : list triple) : Tot indexed_graph =
  {
    ig_triples = g;
    ig_pred = if needs.bn_pred then build_bucket bucket_key_pred g else [];
    ig_subj = if needs.bn_subj then build_bucket bucket_key_subj g else [];
    ig_obj  = if needs.bn_obj  then build_bucket bucket_key_obj  g else [];
    ig_sp   = if needs.bn_sp   then build_bucket bucket_key_sp   g else [];
    ig_po   = if needs.bn_po   then build_bucket bucket_key_po   g else [];
    ig_so   = if needs.bn_so   then build_bucket bucket_key_so   g else [];
    ig_built = needs;
  }

(* Full build -- every bucket, always. Unchanged name/signature/
   behaviour from before the lazy-index-construction change: every
   existing caller that doesn't (or can't) know its own query shape
   -- SHACL.Validation, OWL.Closure, RDFS.Closure, and any future one
   -- keeps building every bucket, byte-identical to before. *)
let build_indexed (g : list triple) : Tot indexed_graph =
  (* #259 fix: sort-and-group per bucket — see comment on build_indexed_aux. *)
  build_indexed_selective all_bucket_needs g
