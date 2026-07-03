module RDF.CottasStore

open RDF.Graph.Executable
open Parser.BallyhooCOTTAS
open Parquet.Footer
open RDF.CottasStore.PageCache
open RDF.CottasStore.ColumnSeq
open FStar.All
module CPO = RDF.CottasStore.CompoundPresenceBitmap

// On-disk COTTAS store, query-time interface (issue #100).
//
// History: this module's contents used to live at the bottom of
// Parser.BallyhooCOTTAS.fst, with 13 `assume val`s whose bodies lived in
// experimental_ocaml_glue/cottas_ondisk_runtime.sh (688 LoC OCaml). Per
// CLAUDE.md rules #1 / #7 / #15 + memory feedback_fstar_first_always.md,
// 11 of those 13 lookup functions were lifted to F* in Phase A
// (commit 967ed4f). Phase B (this commit) lifts the remaining
// `cottas_ondisk_search` / `cottas_ondisk_estimate` to F*, walking the
// parquet row groups on demand via `Parquet.Footer.probe_parquet_*`
// helpers. Only `cottas_ondisk_open` and `cottas_ondisk_close` remain
// I/O-glue.
//
// All semantic logic (encode/decode/predicate-presence/named-graph walk
// + search + estimate) lives here. The OCaml glue at
// cottas_ondisk_runtime.sh now does only ONE thing: at open() time, read
// 4 columns from the Parquet file (across all row groups), parse each
// distinct token to its RDF shape, build the reverse maps + the parallel
// raw-token lists, and hand the F* runtime a populated handle record.
// F* does the rest, lazily iterating row groups via
// `probe_parquet_column_decode_in_row_group`.

noeq type cottas_ondisk_handle = {
  // Path the handle came from. Used by Phase B search/estimate to
  // re-open and walk row groups via Parquet.Footer probes.
  coh_path : string;
  // Aggregate summary (passes through to cods_summary).
  coh_summary : option cottas_artifact_summary;
  // Per-column distinct-term inventories. Index in the list IS the
  // term-id stored in the per-row int columns. Built at open() time
  // by the I/O glue parsing each column's distinct tokens.
  coh_subjects   : list subject;
  coh_predicates : list wf_iri;
  coh_objects    : list rdf_term;
  coh_graphs     : list iri;
  // Reverse maps: canonical key string -> term-id. Used by encode_*
  // to turn a parsed RDF term back into its int term-id, or None if
  // the term is absent from this corpus (caller short-circuits to []).
  coh_subj_revmap  : list (string * nat);
  coh_pred_revmap  : list (string * nat);
  coh_obj_revmap   : list (string * nat);
  coh_graph_revmap : list (string * nat);
  // Phase B (issue #100) — parallel raw-column-token lists, indexed by
  // term-id. Used by search/estimate to convert a bound term-id into
  // the column-token string it would appear as in the parquet row,
  // without needing to re-encode/escape from the typed term.
  // `coh_graphs_raw` does NOT include the "DEFAULT" sentinel — only
  // named-graph IRIs in raw "<iri>" form. Default-graph rows are
  // detected at search time by matching the literal string "DEFAULT".
  coh_subjects_raw   : list string;
  coh_predicates_raw : list string;
  coh_objects_raw    : list string;
  coh_graphs_raw     : list string;
  // Phase B — raw-token-keyed reverse maps, used by search to look up
  // a matched row's IDs without re-parsing. Same shape as the
  // canonical-key revmaps above; the OCaml glue builds both at open()
  // time. (We keep the canonical-key revmaps because the public encode_*
  // functions take typed RDF terms, which produce canonical keys via
  // *_to_revmap_key.)
  coh_subj_raw_revmap  : list (string * nat);
  coh_pred_raw_revmap  : list (string * nat);
  coh_obj_raw_revmap   : list (string * nat);
  coh_graph_raw_revmap : list (string * nat);
}

noeq type cottas_ondisk_store = {
  cods_artifact_path : string;
  cods_summary : option cottas_artifact_summary;
  cods_handle : cottas_ondisk_handle;
}

// ----------------------------------------------------------------------
// Pure F* helpers
// ----------------------------------------------------------------------

// Look up a key in an assoc-list of (string * nat) pairs.
// Mirrors RDF.Graph.Executable.bucket_lookup but for nat-valued maps.
let rec revmap_lookup (m : list (string * nat)) (k : string)
  : Tot (option nat) (decreases m) =
  match m with
  | [] -> None
  | (k', v) :: rest -> if k = k' then Some v else revmap_lookup rest k

// Index into a list. Returns None for out-of-range. The OCaml runtime
// already guarantees term-ids stored in the per-row arrays are in
// [0, length) so well-formed COTTAS data never trips the None branch;
// we still handle it to keep this function total.
let rec list_nth (#a:Type) (xs : list a) (i : nat)
  : Tot (option a) (decreases xs) =
  match xs with
  | [] -> None
  | hd :: tl -> if i = 0 then Some hd else list_nth tl (i - 1)

// Canonical key strings used by encode_*. The OCaml glue at open() time
// builds the reverse map using these same key strings (computed via the
// F*-extracted versions of these functions, so the keys are guaranteed
// to match by construction). Format: tag-prefixed, unit-separator-
// delimited, no escaping needed (none of the components contain U+001F).
//
// The unit separator (U+001F) is forbidden in IRIs by RFC 3987 and not
// produced by our blank-node/lexical-form pipeline, so the segments are
// unambiguous.
let revmap_unit_sep : string = "\x1f"

let subject_to_revmap_key (s : subject) : string =
  match s with
  | S_IRI i   -> String.concat "" ["I_"; i]
  | S_BNode b -> String.concat "" ["B_"; b]

let iri_to_revmap_key (i : iri) : string =
  String.concat "" ["I_"; i]

// Object key: tag-prefixed, with literals encoded as
// "L_" + datatype + US + langtag + US + lexical-form. Lang-tag empty
// when absent. Lexical form is included verbatim — no escape needed
// because literals can't contain U+001F (it's a control character;
// not allowed in well-formed RDF lexical forms either).
let object_to_revmap_key (o : rdf_term) : string =
  match o with
  | T_IRI i -> String.concat "" ["I_"; i]
  | T_BNode b -> String.concat "" ["B_"; b]
  | T_Literal l ->
    let tag = match l.lang_tag with
      | Some t -> t
      | None -> "" in
    String.concat ""
      ["L_"; l.datatype; revmap_unit_sep; tag; revmap_unit_sep; l.lexical_form]

// ----------------------------------------------------------------------
// 11 lookup functions — F* implementations
// ----------------------------------------------------------------------

// Summary passthrough: handle holds it, store holds the handle.
let cottas_ondisk_summary (ds : cottas_ondisk_store)
  : Tot (option cottas_artifact_summary) =
  ds.cods_handle.coh_summary

// Encode subject/predicate/object/graph: revmap lookup. Returns None
// when the term is absent from the corpus dictionary, signalling a
// definitively-empty triple-pattern result.
let cottas_ondisk_encode_subject
  (ds : cottas_ondisk_store) (s : subject)
  : Tot (option cottas_term_ref) =
  revmap_lookup ds.cods_handle.coh_subj_revmap (subject_to_revmap_key s)

let cottas_ondisk_encode_predicate
  (ds : cottas_ondisk_store) (p : wf_iri)
  : Tot (option cottas_term_ref) =
  revmap_lookup ds.cods_handle.coh_pred_revmap (iri_to_revmap_key p)

let cottas_ondisk_encode_object
  (ds : cottas_ondisk_store) (o : rdf_term)
  : Tot (option cottas_term_ref) =
  revmap_lookup ds.cods_handle.coh_obj_revmap (object_to_revmap_key o)

let cottas_ondisk_encode_graph_name
  (ds : cottas_ondisk_store) (g : iri)
  : Tot (option cottas_graph_ref) =
  revmap_lookup ds.cods_handle.coh_graph_revmap (iri_to_revmap_key g)

// Decode: list-indexing into the parsed-term inventory. The cottas_term_ref
// is `nat`, so it's already non-negative; we still need a fallback when
// (improbably) it's out of range. Falls back to a sentinel value:
//   - subject/object: the empty-IRI bnode "_:cottas_decode_oor"
//   - predicate: rdf:type as a stable wf_iri
//   - graph: the empty IRI ""  (NOT a wf_iri; iri = string)
// Out-of-range only happens on corrupt or mismatched COTTAS files; the
// sentinel keeps the function total without raising. This matches the
// rule #15 boundary: the I/O layer catches "this file is broken" via
// failwith at open time; once the handle is accepted, the F*-side decode
// is total.
let cottas_ondisk_decode_subject
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : Tot subject =
  match list_nth ds.cods_handle.coh_subjects id with
  | Some s -> s
  | None -> S_BNode "cottas_decode_oor"

let cottas_ondisk_decode_predicate
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : Tot wf_iri =
  match list_nth ds.cods_handle.coh_predicates id with
  | Some p -> p
  | None ->
    // Out-of-range / unpopulated-list fallback. We deliberately do
    // NOT default to rdf:type here — that hid a real correctness bug
    // for weeks (Bet7's lazy-open leaves `coh_predicates = []`, so
    // every decode missed and silently returned rdf:type, which
    // looked indistinguishable from "the data really had rdf:type
    // here"). The visible-sentinel fallback below ensures the next
    // identical bug crashes loudly into the result set instead.
    //
    // The actual runtime predicate lookup is provided by the
    // OCaml-glue patch `cottas_ondisk_runtime.sh`, which substitutes
    // a `Cottas_ondisk_runtime.decode_predicate_fast` body that
    // consults the populated `tables.ft_id_to_predicate` Hashtbl.
    // This sentinel only fires if that override hasn't run, e.g. on
    // a corpus extracted with no glue patch applied.
    let fallback : iri = "urn:factoidal:cottas-decode-predicate-unknown-id" in
    assert_norm (is_iri fallback);
    fallback

let cottas_ondisk_decode_object
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : Tot rdf_term =
  match list_nth ds.cods_handle.coh_objects id with
  | Some o -> o
  | None -> T_BNode "cottas_decode_oor"

let cottas_ondisk_decode_graph_name
  (ds : cottas_ondisk_store) (id : cottas_graph_ref)
  : Tot iri =
  match list_nth ds.cods_handle.coh_graphs id with
  | Some g -> g
  | None -> ""

// Predicate-presence: look up the predicate in the reverse map. If the
// predicate isn't a dictionary entry it can't appear in any row.
// (The OCaml glue's previous `predicates_seen` cache was an overengineered
// optimisation; the predicate dictionary is small (231 entries on the
// parliament corpus) and the reverse map already encodes membership.)
let cottas_ondisk_predicate_present
  (ds : cottas_ondisk_store) (pred : wf_iri)
  : Tot bool =
  match revmap_lookup ds.cods_handle.coh_pred_revmap (iri_to_revmap_key pred) with
  | None -> false
  | Some _ -> true

// Named-graph inventory: walk the graph distinct-iri list, attaching
// each entry's index as its graph-ref. The list is built at open()
// time, so this is just a list_mapi-like traversal.
let rec named_graphs_aux
  (graphs : list iri) (idx : nat)
  : Tot (list (iri & cottas_graph_ref)) (decreases graphs) =
  match graphs with
  | [] -> []
  | g :: rest -> (g, idx) :: named_graphs_aux rest (idx + 1)

let cottas_ondisk_named_graphs (ds : cottas_ondisk_store)
  : Tot (list (iri & cottas_graph_ref)) =
  named_graphs_aux ds.cods_handle.coh_graphs 0

// ----------------------------------------------------------------------
// ML-effected encode/decode variants — opt-in path through the
// `RDF.CottasStore.LazyDictRegistry` typed boundary. Same semantic
// contract as the Tot variants above but uses Hashtbl-backed
// LazyDict O(1) lookups instead of list-assoc O(n). Consumers that
// can tolerate the ML effect (e.g. external CLI/HTTP entry points
// in bin/) call these for the fast path through the F*-typed
// boundary; consumers that need Tot purity (e.g. the SPARQL
// evaluator's BGP-walk inner loops) stick with the original
// revmap_lookup-based variants above. #254 / #118 plans phase out
// the sed-rewrite cottas_ondisk_runtime.sh patch by migrating
// consumers to these.
//
// Returns None when register_for_path hasn't yet been called for
// the handle's path (e.g. handle opened before the registry was
// wired). Caller can fall back to the Tot variants in that case.

let cottas_ondisk_encode_subject_ml
  (ds : cottas_ondisk_store) (s : subject)
  : ML (option cottas_term_ref) =
  match RDF.CottasStore.LazyDictRegistry.get_subjects_lazy
          ds.cods_handle.coh_path with
  | Some d -> RDF.CottasStore.LazyDict.encode_by_key d
                (subject_to_revmap_key s)
  | None   -> cottas_ondisk_encode_subject ds s

let cottas_ondisk_encode_predicate_ml
  (ds : cottas_ondisk_store) (p : wf_iri)
  : ML (option cottas_term_ref) =
  match RDF.CottasStore.LazyDictRegistry.get_predicates_lazy
          ds.cods_handle.coh_path with
  | Some d -> RDF.CottasStore.LazyDict.encode_by_key d
                (iri_to_revmap_key p)
  | None   -> cottas_ondisk_encode_predicate ds p

let cottas_ondisk_encode_object_ml
  (ds : cottas_ondisk_store) (o : rdf_term)
  : ML (option cottas_term_ref) =
  match RDF.CottasStore.LazyDictRegistry.get_objects_lazy
          ds.cods_handle.coh_path with
  | Some d -> RDF.CottasStore.LazyDict.encode_by_key d
                (object_to_revmap_key o)
  | None   -> cottas_ondisk_encode_object ds o

let cottas_ondisk_decode_subject_ml
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML subject =
  match RDF.CottasStore.LazyDictRegistry.get_subjects_lazy
          ds.cods_handle.coh_path with
  | Some d ->
    (match RDF.CottasStore.LazyDict.decode_by_id d id with
     | Some s -> s
     | None   -> cottas_ondisk_decode_subject ds id)
  | None   -> cottas_ondisk_decode_subject ds id

let cottas_ondisk_decode_predicate_ml
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML wf_iri =
  match RDF.CottasStore.LazyDictRegistry.get_predicates_lazy
          ds.cods_handle.coh_path with
  | Some d ->
    (match RDF.CottasStore.LazyDict.decode_by_id d id with
     | Some p -> p
     | None   -> cottas_ondisk_decode_predicate ds id)
  | None   -> cottas_ondisk_decode_predicate ds id

let cottas_ondisk_decode_object_ml
  (ds : cottas_ondisk_store) (id : cottas_term_ref)
  : ML rdf_term =
  match RDF.CottasStore.LazyDictRegistry.get_objects_lazy
          ds.cods_handle.coh_path with
  | Some d ->
    (match RDF.CottasStore.LazyDict.decode_by_id d id with
     | Some o -> o
     | None   -> cottas_ondisk_decode_object ds id)
  | None   -> cottas_ondisk_decode_object ds id

// ----------------------------------------------------------------------
// Phase B: search + estimate, lazy walk over parquet row groups.
// Implemented in F* via Parquet.Footer.probe_parquet_column_decode_in_row_group.
// Only `cottas_ondisk_open` / `cottas_ondisk_close` remain I/O-glue.
// ----------------------------------------------------------------------

// Open: I/O. Parses the Parquet file, walks every row group, builds the
// 4 distinct-term dictionaries (typed lists + revmaps + raw-token
// parallel lists). Phase C will refactor with mmap.
assume val cottas_ondisk_open :
  artifact_path:string -> Tot (option cottas_ondisk_store)

// Close: I/O. Releases caches; F* runtime hashtables drop via GC.
// Currently not extracted (no use site in F*).
assume val cottas_ondisk_close :
  cottas_ondisk_store -> Tot unit

// ---- Bound term-id -> raw column-token string ----------------------

// Convert a bound term-id (option nat) to the column-token string it
// would appear as in the parquet column, for matching. None means
// "no bound on this column, accept any value".
let id_to_raw_token (raws : list string) (id : option cottas_term_ref)
  : Tot (option string) =
  match id with
  | None -> None
  | Some i ->
    (match list_nth raws i with
     | Some s -> Some s
     // Out-of-range fallback: an impossible sentinel that won't match
     // any well-formed row token. Keeps the function total.
     | None -> Some "\x00cottas_decode_oor")

// Compare a row-cell to the bound's expected token. None bound =
// accept anything; Some s requires equality.
let cell_match (expected : option string) (actual : string) : Tot bool =
  match expected with
  | None -> true
  | Some s -> s = actual

// Graph-cell match. The bound graph is `option cottas_graph_ref`:
//   - None : caller doesn't constrain the graph column. Match anything.
//   - Some i : caller wants that specific named graph. The row's
//     graph token is "DEFAULT" for default-graph rows, "<iri>" otherwise.
//     A "DEFAULT" row never matches a Some-graph bound; an "<iri>" row
//     matches iff string-equal to the bound's "<iri>" form.
let graph_cell_match (expected : option string) (actual : string)
  : Tot bool = cell_match expected actual

// ---- Row-group walk -------------------------------------------------

// Phase 2.7-mini Phase 2 (issue #118): id→raw-token lookup, mirror of
// the token→id assume-vals declared further below.
//
// Why: `id_to_raw_token` walks `h.coh_*_raw` assoc-lists which are
// EMPTY on Bet7-lazy-opened handles (Bet7 defers their construction).
// On Bet7 handles, `id_to_raw_token` falls through to a sentinel
// `"\x00cottas_decode_oor"` which never matches a real column-token,
// so the bound-query F* path silently degenerates: ALL row-groups
// become "candidates" (compute_candidate_rgs_loop's safe-fallback)
// and the executor walks them looking for matches that never come.
// Net symptom: every bound query on a Bet7 handle hits the 30s
// timeout (post-2.5e regression, masked through 7cf9ebc by stale
// binaries).
//
// The OCaml runtime carries this data in
// `Cottas_ondisk_runtime.fast_tables.ft_id_to_*_tok : (int, string)
// Hashtbl.t`, populated by `Cottas_ondisk_lazy.ensure_*_loaded`. These
// four assume-vals expose that lookup to the F* spec, just like
// Phase 1's `ondisk_lookup_*_id_global` did for the inverse direction.
assume val ondisk_id_to_subj_token_global :
  (path : string) -> (id : nat) -> Tot (option string)
assume val ondisk_id_to_pred_token_global :
  (path : string) -> (id : nat) -> Tot (option string)
assume val ondisk_id_to_obj_token_global :
  (path : string) -> (id : nat) -> Tot (option string)
assume val ondisk_id_to_graph_token_global :
  (path : string) -> (id : nat) -> Tot (option string)

// Bet7-aware mirror of `id_to_raw_token`. Used by cottas_ondisk_search
// / _estimate / _search_limited to translate the user-supplied
// `cottas_term_ref` (= nat id from cottas_ondisk_encode_*) to the raw
// column-token string the executor's `cell_match` will compare
// against. If the OCaml table doesn't have this id (definitively-empty
// query: the bound term isn't in the corpus) we return None and the
// caller short-circuits to an empty result.
let id_to_raw_token_via_global
  (lookup : string -> nat -> Tot (option string))
  (path : string)
  (id : option cottas_term_ref)
  : Tot (option string) =
  match id with
  | None -> None
  | Some i -> lookup path i

// Phase 2.7-mini (issue #118): token→id lookup for the search hot path.
//
// The F* spec layer says: "given the raw column-token string `tok`,
// return the term-id `i` such that `list_nth raws i = Some tok`, if
// it exists; else None". Operationally we MIGHT walk the
// `coh_*_raw_revmap` assoc-list (which is what `revmap_lookup` does),
// but on Bet7-lazy-opened handles those F*-side assoc-lists are EMPTY
// — Bet7 defers their construction to keep handle-open under 5 s for
// the parliament corpus. The OCaml runtime carries the data in
// `Cottas_ondisk_runtime.fast_tables.ft_*_tok_to_id` (Hashtbl<string,
// int>), populated lazily by `Cottas_ondisk_lazy.ensure_*_loaded` on
// first-touch.
//
// These four assume-vals are the F* boundary for that lazy lookup.
// Their realisation (cottas_token_lookup_runtime.sh) is a thin
// rule-#11(c) dispatch shim: ensure_loaded + Hashtbl.find_opt. The
// F* spec treats them as oracles. Without this 2.7-mini bridge,
// Phase 2.5e (retiring the OCaml `search_fast` dispatch shim in
// favour of the F*-extracted `cottas_ondisk_search` body) returns
// zero rows on Bet7-opened handles because `build_qp_row` can't
// resolve any token to an id.
//
// Soundness: the assume-val outcome must be observably equivalent to
// `revmap_lookup h.coh_*_raw_revmap tok` on a fully-populated handle.
// The OCaml realisation upholds this by populating the same data the
// F* revmap would have held, just in a different (Hashtbl) shape.
assume val ondisk_lookup_subj_id_global :
  (path : string) -> (token : string) -> Tot (option nat)
assume val ondisk_lookup_pred_id_global :
  (path : string) -> (token : string) -> Tot (option nat)
assume val ondisk_lookup_obj_id_global :
  (path : string) -> (token : string) -> Tot (option nat)
assume val ondisk_lookup_graph_id_global :
  (path : string) -> (token : string) -> Tot (option nat)

// Build the cottas_qp_row for a matched row. Look up each token's id
// via the OCaml-realised `ondisk_lookup_*_id_global` shim, which
// honours Bet7's lazy populate. Graph "DEFAULT" → cqpr_g = None.
let build_qp_row
  (h : cottas_ondisk_handle)
  (s_tok p_tok o_tok g_tok : string)
  : Tot cottas_qp_row =
  let s_id = ondisk_lookup_subj_id_global h.coh_path s_tok in
  let p_id = ondisk_lookup_pred_id_global h.coh_path p_tok in
  let o_id = ondisk_lookup_obj_id_global  h.coh_path o_tok in
  let g_id =
    if g_tok = "DEFAULT" then None
    else ondisk_lookup_graph_id_global h.coh_path g_tok in
  { cqpr_s = s_id; cqpr_p = p_id; cqpr_o = o_id; cqpr_g = g_id; }

// Phase 2.5b/c (issue #118): the seq-shape filter consumes
// `cottas_column` (extracts to OCaml `string option array`) and
// walks via O(1) indexed access. Page cache returns this shape
// post-2.5c. Same acc-rev convention; same bound_match semantics.
//
// Decreases on `n - i` over an indexed walk over the column array.
// F* totality accepts. Tail-recursive throughout.

// Choose the smaller of two nats. Defensive minimum across the four
// columns of a row group; well-formed parquet has them equal.
let nat_min (a b : nat) : Tot nat = if a <= b then a else b

let row_group_row_count (s_col p_col o_col g_col : cottas_column) : Tot nat =
  let n_s = cottas_column_length s_col in
  let n_p = cottas_column_length p_col in
  let n_o = cottas_column_length o_col in
  let n_g = cottas_column_length g_col in
  nat_min (nat_min n_s n_p) (nat_min n_o n_g)

let rec filter_zipped_rows_seq
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : cottas_column)
  (n : nat) (i : nat{i <= n})
  (acc_rev : list cottas_qp_row)
  : Tot (list cottas_qp_row) (decreases (n - i)) =
  if i = n then acc_rev
  else
    let acc_rev' =
      // Defensive bound checks: discharge cottas_column_get's
      // refinement without an extra invariant; well-formed parquet
      // has every column length >= row count.
      if i < cottas_column_length s_col &&
         i < cottas_column_length p_col &&
         i < cottas_column_length o_col &&
         i < cottas_column_length g_col
      then
        match cottas_column_get s_col i, cottas_column_get p_col i,
              cottas_column_get o_col i, cottas_column_get g_col i with
        | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
          if cell_match bound_s s_tok &&
             cell_match bound_p p_tok &&
             cell_match bound_o o_tok &&
             graph_cell_match bound_g g_tok
          then build_qp_row h s_tok p_tok o_tok g_tok :: acc_rev
          else acc_rev
        | _ -> acc_rev
      else acc_rev in
    filter_zipped_rows_seq h bound_s bound_p bound_o bound_g
      s_col p_col o_col g_col n (i + 1) acc_rev'

let rec count_zipped_rows_seq
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : cottas_column)
  (n : nat) (i : nat{i <= n})
  (acc : nat)
  : Tot nat (decreases (n - i)) =
  if i = n then acc
  else
    let acc' =
      if i < cottas_column_length s_col &&
         i < cottas_column_length p_col &&
         i < cottas_column_length o_col &&
         i < cottas_column_length g_col
      then
        match cottas_column_get s_col i, cottas_column_get p_col i,
              cottas_column_get o_col i, cottas_column_get g_col i with
        | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
          if cell_match bound_s s_tok &&
             cell_match bound_p p_tok &&
             cell_match bound_o o_tok &&
             graph_cell_match bound_g g_tok
          then acc + 1
          else acc
        | _ -> acc
      else acc in
    count_zipped_rows_seq bound_s bound_p bound_o bound_g
      s_col p_col o_col g_col n (i + 1) acc'

// Legacy list-shape filter retained for callers we haven't migrated
// yet (filter_zipped_rows_limited at the LIMIT-pushdown path). No
// in-tree callers as of 2.5c; will be deleted with that consolidation.
//
// Zip 4 column lists row-by-row. The OCaml runtime guarantees they
// have equal lengths; we still handle the misaligned case safely
// (truncates at the shortest list).
//
// `bound_*` are the raw-token bounds from `id_to_raw_token` etc.;
// None means "match any". Matching rows are appended to `acc_rev`
// (in reverse row order). Caller flips at the end.
//
// Recursion is over the subject column (which decreases by one cell
// per step); F*'s totality checker accepts that.
let rec filter_zipped_rows
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : list (option string))
  (acc_rev : list cottas_qp_row)
  : Tot (list cottas_qp_row) (decreases s_col) =
  match s_col, p_col, o_col, g_col with
  | s_hd :: s_tl, p_hd :: p_tl, o_hd :: o_tl, g_hd :: g_tl ->
    let acc_rev' =
      match s_hd, p_hd, o_hd, g_hd with
      | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
        if cell_match bound_s s_tok &&
           cell_match bound_p p_tok &&
           cell_match bound_o o_tok &&
           graph_cell_match bound_g g_tok
        then build_qp_row h s_tok p_tok o_tok g_tok :: acc_rev
        else acc_rev
      | _ -> acc_rev in
    filter_zipped_rows h bound_s bound_p bound_o bound_g
      s_tl p_tl o_tl g_tl acc_rev'
  | _ -> acc_rev

// Same as filter_zipped_rows but counts only — no per-row revmap lookup.
// Used by cottas_ondisk_estimate.
let rec count_zipped_rows
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : list (option string))
  (acc : nat)
  : Tot nat (decreases s_col) =
  match s_col, p_col, o_col, g_col with
  | s_hd :: s_tl, p_hd :: p_tl, o_hd :: o_tl, g_hd :: g_tl ->
    let acc' =
      match s_hd, p_hd, o_hd, g_hd with
      | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
        if cell_match bound_s s_tok &&
           cell_match bound_p p_tok &&
           cell_match bound_o o_tok &&
           graph_cell_match bound_g g_tok
        then acc + 1
        else acc
      | _ -> acc in
    count_zipped_rows bound_s bound_p bound_o bound_g
      s_tl p_tl o_tl g_tl acc'
  | _ -> acc

// Default page-cache capacity. Parliament's 26-row-group × 4-column
// surface = 104 entries; 128 gives headroom for slightly larger
// corpora without LRU thrash. For massive corpora the OCaml byte
// cache is the dominant accelerant; this F* cache is correctness-
// preserving across multi-pass walks (Phase D will need it).
let pcache_default_capacity : nat = 128

// Walk row groups [rg_index .. rg_count) in order, decoding each row
// group's 4 columns and accumulating matched rows into `acc_rev`
// (reverse row order). `fuel = rg_count - rg_index` makes termination
// trivial. Decoder errors on a row group are skipped (silently empty).
//
// The page cache is threaded through the recursion. Each row-group
// step decodes 4 columns; on cache miss the underlying decoder is
// invoked and the result inserted. On hit the decoded list comes
// straight from the cache.
// Phase 2.5c (issue #118): the page cache now stores `cottas_column`
// (extracts to `string option array`). The walk consumes the array
// shape directly via filter_zipped_rows_seq, eliminating the per-cell
// list cons cost.
let rec walk_row_groups_search
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list cottas_qp_row)
  (cache : page_cache)
  : Tot (list cottas_qp_row & page_cache) (decreases fuel) =
  if fuel = 0 then (acc_rev, cache)
  else if rg_index >= rg_count then (acc_rev, cache)
  else
    let cap = cache.pc_capacity in
    let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
    let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
    let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
    let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
    let acc_rev' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev
      | _ -> acc_rev in
    walk_row_groups_search h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc_rev' c4

// Phase 2.5c (issue #118): cache returns cottas_column; estimator
// uses count_zipped_rows_seq.
let rec walk_row_groups_estimate
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat) (acc : nat)
  (cache : page_cache)
  : Tot (nat & page_cache) (decreases fuel) =
  if fuel = 0 then (acc, cache)
  else if rg_index >= rg_count then (acc, cache)
  else
    let cap = cache.pc_capacity in
    let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
    let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
    let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
    let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
    let acc' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        count_zipped_rows_seq bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc
      | _ -> acc in
    walk_row_groups_estimate h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc' c4

// ----------------------------------------------------------------------
// Phase 2.5e (issue #118): global-cache walks. Same logic as
// `walk_row_groups_search` / `walk_row_groups_estimate` above but call
// the OCaml-realised `pcache_decode_in_row_group_global` — no cache
// threading. The cross-call cache state lives in OCaml (Cottas-side
// `pcache_global_ref`), so consecutive cottas_ondisk_search calls
// inherit warm-cache hits without burying a `page_cache` argument in
// every public-API caller.
//
// Used by `cottas_ondisk_search` and `cottas_ondisk_estimate` after
// 2.5e retires the OCaml runtime perf-shim.
// ----------------------------------------------------------------------

let rec walk_row_groups_search_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list cottas_qp_row)
  : Tot (list cottas_qp_row) (decreases fuel) =
  if fuel = 0 then acc_rev
  else if rg_index >= rg_count then acc_rev
  else
    let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
    let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
    let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
    let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
    let acc_rev' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev
      | _ -> acc_rev in
    walk_row_groups_search_global h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc_rev'

let rec walk_row_groups_estimate_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat) (acc : nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then acc
  else if rg_index >= rg_count then acc
  else
    let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
    let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
    let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
    let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
    let acc' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        count_zipped_rows_seq bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc
      | _ -> acc in
    walk_row_groups_estimate_global h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc'

// ----------------------------------------------------------------------
// Exact counting for RESULT-producing paths (found via the E1
// clustering experiment, 2026-07-03): cottas_ondisk_estimate's
// bounds-present branch is a deliberate approximation
// (candidate-row-groups x avg_rows_per_rg) for the join-order
// optimiser, but the streaming COUNT fast paths in SPARQL11.Store
// were consuming it as the query RESULT — GROUP BY ?g returned
// near-total row counts for every graph. The walks below are exact.

// Count rows in one graph column whose token matches bound_g.
// Column-3-only: the COUNT(*) GROUP BY ?g shape never needs s/p/o
// decoded, and the global page cache makes the per-named-graph
// re-walks hit already-decoded pages.
let rec count_graph_col_matches_seq
  (bound_g : option string) (g_col : cottas_column)
  (n : nat) (i : nat{i <= n}) (acc : nat)
  : Tot nat (decreases (n - i)) =
  if i = n then acc
  else
    let acc' =
      if i < cottas_column_length g_col then
        match cottas_column_get g_col i with
        | Some g_tok -> if graph_cell_match bound_g g_tok then acc + 1 else acc
        | None -> acc
      else acc in
    count_graph_col_matches_seq bound_g g_col n (i + 1) acc'

let rec walk_row_groups_count_graph_global
  (h : cottas_ondisk_handle) (bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat) (acc : nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then acc
  else if rg_index >= rg_count then acc
  else
    let acc' =
      match pcache_decode_in_row_group_global h.coh_path rg_index 3 with
      | Some gc ->
        count_graph_col_matches_seq bound_g gc (cottas_column_length gc) 0 acc
      | None -> acc in
    walk_row_groups_count_graph_global h bound_g
      (rg_index + 1) rg_count (fuel - 1) acc'

// ----------------------------------------------------------------------
// Phase 2.5b (issue #118): seq-shape variants of the hot-path walks.
//
// These mirror filter_zipped_rows / count_zipped_rows / walk_row_groups_*
// but consume `cottas_column` (an array under the OCaml realisation)
// instead of `list (option string)`. The change eliminates the O(N)
// per-row list-cell allocation that dominated cold-path time on
// parliament's 122,880-row row-groups; cell access is now O(1) via
// `cottas_column_get` (extracted to `Array.unsafe_get`).
//
// Tail-recursion: the seq variants thread an explicit row-index `i`
// alongside the count `n`. F* totality accepts `decreases (n - i)`.
// Same acc-rev convention as the list variants — caller flips at the
// end with `list_rev`.
//
// The list variants above are preserved for the candidate-rgs path
// (still using the page cache) and for the limited / aleph6 LIMIT
// pushdown path. Phase 2.5c will migrate those, which lets the page
// cache value type itself shift to `cottas_column`. Phase 2.5e
// retires the OCaml runtime perf-shim once the F* path is the
// runtime ground truth.
// ----------------------------------------------------------------------

// Phase 2.5c (issue #118): the standalone walk_row_groups_*_seq variants
// added in 2.5b have been folded into walk_row_groups_search /
// walk_row_groups_estimate (which now consume cottas_column from the
// page cache directly). The non-cached seq walks are no longer needed.

// ----------------------------------------------------------------------
// Tsade2 (issue #100 Phase D): per-row-group dictionary cache + column-
// prune query planner.
//
// For predicate-bound queries like `?s wdt:P31 :Human`, we want to walk
// only row groups whose predicate dictionary contains `wdt:P31` —
// skipping the (decoder-expensive) data pages of row groups that
// definitely don't contain the predicate.
//
// We use a per-query F* dict cache: `list ((rg_index, col_index) & list
// string)`. On first need for column C, we populate cache entries for all
// row groups of column C (one dict-page decompress per rg, cheap —
// ~26 entries × ~50KB total for parliament). Subsequent membership
// queries within the same column hit the cache.
//
// Per-query cache (re-built per call) — sufficient because each
// `cottas_ondisk_search` call invokes the planner once. A handle-attached
// cross-query cache would be a Phase E refinement.
// ----------------------------------------------------------------------

type dict_cache = list ((nat & nat) & list string)

let rec dict_cache_lookup (c : dict_cache) (rg : nat) (col : nat)
  : Tot (option (list string)) (decreases c) =
  match c with
  | [] -> None
  | ((r, k), v) :: rest ->
    if r = rg && k = col then Some v
    else dict_cache_lookup rest rg col

// Membership check on a dict list (linear scan). Dict lists are small
// (parliament: 231 distinct predicates total; per-rg subset typically
// smaller), so O(N) is fine.
let rec list_string_mem (xs : list string) (s : string)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | hd :: rest -> if hd = s then true else list_string_mem rest s

// Populate `dict_cache` for column `col_index` across row groups
// [rg_index .. rg_count). Each rg's dict is decoded via the new
// `probe_parquet_column_dictionary_in_row_group` helper. Failures
// (e.g. a column without a dict page) are stored as the empty list,
// which causes the candidate-rgs computation to TREAT THAT RG AS
// "may contain the term" — i.e. fall back to including it.
//
// To distinguish "dict absent" from "dict present and empty", we
// store dict-absent rgs with an absent-marker `["__no_dict__"]` —
// but actually a cleaner approach: skip insertion entirely on None
// (lookup returns None, planner falls back to "include this rg").
let rec populate_dict_cache_loop
  (c : dict_cache) (path : string) (col_index : nat)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  : Tot dict_cache (decreases fuel) =
  if fuel = 0 then c
  else if rg_index >= rg_count then c
  else
    let c' =
      match dict_cache_lookup c rg_index col_index with
      | Some _ -> c  // already populated
      | None ->
        match probe_parquet_column_dictionary_in_row_group path rg_index col_index with
        | None -> c  // no dict page — leave absent (planner falls back)
        | Some dict -> ((rg_index, col_index), dict) :: c in
    populate_dict_cache_loop c' path col_index (rg_index + 1) rg_count (fuel - 1)

let populate_dict_cache_for_column
  (c : dict_cache) (path : string) (col_index : nat) (rg_count : nat)
  : Tot dict_cache =
  populate_dict_cache_loop c path col_index 0 rg_count rg_count

// Compute the candidate row-groups for a column-bound. `bound_token` is
// the raw column-token string (e.g. "<https://id.parliament.uk/...>")
// the search is looking for. Returns (candidate_rgs_in_REVERSE_order,
// dict_cache).
//
// If a row group is absent from the dict cache (e.g. dict page missing,
// or column has no dict at all), we INCLUDE it in candidates — safe
// fallback that may cost a wasted data-page decode, never wrong answers.
let rec compute_candidate_rgs_loop
  (c : dict_cache) (col_index : nat) (bound_token : string)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list nat)
  : Tot (list nat) (decreases fuel) =
  if fuel = 0 then acc_rev
  else if rg_index >= rg_count then acc_rev
  else
    let acc_rev' =
      match dict_cache_lookup c rg_index col_index with
      | None -> rg_index :: acc_rev  // safe fallback: include
      | Some dict ->
        if list_string_mem dict bound_token then rg_index :: acc_rev
        else acc_rev in
    compute_candidate_rgs_loop c col_index bound_token
      (rg_index + 1) rg_count (fuel - 1) acc_rev'

// Returns candidates in row-group order (low to high).
let compute_candidate_rgs
  (c : dict_cache) (col_index : nat) (bound_token : string) (rg_count : nat)
  : Tot (list nat) =
  let rev_list = compute_candidate_rgs_loop c col_index bound_token
    0 rg_count rg_count [] in
  // list_rev is defined in Parquet.Footer (open above brings it in).
  list_rev rev_list

// Intersect two sorted-ascending nat lists. Used to combine
// per-column candidate sets when multiple bounds are present
// (e.g. both subject AND predicate bound).
let rec list_nat_intersect_sorted
  (xs ys : list nat) (acc_rev : list nat) (fuel : nat)
  : Tot (list nat) (decreases fuel) =
  if fuel = 0 then acc_rev
  else
    match xs, ys with
    | [], _ -> acc_rev
    | _, [] -> acc_rev
    | x :: xrest, y :: yrest ->
      if x = y then
        list_nat_intersect_sorted xrest yrest (x :: acc_rev) (fuel - 1)
      else if x < y then
        list_nat_intersect_sorted xrest ys acc_rev (fuel - 1)
      else
        list_nat_intersect_sorted xs yrest acc_rev (fuel - 1)

// Public intersect: takes two ascending-sorted lists and returns the
// ascending-sorted intersection.
let intersect_sorted_rg_lists (xs ys : list nat) : Tot (list nat) =
  let len_xs : nat = List.Tot.length xs in
  let len_ys : nat = List.Tot.length ys in
  let fuel : nat = len_xs + len_ys + 1 in
  let rev = list_nat_intersect_sorted xs ys [] fuel in
  list_rev rev

// ---- Pruned row-group walk -----------------------------------------

// Walk a SPECIFIC list of row-group indices (the candidate set),
// decoding all 4 columns per rg and filtering. Same semantics as
// `walk_row_groups_search` but driven by a candidate list rather
// than a contiguous [rg_index .. rg_count) range.
let rec walk_candidate_rgs_search
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat)
  (acc_rev : list cottas_qp_row)
  (cache : page_cache)
  : Tot (list cottas_qp_row & page_cache) (decreases candidates) =
  match candidates with
  | [] -> (acc_rev, cache)
  | rg_index :: rest ->
    let cap = cache.pc_capacity in
    let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
    let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
    let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
    let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
    let acc_rev' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev
      | _ -> acc_rev in
    walk_candidate_rgs_search h bound_s bound_p bound_o bound_g
      rest acc_rev' c4

let rec walk_candidate_rgs_estimate
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat) (acc : nat)
  (cache : page_cache)
  : Tot (nat & page_cache) (decreases candidates) =
  match candidates with
  | [] -> (acc, cache)
  | rg_index :: rest ->
    let cap = cache.pc_capacity in
    let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
    let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
    let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
    let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
    let acc' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        count_zipped_rows_seq bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc
      | _ -> acc in
    walk_candidate_rgs_estimate h bound_s bound_p bound_o bound_g
      rest acc' c4

// Phase 2.5e: candidate-rg walks using the global-cache decoder.
let rec walk_candidate_rgs_search_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat)
  (acc_rev : list cottas_qp_row)
  : Tot (list cottas_qp_row) (decreases candidates) =
  match candidates with
  | [] -> acc_rev
  | rg_index :: rest ->
    let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
    let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
    let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
    let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
    let acc_rev' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev
      | _ -> acc_rev in
    walk_candidate_rgs_search_global h bound_s bound_p bound_o bound_g
      rest acc_rev'

let rec walk_candidate_rgs_estimate_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat) (acc : nat)
  : Tot nat (decreases candidates) =
  match candidates with
  | [] -> acc
  | rg_index :: rest ->
    let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
    let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
    let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
    let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
    let acc' =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        count_zipped_rows_seq bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc
      | _ -> acc in
    walk_candidate_rgs_estimate_global h bound_s bound_p bound_o bound_g
      rest acc'

// ---- Candidate-set computation -------------------------------------

// Build the per-rg candidate set for one column-bound. col_index is the
// parquet column index (0=subject, 1=predicate, 2=object, 3=graph).
// Returns the (candidate_rgs_in_ascending_order, updated_dict_cache).
let candidates_for_one_bound
  (c : dict_cache) (path : string) (col_index : nat)
  (bound_token : string) (rg_count : nat)
  : Tot (list nat & dict_cache) =
  let c' = populate_dict_cache_for_column c path col_index rg_count in
  let cands = compute_candidate_rgs c' col_index bound_token rg_count in
  (cands, c')

// Generate the full ascending list [0 .. rg_count). Used as the
// candidate set when no column-bound is present (degenerates to a
// full walk, semantically equivalent to walk_row_groups_search).
let rec all_rgs_loop (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list nat)
  : Tot (list nat) (decreases fuel) =
  if fuel = 0 then acc_rev
  else if rg_index >= rg_count then acc_rev
  else all_rgs_loop (rg_index + 1) rg_count (fuel - 1) (rg_index :: acc_rev)

let all_rgs (rg_count : nat) : Tot (list nat) =
  list_rev (all_rgs_loop 0 rg_count rg_count [])

// Compose candidate sets for whichever bounds are present. Returns the
// final candidate-rg list (ascending) + updated dict cache.
//
// Semantics:
//   - No s/p/o bound → all_rgs (full walk).
//   - One bound → that column's candidates.
//   - Multiple bounds → intersection of their candidate sets.
//   - Graph bound (col 3) is ALSO usable for pruning; we include it.
let plan_candidate_rgs
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_count : nat)
  : Tot (list nat & dict_cache) =
  let path = h.coh_path in
  // Start with "all rgs" as the universal set; intersect each present
  // bound's candidate set into it. We track whether any bound has been
  // applied to avoid a wasted intersect when none were.
  let init : list nat & dict_cache & bool = (all_rgs rg_count, [], false) in
  let step (acc : list nat & dict_cache & bool) (col_index : nat)
           (bound : option string)
    : Tot (list nat & dict_cache & bool) =
    match bound with
    | None -> acc
    | Some tok ->
      let (cur, c, _started) = acc in
      let (cands, c') = candidates_for_one_bound c path col_index tok rg_count in
      let combined = intersect_sorted_rg_lists cur cands in
      (combined, c', true) in
  let st1 = step init  0 bound_s in
  let st2 = step st1   1 bound_p in
  let st3 = step st2   2 bound_o in
  let st4 = step st3   3 bound_g in
  let (final, c, _) = st4 in
  (final, c)

// Phase 2.6 (issue #118): compound (p, o) joint-presence prune.
//
// `plan_candidate_rgs` above intersects per-column dict-page candidate
// sets — strictly more selective than the per-RG presence bitmaps but
// still per-column. When BOTH bound_p and bound_o are present, the
// compound (p, o) bitmap (`<path>.po.presence`, written at corpus
// build time and read by `RDF.CottasStore.CompoundPresenceBitmap`)
// can rule out RGs that have BOTH tokens present individually but
// never as the same row. On the parliament corpus's Q03
// (`?o a wktLiteral`) this drops candidates from 2 RGs to 0.
//
// Implementation notes:
//
//   * Token→id is resolved via `ondisk_lookup_pred_id_global` /
//     `_obj_id_global` — the same Phase 2.7-mini boundary
//     `build_qp_row` uses, so the lookup honours Bet7's lazy populate.
//
//   * Companion file `<path>.po.presence` is opened per call. It is
//     small (kB-scale on parliament's 956k objects × 232 predicates
//     × 26 RGs) so the open cost is negligible vs the saved DLBA
//     decode of pruned RGs. Future: open at handle-open time and
//     cache via assume val.
//
//   * Either bound missing, or either lookup returning None, or the
//     companion file missing → return candidates unchanged
//     (sound over-include; the executor's filter-loop will catch the
//     rest).
let filter_candidates_by_compound_po
  (path : string)
  (candidates : list nat)
  (bound_p_str bound_o_str : option string)
  : Tot (list nat) =
  match bound_p_str, bound_o_str with
  | Some bp, Some bo ->
    let p_id = ondisk_lookup_pred_id_global path bp in
    let o_id = ondisk_lookup_obj_id_global  path bo in
    (match p_id, o_id with
     | Some _, Some _ ->
       let oh = CPO.open_compound (path ^ ".po.presence") in
       (match oh with
        | None -> candidates  // companion file missing → no opinion
        | Some _ ->
          List.Tot.filter
            (fun rg -> CPO.compound_rg_passes_pair oh rg p_id o_id)
            candidates)
     | _ -> candidates)
  | _ -> candidates

// ---- Public search / estimate --------------------------------------

// Phase 2.5e (issue #118): use the global-cache walks. Page cache state
// is now held in OCaml (`pcache_global_ref`); F* owns the search
// algorithm and the LRU semantics, OCaml provides the cross-call
// storage cell. Removes the rule-#11 violation where the OCaml runtime
// patch substituted this body with a dispatch to
// `Cottas_ondisk_runtime.search_fast`. Token→id resolution flows
// through `ondisk_lookup_*_id_global` (Phase 2.7-mini) which honours
// Bet7's lazy populate.
let cottas_ondisk_search
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot (list cottas_qp_row) =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token_via_global ondisk_id_to_subj_token_global  h.coh_path bound.cbqp_s in
  let bound_p = id_to_raw_token_via_global ondisk_id_to_pred_token_global  h.coh_path bound.cbqp_p in
  let bound_o = id_to_raw_token_via_global ondisk_id_to_obj_token_global   h.coh_path bound.cbqp_o in
  let bound_g = id_to_raw_token_via_global ondisk_id_to_graph_token_global h.coh_path bound.cbqp_g in
  match probe_parquet_row_group_count h.coh_path with
  | None -> []
  | Some rg_count ->
    // Phase D: column-prune planner. If any column-bound is present,
    // compute the candidate-rgs via per-rg dict probes; else full walk.
    let any_bound_present =
      Some? bound_s || Some? bound_p || Some? bound_o || Some? bound_g in
    if any_bound_present then
      let (candidates0, _dc) = plan_candidate_rgs h
        bound_s bound_p bound_o bound_g rg_count in
      // Phase 2.6: AND-compose with compound (p,o) bitmap when both bound.
      let candidates = filter_candidates_by_compound_po
        h.coh_path candidates0 bound_p bound_o in
      let acc_rev = walk_candidate_rgs_search_global h
        bound_s bound_p bound_o bound_g
        candidates [] in
      list_rev acc_rev
    else
      let acc_rev = walk_row_groups_search_global h
        bound_s bound_p bound_o bound_g
        0 rg_count rg_count [] in
      list_rev acc_rev

// ----------------------------------------------------------------------
// Aleph6 (issue #100, demo prep): LIMIT pushdown variants of the row-group
// walkers. They short-circuit once `acc_rev` accumulates `limit` matched
// rows, avoiding the rest-of-corpus walk for queries like
// `SELECT ?s ?o WHERE { ?s :pred ?o } LIMIT 5`.
//
// Semantically equivalent to taking the first `limit` rows of
// `cottas_ondisk_search`. The unlimited variants above stay for full-table
// callers (e.g. CONSTRUCT, materialised SELECT without LIMIT).
// ----------------------------------------------------------------------

// Phase 2.5c (issue #118): seq-shape LIMIT-pushdown filter. Same
// semantics as the list-shape filter_zipped_rows_limited but indexed
// over a cottas_column. Decreases on `n - i`.
let rec filter_zipped_rows_limited_seq
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : cottas_column)
  (n : nat) (i : nat{i <= n})
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  : Tot (list cottas_qp_row & nat & bool) (decreases (n - i)) =
  if acc_count >= limit then (acc_rev, acc_count, true)
  else if i = n then (acc_rev, acc_count, acc_count >= limit)
  else
    let (acc_rev', acc_count') =
      if i < cottas_column_length s_col &&
         i < cottas_column_length p_col &&
         i < cottas_column_length o_col &&
         i < cottas_column_length g_col
      then
        match cottas_column_get s_col i, cottas_column_get p_col i,
              cottas_column_get o_col i, cottas_column_get g_col i with
        | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
          if cell_match bound_s s_tok &&
             cell_match bound_p p_tok &&
             cell_match bound_o o_tok &&
             graph_cell_match bound_g g_tok
          then (build_qp_row h s_tok p_tok o_tok g_tok :: acc_rev,
                acc_count + 1)
          else (acc_rev, acc_count)
        | _ -> (acc_rev, acc_count)
      else (acc_rev, acc_count) in
    filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
      s_col p_col o_col g_col n (i + 1) acc_rev' acc_count' limit

// Legacy list-shape (no in-tree callers post-2.5c; kept for compat).
// Filter a single row-group's zipped columns, stopping when `acc_rev`
// reaches `limit`. Returns (acc_rev, hit_limit).
let rec filter_zipped_rows_limited
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (s_col p_col o_col g_col : list (option string))
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  : Tot (list cottas_qp_row & nat & bool) (decreases s_col) =
  if acc_count >= limit then (acc_rev, acc_count, true)
  else
    match s_col, p_col, o_col, g_col with
    | s_hd :: s_tl, p_hd :: p_tl, o_hd :: o_tl, g_hd :: g_tl ->
      let (acc_rev', acc_count') =
        match s_hd, p_hd, o_hd, g_hd with
        | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
          if cell_match bound_s s_tok &&
             cell_match bound_p p_tok &&
             cell_match bound_o o_tok &&
             graph_cell_match bound_g g_tok
          then (build_qp_row h s_tok p_tok o_tok g_tok :: acc_rev,
                acc_count + 1)
          else (acc_rev, acc_count)
        | _ -> (acc_rev, acc_count) in
      filter_zipped_rows_limited h bound_s bound_p bound_o bound_g
        s_tl p_tl o_tl g_tl acc_rev' acc_count' limit
    | _ -> (acc_rev, acc_count, acc_count >= limit)

let rec walk_row_groups_search_limited
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  (cache : page_cache)
  : Tot (list cottas_qp_row & page_cache) (decreases fuel) =
  if fuel = 0 then (acc_rev, cache)
  else if rg_index >= rg_count then (acc_rev, cache)
  else if acc_count >= limit then (acc_rev, cache)
  else
    let cap = cache.pc_capacity in
    let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
    let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
    let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
    let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
    let (acc_rev', acc_count', hit) =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev acc_count limit
      | _ -> (acc_rev, acc_count, false) in
    if hit then (acc_rev', c4)
    else
      walk_row_groups_search_limited h bound_s bound_p bound_o bound_g
        (rg_index + 1) rg_count (fuel - 1) acc_rev' acc_count' limit c4

let rec walk_candidate_rgs_search_limited
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat)
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  (cache : page_cache)
  : Tot (list cottas_qp_row & page_cache) (decreases candidates) =
  if acc_count >= limit then (acc_rev, cache)
  else
    match candidates with
    | [] -> (acc_rev, cache)
    | rg_index :: rest ->
      let cap = cache.pc_capacity in
      let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
      let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
      let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
      let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
      let (acc_rev', acc_count', hit) =
        match s_col, p_col, o_col, g_col with
        | Some sc, Some pc, Some oc, Some gc ->
          let n = row_group_row_count sc pc oc gc in
          filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
            sc pc oc gc n 0 acc_rev acc_count limit
        | _ -> (acc_rev, acc_count, false) in
      if hit then (acc_rev', c4)
      else
        walk_candidate_rgs_search_limited h bound_s bound_p bound_o bound_g
          rest acc_rev' acc_count' limit c4

// Phase 2.5e: global-cache LIMIT walks. Same shape as
// walk_*_search_limited but no threaded cache; uses
// `pcache_decode_in_row_group_global`.

let rec walk_row_groups_search_limited_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (rg_index : nat) (rg_count : nat) (fuel : nat)
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  : Tot (list cottas_qp_row) (decreases fuel) =
  if fuel = 0 then acc_rev
  else if rg_index >= rg_count then acc_rev
  else if acc_count >= limit then acc_rev
  else
    let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
    let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
    let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
    let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
    let (acc_rev', acc_count', hit) =
      match s_col, p_col, o_col, g_col with
      | Some sc, Some pc, Some oc, Some gc ->
        let n = row_group_row_count sc pc oc gc in
        filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
          sc pc oc gc n 0 acc_rev acc_count limit
      | _ -> (acc_rev, acc_count, false) in
    if hit then acc_rev'
    else
      walk_row_groups_search_limited_global h bound_s bound_p bound_o bound_g
        (rg_index + 1) rg_count (fuel - 1) acc_rev' acc_count' limit

let rec walk_candidate_rgs_search_limited_global
  (h : cottas_ondisk_handle)
  (bound_s bound_p bound_o bound_g : option string)
  (candidates : list nat)
  (acc_rev : list cottas_qp_row) (acc_count : nat) (limit : nat)
  : Tot (list cottas_qp_row) (decreases candidates) =
  if acc_count >= limit then acc_rev
  else
    match candidates with
    | [] -> acc_rev
    | rg_index :: rest ->
      let s_col = pcache_decode_in_row_group_global h.coh_path rg_index 0 in
      let p_col = pcache_decode_in_row_group_global h.coh_path rg_index 1 in
      let o_col = pcache_decode_in_row_group_global h.coh_path rg_index 2 in
      let g_col = pcache_decode_in_row_group_global h.coh_path rg_index 3 in
      let (acc_rev', acc_count', hit) =
        match s_col, p_col, o_col, g_col with
        | Some sc, Some pc, Some oc, Some gc ->
          let n = row_group_row_count sc pc oc gc in
          filter_zipped_rows_limited_seq h bound_s bound_p bound_o bound_g
            sc pc oc gc n 0 acc_rev acc_count limit
        | _ -> (acc_rev, acc_count, false) in
      if hit then acc_rev'
      else
        walk_candidate_rgs_search_limited_global h bound_s bound_p bound_o bound_g
          rest acc_rev' acc_count' limit

// LIMIT-pushdown public entry: same as `cottas_ondisk_search` but stops
// once `limit` matching rows have been accumulated. Returns at most
// `limit` rows.
//
// Phase 2.5e: global-cache walks. F* owns the algorithm.
let cottas_ondisk_search_limited
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp) (limit : nat)
  : Tot (list cottas_qp_row) =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token_via_global ondisk_id_to_subj_token_global  h.coh_path bound.cbqp_s in
  let bound_p = id_to_raw_token_via_global ondisk_id_to_pred_token_global  h.coh_path bound.cbqp_p in
  let bound_o = id_to_raw_token_via_global ondisk_id_to_obj_token_global   h.coh_path bound.cbqp_o in
  let bound_g = id_to_raw_token_via_global ondisk_id_to_graph_token_global h.coh_path bound.cbqp_g in
  match probe_parquet_row_group_count h.coh_path with
  | None -> []
  | Some rg_count ->
    let any_bound_present =
      Some? bound_s || Some? bound_p || Some? bound_o || Some? bound_g in
    if any_bound_present then
      let (candidates0, _dc) = plan_candidate_rgs h
        bound_s bound_p bound_o bound_g rg_count in
      // Phase 2.6: compound (p,o) prune.
      let candidates = filter_candidates_by_compound_po
        h.coh_path candidates0 bound_p bound_o in
      let acc_rev = walk_candidate_rgs_search_limited_global h
        bound_s bound_p bound_o bound_g
        candidates [] 0 limit in
      list_rev acc_rev
    else
      let acc_rev = walk_row_groups_search_limited_global h
        bound_s bound_p bound_o bound_g
        0 rg_count rg_count [] 0 limit in
      list_rev acc_rev

let cottas_ondisk_estimate
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot nat =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token_via_global ondisk_id_to_subj_token_global  h.coh_path bound.cbqp_s in
  let bound_p = id_to_raw_token_via_global ondisk_id_to_pred_token_global  h.coh_path bound.cbqp_p in
  let bound_o = id_to_raw_token_via_global ondisk_id_to_obj_token_global   h.coh_path bound.cbqp_o in
  let bound_g = id_to_raw_token_via_global ondisk_id_to_graph_token_global h.coh_path bound.cbqp_g in
  let any_bound_present =
    Some? bound_s || Some? bound_p || Some? bound_o || Some? bound_g in
  if not any_bound_present then
    // Aleph6 (issue #100, demo prep): unbound COUNT(*) fast path.
    // The total row count is encoded in the parquet metadata's
    // FileMetaData.num_rows field; reading it doesn't require decoding
    // any data pages. For parliament's 3.1M-row corpus this is
    // microseconds vs minutes for the per-row-group walk.
    //
    // Bounds-present queries still walk row groups: the bound determines
    // which rows match, and the parquet metadata's per-rg row counts
    // don't tell us that.
    (match probe_parquet_num_rows h.coh_path with
     | Some n -> n
     | None ->
       // Fallback: shouldn't reach here for well-formed parquet files.
       // If the metadata read fails, do a row-group walk to be safe.
       (match probe_parquet_row_group_count h.coh_path with
        | None -> 0
        | Some rg_count ->
          // Phase 2.5e: global-cache walk; F* owns algorithm, OCaml
          // provides cross-call cache cell.
          walk_row_groups_estimate_global h
            bound_s bound_p bound_o bound_g
            0 rg_count rg_count 0))
  else
    // Mem5 (issue #100, demo prep): presence-bitmap fast path for the
    // BGP join-order optimiser. Compute candidate row-groups from the
    // per-rg dictionary pages (cheap — `plan_candidate_rgs` reads only
    // dict pages, never decodes data pages). Then approximate the
    // estimate as `length(candidates) * avg_rows_per_rg`, where
    // avg_rows_per_rg is read from the parquet footer (no I/O cost).
    //
    // This is an APPROXIMATION — the true count requires data-page
    // decode and the slow filter walk that this used to do. The
    // optimiser only needs ordinal cardinality (off-by-2x is fine,
    // off-by-100x wastes plan budget but doesn't change results), so
    // the approximation is acceptable. Empty candidates correctly
    // returns 0 (early-out for definitively-empty patterns). For the
    // exact count, callers should issue an actual COUNT(*) query.
    //
    // Replaces the previous walk_candidate_rgs_estimate path which
    // decoded all 4 columns of every candidate rg and counted matching
    // rows — minutes for a 3.1M-row corpus, microseconds with this.
    match probe_parquet_row_group_count h.coh_path with
    | None -> 0
    | Some rg_count ->
      let (candidates0, _dc) = plan_candidate_rgs h
        bound_s bound_p bound_o bound_g rg_count in
      // Phase 2.6: compound (p,o) prune for the estimator too.
      let candidates = filter_candidates_by_compound_po
        h.coh_path candidates0 bound_p bound_o in
      let n_candidates : nat = List.Tot.length candidates in
      if n_candidates = 0 then 0
      else if rg_count = 0 then 0
      else
        (match probe_parquet_num_rows h.coh_path with
         | None -> n_candidates  // fallback: at least 1 row per candidate rg
         | Some total_rows ->
           // avg_rows_per_rg = total_rows / rg_count (truncating).
           // estimate = n_candidates * avg_rows_per_rg.
           let avg : nat = total_rows / rg_count in
           // Clamp for the F* subtyping checker: `nat * nat = int` in
           // Prims, so an explicit non-negative check is needed to
           // give the function its declared `Tot nat` return type.
           let prod : int = n_candidates `op_Multiply` avg in
           if prod < 0 then 0 else prod)

// EXACT count — for result-producing callers (the streaming COUNT
// fast paths in SPARQL11.Store). Contract difference from
// cottas_ondisk_estimate: never approximates. Unbound: parquet
// num_rows metadata (exact, free). Graph-only bound: single-column
// walk over the g column (page-cache-amortised across graphs).
// General bounds: the full zipped row-group walk.
let cottas_ondisk_count_exact
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot nat =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token_via_global ondisk_id_to_subj_token_global  h.coh_path bound.cbqp_s in
  let bound_p = id_to_raw_token_via_global ondisk_id_to_pred_token_global  h.coh_path bound.cbqp_p in
  let bound_o = id_to_raw_token_via_global ondisk_id_to_obj_token_global   h.coh_path bound.cbqp_o in
  let bound_g = id_to_raw_token_via_global ondisk_id_to_graph_token_global h.coh_path bound.cbqp_g in
  if None? bound_s && None? bound_p && None? bound_o && None? bound_g then
    (match probe_parquet_num_rows h.coh_path with
     | Some n -> n
     | None ->
       (match probe_parquet_row_group_count h.coh_path with
        | None -> 0
        | Some rg_count ->
          walk_row_groups_estimate_global h
            bound_s bound_p bound_o bound_g 0 rg_count rg_count 0))
  else
    (match probe_parquet_row_group_count h.coh_path with
     | None -> 0
     | Some rg_count ->
       if None? bound_s && None? bound_p && None? bound_o then
         walk_row_groups_count_graph_global h bound_g 0 rg_count rg_count 0
       else
         walk_row_groups_estimate_global h
           bound_s bound_p bound_o bound_g 0 rg_count rg_count 0)

// ----------------------------------------------------------------------
// Bound-pattern + row-to-quad helpers (moved from Parser.BallyhooCOTTAS).
// These compose the encode/decode primitives and are pure F*.
// ----------------------------------------------------------------------

// Build a bound query-pattern from a triple-pattern + a graph-IRI bound.
// Returns None when any bound term is absent from the dictionary,
// meaning a definitively empty result.
let cottas_ondisk_build_bound_qp_opt
  (ds : cottas_ondisk_store)
  (s : option subject) (p : option wf_iri) (o : option rdf_term) (g : option iri)
  : option cottas_bound_qp =
  let s' = match s with | None -> Some None | Some sv -> (match cottas_ondisk_encode_subject ds sv with | None -> None | Some r -> Some (Some r)) in
  let p' = match p with | None -> Some None | Some pv -> (match cottas_ondisk_encode_predicate ds pv with | None -> None | Some r -> Some (Some r)) in
  let o' = match o with | None -> Some None | Some ov -> (match cottas_ondisk_encode_object ds ov with | None -> None | Some r -> Some (Some r)) in
  let g' = match g with | None -> Some None | Some gv -> (match cottas_ondisk_encode_graph_name ds gv with | None -> None | Some r -> Some (Some r)) in
  match s', p', o', g' with
  | Some sb, Some pb, Some ob, Some gb ->
    Some { cbqp_s = sb; cbqp_p = pb; cbqp_o = ob; cbqp_g = gb }
  | _ -> None

// Convert an on-disk term-id row to a parsed (triple & option iri).
let cottas_ondisk_row_to_quad (ds : cottas_ondisk_store) (row : cottas_qp_row)
  : option (triple & option iri) =
  match row.cqpr_s, row.cqpr_p, row.cqpr_o with
  | Some sr, Some pr, Some orf ->
    Some
      ({
        s = cottas_ondisk_decode_subject ds sr;
        p = cottas_ondisk_decode_predicate ds pr;
        o = cottas_ondisk_decode_object ds orf;
      },
       (match row.cqpr_g with
        | None -> None
        | Some gr -> Some (cottas_ondisk_decode_graph_name ds gr)))
  | _ -> None

// Tail-recursive accumulator companion. The original
// `cottas_ondisk_rows_to_quads` was non-tail-rec (recurses BEFORE consing
// the result). On a 3.14M-row result this overflowed the macOS main-thread
// stack the same way Tav5's `json_rows_body` did (commit 4ff2321).
// Pattern mirrors `json_rows_body_acc` / `xml_rows_body_acc` /
// `csv_rows_body_acc` in `SPARQL.Protocol.fst`.
let rec cottas_ondisk_rows_to_quads_acc
    (ds : cottas_ondisk_store)
    (rows : list cottas_qp_row)
    (acc : list (triple & option iri))
  : Tot (list (triple & option iri)) (decreases rows) =
  match rows with
  | [] -> acc
  | row :: rest ->
    (match cottas_ondisk_row_to_quad ds row with
     | None      -> cottas_ondisk_rows_to_quads_acc ds rest acc
     | Some quad -> cottas_ondisk_rows_to_quads_acc ds rest (quad :: acc))

let cottas_ondisk_rows_to_quads (ds : cottas_ondisk_store) (rows : list cottas_qp_row)
  : Tot (list (triple & option iri)) =
  List.Tot.rev (cottas_ondisk_rows_to_quads_acc ds rows [])

// Fused tail-rec walk: rows -> triples (drops the graph-name component).
// Avoids the non-tail-rec `List.Tot.map fst (cottas_ondisk_rows_to_quads
// ...)` pattern on 3M-row results, which would re-walk the list and blow
// the stack again. Sin7 fix (2026-04-26).
let rec cottas_ondisk_rows_to_triples_acc
    (ds : cottas_ondisk_store)
    (rows : list cottas_qp_row)
    (acc : list triple)
  : Tot (list triple) (decreases rows) =
  match rows with
  | [] -> acc
  | row :: rest ->
    (match cottas_ondisk_row_to_quad ds row with
     | None              -> cottas_ondisk_rows_to_triples_acc ds rest acc
     | Some (t, _gname)  -> cottas_ondisk_rows_to_triples_acc ds rest (t :: acc))

let cottas_ondisk_rows_to_triples (ds : cottas_ondisk_store) (rows : list cottas_qp_row)
  : Tot (list triple) =
  List.Tot.rev (cottas_ondisk_rows_to_triples_acc ds rows [])
