module RDF.CottasStore

open RDF.Graph.Executable
open Parser.BallyhooCOTTAS
open Parquet.Footer
open RDF.CottasStore.PageCache

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
    // rdf:type as the stable out-of-range fallback wf_iri.
    let fallback : iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
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

// Build the cottas_qp_row for a matched row. Look up each token's id
// from the raw-token revmap. Graph "DEFAULT" → cqpr_g = None.
let build_qp_row
  (h : cottas_ondisk_handle)
  (s_tok p_tok o_tok g_tok : string)
  : Tot cottas_qp_row =
  let s_id = revmap_lookup h.coh_subj_raw_revmap  s_tok in
  let p_id = revmap_lookup h.coh_pred_raw_revmap  p_tok in
  let o_id = revmap_lookup h.coh_obj_raw_revmap   o_tok in
  let g_id =
    if g_tok = "DEFAULT" then None
    else revmap_lookup h.coh_graph_raw_revmap g_tok in
  { cqpr_s = s_id; cqpr_p = p_id; cqpr_o = o_id; cqpr_g = g_id; }

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
        filter_zipped_rows h bound_s bound_p bound_o bound_g
          sc pc oc gc acc_rev
      | _ -> acc_rev in
    walk_row_groups_search h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc_rev' c4

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
        count_zipped_rows bound_s bound_p bound_o bound_g
          sc pc oc gc acc
      | _ -> acc in
    walk_row_groups_estimate h bound_s bound_p bound_o bound_g
      (rg_index + 1) rg_count (fuel - 1) acc' c4

// ---- Public search / estimate --------------------------------------

let cottas_ondisk_search
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot (list cottas_qp_row) =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token h.coh_subjects_raw   bound.cbqp_s in
  let bound_p = id_to_raw_token h.coh_predicates_raw bound.cbqp_p in
  let bound_o = id_to_raw_token h.coh_objects_raw    bound.cbqp_o in
  let bound_g = id_to_raw_token h.coh_graphs_raw     bound.cbqp_g in
  match probe_parquet_row_group_count h.coh_path with
  | None -> []
  | Some rg_count ->
    let cache0 = pcache_empty pcache_default_capacity in
    let (acc_rev, _cache') = walk_row_groups_search h
      bound_s bound_p bound_o bound_g
      0 rg_count rg_count [] cache0 in
    list_rev acc_rev

let cottas_ondisk_estimate
  (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot nat =
  let h = ds.cods_handle in
  let bound_s = id_to_raw_token h.coh_subjects_raw   bound.cbqp_s in
  let bound_p = id_to_raw_token h.coh_predicates_raw bound.cbqp_p in
  let bound_o = id_to_raw_token h.coh_objects_raw    bound.cbqp_o in
  let bound_g = id_to_raw_token h.coh_graphs_raw     bound.cbqp_g in
  match probe_parquet_row_group_count h.coh_path with
  | None -> 0
  | Some rg_count ->
    let cache0 = pcache_empty pcache_default_capacity in
    let (count, _cache') = walk_row_groups_estimate h
      bound_s bound_p bound_o bound_g
      0 rg_count rg_count 0 cache0 in
    count

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

let rec cottas_ondisk_rows_to_quads (ds : cottas_ondisk_store) (rows : list cottas_qp_row)
  : Tot (list (triple & option iri)) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = cottas_ondisk_rows_to_quads ds rest in
    match cottas_ondisk_row_to_quad ds row with
    | Some q -> q :: rest'
    | None -> rest'
