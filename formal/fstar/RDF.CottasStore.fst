module RDF.CottasStore

open RDF.Graph.Executable
open Parser.BallyhooCOTTAS

// On-disk COTTAS store, query-time interface (issue #100 Phase A).
//
// History: this module's contents used to live at the bottom of
// Parser.BallyhooCOTTAS.fst, with 13 `assume val`s whose bodies lived in
// experimental_ocaml_glue/cottas_ondisk_runtime.sh (688 LoC OCaml). Per
// CLAUDE.md rules #1 / #7 / #15 + memory feedback_fstar_first_always.md,
// 11 of those 13 functions are now real F* `Tot` definitions over an
// enriched `cottas_ondisk_handle` record. The remaining 2 (`_open`,
// search/estimate) stay `assume val` — Phase B / C will lift them as the
// search loop / mmap design crystallises.
//
// All semantic logic (encode/decode/predicate-presence/named-graph walk)
// lives here. The OCaml glue at cottas_ondisk_runtime.sh now does only
// one thing: at open() time, read 4 columns from the Parquet file, parse
// each distinct token to its RDF shape, build the reverse maps, and
// hand the F* runtime a populated `cottas_ondisk_handle` record. F* does
// the rest.

// `columns_handle` is the per-row int-array bundle that the I/O glue
// builds at open() time. Search / estimate (Phase B scope) walk these
// arrays in tight loops; F* doesn't yet need to see inside.
assume type columns_handle

noeq type cottas_ondisk_handle = {
  // Path the handle came from (debugging / re-open coalescing).
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
  // The per-row int-array bundle (subject/predicate/object/graph
  // term-id columns + lengths). Owned by the I/O glue; F* search /
  // estimate dispatch through it via `assume val`. Phase B will
  // replace this with a typed F*-side iterator.
  coh_columns : columns_handle;
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
// Remaining 2 assume vals — Phase B / C scope.
// ----------------------------------------------------------------------

// Open: I/O. Parses the Parquet file, decodes 4 columns, builds the
// `cottas_ondisk_handle` record (parsed-term lists + reverse maps +
// columns_handle). Phase C will refactor with mmap.
assume val cottas_ondisk_open :
  artifact_path:string -> Tot (option cottas_ondisk_store)

// Close: I/O. Releases the columns_handle; F* runtime hashtables drop
// via GC. Currently not extracted (no use site in F*).
assume val cottas_ondisk_close :
  cottas_ondisk_store -> Tot unit

// Search: walks the per-row int-array columns inside columns_handle,
// comparing each row to the bound term-ids. Stays I/O-glue for Phase A
// because Phase B will redesign this with row-group iteration / page
// streaming and the API shape will shift.
assume val cottas_ondisk_search :
  cottas_ondisk_store -> cottas_bound_qp -> Tot (list cottas_qp_row)

assume val cottas_ondisk_estimate :
  cottas_ondisk_store -> cottas_bound_qp -> Tot nat

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
