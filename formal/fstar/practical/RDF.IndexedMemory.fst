module RDF.IndexedMemory

// Bucket: PRAGMATIC IMPLEMENTATION.
//
// Draft default in-memory RDF graph backend. The core spec keeps graphs as
// mathematical collections; this module gives the executable/query side a
// concrete indexed representation without making that representation part of
// RDF's abstract syntax.

open FStar.List.Tot
open RDF.CoreSpec

type graph_list = list triple
type term_id = nat

noeq type triple_pattern_bound = {
  bs : option subject;
  bp : option predicate;
  bo : option term;
}

noeq type term_binding = {
  tb_id : term_id;
  tb_term : term;
}

noeq type encoded_triple = {
  et_s : term_id;
  et_p : term_id;
  et_o : term_id;
  et_triple : triple;
}

noeq type index_bucket = {
  ib_key : term_id;
  ib_rows : list encoded_triple;
}

noeq type indexed_graph_store = {
  ig_terms : list term_binding;
  ig_rows : list encoded_triple;
  ig_spo : list index_bucket;
  ig_pos : list index_bucket;
  ig_osp : list index_bucket;
  ig_size : nat;
}

let empty_indexed_graph_store : indexed_graph_store =
  {
    ig_terms = [];
    ig_rows = [];
    ig_spo = [];
    ig_pos = [];
    ig_osp = [];
    ig_size = 0;
  }

let subject_as_term (s : subject) : term =
  match s with
  | SubjectIRI i -> IRI i
  | SubjectBlank b -> Blank b

let predicate_as_term (p : predicate) : term =
  IRI p

let term_eq (a b : term) : bool = a = b
let subject_eq (a b : subject) : bool = a = b
let triple_eq (a b : triple) : bool = a = b

let rec lookup_term_id (t : term) (terms : list term_binding)
  : Tot (option term_id) (decreases terms) =
  match terms with
  | [] -> None
  | hd :: rest ->
    if term_eq hd.tb_term t then Some hd.tb_id else lookup_term_id t rest

let intern_term (t : term) (terms : list term_binding)
  : term_id * list term_binding =
  match lookup_term_id t terms with
  | Some id -> (id, terms)
  | None ->
    let id = List.Tot.length terms in
    (id, terms @ [{ tb_id = id; tb_term = t }])

let encode_triple (t : triple) (terms : list term_binding)
  : encoded_triple * list term_binding =
  let sid, terms1 = intern_term (subject_as_term t.s) terms in
  let pid, terms2 = intern_term (predicate_as_term t.p) terms1 in
  let oid, terms3 = intern_term t.o terms2 in
  ({ et_s = sid; et_p = pid; et_o = oid; et_triple = t }, terms3)

let rec mem_triple (needle : triple) (g : graph_list)
  : Tot bool (decreases g) =
  match g with
  | [] -> false
  | hd :: rest -> triple_eq needle hd || mem_triple needle rest

let rec add_to_bucket (key : term_id) (row : encoded_triple) (buckets : list index_bucket)
  : Tot (list index_bucket) (decreases buckets) =
  match buckets with
  | [] -> [{ ib_key = key; ib_rows = [row] }]
  | hd :: rest ->
    if hd.ib_key = key
    then { ib_key = hd.ib_key; ib_rows = row :: hd.ib_rows } :: rest
    else hd :: add_to_bucket key row rest

let add_row_to_indexes
  (row : encoded_triple)
  (spo : list index_bucket)
  (pos : list index_bucket)
  (osp : list index_bucket)
  : list index_bucket * list index_bucket * list index_bucket =
  (
    add_to_bucket row.et_s row spo,
    add_to_bucket row.et_p row pos,
    add_to_bucket row.et_o row osp
  )

let rec lookup_bucket (key : term_id) (buckets : list index_bucket)
  : Tot (list encoded_triple) (decreases buckets) =
  match buckets with
  | [] -> []
  | hd :: rest ->
    if hd.ib_key = key then hd.ib_rows else lookup_bucket key rest

let option_id_matches (wanted : option term_id) (actual : term_id) : bool =
  match wanted with
  | None -> true
  | Some id -> id = actual

let row_matches_bound_ids
  (sid : option term_id) (pid : option term_id) (oid : option term_id)
  (row : encoded_triple)
  : bool =
  option_id_matches sid row.et_s &&
  option_id_matches pid row.et_p &&
  option_id_matches oid row.et_o

let rec filter_rows_by_ids
  (sid : option term_id) (pid : option term_id) (oid : option term_id)
  (rows : list encoded_triple)
  : Tot (list encoded_triple) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rest' = filter_rows_by_ids sid pid oid rest in
    if row_matches_bound_ids sid pid oid row then row :: rest' else rest'

let bound_subject_id (b : triple_pattern_bound) (terms : list term_binding)
  : option term_id =
  match b.bs with
  | None -> None
  | Some s -> lookup_term_id (subject_as_term s) terms

let bound_predicate_id (b : triple_pattern_bound) (terms : list term_binding)
  : option term_id =
  match b.bp with
  | None -> None
  | Some p -> lookup_term_id (predicate_as_term p) terms

let bound_object_id (b : triple_pattern_bound) (terms : list term_binding)
  : option term_id =
  match b.bo with
  | None -> None
  | Some o -> lookup_term_id o terms

let requested_missing (requested : bool) (id : option term_id) : bool =
  requested && (match id with | None -> true | Some _ -> false)

let requested_subject (b : triple_pattern_bound) : bool =
  match b.bs with | None -> false | Some _ -> true

let requested_predicate (b : triple_pattern_bound) : bool =
  match b.bp with | None -> false | Some _ -> true

let requested_object (b : triple_pattern_bound) : bool =
  match b.bo with | None -> false | Some _ -> true

let row_candidates
  (igs : indexed_graph_store)
  (sid : option term_id) (pid : option term_id) (oid : option term_id)
  : list encoded_triple =
  match sid, pid, oid with
  | Some s, _, _ -> lookup_bucket s igs.ig_spo
  | None, Some p, _ -> lookup_bucket p igs.ig_pos
  | None, None, Some o -> lookup_bucket o igs.ig_osp
  | None, None, None -> igs.ig_rows

let indexed_search (igs : indexed_graph_store) (b : triple_pattern_bound)
  : list triple =
  let sid = bound_subject_id b igs.ig_terms in
  let pid = bound_predicate_id b igs.ig_terms in
  let oid = bound_object_id b igs.ig_terms in
  if requested_missing (requested_subject b) sid ||
     requested_missing (requested_predicate b) pid ||
     requested_missing (requested_object b) oid
  then []
  else
    let candidates = row_candidates igs sid pid oid in
    List.Tot.map
      (fun row -> row.et_triple)
      (filter_rows_by_ids sid pid oid candidates)

let indexed_estimate (igs : indexed_graph_store) (b : triple_pattern_bound) : nat =
  List.Tot.length (indexed_search igs b)

let indexed_predicate_present (igs : indexed_graph_store) (pred : predicate) : bool =
  match lookup_term_id (predicate_as_term pred) igs.ig_terms with
  | None -> false
  | Some pid ->
    match lookup_bucket pid igs.ig_pos with
    | [] -> false
    | _ -> true

let rec build_indexed_graph_store_acc
  (remaining : graph_list)
  (seen : graph_list)
  (terms : list term_binding)
  (rows : list encoded_triple)
  (spo : list index_bucket)
  (pos : list index_bucket)
  (osp : list index_bucket)
  : Tot indexed_graph_store (decreases remaining) =
  match remaining with
  | [] ->
    {
      ig_terms = terms;
      ig_rows = rows;
      ig_spo = spo;
      ig_pos = pos;
      ig_osp = osp;
      ig_size = List.Tot.length rows;
    }
  | t :: rest ->
    if mem_triple t seen
    then build_indexed_graph_store_acc rest seen terms rows spo pos osp
    else
      let row, terms1 = encode_triple t terms in
      let spo1, pos1, osp1 = add_row_to_indexes row spo pos osp in
      build_indexed_graph_store_acc
        rest
        (t :: seen)
        terms1
        (row :: rows)
        spo1
        pos1
        osp1

let build_indexed_graph_store (g : graph_list) : indexed_graph_store =
  build_indexed_graph_store_acc g [] [] [] [] [] []
