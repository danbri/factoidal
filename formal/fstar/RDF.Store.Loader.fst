module RDF.Store.Loader

(* Pure-F* dataset fold helpers used by the OCaml-side loaders in
   bin/factoidal-http/ and bin/factoidal-cli/.

   Migration target for #200 Section A non-codename items:
     - load_cottas_part      (this file)
     - load_cottas_dataset   (future)
     - build_dataset_backend (RDF.Store.Combine.fst, future)

   The OCaml caller still owns Parquet I/O — opening a .cottas file,
   reading parquet metadata, decoding columns. That I/O is rule-#11(a)
   legitimate (file/clock/socket I/O, declared via `assume val` from
   the appropriate F* module).

   What lives here: the PURE FOLD that combines multiple loaded
   `rdf_dataset` values into one. Previously this was inlined in
   bin/factoidal-http/factoidal_http.ml as `load_cottas_part`, mixing
   the fold with `try ... with` exception handling around the I/O
   call. Splitting them lets the fold itself live in F* (pure,
   verified by extension) while the OCaml side keeps only the I/O +
   exception handling. *)

open RDF.Graph.Executable

module Lh = RDF.List.Helpers

(* Merge two datasets. Default graphs concatenate; named-graph lists
   concatenate. Bag (multiset) semantics — duplicates preserved.

   Used as the inner step of `merge_datasets`. *)
let merge_pair (acc extra : rdf_dataset) : Tot rdf_dataset =
  { ds_default = Lh.append_tr acc.ds_default extra.ds_default;
    ds_named   = Lh.append_tr acc.ds_named   extra.ds_named }

(* Fold a list of additional datasets onto a base. The caller (OCaml)
   pre-loads each `extras[i]` via the appropriate I/O path (e.g.
   `load_cottas_dataset` over a parquet file, or `load_dataset_fast`
   over a turtle file) and hands the pre-loaded list here. The fold
   itself is pure. *)
let merge_datasets (base : rdf_dataset) (extras : list rdf_dataset)
  : Tot rdf_dataset
  =
  List.Tot.fold_left merge_pair base extras

(* ---------------------------------------------------------------------
   bucket_quads / load_cottas_dataset (#200 PR3 follow-up, 2026-05-09)

   Section A non-codename migration: the OCaml side of factoidal_http
   resolves each COTTAS quad-row into (subject, predicate, object,
   optional graph IRI) using its hashtable caches. The pure FOLD that
   buckets resolved quads into a default-graph + named-graph dataset
   was previously inlined in OCaml; this is the F* version.

   The OCaml caller's responsibility:
     1. Open the COTTAS artifact via Parser_BallyhooCOTTAS.cottas_open_dataset_store
        (already F*-extracted I/O glue per rule #11(a)).
     2. For each cached quad, resolve s/p/o/g via its hashtables (O(1)
        lookups; F* would be O(n) without imperative arrays — perf
        isn't compatible with parliament-scale corpora).
     3. Build a list of `resolved_quad` records.
     4. Call `bucket_quads` to get the rdf_dataset.

   The bucketing fold itself is pure: walk the list, collect default-
   graph triples in a separate list, group named-graph triples by
   IRI. Order-preserving via List.Tot.rev at the end. *)

noeq type resolved_quad = {
  rq_triple : triple;
  rq_graph  : option string;  // None = default graph
}

(* Helper: append a triple to the bucket for [iri] in [acc], or
   create a new bucket if [iri] isn't present. *)
let rec extend_named_bucket
  (iri : string) (t : triple) (acc : list named_graph)
  : Tot (list named_graph) (decreases acc)
  =
  match acc with
  | [] -> [{ ng_name = iri; ng_graph = [t] }]
  | ng :: rest ->
    if ng.ng_name = iri
    then { ng_name = ng.ng_name; ng_graph = t :: ng.ng_graph } :: rest
    else ng :: extend_named_bucket iri t rest

(* Walk a list of resolved quads, partitioning into:
     default_acc :  list triple    (built in reverse)
     named_acc   :  list named_graph (each ng_graph in reverse)

   Final reverse on default_acc + per-bucket reverse-via-helper
   restores source order. *)

let rec bucket_quads_acc
  (default_acc : list triple)
  (named_acc   : list named_graph)
  (quads : list resolved_quad)
  : Tot (list triple * list named_graph) (decreases quads)
  =
  match quads with
  | [] -> (default_acc, named_acc)
  | q :: rest ->
    let t = q.rq_triple in
    match q.rq_graph with
    | None ->
      bucket_quads_acc (t :: default_acc) named_acc rest
    | Some g_iri ->
      bucket_quads_acc default_acc (extend_named_bucket g_iri t named_acc) rest

let reverse_named_graph (ng : named_graph) : Tot named_graph =
  { ng_name = ng.ng_name; ng_graph = List.Tot.rev ng.ng_graph }

(* Top-level bucketing fold. Caller provides resolved quads (I/O
   already done); F* produces the rdf_dataset. *)
let bucket_quads (quads : list resolved_quad) : Tot rdf_dataset =
  let (default_rev, named_rev) = bucket_quads_acc [] [] quads in
  let default_g = List.Tot.rev default_rev in
  let named_gs  = List.Tot.map reverse_named_graph named_rev in
  { ds_default = default_g; ds_named = named_gs }
