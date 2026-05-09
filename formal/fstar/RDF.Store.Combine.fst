module RDF.Store.Combine

(* Combine multiple dataset_backends into one. The OCaml caller
   (bin/factoidal-http and bin/factoidal-cli's build_dataset_backend)
   produces a list of dataset_backend values — one for the in-memory
   side, one per --data-cottas file — and needs to expose them through
   a single dispatch surface. The pure FOLD that does the per-IRI
   regrouping was previously inlined in OCaml using Hashtbl + ref;
   this F* version uses ordered list-based bucketing.

   #200 Section A non-codename migration (last of the 3 items),
   2026-05-09. Mirrors the bucket_quads pattern in RDF.Store.Loader. *)

open RDF.Graph.Executable
open SPARQL11.Store
open FStar.List.Tot

(* Find a bucket for [iri] in [acc] and add [g] to its graph list.
   Preserves insertion order:
     - First time we see [iri], create a fresh bucket with `g` plain
       (no Union wrap — matches OCaml's "single" case).
     - Subsequent additions wrap into GB_Union: if the existing graph
       is already a Union, extend its members list; otherwise wrap
       the existing single + `g` into a 2-element Union.
*)
let rec extend_backend_bucket
  (iri_name : iri) (g : graph_backend) (acc : list named_graph_backend)
  : Tot (list named_graph_backend) (decreases acc)
  =
  match acc with
  | [] -> [{ ngb_name = iri_name; ngb_graph = g }]
  | ng :: rest ->
    if ng.ngb_name = iri_name
    then
      let new_graph =
        match ng.ngb_graph with
        | GB_Union members -> GB_Union (append members [g])
        | single -> GB_Union [single; g]
      in
      { ngb_name = ng.ngb_name; ngb_graph = new_graph } :: rest
    else
      ng :: extend_backend_bucket iri_name g rest

(* Fold a list of named_graph_backends into [acc] one at a time,
   regrouping by IRI via extend_backend_bucket. *)
let rec extend_backend_buckets
  (acc : list named_graph_backend)
  (incoming : list named_graph_backend)
  : Tot (list named_graph_backend) (decreases incoming)
  =
  match incoming with
  | [] -> acc
  | ngb :: rest ->
    extend_backend_buckets
      (extend_backend_bucket ngb.ngb_name ngb.ngb_graph acc)
      rest

(* Top-level combiner: given a list of dataset_backend values
   (typically [in_memory] :: cottas_backends), produce a single
   combined dataset_backend.

   Rules:
   - Empty list: an empty dataset (Union of nothing for default,
     no named graphs).
   - Single element: returned unchanged (no useless Union wrap).
   - Multiple: default-graphs unioned in order; named-graphs
     regrouped by IRI per extend_backend_buckets.
*)
let combine_dataset_backends (backends : list dataset_backend)
  : Tot dataset_backend
  =
  match backends with
  | []  -> { dsb_default = GB_Union []; dsb_named = [] }
  | [b] -> b
  | _   ->
    let dsb_default =
      GB_Union (map (fun (b : dataset_backend) -> b.dsb_default) backends)
    in
    let dsb_named =
      fold_left
        (fun acc (b : dataset_backend) -> extend_backend_buckets acc b.dsb_named)
        []
        backends
    in
    { dsb_default; dsb_named }
