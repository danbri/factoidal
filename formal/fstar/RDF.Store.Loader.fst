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
