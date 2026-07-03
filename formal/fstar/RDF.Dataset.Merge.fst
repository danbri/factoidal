module RDF.Dataset.Merge

// Per-document blank-node scoping for multi-file dataset loading
// (standing priority 2d; found by the Jena ARQ graph probe:
// graph-09/10b — `_:x` labels from separately loaded files spuriously
// joined because the loader concatenated datasets without renaming).
//
// RDF 1.1 semantics: blank-node labels are scoped to the document
// they appear in. When a consumer loads N documents into one dataset,
// each document's labels must be made disjoint before merging. Label
// renaming is a semantic decision about bnode identity, so it lives
// here (rule #15), not in consumer OCaml; consumers apply
// rename_dataset_bnodes with a distinct prefix per input document
// (e.g. "f0_", "f1_", ...) and then concatenate.
//
// Renaming is a bijection on labels within one document (prefixing
// preserves distinctness), so the renamed graph is isomorphic to the
// input — no triples are gained, lost, or merged within a document.

open FStar.List.Tot
open RDF.Graph.Executable

let rename_bnode_label (prefix : string) (b : string) : string =
  String.concat "" [prefix; b]

let rename_subject (prefix : string) (s : subject) : subject =
  match s with
  | S_BNode b -> S_BNode (rename_bnode_label prefix b)
  | _ -> s

let rename_term (prefix : string) (t : rdf_term) : rdf_term =
  match t with
  | T_BNode b -> T_BNode (rename_bnode_label prefix b)
  | _ -> t

let rename_triple (prefix : string) (t : triple) : triple =
  {
    s = rename_subject prefix t.s;
    p = t.p;
    o = rename_term prefix t.o;
  }

let rename_graph_bnodes (prefix : string) (g : rdf_graph) : rdf_graph =
  List.Tot.map (rename_triple prefix) g

let rename_named_graph (prefix : string) (ng : named_graph) : named_graph =
  { ng with ng_graph = rename_graph_bnodes prefix ng.ng_graph }

// Note: graph NAMES are IRIs in this model (ng_name), so only triple
// content is renamed. If graph-name bnodes are ever admitted, this is
// the single place to extend.
let rename_dataset_bnodes (prefix : string) (ds : rdf_dataset) : rdf_dataset =
  {
    ds_default = rename_graph_bnodes prefix ds.ds_default;
    ds_named = List.Tot.map (rename_named_graph prefix) ds.ds_named;
  }
