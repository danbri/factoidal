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

// Graph NAMES are iri-typed (ng_name), but blank-node graph labels are
// admitted as the literal string "_:<label>" inside that slot — the
// Parser.NQuads convention, also used by Parser.TriG and Parser.JSONLD
// (see docs/designissues/2026-04-25-nquads-bnode-graph-fix.md). Those
// labels are document-scoped exactly like triple-level bnodes, so they
// are renamed with the same prefix: a bnode used both as a graph name
// and as a subject/object (e.g. JSON-LD toRdf/0117) keeps one identity
// after renaming, and equal labels from different documents stay
// disjoint.
let rename_graph_name (prefix : string) (name : iri) : iri =
  if String.length name >= 2 then
    (if String.sub name 0 2 = "_:" then
       String.concat "" ["_:"; prefix; String.sub name 2 (String.length name - 2)]
     else name)
  else name

let rename_named_graph (prefix : string) (ng : named_graph) : named_graph =
  { ng_name = rename_graph_name prefix ng.ng_name;
    ng_graph = rename_graph_bnodes prefix ng.ng_graph }
let rename_dataset_bnodes (prefix : string) (ds : rdf_dataset) : rdf_dataset =
  {
    ds_default = rename_graph_bnodes prefix ds.ds_default;
    ds_named = List.Tot.map (rename_named_graph prefix) ds.ds_named;
  }
