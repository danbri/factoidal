module RDF.Graph

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5. One concept, one screen: what is a graph, what is
// a dataset. A copy-move from RDF.Graph.Executable.fst (the
// `rdf_graph`/`named_graph`/`rdf_dataset` types + `empty_graph`/
// `empty_dataset`/`lookup_named_graph`), no behavior change.
// Transparent `let`s/`type`s throughout — see RDF.Term.fsti's banner
// for why.
//
// Deliberately NOT here: `graph_add`/`graph_remove`/`graph_union`,
// `find_by_subject`/`find_by_predicate`, `graph_bnodes`, the
// `rename_*_bnodes` family, `graph_dedup_sort`/`graph_finalise` —
// design doc §2.2 assigns those here eventually, but this slice moves
// only the type tier (RDF.Term.fsti's banner explains the narrower
// scoping this step actually shipped, same call as step 3's
// RDF.Indexed). They stay in RDF.Graph.Executable.fst for now.

open RDF.Term
open RDF.Triple

(** ------------------------------------------------------------------ *)
(** RDF graphs — RDF 1.1 Concepts §3 ("a set of RDF triples")          *)
(** ------------------------------------------------------------------ *)

/// An RDF graph is a set of triples. Represented as a list (not a set)
/// so it extracts and executes directly; the algebra and de-
/// duplication helpers that keep list semantics behaving like set
/// semantics (`graph_add`'s membership check, `graph_dedup_sort`)
/// stay in `RDF.Graph.Executable.fst`.
type rdf_graph = list triple

let empty_graph : rdf_graph = []

(** ------------------------------------------------------------------ *)
(** RDF datasets — RDF 1.1 Concepts §4 ("one default graph ... zero or *)
(** more named graphs, each ... identified by an IRI")                 *)
(** ------------------------------------------------------------------ *)

/// One named graph: an IRI naming a graph, per RDF 1.1 Concepts §4's
/// dataset definition.
noeq type named_graph = {
  ng_name : iri;
  ng_graph : rdf_graph;
}

/// An RDF dataset: exactly one default graph, plus zero or more named
/// graphs. This is the unit SPARQL's `FROM`/`FROM NAMED`/`GRAPH`
/// clauses (SPARQL 1.1 §13.2) query against.
noeq type rdf_dataset = {
  ds_default : rdf_graph;
  ds_named : list named_graph;
}

let empty_dataset : rdf_dataset = { ds_default = empty_graph; ds_named = [] }

/// Look up a named graph by its IRI; `None` if the dataset has no
/// graph under that name.
let rec lookup_named_graph (name : iri) (named : list named_graph) : option rdf_graph =
  match named with
  | [] -> None
  | ng :: rest -> if ng.ng_name = name then Some ng.ng_graph else lookup_named_graph name rest
