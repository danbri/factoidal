module RDF.Dataset.Graphs

// Graphs-first API surface — thin accessors over rdf_dataset, per
// docs/designissues/2026-07-05-graphs-api-design.md section 1.1.
// This is a pragmatics/accessor module (skills/fstar-module-style):
// every definition below is a Tot composition of existing
// RDF.Graph.Executable accessors, so it carries no new proof
// obligations beyond what rdf_dataset already does. RDF 1.1 assigns
// no semantics to the relation between named graphs (Zimmermann
// Note) -- this module is vocabulary + convention on top of
// rdf_dataset, not a change to it.

open FStar.List.Tot
open RDF.Graph.Executable

// An IRI, not a new term kind. Includes the "_:<label>" blank-node
// graph-name convention (RDF.Dataset.Merge.rename_graph_name).
type graph_ref = iri

// All (name, graph) pairs, default graph excluded -- SPARQL's
// FROM NAMED universe. Order matches ds.ds_named.
let graphs (ds : rdf_dataset) : list (graph_ref * rdf_graph) =
  List.Tot.map (fun (ng : named_graph) -> (ng.ng_name, ng.ng_graph)) ds.ds_named

// Re-export of lookup_named_graph under the graphs-API name.
let component_of (ds : rdf_dataset) (name : graph_ref) : option rdf_graph =
  lookup_named_graph name ds.ds_named
