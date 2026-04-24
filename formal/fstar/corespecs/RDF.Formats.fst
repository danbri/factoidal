module RDF.Formats

open RDF.CoreSpec

// RDF concrete syntaxes and result syntaxes.
//
// Bucket: CORE SPEC.
//
// This file names the standards-level mapping between static data items and
// RDF graphs/datasets. Concrete scanner/parser implementations belong in
// `practical/`; context/network policy belongs in `midzone/`.

type rdf_graph_syntax =
  | NTriples
  | Turtle
  | RDFXML

type rdf_dataset_syntax =
  | NQuads
  | TriG
  | JSONLD

type sparql_result_syntax =
  | SPARQLResultsXML
  | SPARQLResultsJSON
  | SPARQLResultsCSV
  | SPARQLResultsTSV

noeq type graph_document = {
  syntax : rdf_graph_syntax;
  source : data_item;
}

noeq type dataset_document = {
  syntax : rdf_dataset_syntax;
  source : data_item;
}

// Standards-level parse/denotation relations. These are deliberately
// relational rather than functions: errors, base IRIs, blank-node allocation,
// and JSON-LD contexts need extra assumptions that should be explicit.
let graph_document_denotes (doc:graph_document) (g:graph) : proposition =
  denotes_graph doc.source g

let dataset_document_denotes (doc:dataset_document) (d:dataset) : proposition =
  denotes_dataset doc.source d
