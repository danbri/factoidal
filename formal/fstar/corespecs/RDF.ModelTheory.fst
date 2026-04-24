module RDF.ModelTheory

open RDF.CoreSpec

// RDF Semantics / model theory layer.
//
// Bucket: CORE SPEC.
//
// This module is deliberately separate from `RDF.CoreSpec`: Concepts defines
// the abstract syntax of RDF graphs; Semantics gives interpretations, truth,
// satisfaction, and entailment. That distinction is important enough to keep
// visible in the folder structure.

type resource = string

type property_extension = resource -> resource -> proposition

noeq type interpretation = {
  resources             : collection resource;
  properties            : collection resource;
  iri_denotes           : iri -> resource;
  literal_denotes       : literal -> option resource;
  property_extension_of : resource -> property_extension;
}

// Blank nodes are treated through an assignment into the universe of discourse.
// This is where the existential character of blank nodes belongs; it should not
// be collapsed into implementation labels in the graph data model.
type blank_node_assignment = blank_node -> resource

let subject_denotes
  (interp:interpretation)
  (assign:blank_node_assignment)
  (s:subject)
  (r:resource)
  : proposition =
  match s with
  | SubjectIRI i -> interp.iri_denotes i == r
  | SubjectBlank b -> assign b == r

let term_denotes
  (interp:interpretation)
  (assign:blank_node_assignment)
  (t:term)
  (r:resource)
  : proposition =
  match t with
  | IRI i -> interp.iri_denotes i == r
  | Blank b -> assign b == r
  | Literal l -> interp.literal_denotes l == Some r

let triple_true
  (interp:interpretation)
  (assign:blank_node_assignment)
  (t:triple)
  : proposition =
  exists (rs:resource). exists (ro:resource).
    subject_denotes interp assign t.s rs /\
    term_denotes interp assign t.o ro /\
    interp.property_extension_of (interp.iri_denotes t.p) rs ro

let graph_true
  (interp:interpretation)
  (assign:blank_node_assignment)
  (g:graph)
  : proposition =
  t:triple -> g t -> triple_true interp assign t

// A graph is satisfied by an interpretation when there exists a blank-node
// assignment making every triple in the graph true.
let satisfies_graph
  (interp:interpretation)
  (g:graph)
  : proposition =
  exists (assign:blank_node_assignment). graph_true interp assign g

// Simple entailment: every interpretation satisfying g1 also satisfies g2.
// RDF/RDFS/datatype entailment should refine the class of interpretations,
// not replace this model-theoretic shape with an implementation shortcut.
let simple_entails (g1 g2:graph) : proposition =
  interp:interpretation -> satisfies_graph interp g1 -> satisfies_graph interp g2
