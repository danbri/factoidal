module RDF.CoreSpec

// Core RDF Concepts and Abstract Syntax vocabulary.
//
// Bucket: CORE SPEC.
//
// This module is meant to read like the normative RDF data model: terms,
// triples, graphs, datasets, and graph comparison shape. It intentionally
// avoids parser validation, storage layout, execution strategy, test-runner
// conventions, entailment-regime policy choices, and performance shortcuts.

type iri = string
type blank_node = string
type lexical_form = string
type language_tag = string
type datatype_iri = iri

type literal =
  | TypedLiteral : lexical_form -> datatype_iri -> literal
  | LangLiteral  : lexical_form -> language_tag -> literal

type term =
  | IRI     : iri -> term
  | Blank   : blank_node -> term
  | Literal : literal -> term

type subject =
  | SubjectIRI   : iri -> subject
  | SubjectBlank : blank_node -> subject

type predicate = iri

type triple = {
  s : subject;
  p : predicate;
  o : term;
}

// Reader-facing aliases for the mathematical layer.
//
// `proposition` is F*'s universe of statements that may need proof. Keeping
// the name here avoids exposing `Type0` at every graph/dataset definition.
type proposition = Type

// A mathematical collection is described by its membership predicate. This is
// not an implementation choice; it is the cleanest way to say "set" without
// choosing a hash table, balanced tree, list, or canonical ordering.
type collection (item:Type) = item -> proposition

type contains (#item:Type) (xs:collection item) (x:item) = xs x

// Mathematical graph: an extensional collection of triples.
type graph = collection triple

let empty_graph : graph =
  fun _ -> False

let graph_included (g1 g2 : graph) : proposition =
  t:triple -> g1 t -> g2 t

let graph_equal (g1 g2 : graph) : proposition =
  graph_included g1 g2 * graph_included g2 g1

// RDF dataset names are IRIs or blank nodes in RDF 1.1 Concepts.
type graph_name = subject

noeq type named_graph = {
  name  : graph_name;
  graph : graph;
}

noeq type dataset = {
  default_graph : graph;
  named_graphs  : collection named_graph;
}

// Static information objects: concrete data before RDF interpretation.
//
// This layer lets us state relationships between graph/dataset values and the
// bytes/chars/documents from which they are read or to which they are written.
// That is especially important for formats such as JSON-LD, where remote
// contexts mean the same local bytes may map to different RDF data depending
// on the context-loading environment.

type byte = b:nat{b < 256}
type byte_string = list byte
type char_string = string

type media_type = string
type character_encoding = string

noeq type data_item = {
  bytes    : byte_string;
  media    : option media_type;
  charset  : option character_encoding;
}

type graph_syntax = data_item
type dataset_syntax = data_item

// Abstract conformance relation: a data item may parse as a graph or dataset
// under the relevant syntax specification. Concrete parser algorithms and
// network/context loading policies are deliberately outside this core module.
type denotes_graph (source:graph_syntax) (g:graph) : proposition = True
type denotes_dataset (source:dataset_syntax) (d:dataset) : proposition = True

type bnode_map = blank_node -> blank_node

let rename_subject (m:bnode_map) (s:subject) : subject =
  match s with
  | SubjectIRI i -> SubjectIRI i
  | SubjectBlank b -> SubjectBlank (m b)

let rename_term (m:bnode_map) (t:term) : term =
  match t with
  | IRI i -> IRI i
  | Blank b -> Blank (m b)
  | Literal l -> Literal l

let rename_triple (m:bnode_map) (t:triple) : triple =
  {
    s = rename_subject m t.s;
    p = t.p;
    o = rename_term m t.o;
  }

let rename_graph (m:bnode_map) (g:graph) : graph =
  fun t -> exists (t0:triple). g t0 /\ rename_triple m t0 == t

// Graph isomorphism as a mathematical witness shape. This is core RDF
// Concepts, but an algorithm for finding the witness belongs elsewhere.
type graph_isomorphic (g1 g2 : graph) : Type0 =
  m:bnode_map & n:bnode_map &
    graph_equal (rename_graph m g1) g2 *
    graph_equal (rename_graph n g2) g1
