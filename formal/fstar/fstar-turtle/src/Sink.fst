module Sink

// Callback interface for emitting parsed RDF data.
// Modeled after Serd's sink pattern: the parser calls these functions
// as it encounters base declarations, prefix bindings, and statements.
//
// This is Layer 5 in the architecture but simple enough to define early
// since TurtleReader needs the types.

open Node
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open LowStar.Buffer
module B = LowStar.Buffer

// Callback for @base directives: base(iri)
// Called when the parser encounters @base <iri> . or BASE <iri>
type base_sink = node -> FStar.HyperStack.ST.Stack ByteSource.status
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

// Callback for @prefix directives: prefix(name, iri)
// Called when the parser encounters @prefix name: <iri> . or PREFIX name: <iri>
type prefix_sink = node -> node -> FStar.HyperStack.ST.Stack ByteSource.status
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

// Callback for RDF statements: statement(flags, graph, subject, predicate, object, datatype, lang)
// Called for each triple/quad the parser produces.
// For blank node abbreviations and collections, the parser expands
// inline syntax and emits multiple statements.
type statement_sink = stmt_flags -> node -> node -> node -> node -> node -> node -> FStar.HyperStack.ST.Stack ByteSource.status
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

// Callback for end of anonymous blank node scope.
// Called when ] is encountered, closing an anonymous structure.
type end_sink = node -> FStar.HyperStack.ST.Stack ByteSource.status
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

// Bundle of all sink callbacks. The parser holds one of these.
noeq type sinks = {
  on_base: base_sink;
  on_prefix: prefix_sink;
  on_statement: statement_sink;
  on_end: end_sink;
}
