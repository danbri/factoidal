module Node

// RDF term representation for the streaming Turtle parser.
// Minimal tagged type: IRI | BlankNode | Literal.
//
// This is the output type emitted by the parser's sink callbacks.
// Designed for zero-copy where possible: values reference byte buffers
// owned by the parser's node stack.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open LowStar.Buffer
module B = LowStar.Buffer

// An RDF node type tag (matches Serd's SerdType)
type node_type =
  | NT_Nothing   // sentinel / null
  | NT_IRI       // absolute or relative IRI
  | NT_Blank     // blank node
  | NT_Literal   // literal value

// Statement flags for inline abbreviations (anonymous nodes, lists)
type stmt_flags =
  | SF_None
  | SF_AnonSBegin    // start of anonymous blank node as subject
  | SF_AnonOBegin    // start of anonymous blank node as object
  | SF_AnonCont      // continuation inside anonymous
  | SF_ListSBegin    // start of collection as subject
  | SF_ListOBegin    // start of collection as object
  | SF_ListCont      // continuation inside collection

// An RDF node: a view into a byte buffer plus metadata.
// The buf/len fields point into the parser's node stack (not owned).
noeq type node = {
  ntype: node_type;
  buf: B.buffer U8.t;   // UTF-8 value (IRI string, blank ID, or lexical form)
  len: U32.t;           // byte length of value
}

// A literal with optional language tag or datatype IRI.
// In Turtle, a literal is one of:
//   "value"
//   "value"@lang
//   "value"^^<datatype>
//   "value"^^prefix:local  (CURIE, resolved later)
noeq type literal_info = {
  value: node;            // the literal's lexical form
  datatype: node;         // datatype IRI (NT_IRI or NT_Nothing if absent)
  lang: node;             // language tag (NT_Literal for the tag string, or NT_Nothing)
}

// A complete RDF statement (triple or quad).
noeq type statement = {
  subject: node;
  predicate: node;
  object_node: node;      // "object" is an F* keyword, so we use object_node
  object_datatype: node;  // datatype of object if literal (NT_Nothing otherwise)
  object_lang: node;      // language tag of object if literal (NT_Nothing otherwise)
  graph: node;            // named graph (NT_Nothing for default graph)
  flags: stmt_flags;
}

// Null node constant
let node_nothing : node = {
  ntype = NT_Nothing;
  buf = B.null #U8.t;
  len = 0ul;
}

// Create an IRI node from a buffer slice
let make_iri (buf: B.buffer U8.t) (len: U32.t) : node = {
  ntype = NT_IRI;
  buf = buf;
  len = len;
}

// Create a blank node from a buffer slice
let make_blank (buf: B.buffer U8.t) (len: U32.t) : node = {
  ntype = NT_Blank;
  buf = buf;
  len = len;
}

// Create a literal node from a buffer slice
let make_literal (buf: B.buffer U8.t) (len: U32.t) : node = {
  ntype = NT_Literal;
  buf = buf;
  len = len;
}

// Well-known IRI constants (as byte sequences)
// These are used for rdf:type shorthand 'a' and collection expansion.
let rdf_ns : list U8.t = [
  0x68uy; 0x74uy; 0x74uy; 0x70uy; 0x3Auy; 0x2Fuy; 0x2Fuy;  // "http://"
  0x77uy; 0x77uy; 0x77uy; 0x2Euy;                              // "www."
  0x77uy; 0x33uy; 0x2Euy;                                      // "w3."
  0x6Fuy; 0x72uy; 0x67uy; 0x2Fuy;                              // "org/"
  0x31uy; 0x39uy; 0x39uy; 0x39uy; 0x2Fuy;                      // "1999/"
  0x30uy; 0x32uy; 0x2Fuy;                                      // "02/"
  0x32uy; 0x32uy; 0x2Duy;                                      // "22-"
  0x72uy; 0x64uy; 0x66uy; 0x2Duy;                              // "rdf-"
  0x73uy; 0x79uy; 0x6Euy; 0x74uy; 0x61uy; 0x78uy; 0x2Duy;     // "syntax-"
  0x6Euy; 0x73uy; 0x23uy                                        // "ns#"
]
// = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

// rdf:type = rdf_ns + "type"
let rdf_type_suffix : list U8.t = [ 0x74uy; 0x79uy; 0x70uy; 0x65uy ] // "type"

// rdf:first = rdf_ns + "first"
let rdf_first_suffix : list U8.t = [ 0x66uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy ]

// rdf:rest = rdf_ns + "rest"
let rdf_rest_suffix : list U8.t = [ 0x72uy; 0x65uy; 0x73uy; 0x74uy ]

// rdf:nil = rdf_ns + "nil"
let rdf_nil_suffix : list U8.t = [ 0x6Euy; 0x69uy; 0x6Cuy ]
