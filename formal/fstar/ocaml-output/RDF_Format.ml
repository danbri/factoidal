open Prims
type rdf_format =
  | NT 
  | Turtle 
  | NQuads 
  | TriG 
  | RDFXML 
let uu___is_NT (projectee : rdf_format) : Prims.bool=
  match projectee with | NT -> true | uu___ -> false
let uu___is_Turtle (projectee : rdf_format) : Prims.bool=
  match projectee with | Turtle -> true | uu___ -> false
let uu___is_NQuads (projectee : rdf_format) : Prims.bool=
  match projectee with | NQuads -> true | uu___ -> false
let uu___is_TriG (projectee : rdf_format) : Prims.bool=
  match projectee with | TriG -> true | uu___ -> false
let uu___is_RDFXML (projectee : rdf_format) : Prims.bool=
  match projectee with | RDFXML -> true | uu___ -> false
let rdf_format_default : rdf_format= Turtle
let format_of_extension (ext : Prims.string) :
  rdf_format FStar_Pervasives_Native.option=
  match FStar_String.lowercase ext with
  | ".nt" -> FStar_Pervasives_Native.Some NT
  | ".ntriples" -> FStar_Pervasives_Native.Some NT
  | ".ttl" -> FStar_Pervasives_Native.Some Turtle
  | ".turtle" -> FStar_Pervasives_Native.Some Turtle
  | ".nq" -> FStar_Pervasives_Native.Some NQuads
  | ".nquads" -> FStar_Pervasives_Native.Some NQuads
  | ".trig" -> FStar_Pervasives_Native.Some TriG
  | ".rdf" -> FStar_Pervasives_Native.Some RDFXML
  | ".xml" -> FStar_Pervasives_Native.Some RDFXML
  | ".rdfxml" -> FStar_Pervasives_Native.Some RDFXML
  | ".owl" -> FStar_Pervasives_Native.Some RDFXML
  | uu___ -> FStar_Pervasives_Native.None
let format_of_string (s : Prims.string) :
  rdf_format FStar_Pervasives_Native.option=
  match FStar_String.lowercase s with
  | "ntriples" -> FStar_Pervasives_Native.Some NT
  | "nt" -> FStar_Pervasives_Native.Some NT
  | "n-triples" -> FStar_Pervasives_Native.Some NT
  | "turtle" -> FStar_Pervasives_Native.Some Turtle
  | "ttl" -> FStar_Pervasives_Native.Some Turtle
  | "nquads" -> FStar_Pervasives_Native.Some NQuads
  | "nq" -> FStar_Pervasives_Native.Some NQuads
  | "n-quads" -> FStar_Pervasives_Native.Some NQuads
  | "trig" -> FStar_Pervasives_Native.Some TriG
  | "rdfxml" -> FStar_Pervasives_Native.Some RDFXML
  | "rdf/xml" -> FStar_Pervasives_Native.Some RDFXML
  | "rdf" -> FStar_Pervasives_Native.Some RDFXML
  | "xml" -> FStar_Pervasives_Native.Some RDFXML
  | uu___ -> FStar_Pervasives_Native.None
let format_name (f : rdf_format) : Prims.string=
  match f with
  | NT -> "N-Triples"
  | Turtle -> "Turtle"
  | NQuads -> "N-Quads"
  | TriG -> "TriG"
  | RDFXML -> "RDF/XML"
let detect_format_or_default (extension : Prims.string) : rdf_format=
  match format_of_extension extension with
  | FStar_Pervasives_Native.Some f -> f
  | FStar_Pervasives_Native.None -> rdf_format_default
