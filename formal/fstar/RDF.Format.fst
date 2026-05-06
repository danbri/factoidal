module RDF.Format

// Identifies an RDF serialization format by the verbose name we print
// to logs and by the file extensions / short labels we accept on the
// CLI and HTTP `--format` arguments.
//
// Migration of `type rdf_format` plus `detect_format` /
// `format_of_string` / `format_name` from
// `formal/fstar/ocaml-output/factoidal_http.ml` and
// `formal/fstar/ocaml-output/factoidal_cli.ml`. Both files had identical
// copies of this table, which is exactly the kind of drift Iron Rule #1
// ("F\* is the source of truth") wants out of OCaml.
//
// The decisions in this module are:
//   - which file-extension strings denote which RDF serialization;
//   - which short-name strings denote which RDF serialization;
//   - what verbose name to display for each.
// All three are pure semantic mappings — no I/O, no system-dependent
// behaviour. The only OS-aware bit is the *extraction* of an extension
// from a file path; that's `Filename.extension` on the OCaml caller,
// which is correctly retained as glue.

open FStar.String

type rdf_format =
  | NT
  | Turtle
  | NQuads
  | TriG
  | RDFXML

// Default fallback when the caller can't determine the format. Matches
// the legacy OCaml behaviour ("when in doubt, parse as Turtle").
let rdf_format_default : rdf_format = Turtle

// Map a file extension (as returned by `Filename.extension`, e.g.
// ".TTL" or ".nq" — case-insensitive) to a format. We lowercase
// inside the function rather than asking the caller, so the
// semantic table here is the single source of truth and there's no
// way to forget the normalization step at a call site.
let format_of_extension (ext : string) : option rdf_format =
  match lowercase ext with
  | ".nt"        -> Some NT
  | ".ntriples"  -> Some NT
  | ".ttl"       -> Some Turtle
  | ".turtle"    -> Some Turtle
  | ".nq"        -> Some NQuads
  | ".nquads"    -> Some NQuads
  | ".trig"      -> Some TriG
  | ".rdf"       -> Some RDFXML
  | ".xml"       -> Some RDFXML
  | ".rdfxml"    -> Some RDFXML
  | ".owl"       -> Some RDFXML
  | _            -> None

// Like `format_of_extension`, but for the short labels accepted on
// `--format X` / HTTP request `?format=X`. Same case-insensitive
// match, same single source of truth.
let format_of_string (s : string) : option rdf_format =
  match lowercase s with
  | "ntriples"   -> Some NT
  | "nt"         -> Some NT
  | "n-triples"  -> Some NT
  | "turtle"     -> Some Turtle
  | "ttl"        -> Some Turtle
  | "nquads"     -> Some NQuads
  | "nq"         -> Some NQuads
  | "n-quads"    -> Some NQuads
  | "trig"       -> Some TriG
  | "rdfxml"     -> Some RDFXML
  | "rdf/xml"    -> Some RDFXML
  | "rdf"        -> Some RDFXML
  | "xml"        -> Some RDFXML
  | _            -> None

// Verbose display name. Used in startup logs and `--format help`.
let format_name (f : rdf_format) : string =
  match f with
  | NT     -> "N-Triples"
  | Turtle -> "Turtle"
  | NQuads -> "N-Quads"
  | TriG   -> "TriG"
  | RDFXML -> "RDF/XML"

// Convenience: detect the format of a path's extension, falling back
// to `rdf_format_default` if the extension is unknown or absent.
// This matches the legacy `detect_format` semantics from
// factoidal_http.ml and factoidal_cli.ml exactly.
let detect_format_or_default (extension : string) : rdf_format =
  match format_of_extension extension with
  | Some f -> f
  | None   -> rdf_format_default
