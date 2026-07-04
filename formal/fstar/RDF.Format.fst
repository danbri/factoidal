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
  | JSONLD

// Default fallback when the caller can't determine the format. Matches
// the legacy OCaml behaviour ("when in doubt, parse as Turtle").
let rdf_format_default : rdf_format = Turtle

// Map a file extension (as returned by `Filename.extension`, e.g.
// ".TTL" or ".nq" — case-insensitive) to a format. We lowercase
// inside the function rather than asking the caller, so the
// semantic table here is the single source of truth and there's no
// way to forget the normalization step at a call site.
// Implementation note: `if/else if` chain rather than `match`-on-string
// literals so that KaRaMeL's C extraction succeeds (Warning 250 /
// `[MLP_Const]`). #200 G3.
let format_of_extension (ext : string) : option rdf_format =
  let lo = lowercase ext in
  if      lo = ".nt"        then Some NT
  else if lo = ".ntriples"  then Some NT
  else if lo = ".ttl"       then Some Turtle
  else if lo = ".turtle"    then Some Turtle
  else if lo = ".nq"        then Some NQuads
  else if lo = ".nquads"    then Some NQuads
  else if lo = ".trig"      then Some TriG
  else if lo = ".rdf"       then Some RDFXML
  else if lo = ".xml"       then Some RDFXML
  else if lo = ".rdfxml"    then Some RDFXML
  else if lo = ".owl"       then Some RDFXML
  else if lo = ".jsonld"    then Some JSONLD
  else if lo = ".json-ld"   then Some JSONLD
  else                           None

// Like `format_of_extension`, but for the short labels accepted on
// `--format X` / HTTP request `?format=X`. Same case-insensitive
// matching, same single source of truth, same KaRaMeL-compatible
// if/else-if shape.
let format_of_string (s : string) : option rdf_format =
  let lo = lowercase s in
  if      lo = "ntriples"   then Some NT
  else if lo = "nt"         then Some NT
  else if lo = "n-triples"  then Some NT
  else if lo = "turtle"     then Some Turtle
  else if lo = "ttl"        then Some Turtle
  else if lo = "nquads"     then Some NQuads
  else if lo = "nq"         then Some NQuads
  else if lo = "n-quads"    then Some NQuads
  else if lo = "trig"       then Some TriG
  else if lo = "rdfxml"     then Some RDFXML
  else if lo = "rdf/xml"    then Some RDFXML
  else if lo = "rdf"        then Some RDFXML
  else if lo = "xml"        then Some RDFXML
  else if lo = "jsonld"     then Some JSONLD
  else if lo = "json-ld"    then Some JSONLD
  else if lo = "application/ld+json" then Some JSONLD
  else                           None

// Verbose display name. Used in startup logs and `--format help`.
let format_name (f : rdf_format) : string =
  match f with
  | NT     -> "N-Triples"
  | Turtle -> "Turtle"
  | NQuads -> "N-Quads"
  | TriG   -> "TriG"
  | RDFXML -> "RDF/XML"
  | JSONLD -> "JSON-LD (expanded form)"

// Convenience: detect the format of a path's extension, falling back
// to `rdf_format_default` if the extension is unknown or absent.
// This matches the legacy `detect_format` semantics from
// factoidal_http.ml and factoidal_cli.ml exactly.
let detect_format_or_default (extension : string) : rdf_format =
  match format_of_extension extension with
  | Some f -> f
  | None   -> rdf_format_default
