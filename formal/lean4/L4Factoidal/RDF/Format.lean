/-
L4Factoidal.RDF.Format — which string denotes which serialisation.

Port of `formal/fstar/RDF.Format.fst` (103 lines).

The F\* module exists because `factoidal_http.ml` and `factoidal_cli.ml`
each carried an identical copy of this table — the drift iron rule #1
wants out of OCaml. Three semantic mappings live here: which file
extension denotes which serialisation, which short name does, and what
verbose name to display. Extracting an extension from a path is
`Filename.extension` on the caller and stays glue.

## One difference from the F\*

The F\* module uses an `if`/`else if` chain rather than a `match` on
string literals, because KaRaMeL's C extraction rejects the latter
(warning 250, `[MLP_Const]`). Lean has no such constraint, but the chain
is kept: it is one table read top to bottom in both trees, so a
divergence between them is a diff on the same shape rather than a
restructure.
-/

namespace L4Factoidal.RDF

inductive RdfFormat where
  | nt | turtle | nquads | trig | rdfxml | jsonld
  deriving Repr, DecidableEq, Inhabited

/-- The fallback when the caller cannot determine the format. Matches
    the legacy OCaml behaviour: when in doubt, parse as Turtle. -/
def rdfFormatDefault : RdfFormat := .turtle

/-- A file extension as `Filename.extension` returns it (`".TTL"`,
    `".nq"`). Lowercasing happens HERE rather than at the call site, so
    the table stays the single source of truth and no caller can forget
    the normalisation. -/
def formatOfExtension (ext : String) : Option RdfFormat :=
  let lo := ext.toLower
  if      lo == ".nt"       then some .nt
  else if lo == ".ntriples" then some .nt
  else if lo == ".ttl"      then some .turtle
  else if lo == ".turtle"   then some .turtle
  else if lo == ".nq"       then some .nquads
  else if lo == ".nquads"   then some .nquads
  else if lo == ".trig"     then some .trig
  else if lo == ".rdf"      then some .rdfxml
  else if lo == ".xml"      then some .rdfxml
  else if lo == ".rdfxml"   then some .rdfxml
  else if lo == ".owl"      then some .rdfxml
  else if lo == ".jsonld"   then some .jsonld
  else if lo == ".json-ld"  then some .jsonld
  else none

/-- The short labels accepted on `--format X` and `?format=X`. Same
    case-insensitive matching, same single source of truth. The F* name
    is `format_of_string`; renamed here because the extension table
    also takes a string and the two are NOT interchangeable — see the
    guards at the bottom. -/
def formatOfLabel (s : String) : Option RdfFormat :=
  let lo := s.toLower
  if      lo == "ntriples"  then some .nt
  else if lo == "nt"        then some .nt
  else if lo == "n-triples" then some .nt
  else if lo == "turtle"    then some .turtle
  else if lo == "ttl"       then some .turtle
  else if lo == "nquads"    then some .nquads
  else if lo == "nq"        then some .nquads
  else if lo == "n-quads"   then some .nquads
  else if lo == "trig"      then some .trig
  else if lo == "rdfxml"    then some .rdfxml
  else if lo == "rdf/xml"   then some .rdfxml
  else if lo == "rdf"       then some .rdfxml
  else if lo == "xml"       then some .rdfxml
  else if lo == "jsonld"    then some .jsonld
  else if lo == "json-ld"   then some .jsonld
  else if lo == "application/ld+json" then some .jsonld
  else none

/-- Verbose display name, for startup logs and `--format help`. -/
def formatName : RdfFormat → String
  | .nt     => "N-Triples"
  | .turtle => "Turtle"
  | .nquads => "N-Quads"
  | .trig   => "TriG"
  | .rdfxml => "RDF/XML"
  | .jsonld => "JSON-LD (expanded form)"

/-- The extension's format, falling back to `rdfFormatDefault` when the
    extension is unknown or absent. -/
def detectFormatOrDefault (ext : String) : RdfFormat :=
  (formatOfExtension ext).getD rdfFormatDefault

/-! ## Build-time checks -/

#guard formatOfExtension ".ttl" == some .turtle
#guard formatOfExtension ".TTL" == some .turtle
#guard formatOfExtension ".Nq" == some .nquads
#guard formatOfExtension ".owl" == some .rdfxml
#guard formatOfExtension ".json-ld" == some .jsonld
#guard formatOfExtension ".unknown" == none
#guard formatOfExtension "" == none

/-! The extension table takes a LEADING DOT. A bare `ttl` is a label,
    not an extension, and must not be accepted by the extension table —
    that confusion is what a single shared table would hide. -/

#guard formatOfExtension "ttl" == none
#guard formatOfLabel "ttl" == some .turtle
#guard formatOfLabel ".ttl" == none

#guard formatOfLabel "RDF/XML" == some .rdfxml
#guard formatOfLabel "application/ld+json" == some .jsonld
#guard formatOfLabel "nonsense" == none

/-! The fallback is Turtle, and it applies to an unknown extension and
    to an absent one alike. -/

#guard detectFormatOrDefault ".unknown" == .turtle
#guard detectFormatOrDefault "" == .turtle
#guard detectFormatOrDefault ".nq" == .nquads

/-! Every constructor has a display name, and they are distinct — a
    copy-paste that gave two formats the same name would pass a
    per-constructor check. -/

#guard ([RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].map formatName).eraseDups.length == 6

end L4Factoidal.RDF
