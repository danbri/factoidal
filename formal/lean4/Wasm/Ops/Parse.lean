/-
Wasm.Ops.Parse — parseToDatasetJson / serializeNQuads / serializeTurtle.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  parseToDatasetJson(text, formatTag, baseIRI)
    -> {"ok":true,"count":N,"nquads":"…"} | {"ok":false,"error":"…"}
  serializeNQuads(nquads)
    -> {"ok":true,"nquads":"…"}
  serializeTurtle(nquads)
    -> {"ok":true,"turtle":"…"}

The dataset handle IS the returned N-Quads string, exactly as in the F*
entry. Format tags follow `RDF.Format.fst`'s `format_of_string` table
for the formats the Lean engine parses; a `*12` tag routes to the RDF
1.2 (`Mode.rdf12`) entry points, mirroring `entry_jsoo.ml`'s
consumer-side dispatch. `jsonld` is a named gap, not a silent one.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.NQuadsFast

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Total quad count of a dataset (the F* `dataset_triple_count`).
Not private: `Wasm/Ops/Handles.lean`'s count envelopes use it too. -/
def datasetQuadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (·.graph.length)).foldl (· + ·) 0

/-- Parse `text` under `formatTag` into a `Dataset`. Graph-shaped
formats (Turtle, N-Triples, RDF/XML) wrap as the default graph.
Not private: `Wasm/Ops/Handles.lean`'s `datasetOpen` is the same parse. -/
def parseTextToDataset (text formatTag baseIRI : String) :
    Except String Dataset :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  -- Consumer-side RDF 1.2 opt-in, exactly as entry_jsoo.ml: a "*12"
  -- tag selects Mode.rdf12; every other tag keeps the 1.1 path.
  let lo := formatTag.toLower
  let (mode, tag) :=
    match lo with
    | "ttl12" | "turtle12"   => (Mode.rdf12, "ttl")
    | "nt12"  | "ntriples12" => (Mode.rdf12, "nt")
    | "nq12"  | "nquads12"   => (Mode.rdf12, "nq")
    | "trig12"               => (Mode.rdf12, "trig")
    | _                      => (Mode.rdf11, lo)
  let wrapGraph (r : Except ParseError Graph) : Except String Dataset :=
    match r with
    | .error e => .error (fmtParseError e)
    | .ok g    => .ok { default := g, named := [] }
  match tag with
  | "" | "turtle" | "ttl" => wrapGraph (parseTurtle text base mode)
  | "ntriples" | "nt" | "n-triples" => wrapGraph (parseNTriples text mode)
  | "nquads" | "nq" | "n-quads" =>
      (parseNQuadsFast text mode).mapError fmtParseError
  | "trig" => (parseTriG text base mode).mapError fmtParseError
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" =>
      wrapGraph (RdfXml.parseRdfXml text base)
  | "jsonld" | "json-ld" | "application/ld+json" =>
      .error "JSON-LD is not in the Lean engine's v1 surface"
  | _ => .error s!"unknown format tag '{formatTag}'"

/-- `parseToDatasetJson(text, formatTag, baseIRI)`. -/
def parseToDatasetJson (text formatTag baseIRI : String) : String :=
  match parseTextToDataset text formatTag baseIRI with
  | .error msg => errJson msg
  | .ok ds =>
      okWith [("count", .number (toString (datasetQuadCount ds))),
              ("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- `serializeNQuads(nquads)` — reparse and re-serialise in canonical
N-Quads form. -/
def serializeNQuads (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- `serializeTurtle(nquads)` — prefix-compacted pretty-print. Named
graphs are flattened into the default graph for this path (the
fidelity-preserving path is serializeNQuads / canonicalizeToNQuads),
mirroring `entry_jsoo.ml`'s `serialize_turtle`. -/
def serializeTurtle (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      let g := ds.default ++ ds.named.flatMap (·.graph)
      okWith [("turtle", .string (turtleOfGraphAuto g))]

end L4Wasm.Ops
