/-
Wasm.Ops.Query — queryDataset / updateDataset.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  queryDataset(nquads, sparql)
    -> {"ok":true,"kind":"select","srj":{…SPARQL results JSON…}}
     | {"ok":true,"kind":"ask","boolean":true|false}
     | {"ok":true,"kind":"construct","nquads":"…"}
     | {"ok":false,"error":"…"}
  updateDataset(nquads, sparqlUpdate)
    -> {"ok":true,"nquads":"…"} | {"ok":false,"error":"…"}

`srj` is a JSON OBJECT embedded in the envelope, not a string — the
Lean `QueryResult.toSrj` document is spliced in verbatim (it is itself
JSON produced by the ported serialiser, so the envelope stays valid
JSON). DESCRIBE returns the F* entry's exact error text.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuads
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Results
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.Update

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.JSON

/-- `queryDataset(nquads, sparql)`. -/
def queryDataset (nq sparql : String) : String :=
  match parseNQuads nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
  match parseSparql sparql with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    let env : EvalEnv := { base := q.base }
    match q.form with
    | .ask =>
        let b := evalAsk env ds q
        okWith [("kind", .string "ask"), ("boolean", .bool b)]
    | .select _ =>
        let (vars, rows) := evalSelect env ds q
        let srj := QueryResult.toSrj (.bindings vars rows)
        -- srj is a JSON object document; splice it in verbatim.
        "{\"ok\":true,\"kind\":\"select\",\"srj\":" ++ srj ++ "}"
    | .construct _ =>
        let g := evalConstruct env ds q
        match Graph.toNTriples g with
        | .error e  => errJson s!"construct serialisation: {e}"
        | .ok lines => okWith [("kind", .string "construct"),
                               ("nquads", .string lines)]
    | .describe _ =>
        errJson "DESCRIBE is not supported by the npm entry yet"

/-- `updateDataset(nquads, sparqlUpdate)`. -/
def updateDataset (nq updateText : String) : String :=
  match parseNQuads nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
  match parseSparqlUpdate updateText with
  | .error e => errJson s!"SPARQL update parse error: {fmtParseError e}"
  | .ok u =>
  match applyUpdate ds u with
  | .error e  => errJson (toString e)
  | .ok ds'   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds'))]

end L4Wasm.Ops
