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
import L4Factoidal.Geo.Functions
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Syntax.NQuadsFast

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.JSON

/-- Evaluate over a dataset AND its indexed backend.  SELECT and ASK go
through the optimized Lean physical-plan algorithm
(`runSelectQueryBackendDataset` / `runAskQueryBackendDataset`, the same
path the native persisted query host uses: equivalence-aware indexes and
hash joins, refined against the reference evaluator).  A query shape that
path does not handle — it answers `none` — or a `FROM`/`FROM NAMED` clause
falls back to the reference evaluator, so the answer is never partial.
CONSTRUCT stays on the reference evaluator.  The backend is built once per
dataset handle (`Wasm/Ops/Handles.lean`); the stateless op builds it per
call. -/
def queryParsedDatasetWith (ds : Dataset) (dsb : DatasetBackend) (sparql : String) : String :=
  match parseSparql sparql with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    -- The query-facing WASM entry installs the same explicit GeoSPARQL
    -- extension table as the native evaluator.  The core evaluator remains
    -- pure: unknown function IRIs still fail through `none`, while the
    -- registered `geof:` predicates are ordinary values in this environment.
    -- §18.6: EXISTS / NOT EXISTS inside a FILTER evaluate against the
    -- query's dataset.  The reference evaluator sets `env.dataset` itself
    -- (`evalSelect`); the backend runners do not, so the environment must
    -- carry it here.  Without it `substituteExistentials` leaves the
    -- EXISTS pattern in place and the filter drops every row (regression
    -- found 2026-09-02 by tools/w3c-persisted-census.sh: FILTER NOT EXISTS
    -- answered zero rows).  With no FROM clause (the only case the backend
    -- path takes) the query's dataset is `ds` itself.
    let env : EvalEnv := { base := q.base, ext := L4Factoidal.Geo.extFns, dataset := some ds }
    let backendEligible := q.dataset.isEmpty
    match q.form with
    | .ask =>
        let b := match (if backendEligible then runAskQueryBackendDataset env q dsb else none) with
          | some answer => answer
          | none => evalAsk env ds q
        okWith [("kind", .string "ask"), ("boolean", .bool b)]
    | .select sel =>
        let (vars, rows) :=
          match (if backendEligible then runSelectQueryBackendDataset env q dsb else none) with
          | some rows =>
              let vars := match sel with
                | .vars items => selectItemVars items
                | .all        => collectVarsInOrder rows
              (vars, rows)
          | none => evalSelect env ds q
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

/-- The `queryDataset` envelope family over an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetQuery`
(`Wasm/Ops/Handles.lean`), so both answer byte-identical envelopes.  The
stateless form indexes the dataset for this one call. -/
def queryParsedDataset (ds : Dataset) (sparql : String) : String :=
  queryParsedDatasetWith ds (indexedDatasetBackend ds) sparql

/-- `queryDataset(nquads, sparql)`. The N-Quads argument is read in
RDF 1.2 mode: the engine's own ops emit RDF 1.2 canonical N-Quads,
including `<<( … )>>` triple terms, so the query op must read back
what the op family writes. RDF 1.2 N-Quads is a superset of the 1.1
grammar; `Mode.rdf11` stays the default everywhere else. -/
def queryDataset (nq sparql : String) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => queryParsedDataset ds sparql

/-- Parse and apply a SPARQL Update to an ALREADY-PARSED dataset —
shared by the stateless op below and the handle op `datasetUpdate`
(`Wasm/Ops/Handles.lean`). The error strings are the envelope error
texts both ops answer. -/
def applyUpdateText (ds : Dataset) (updateText : String) :
    Except String Dataset :=
  match parseSparqlUpdate updateText with
  | .error e => .error s!"SPARQL update parse error: {fmtParseError e}"
  | .ok u =>
  match applyUpdate ds u with
  | .error e  => .error (toString e)
  | .ok ds'   => .ok ds'

/-- `updateDataset(nquads, sparqlUpdate)`. RDF 1.2 read mode for the
same reason as `queryDataset` above: the stateless pair must accept
its own canonical N-Quads output. -/
def updateDataset (nq updateText : String) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
  match applyUpdateText ds updateText with
  | .error e  => errJson e
  | .ok ds'   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds'))]

end L4Wasm.Ops
