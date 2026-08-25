/-
Wasm.Ops.CL — clParse / clToDataset / queryWithIklService.

The Common Logic / IKL ops (L4Factoidal/CL/, issue 580):

  clParse(cliftext)
    -> {"ok":true,"sentences":N,"pureCL":true|false,"normalized":"…"}
     | {"ok":false,"error":"…"}
  clToDataset(cliftext, base)
    -> {"ok":true,"count":N,"skipped":M,"nquads":"…"}
     | {"ok":false,"error":"…"}
  queryWithIklService(dataNq, cliftext, sparql)
    -> the queryDataset envelope family (select/ask/construct)

`clParse` reads a whole CLIF text (zero or more sentences) and returns
the sentence count, whether the text is pure ISO/IEC 24707 CL (no IKL
`that`), and the canonical re-serialisation, newline-separated.

`clToDataset` is the CL→RDF bridge (`CL/ToRdf.lean`, graph-decoration
translation — issue 581): names become IRIs under the caller's base;
EVERY top-level sentence (a top-level `and` included — one sentence,
one proposition) becomes a NAMED GRAPH named
`<base>that:sha256:<hex64>` — the content address of the
alpha-normalized canonical CLIF (issue 589), holding the sentence
text under `urn:cl:def:sentence` plus its translatable atoms — and
the default graph holds only DECORATIONS (`urn:cl:def:asserts`
assertion triples, link triples for predications about propositions,
and `urn:cl:def:rdfProjection` triple-term projections for
single-atom propositions; `rdf:reifies` is deliberately unused —
reserved for future report/occurrence nodes, see `CL/ToRdf.lean`).
The returned N-Quads carry the graph names, and RDF 1.2 `<<( … )>>`
triple terms where projections were emitted. `count` counts
graph-content triples PLUS decorations (sentence records excluded);
`skipped` the sentences/conjuncts outside the fragment — reported,
never silently dropped.

`queryWithIklService` is the combination op: the SPARQL query runs
over `dataNq`'s dataset, with

  * the SERVICE endpoint IRI `urn:ikl:kb` (SPARQL 1.1 Federated Query
    §2) bound in `EvalEnv.services` to the translation's DEFAULT
    graph (the decorations) unioned with the content of every
    ASSERTED proposition graph — the same rule the `x-ikl-*` regime
    applies (`CL.IklRegime.extendDataset`, issue 581). So
    `SERVICE <urn:ikl:kb> { … }` matches what the CL text SAYS —
    assertions, links and projections, plus what its asserted
    propositions claim — while the content of a merely-mentioned
    proposition (`believes`/`ist`/… link, no assertion) stays out;
  * the translation's NAMED graphs merged into the evaluation
    dataset, so `GRAPH ?p { … }` quantifies over every IKL
    proposition (asserted or not) in the same query. The
    translation's default-graph triples stay OUT of the evaluation
    default graph — they are reachable through the SERVICE pattern,
    keeping the user's data and the IKL-derived knowledge
    distinguishable.

The CL translation base is fixed at `urn:cl:` for this op (the
documented mapping in `CL/ToRdf.lean`).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.CL.Clif
import L4Factoidal.CL.ToRdf
import L4Factoidal.CL.IklRegime
import L4Factoidal.Syntax.NQuads
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Results
import L4Factoidal.SPARQL.ResultsJson

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.SPARQL
open L4Factoidal.JSON

/-- The SERVICE endpoint IRI `queryWithIklService` serves. -/
def iklServiceIri : String := "urn:ikl:kb"

/-- The name→IRI base the service op translates under. -/
def iklServiceBase : String := "urn:cl:"

/-- `clParse(cliftext)`. -/
def clParse (cliftext : String) : String :=
  match L4Factoidal.CL.parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      okWith
        [ ("sentences", .number (toString ss.length))
        , ("pureCL", .bool (L4Factoidal.CL.sentencesPureCL ss))
        , ("normalized", .string (String.intercalate "\n"
            (ss.map L4Factoidal.CL.Sentence.toClif))) ]

/-- `clToDataset(cliftext, base)`. `count` is graph-content triples
plus default-graph decorations (asserts / link / projection); sentence
records are not counted (`CL/ToRdf.lean`, module header). -/
def clToDataset (cliftext base : String) : String :=
  match L4Factoidal.CL.parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      match L4Factoidal.CL.toRdfDataset base ss with
      | .error msg => errJson msg
      | .ok r =>
          okWith
            [ ("count", .number (toString r.count))
            , ("skipped", .number (toString r.skipped))
            , ("nquads", .string (Dataset.toCanonicalNQuads r.ds)) ]

/-- The SERVICE endpoint's graph: the translation's default graph
(the decorations) unioned with the content of every ASSERTED
proposition graph — computed by the SAME rule the `x-ikl-*` regime
applies to a dataset (`CL.IklRegime.extendDataset`, issue 581), so
the SERVICE view and the regime cannot drift apart. -/
private def serviceView (ds : Dataset) : Graph :=
  ((L4Factoidal.CL.IklRegime.mk "").extendDataset ds).default

/-- `queryWithIklService(dataNq, cliftext, sparql)`. -/
def queryWithIklService (dataNq cliftext sparql : String) : String :=
  match parseNQuads dataNq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
  match L4Factoidal.CL.parseClifText cliftext with
  | .error e => errJson s!"CLIF parse error: {fmtParseError e}"
  | .ok ss =>
  match L4Factoidal.CL.toRdfDataset iklServiceBase ss with
  | .error msg => errJson msg
  | .ok r =>
  match parseSparql sparql with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok q =>
    -- IKL propositions are named graphs of the evaluation dataset;
    -- the decorations + asserted content are the `urn:ikl:kb`
    -- SERVICE graph (see the module header).
    let dsEval : Dataset := { ds with named := ds.named ++ r.ds.named }
    let env : EvalEnv :=
      { base := q.base
        services := [(iklServiceIri, serviceView r.ds)] }
    match q.form with
    | .ask =>
        let b := evalAsk env dsEval q
        okWith [("kind", .string "ask"), ("boolean", .bool b)]
    | .select _ =>
        let (vars, rows) := evalSelect env dsEval q
        let srj := QueryResult.toSrj (.bindings vars rows)
        -- srj is a JSON object document; splice it in verbatim.
        "{\"ok\":true,\"kind\":\"select\",\"srj\":" ++ srj ++ "}"
    | .construct _ =>
        let g := evalConstruct env dsEval q
        match Graph.toNTriples g with
        | .error e  => errJson s!"construct serialisation: {e}"
        | .ok lines => okWith [("kind", .string "construct"),
                               ("nquads", .string lines)]
    | .describe _ =>
        errJson "DESCRIBE is not supported by the npm entry yet"

end L4Wasm.Ops
