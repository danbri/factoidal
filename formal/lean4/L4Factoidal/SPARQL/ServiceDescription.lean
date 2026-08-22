/-
L4Factoidal.SPARQL.ServiceDescription — SPARQL 1.1 Service Description
(W3C Recommendation, §4). Port of
`formal/fstar/SPARQL.ServiceDescription.fst`.

Spec: https://www.w3.org/TR/sparql11-service-description/

`buildSd` constructs the RDF graph that describes an endpoint, given
the endpoint IRI: the endpoint is the `sd:Service` subject (§4.1),
with `sd:endpoint` (§4.2.1), `sd:supportedLanguage` (§4.2.3),
`sd:resultFormat` (§4.2.5), `sd:feature` (§4.2.2) and
`sd:defaultDataset` → `sd:Dataset` → `sd:defaultGraph` → `sd:Graph`
(§4.2.6, §4.3, §4.4, §4.5). The dataset and graph subjects are IRIs
derived from the endpoint (`#dataset`, `#default-graph`) rather than
blank nodes, as in the F*, so the description is IRI-keyed.

The three checks are the W3C `service-description` suite's structural
conformance tests, which ship no query or data files — only names:
`returnsRdf` (non-empty), `hasEndpointTriple` (`<e> sd:endpoint <e>`),
`conformsToSchema` (rdf:type sd:Service, an sd:endpoint, at least one
sd:supportedLanguage).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.SPARQL.ServiceDescription

open L4Factoidal.RDF
open L4Factoidal.RDFS (rdfType)

/-! ## sd: vocabulary -/

def sdNs : String := "http://www.w3.org/ns/sparql-service-description#"

def sdService : WfIri := ⟨sdNs ++ "Service", rfl⟩
def sdEndpoint : WfIri := ⟨sdNs ++ "endpoint", rfl⟩
def sdSupportedLanguage : WfIri := ⟨sdNs ++ "supportedLanguage", rfl⟩
def sdResultFormat : WfIri := ⟨sdNs ++ "resultFormat", rfl⟩
def sdFeature : WfIri := ⟨sdNs ++ "feature", rfl⟩
def sdDefaultDataset : WfIri := ⟨sdNs ++ "defaultDataset", rfl⟩
def sdDataset : WfIri := ⟨sdNs ++ "Dataset", rfl⟩
def sdDefaultGraph : WfIri := ⟨sdNs ++ "defaultGraph", rfl⟩
def sdGraph : WfIri := ⟨sdNs ++ "Graph", rfl⟩

/-- Language IRIs (§4.2.3). -/
def sdSPARQL10Query : WfIri := ⟨sdNs ++ "SPARQL10Query", rfl⟩
def sdSPARQL11Query : WfIri := ⟨sdNs ++ "SPARQL11Query", rfl⟩
def sdSPARQL11Update : WfIri := ⟨sdNs ++ "SPARQL11Update", rfl⟩

/-- Feature IRIs (§4.2.2). -/
def sdBasicFederatedQuery : WfIri := ⟨sdNs ++ "BasicFederatedQuery", rfl⟩
def sdDereferencesURIs : WfIri := ⟨sdNs ++ "DereferencesURIs", rfl⟩

/-- Result-format IRIs (`http://www.w3.org/ns/formats/`). -/
def formatsNs : String := "http://www.w3.org/ns/formats/"
def fmtSparqlResultsXml : WfIri := ⟨formatsNs ++ "SPARQL_Results_XML", rfl⟩
def fmtSparqlResultsJson : WfIri := ⟨formatsNs ++ "SPARQL_Results_JSON", rfl⟩
def fmtSparqlResultsCsv : WfIri := ⟨formatsNs ++ "SPARQL_Results_CSV", rfl⟩
def fmtSparqlResultsTsv : WfIri := ⟨formatsNs ++ "SPARQL_Results_TSV", rfl⟩
def fmtTurtle : WfIri := ⟨formatsNs ++ "Turtle", rfl⟩
def fmtNTriples : WfIri := ⟨formatsNs ++ "N-Triples", rfl⟩
def fmtRdfXml : WfIri := ⟨formatsNs ++ "RDF_XML", rfl⟩

/-! ## Builder -/

/-- A triple whose three positions are IRIs. -/
def mkTripleIri (s p o : WfIri) : Triple := { s := .iri s, p := p, o := .iri o }

/-- `<endpoint>#dataset`: a well-formed IRI because the endpoint
already carries the colon `isIri` looks for. -/
def datasetIriOf (endpoint : WfIri) : WfIri :=
  if h : isIri (endpoint.val ++ "#dataset") = true then ⟨_, h⟩ else endpoint

def defaultGraphIriOf (endpoint : WfIri) : WfIri :=
  if h : isIri (endpoint.val ++ "#default-graph") = true then ⟨_, h⟩ else endpoint

/-- The service description graph for `endpoint` (§4). -/
def buildSd (endpoint : WfIri) : Graph :=
  let ds := datasetIriOf endpoint
  let dg := defaultGraphIriOf endpoint
  [ -- <endpoint> a sd:Service
    mkTripleIri endpoint rdfType sdService,
    -- <endpoint> sd:endpoint <endpoint>
    mkTripleIri endpoint sdEndpoint endpoint,
    -- supported languages
    mkTripleIri endpoint sdSupportedLanguage sdSPARQL11Query,
    mkTripleIri endpoint sdSupportedLanguage sdSPARQL11Update,
    mkTripleIri endpoint sdSupportedLanguage sdSPARQL10Query,
    -- result formats
    mkTripleIri endpoint sdResultFormat fmtSparqlResultsXml,
    mkTripleIri endpoint sdResultFormat fmtSparqlResultsJson,
    mkTripleIri endpoint sdResultFormat fmtSparqlResultsCsv,
    mkTripleIri endpoint sdResultFormat fmtSparqlResultsTsv,
    mkTripleIri endpoint sdResultFormat fmtTurtle,
    mkTripleIri endpoint sdResultFormat fmtNTriples,
    mkTripleIri endpoint sdResultFormat fmtRdfXml,
    -- features (basic federated query via SERVICE)
    mkTripleIri endpoint sdFeature sdBasicFederatedQuery,
    -- <endpoint> sd:defaultDataset <ds> ; <ds> a sd:Dataset ;
    -- <ds> sd:defaultGraph <dg> ; <dg> a sd:Graph
    mkTripleIri endpoint sdDefaultDataset ds,
    mkTripleIri ds rdfType sdDataset,
    mkTripleIri ds sdDefaultGraph dg,
    mkTripleIri dg rdfType sdGraph ]

/-! ## Structural checks (the W3C `service-description` suite) -/

/-- Is `<e> sd:endpoint <e>` in `g`? -/
def hasEndpointTriple (e : WfIri) (g : Graph) : Bool :=
  g.any (fun t => t.s == .iri e && t.p == sdEndpoint && t.o == .iri e)

/-- Is `<e> rdf:type sd:Service` in `g`? -/
def hasServiceType (e : WfIri) (g : Graph) : Bool :=
  g.any (fun t => t.s == .iri e && t.p == rdfType && t.o == .iri sdService)

/-- At least one `<e> sd:supportedLanguage ?l`. -/
def hasSupportedLanguage (e : WfIri) (g : Graph) : Bool :=
  g.any (fun t => t.s == .iri e && t.p == sdSupportedLanguage)

/-- Minimum shape per §4: typed sd:Service, an sd:endpoint triple,
a supported language. -/
def conformsToSchema (e : WfIri) (g : Graph) : Bool :=
  hasServiceType e g && hasEndpointTriple e g && hasSupportedLanguage e g

/-- "GET on endpoint returns RDF": the description is non-empty. -/
def returnsRdf (g : Graph) : Bool := !g.isEmpty

end L4Factoidal.SPARQL.ServiceDescription
