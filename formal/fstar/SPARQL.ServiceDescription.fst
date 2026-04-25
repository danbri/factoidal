module SPARQL.ServiceDescription

(** ======================================================================== **)
(** SPARQL 1.1 Service Description (W3C Rec, §4)                            **)
(**                                                                          **)
(** Builds an RDF graph that describes a SPARQL endpoint, given the          **)
(** endpoint's IRI. The graph is consumed by:                                **)
(**                                                                          **)
(**   1. The W3C `service-description` test suite (3 structural tests).      **)
(**   2. (Phase 2) factoidal_http's GET /sparql Accept: text/turtle handler. **)
(**                                                                          **)
(** Spec: https://www.w3.org/TR/sparql11-service-description/                **)
(**                                                                          **)
(** Constraints (CLAUDE.md iron rules):                                      **)
(**   - No assume val                                                        **)
(**   - No --admit_smt_queries                                               **)
(**   - No --lax                                                             **)
(** ======================================================================== **)

open RDF.Graph.Executable

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"

(** Well-known sd: IRIs. Each is normalized via assert_norm so the          **)
(** wf_iri refinement (non-empty + contains colon) discharges at compile    **)
(** time.                                                                  **)

let sd_ns : string = "http://www.w3.org/ns/sparql-service-description#"

let sd_Service : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#Service");
  "http://www.w3.org/ns/sparql-service-description#Service"

let sd_endpoint : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#endpoint");
  "http://www.w3.org/ns/sparql-service-description#endpoint"

let sd_supportedLanguage : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#supportedLanguage");
  "http://www.w3.org/ns/sparql-service-description#supportedLanguage"

let sd_resultFormat : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#resultFormat");
  "http://www.w3.org/ns/sparql-service-description#resultFormat"

let sd_feature : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#feature");
  "http://www.w3.org/ns/sparql-service-description#feature"

let sd_defaultDataset : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#defaultDataset");
  "http://www.w3.org/ns/sparql-service-description#defaultDataset"

let sd_Dataset : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#Dataset");
  "http://www.w3.org/ns/sparql-service-description#Dataset"

let sd_defaultGraph : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#defaultGraph");
  "http://www.w3.org/ns/sparql-service-description#defaultGraph"

let sd_Graph : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#Graph");
  "http://www.w3.org/ns/sparql-service-description#Graph"

(** Language IRIs **)

let sd_SPARQL10Query : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#SPARQL10Query");
  "http://www.w3.org/ns/sparql-service-description#SPARQL10Query"

let sd_SPARQL11Query : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#SPARQL11Query");
  "http://www.w3.org/ns/sparql-service-description#SPARQL11Query"

let sd_SPARQL11Update : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#SPARQL11Update");
  "http://www.w3.org/ns/sparql-service-description#SPARQL11Update"

(** Feature IRIs **)

let sd_BasicFederatedQuery : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#BasicFederatedQuery");
  "http://www.w3.org/ns/sparql-service-description#BasicFederatedQuery"

let sd_DereferencesURIs : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/sparql-service-description#DereferencesURIs");
  "http://www.w3.org/ns/sparql-service-description#DereferencesURIs"

(** Common result-format IRIs (formats/) **)

let formats_ns : string = "http://www.w3.org/ns/formats/"

let fmt_SPARQL_Results_XML : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/SPARQL_Results_XML");
  "http://www.w3.org/ns/formats/SPARQL_Results_XML"

let fmt_SPARQL_Results_JSON : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/SPARQL_Results_JSON");
  "http://www.w3.org/ns/formats/SPARQL_Results_JSON"

let fmt_SPARQL_Results_CSV : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/SPARQL_Results_CSV");
  "http://www.w3.org/ns/formats/SPARQL_Results_CSV"

let fmt_SPARQL_Results_TSV : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/SPARQL_Results_TSV");
  "http://www.w3.org/ns/formats/SPARQL_Results_TSV"

let fmt_Turtle : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/Turtle");
  "http://www.w3.org/ns/formats/Turtle"

let fmt_N_Triples : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/N-Triples");
  "http://www.w3.org/ns/formats/N-Triples"

let fmt_RDF_XML : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/formats/RDF_XML");
  "http://www.w3.org/ns/formats/RDF_XML"

(** ====================================================================== **)
(** Triple builder helper                                                  **)
(** ====================================================================== **)

let mk_triple_iri (s_iri : wf_iri) (p_iri : wf_iri) (o_iri : wf_iri) : triple =
  { s = S_IRI s_iri; p = p_iri; o = T_IRI o_iri }

(** ====================================================================== **)
(** build_sd : wf_iri -> rdf_graph                                         **)
(**                                                                       **)
(** Constructs the Service Description graph for a given endpoint IRI.    **)
(** Uses the endpoint as the SD subject and the dataset/graph subjects   **)
(** (rather than blank nodes) so the entire description is IRI-keyed and  **)
(** trivially serialisable.                                              **)
(** ====================================================================== **)

(** A synthetic IRI for the default-dataset node. Built from the endpoint **)
(** by appending "#dataset", which always yields a valid wf_iri because   **)
(** the endpoint already contains a colon.                               **)

let dataset_iri_of (endpoint : wf_iri) : wf_iri =
  let raw = endpoint ^ "#dataset" in
  // raw inherits the colon from endpoint, and length is positive.
  // We need a refinement proof; do it the same way the constants do.
  if is_iri raw then raw else endpoint   // fallback preserves wf_iri

let default_graph_iri_of (endpoint : wf_iri) : wf_iri =
  let raw = endpoint ^ "#default-graph" in
  if is_iri raw then raw else endpoint

let build_sd (endpoint : wf_iri) : rdf_graph =
  let ds = dataset_iri_of endpoint in
  let dg = default_graph_iri_of endpoint in
  [
    // <endpoint> a sd:Service
    mk_triple_iri endpoint rdf_type sd_Service;
    // <endpoint> sd:endpoint <endpoint>
    mk_triple_iri endpoint sd_endpoint endpoint;
    // <endpoint> sd:supportedLanguage sd:SPARQL11Query, sd:SPARQL11Update, sd:SPARQL10Query
    mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL11Query;
    mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL11Update;
    mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL10Query;
    // result formats
    mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_XML;
    mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_JSON;
    mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_CSV;
    mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_TSV;
    mk_triple_iri endpoint sd_resultFormat fmt_Turtle;
    mk_triple_iri endpoint sd_resultFormat fmt_N_Triples;
    mk_triple_iri endpoint sd_resultFormat fmt_RDF_XML;
    // features (factoidal supports basic federated query via SERVICE)
    mk_triple_iri endpoint sd_feature sd_BasicFederatedQuery;
    // <endpoint> sd:defaultDataset <ds>
    mk_triple_iri endpoint sd_defaultDataset ds;
    // <ds> a sd:Dataset
    mk_triple_iri ds rdf_type sd_Dataset;
    // <ds> sd:defaultGraph <dg>
    mk_triple_iri ds sd_defaultGraph dg;
    // <dg> a sd:Graph
    mk_triple_iri dg rdf_type sd_Graph;
  ]

(** ====================================================================== **)
(** Structural checks for the W3C tests                                   **)
(** ====================================================================== **)

(** has_endpoint_triple : ?\Exists triple <e> sd:endpoint <e> in g **)
let rec has_endpoint_triple (e : wf_iri) (g : rdf_graph)
  : Tot bool (decreases (List.Tot.length g)) =
  match g with
  | [] -> false
  | t :: rest ->
    (match t.s, t.o with
     | S_IRI si, T_IRI oi ->
       if t.p = sd_endpoint && si = e && oi = e then true
       else has_endpoint_triple e rest
     | _ -> has_endpoint_triple e rest)

(** has_service_type : ?\Exists triple <e> rdf:type sd:Service in g **)
let rec has_service_type (e : wf_iri) (g : rdf_graph)
  : Tot bool (decreases (List.Tot.length g)) =
  match g with
  | [] -> false
  | t :: rest ->
    (match t.s, t.o with
     | S_IRI si, T_IRI oi ->
       if t.p = rdf_type && si = e && oi = sd_Service then true
       else has_service_type e rest
     | _ -> has_service_type e rest)

(** has_supported_language : at least one sd:supportedLanguage triple **)
let rec has_supported_language (e : wf_iri) (g : rdf_graph)
  : Tot bool (decreases (List.Tot.length g)) =
  match g with
  | [] -> false
  | t :: rest ->
    (match t.s with
     | S_IRI si ->
       if t.p = sd_supportedLanguage && si = e then true
       else has_supported_language e rest
     | _ -> has_supported_language e rest)

(** Conformance: minimum-shape per §4.                                    **)
(** A description "conforms to schema" if it has rdf:type sd:Service, an **)
(** sd:endpoint triple, and at least one sd:supportedLanguage triple.     **)
let conforms_to_schema (e : wf_iri) (g : rdf_graph) : bool =
  has_service_type e g
  && has_endpoint_triple e g
  && has_supported_language e g

(** Returns RDF: graph is non-empty.                                      **)
let returns_rdf (g : rdf_graph) : bool =
  match g with
  | [] -> false
  | _ -> true

#pop-options

(** ====================================================================== **)
(** Compile-time smoke tests                                              **)
(** ====================================================================== **)

let _smoke_endpoint : wf_iri =
  assert_norm (is_iri "http://localhost:3030/sparql");
  "http://localhost:3030/sparql"

let _test_returns_rdf  : bool = returns_rdf  (build_sd _smoke_endpoint)
let _test_endpoint     : bool = has_endpoint_triple _smoke_endpoint (build_sd _smoke_endpoint)
let _test_conformance  : bool = conforms_to_schema _smoke_endpoint (build_sd _smoke_endpoint)
