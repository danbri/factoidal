open Prims
let sd_ns : Prims.string= "http://www.w3.org/ns/sparql-service-description#"
let sd_Service : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#Service"
let sd_endpoint : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#endpoint"
let sd_supportedLanguage : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#supportedLanguage"
let sd_resultFormat : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#resultFormat"
let sd_feature : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#feature"
let sd_defaultDataset : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#defaultDataset"
let sd_Dataset : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#Dataset"
let sd_defaultGraph : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#defaultGraph"
let sd_Graph : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#Graph"
let sd_SPARQL10Query : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#SPARQL10Query"
let sd_SPARQL11Query : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#SPARQL11Query"
let sd_SPARQL11Update : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#SPARQL11Update"
let sd_BasicFederatedQuery : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#BasicFederatedQuery"
let sd_DereferencesURIs : RDF_Term.wf_iri=
  "http://www.w3.org/ns/sparql-service-description#DereferencesURIs"
let formats_ns : Prims.string= "http://www.w3.org/ns/formats/"
let fmt_SPARQL_Results_XML : RDF_Term.wf_iri=
  "http://www.w3.org/ns/formats/SPARQL_Results_XML"
let fmt_SPARQL_Results_JSON : RDF_Term.wf_iri=
  "http://www.w3.org/ns/formats/SPARQL_Results_JSON"
let fmt_SPARQL_Results_CSV : RDF_Term.wf_iri=
  "http://www.w3.org/ns/formats/SPARQL_Results_CSV"
let fmt_SPARQL_Results_TSV : RDF_Term.wf_iri=
  "http://www.w3.org/ns/formats/SPARQL_Results_TSV"
let fmt_Turtle : RDF_Term.wf_iri= "http://www.w3.org/ns/formats/Turtle"
let fmt_N_Triples : RDF_Term.wf_iri= "http://www.w3.org/ns/formats/N-Triples"
let fmt_RDF_XML : RDF_Term.wf_iri= "http://www.w3.org/ns/formats/RDF_XML"
let mk_triple_iri (s_iri : RDF_Term.wf_iri) (p_iri : RDF_Term.wf_iri)
  (o_iri : RDF_Term.wf_iri) : RDF_Triple.triple=
  {
    RDF_Triple.s = (RDF_Term.S_IRI s_iri);
    RDF_Triple.p = p_iri;
    RDF_Triple.o = (RDF_Term.T_IRI o_iri)
  }
let dataset_iri_of (endpoint : RDF_Term.wf_iri) : RDF_Term.wf_iri=
  let raw = Prims.strcat endpoint "#dataset" in
  if RDF_Term.is_iri raw then raw else endpoint
let default_graph_iri_of (endpoint : RDF_Term.wf_iri) : RDF_Term.wf_iri=
  let raw = Prims.strcat endpoint "#default-graph" in
  if RDF_Term.is_iri raw then raw else endpoint
let build_sd (endpoint : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  let ds = dataset_iri_of endpoint in
  let dg = default_graph_iri_of endpoint in
  [mk_triple_iri endpoint RDFS_Closure.rdf_type sd_Service;
  mk_triple_iri endpoint sd_endpoint endpoint;
  mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL11Query;
  mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL11Update;
  mk_triple_iri endpoint sd_supportedLanguage sd_SPARQL10Query;
  mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_XML;
  mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_JSON;
  mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_CSV;
  mk_triple_iri endpoint sd_resultFormat fmt_SPARQL_Results_TSV;
  mk_triple_iri endpoint sd_resultFormat fmt_Turtle;
  mk_triple_iri endpoint sd_resultFormat fmt_N_Triples;
  mk_triple_iri endpoint sd_resultFormat fmt_RDF_XML;
  mk_triple_iri endpoint sd_feature sd_BasicFederatedQuery;
  mk_triple_iri endpoint sd_defaultDataset ds;
  mk_triple_iri ds RDFS_Closure.rdf_type sd_Dataset;
  mk_triple_iri ds sd_defaultGraph dg;
  mk_triple_iri dg RDFS_Closure.rdf_type sd_Graph]
let rec has_endpoint_triple (e : RDF_Term.wf_iri) (g : RDF_Graph.rdf_graph) :
  Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
       | (RDF_Term.S_IRI si, RDF_Term.T_IRI oi) ->
           if ((t.RDF_Triple.p = sd_endpoint) && (si = e)) && (oi = e)
           then true
           else has_endpoint_triple e rest
       | uu___ -> has_endpoint_triple e rest)
let rec has_service_type (e : RDF_Term.wf_iri) (g : RDF_Graph.rdf_graph) :
  Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
       | (RDF_Term.S_IRI si, RDF_Term.T_IRI oi) ->
           if
             ((t.RDF_Triple.p = RDFS_Closure.rdf_type) && (si = e)) &&
               (oi = sd_Service)
           then true
           else has_service_type e rest
       | uu___ -> has_service_type e rest)
let rec has_supported_language (e : RDF_Term.wf_iri)
  (g : RDF_Graph.rdf_graph) : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      (match t.RDF_Triple.s with
       | RDF_Term.S_IRI si ->
           if (t.RDF_Triple.p = sd_supportedLanguage) && (si = e)
           then true
           else has_supported_language e rest
       | uu___ -> has_supported_language e rest)
let conforms_to_schema (e : RDF_Term.wf_iri) (g : RDF_Graph.rdf_graph) :
  Prims.bool=
  ((has_service_type e g) && (has_endpoint_triple e g)) &&
    (has_supported_language e g)
let returns_rdf (g : RDF_Graph.rdf_graph) : Prims.bool=
  match g with | [] -> false | uu___ -> true
let _smoke_endpoint : RDF_Term.wf_iri= "http://localhost:3030/sparql"
let _test_returns_rdf : Prims.bool= returns_rdf (build_sd _smoke_endpoint)
let _test_endpoint : Prims.bool=
  has_endpoint_triple _smoke_endpoint (build_sd _smoke_endpoint)
let _test_conformance : Prims.bool=
  conforms_to_schema _smoke_endpoint (build_sd _smoke_endpoint)
