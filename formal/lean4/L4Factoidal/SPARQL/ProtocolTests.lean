/-
L4Factoidal.SPARQL.ProtocolTests — build-time `#guard`s for the
protocol-shaped modules: one per decoding rule of SPARQL 1.1 Protocol
§2.1 / §2.2, the percent-decoding cases, the Graph Store state
machine and target decoding, and the Service Description checks.

The request shapes below are the ones the W3C `sparql11/protocol`
manifest uses (copied from its `rdfs:comment` blocks), so a rule that
regresses fails the build at a named line. Not a conformance score:
the real manifests are read only by `lake exe l4w3c` (iron rule #6).

A wrong answer here is a BUILD ERROR: `#guard` evaluates during
elaboration.
-/
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.SPARQL.GraphStore
import L4Factoidal.SPARQL.ServiceDescription

namespace L4Factoidal.SPARQL.ProtocolTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.GraphStore
open L4Factoidal.SPARQL.ServiceDescription

/-! ## Percent-decoding (RFC 3986 §2.1; form `+`) -/

#guard urlDecode "SELECT%20%2A%20WHERE%20%7B%3Fs%20%3Fp%20%3Fo%7D" == "SELECT * WHERE {?s ?p ?o}"
-- `+` is literal under URL decoding and a space under form decoding.
#guard urlDecode "a+b" == "a+b"
#guard formDecode "a+b" == "a b"
-- Lower-case hex digits decode too.
#guard urlDecode "%7b%7d" == "{}"
-- A `%` not followed by two hex digits is kept literally.
#guard urlDecode "100%" == "100%"
#guard urlDecode "%2" == "%2"
#guard urlDecode "%G1x" == "%G1x"
-- `%%41`: the first `%` is literal, then `%41` is `A`.
#guard urlDecode "%%41" == "%A"
-- Escaped UTF-8 bytes reassemble into one character (2, 3, 4 bytes).
#guard urlDecode "caf%C3%A9" == "café"
#guard urlDecode "%E2%82%AC" == "€"
#guard urlDecode "%F0%9F%98%80" == "😀"
-- An escape run that is not UTF-8 falls back to one codepoint per byte.
#guard urlDecode "%E9" == "é"
-- A literal non-ASCII character is untouched, escaped or not around it.
#guard urlDecode "é%20x" == "é x"
-- Encoding round trips (the theorem covers ASCII; these pin the rest).
#guard percentEncode "a b/c?d=e&f" == "a%20b%2Fc%3Fd%3De%26f"
#guard percentEncode "-._~AZaz09" == "-._~AZaz09"
#guard percentEncode "café" == "caf%C3%A9"
#guard urlDecode (percentEncode "ASK { <http://x/é> ?p \"a+b\" }") == "ASK { <http://x/é> ?p \"a+b\" }"

/-! ## Query-string parsing (Protocol §2.1.1 parameter bag) -/

#guard parseQueryString "a=1&b=hello+world&a=2" == [("a", "1"), ("b", "hello world"), ("a", "2")]
#guard parseQueryString "" == []
#guard parseQueryString "flag&k=v" == [("flag", ""), ("k", "v")]
#guard collectValues "a" (parseQueryString "a=1&b=2&a=3") == ["1", "3"]
#guard firstValue "b" (parseQueryString "a=1&b=2") == some "2"
#guard firstValue "z" (parseQueryString "a=1&b=2") == none
#guard splitOnce "k=v=w" '=' == ("k", some "v=w")
#guard splitOnce "kv" '=' == ("kv", none)

/-! ## Content-Type handling -/

#guard contentTypeBase "Application/SPARQL-Query; charset=utf-8" == "application/sparql-query"
#guard extractCharsetParam "application/sparql-query; charset=UTF-16" == some "utf-16"
#guard extractCharsetParam "application/sparql-query" == none
#guard charsetIsUtf8OrAbsent "application/sparql-query; charset=UTF-8" == true
#guard charsetIsUtf8OrAbsent "application/sparql-query; Charset = utf8" == true -- `Charset =` is not a `charset=` parameter: absent, so UTF-8
#guard charsetIsUtf8OrAbsent "application/sparql-update; charset=UTF-16" == false
#guard pathIsUpdate "/sparql/update" == true
#guard pathIsUpdate "/sparql/UPDATE" == true
#guard pathIsUpdate "/sparql/" == false
#guard splitPathQs "/sparql?query=x" == ("/sparql", "query=x")

/-! ## USING / WITH detection (§2.2.4) -/

#guard updateHasDatasetClause "WITH <g> DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }" == true
#guard updateHasDatasetClause "DELETE { ?s ?p ?o } USING <g> WHERE { ?s ?p ?o }" == true
#guard updateHasDatasetClause "INSERT DATA { <a> <b> <c> }" == false
-- A prefix match not bounded by whitespace does not count, and does not
-- stop the scan (the F* divergence noted in the module header).
#guard updateHasDatasetClause "INSERT DATA { <withdraw> <b> <c> }" == false
#guard updateHasDatasetClause "INSERT { <withdraw> <b> <c> } USING <g> WHERE {}" == true

/-! ## decodeRequest — the W3C `sparql11/protocol` request shapes

Positive tests (2xx expected): the decoder accepts. -/

-- query_post_form: POST, form-encoded `query=ASK%20%7B%7D`.
#guard decodeRequest "POST" "/sparql/" "" "application/x-www-form-urlencoded" "query=ASK%20%7B%7D"
       == .query "ASK {}" [] []
-- query_get: GET with the query in the URL.
#guard decodeRequest "GET" "/sparql" "query=ASK%20%7B%7D" "" "" == .query "ASK {}" [] []
-- query_dataset_default_graphs_get: repeated default-graph-uri.
#guard decodeRequest "GET" "/sparql"
         "query=ASK%20%7B%7D&default-graph-uri=http%3A%2F%2Fkasei.us%2F2009%2F09%2Fsparql%2Fdata%2Fdata1.rdf&default-graph-uri=http%3A%2F%2Fkasei.us%2F2009%2F09%2Fsparql%2Fdata%2Fdata2.rdf"
         "" ""
       == .query "ASK {}" ["http://kasei.us/2009/09/sparql/data/data1.rdf",
                           "http://kasei.us/2009/09/sparql/data/data2.rdf"] []
-- query_dataset_named_graphs_post: named-graph-uri in a form body.
#guard decodeRequest "POST" "/sparql" "" "application/x-www-form-urlencoded"
         "query=ASK%20%7B%7D&named-graph-uri=http%3A%2F%2Fa%2F&named-graph-uri=http%3A%2F%2Fb%2F"
       == .query "ASK {}" [] ["http://a/", "http://b/"]
-- query_post_direct: the body is the query.
#guard decodeRequest "POST" "/sparql/" "" "application/sparql-query" "ASK {}" == .query "ASK {}" [] []
-- A charset parameter of UTF-8 is accepted.
#guard decodeRequest "POST" "/sparql/" "" "application/sparql-query; charset=utf-8" "ASK {}"
       == .query "ASK {}" [] []
-- update_post_form: `update=` in a form body decides UPDATE even on /sparql/.
#guard decodeRequest "POST" "/sparql/" "" "application/x-www-form-urlencoded" "update=CLEAR%20ALL"
       == .update "CLEAR ALL" [] []
-- update_post_direct.
#guard decodeRequest "POST" "/sparql/" "" "application/sparql-update" "CLEAR ALL" == .update "CLEAR ALL" [] []
-- update_dataset_default_graph: using-graph-uri in the URL, direct body.
#guard decodeRequest "POST" "/sparql" "using-graph-uri=http%3A%2F%2Fkasei.us%2Fdata1.rdf"
         "application/sparql-update" "CLEAR ALL"
       == .update "CLEAR ALL" [] []
-- A path ending in /update with update= in the form body.
#guard decodeRequest "POST" "/sparql/update" "" "application/x-www-form-urlencoded" "update=CLEAR%20ALL"
       == .update "CLEAR ALL" [] []
-- The method is matched case-insensitively.
#guard decodeRequest "get" "/sparql" "query=ASK%20%7B%7D" "" "" == .query "ASK {}" [] []

/-! Negative tests (4xx expected): the decoder rejects, naming the rule. -/

-- bad_query_method: PUT.
#guard (decodeRequest "PUT" "/sparql" "query=ASK%20%7B%7D" "" "").isBad
-- bad_multiple_queries (§2.1.4).
#guard decodeRequest "GET" "/sparql" "query=ASK%20%7B%7D&query=SELECT%20%2A%20%7B%7D" "" ""
       == .bad "more than one query= parameter (Protocol 2.1.4)"
-- bad_query_wrong_media_type.
#guard decodeRequest "POST" "/sparql/" "" "text/plain" "ASK {}" == .bad "unsupported Content-Type: text/plain"
-- bad_query_missing_form_type / bad_query_missing_direct_type: no Content-Type.
#guard decodeRequest "POST" "/sparql/" "" "" "query=ASK%20%7B%7D" == .bad "POST request missing Content-Type"
#guard decodeRequest "POST" "/sparql/" "" "" "ASK {}" == .bad "POST request missing Content-Type"
-- bad_query_non_utf8 (§2.1.6).
#guard decodeRequest "POST" "/sparql/" "" "application/sparql-query; charset=UTF-16" "ASK {}"
       == .bad "non-UTF-8 charset rejected per Protocol 2.1.6"
-- bad_update_get (§2.2.2).
#guard decodeRequest "GET" "/sparql" "update=CLEAR%20ALL" "" "" == .bad "UPDATE invoked via GET (Protocol 2.2.2)"
-- bad_multiple_updates (§2.2.4).
#guard decodeRequest "POST" "/sparql/" "" "application/x-www-form-urlencoded"
         "update=CLEAR%20NAMED&update=CLEAR%20DEFAULT"
       == .bad "more than one update= parameter (Protocol 2.2.4)"
-- bad_update_wrong_media_type.
#guard decodeRequest "POST" "/sparql/" "" "text/plain" "CLEAR NAMED" == .bad "unsupported Content-Type: text/plain"
-- bad_update_missing_form_type.
#guard decodeRequest "POST" "/sparql/" "" "" "update=CLEAR%20NAMED" == .bad "POST request missing Content-Type"
-- bad_update_non_utf8.
#guard decodeRequest "POST" "/sparql/" "" "application/sparql-update; charset=UTF-16" "CLEAR NAMED"
       == .bad "non-UTF-8 charset rejected per Protocol 2.1.6"
-- bad_update_dataset_conflict (§2.2.4): using-graph-uri + USING in the text.
#guard decodeRequest "POST" "/sparql/" "" "application/x-www-form-urlencoded"
         "using-graph-uri=http%3A%2F%2Fexample%2Fpeople&update=DELETE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D%20USING%20%3Chttp%3A%2F%2Fexample%2Faddresses%3E%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D"
       == .bad "using-graph-uri/using-named-graph-uri form params conflict with USING/WITH in update text (Protocol 2.2.4)"
-- Both query= and update= on one request.
#guard decodeRequest "POST" "/sparql/" "" "application/x-www-form-urlencoded" "query=ASK%20%7B%7D&update=CLEAR%20ALL"
       == .bad "both query= and update= present (Protocol 2.2.4)"
-- GET with no query parameter at all.
#guard decodeRequest "GET" "/sparql" "" "" "" == .bad "missing query parameter"
#guard decodeRequest "GET" "/sparql/update" "" "" "" == .bad "missing update parameter"
-- query= sent to an /update path.
#guard decodeRequest "GET" "/sparql/update" "query=ASK%20%7B%7D" "" ""
       == .bad "expected update= on /update endpoint, got query="
-- HEAD / OPTIONS / DELETE.
#guard (decodeRequest "HEAD" "/sparql" "query=ASK%20%7B%7D" "" "").isBad
#guard (decodeRequest "DELETE" "/sparql" "query=ASK%20%7B%7D" "" "").isBad

/-! ## Test-manifest scrapers (the W3C `rdfs:comment` block shape) -/

/-- `query_post_form`'s comment, verbatim shape (4-space indented block). -/
def sampleComment : String := String.intercalate "\n"
  [ "",
    "#### Request",
    "",
    "    POST /sparql/ HTTP/1.1",
    "    Host: www.example",
    "    User-agent: sparql-client/0.1",
    "    Content-Type: application/x-www-form-urlencoded",
    "    Content-Length: XXX",
    "",
    "    query=ASK%20%7B%7D",
    "    ",
    "#### Response",
    "",
    "    2xx or 3xx response",
    "    Content-Type: application/sparql-results+xml or application/sparql-results+json",
    "",
    "    true",
    "       " ]

#guard (extractRequest sampleComment).map (·.method) == some "POST"
#guard (extractRequest sampleComment).map (·.path) == some "/sparql/"
#guard (extractRequest sampleComment).map (·.qs) == some ""
#guard (extractRequest sampleComment).map (·.body) == some "query=ASK%20%7B%7D"
#guard (extractRequest sampleComment).map (fun r => header r.headers "Content-Type")
       == some "application/x-www-form-urlencoded"
#guard (extractRequest sampleComment).map (fun r => header r.headers "host") == some "www.example"
#guard (extractRequest sampleComment).map (fun r => header r.headers "accept") == some ""
#guard extractStatusClass sampleComment == .s2or3

/-- `bad_query_method`: a 2-token request line with trailing spaces and
no headers. -/
def sampleBad : String := String.intercalate "\n"
  [ "", "#### Request", "", "    PUT /sparql?query=ASK%20%7B%7D            ", "    ",
    "#### Response", "", "    4xx", "       " ]

#guard (extractRequest sampleBad).map (·.method) == some "PUT"
#guard (extractRequest sampleBad).map (·.path) == some "/sparql"
#guard (extractRequest sampleBad).map (·.qs) == some "query=ASK%20%7B%7D"
#guard (extractRequest sampleBad).map (·.headers) == some []
#guard (extractRequest sampleBad).map (·.body) == some ""
#guard extractStatusClass sampleBad == .s4xx
#guard extractStatusClass "no response block" == .unknown
#guard extractRequest "no request block" == none

/-- A multi-line body, and a second `#### Request` block that must be
ignored (the update-then-ASK entries). -/
def sampleTwoBlocks : String := String.intercalate "\n"
  [ "#### Request", "", "    POST /sparql HTTP/1.1", "    Host: www.example",
    "    Content-Type: application/sparql-update", "",
    "    CLEAR ALL ;", "    INSERT DATA {", "        <a> <b> <c>", "    }", "",
    "#### Response", "", "    2xx or 3xx response", "", "followed by", "",
    "#### Request", "", "    POST /sparql HTTP/1.1", "", "    ASK {}", "",
    "#### Response", "", "    4xx" ]

#guard (extractRequest sampleTwoBlocks).map (·.body)
       == some "CLEAR ALL ;\nINSERT DATA {\n    <a> <b> <c>\n}"
-- Both Response blocks are scanned (4xx is found in the second), as in the F*.
#guard extractStatusClass sampleTwoBlocks == .s4xx

/-- A Graph Store entry: numeric status, two blank lines after the heading. -/
def sampleGsp : String := String.intercalate "\n"
  [ "", "#### Request", "", "",
    "    PUT $GRAPHSTORE$/person/1.ttl HTTP/1.1", "    Host: $HOST$",
    "    Content-Type: text/turtle; charset=utf-8", "",
    "    @prefix foaf: <http://xmlns.com/foaf/0.1/> .", "",
    "    <http://$HOST$/$GRAPHSTORE$/person/1> a foaf:Person .", "",
    "#### Response", "", "    201 Created", "    " ]

#guard (extractRequest sampleGsp).map (·.method) == some "PUT"
#guard (extractRequest sampleGsp).map (·.path) == some "$GRAPHSTORE$/person/1.ttl"
#guard (extractRequest sampleGsp).map (·.body)
       == some "@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n\n<http://$HOST$/$GRAPHSTORE$/person/1> a foaf:Person ."
#guard extractResponseStatus sampleGsp == some 201
#guard extractResponseStatus "#### Response\n\n    404 Not Found\n" == some 404
#guard extractResponseStatus "#### Response\n\n    200\n" == some 200
#guard extractResponseStatus "#### Response\n\n    2xx or 3xx response\n" == none
#guard extractResponseStatus "#### Response\n\n    Content-Length: 1234 bytes\n    200 OK\n" == some 200

#guard stripIndent "    x" == "x"
#guard stripIndent "      x" == "  x"
#guard stripIndent "\tx" == "x"
#guard stripIndent "  \tx" == "x" -- a tab after spaces is consumed and stops the scan
#guard stripIndent "x" == "x"

/-! ## Graph Store state machine (GSP §5) -/

def exTriple : Triple :=
  { s := .iri ⟨"http://example/s", rfl⟩, p := ⟨"http://example/p", rfl⟩, o := .iri ⟨"http://example/o", rfl⟩ }
def exTriple2 : Triple :=
  { s := .iri ⟨"http://example/s", rfl⟩, p := ⟨"http://example/p", rfl⟩, o := .iri ⟨"http://example/o2", rfl⟩ }

-- PUT creates (201) then replaces (204); GET/HEAD see it; DELETE 204 then 404.
#guard (handle .put (.named "/g") [exTriple] {}).2 == 201
#guard (handle .put (.named "/g") [exTriple2] (handle .put (.named "/g") [exTriple] {}).1).2 == 204
#guard (handle .put (.named "/g") [exTriple2] (handle .put (.named "/g") [exTriple] {}).1).1.named
       == [("/g", [exTriple2])]
#guard (handle .get (.named "/g") [] (handle .put (.named "/g") [exTriple] {}).1).2 == 200
#guard (handle .get (.named "/h") [] (handle .put (.named "/g") [exTriple] {}).1).2 == 404
#guard (handle .head (.named "/g") [] (handle .put (.named "/g") [exTriple] {}).1).2 == 200
#guard (handle .head (.named "/h") [] {}).2 == 404
#guard (handle .delete (.named "/g") [] (handle .put (.named "/g") [exTriple] {}).1).2 == 204
#guard (handle .delete (.named "/g") [] {}).2 == 404
-- POST creates (201) or merges (200); the merge keeps both triples.
#guard (handle .post (.named "/g") [exTriple] {}).2 == 201
#guard (handle .post (.named "/g") [exTriple2] (handle .put (.named "/g") [exTriple] {}).1).2 == 200
#guard ((handle .post (.named "/g") [exTriple2] (handle .put (.named "/g") [exTriple] {}).1).1.named.map
          (fun kg => kg.2.length)) == [2]
-- The default graph: GET/HEAD 404 while empty, 200 once PUT; PUT on empty is 201.
#guard (handle .get .default [] {}).2 == 404
#guard (handle .put .default [exTriple] {}).2 == 201
#guard (handle .get .default [] (handle .put .default [exTriple] {}).1).2 == 200
#guard (handle .delete .default [] (handle .put .default [exTriple] {}).1).2 == 204
#guard (get .default {}) == some []
-- PATCH is not implemented: 405.
#guard (handle .patch (.named "/g") [] {}).2 == 405
#guard Method.ofString "delete" == some .delete
#guard Method.ofString "TRACE" == none

/-! ## Graph identification (GSP §4.1) -/

def isDefault : Except Nat Target → Bool
  | .ok .default => true
  | _ => false
def namedKey : Except Nat Target → Option String
  | .ok (.named k) => some k
  | _ => none
def errorCode : Except Nat Target → Option Nat
  | .error n => some n
  | _ => none

#guard isDefault (decodeTarget "/store" "default")
#guard isDefault (decodeTarget "/store" "default=")
#guard namedKey (decodeTarget "/store" "graph=http%3A%2F%2Fexample%2Fg") == some "http://example/g"
#guard namedKey (decodeTarget "$GRAPHSTORE$" "graph=http://$HOST$/$GRAPHSTORE$/person/1.ttl")
       == some "http://$HOST$/$GRAPHSTORE$/person/1.ttl"
#guard namedKey (decodeTarget "/person/1.ttl" "") == some "/person/1.ttl"
-- Malformed indirect identification: empty, or no scheme colon → 400.
#guard errorCode (decodeTarget "/store" "graph=") == some 400
#guard errorCode (decodeTarget "/store" "graph=not-an-iri") == some 400

/-! ## Service Description (§4) -/

def endpoint : WfIri := ⟨"http://localhost:3030/sparql", rfl⟩

#guard returnsRdf (buildSd endpoint)
#guard hasEndpointTriple endpoint (buildSd endpoint)
#guard conformsToSchema endpoint (buildSd endpoint)
#guard (buildSd endpoint).length == 17
#guard hasEndpointTriple ⟨"http://other/sparql", rfl⟩ (buildSd endpoint) == false
#guard conformsToSchema endpoint [] == false
#guard (datasetIriOf endpoint).val == "http://localhost:3030/sparql#dataset"

end L4Factoidal.SPARQL.ProtocolTests
