(* sparql_protocol_client_unit.ml -- pins SPARQL.Protocol.Client, the
   SPARQL 1.1 Protocol HIGH-LEVEL client module (request construction +
   response dispatch) added this session alongside
   bin/factoidal-http-client/factoidal_http_client.ml. That consumer
   does socket I/O only; every decision this test pins (percent-
   encoding, request-line/header shape, Accept-header selection,
   Content-Type dispatch) is pure F* living in
   formal/fstar/SPARQL.Protocol.Client.fst.

   The .fst file already carries compile-time `let _test_...` smoke
   checks (Part 8 of that file) -- this suite is deliberately a
   SUPERSET with more edge cases (multi-byte UTF-8 percent-encoding,
   graph-URI query params, every dispatch method x every content type,
   the sniff-then-Accept pipeline, non-2xx/unknown-content-type
   fallthrough) run as an ordinary executable rather than only at
   F*-compile-time, so a regression shows up in `tests/unit/run-all.sh`
   without needing a fresh `fstar.exe` typecheck. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

open SPARQL_Protocol_Client

let () =
  (* --- pct_encode: RFC 3986 unreserved passthrough ------------------ *)
  check ~name:"pct_encode: ASCII unreserved set unchanged"
    "abcXYZ019-._~"
    (pct_encode "abcXYZ019-._~");
  check ~name:"pct_encode: empty string" "" (pct_encode "");

  (* --- pct_encode: reserved / space ---------------------------------- *)
  check ~name:"pct_encode: space -> %20" "a%20b" (pct_encode "a b");
  check ~name:"pct_encode: colon -> %3A" "urn%3Ax" (pct_encode "urn:x");
  check ~name:"pct_encode: braces in a SPARQL query"
    "ASK%20WHERE%20%7B%7D" (pct_encode "ASK WHERE {}");
  check ~name:"pct_encode: ampersand/equals encoded (query-string safety)"
    "a%3Db%26c" (pct_encode "a=b&c");
  check ~name:"pct_encode: percent sign itself encoded"
    "100%25" (pct_encode "100%");

  (* --- pct_encode: UTF-8 multi-byte codepoints ----------------------- *)
  (* U+00E9 (e-acute) is 2-byte UTF-8: 0xC3 0xA9. *)
  check ~name:"pct_encode: 2-byte UTF-8 codepoint (e-acute)"
    "caf%C3%A9" (pct_encode "caf\xc3\xa9");
  (* U+4E2D (CJK "middle") is 3-byte UTF-8: 0xE4 0xB8 0xAD. *)
  check ~name:"pct_encode: 3-byte UTF-8 codepoint (CJK)"
    "%E4%B8%AD" (pct_encode "\xe4\xb8\xad");
  (* U+1F600 (grinning face emoji) is 4-byte UTF-8: 0xF0 0x9F 0x98 0x80. *)
  check ~name:"pct_encode: 4-byte UTF-8 codepoint (emoji)"
    "%F0%9F%98%80" (pct_encode "\xf0\x9f\x98\x80");

  (* --- encode_pairs: query-string / form-body assembly --------------- *)
  check ~name:"encode_pairs: single pair"
    "query=ASK%7B%7D"
    (encode_pairs [("query", "ASK{}")]);
  check ~name:"encode_pairs: multiple pairs joined with &"
    "query=ASK%7B%7D&default-graph-uri=urn%3Ag"
    (encode_pairs [("query", "ASK{}"); ("default-graph-uri", "urn:g")]);
  check ~name:"encode_pairs: empty list" "" (encode_pairs []);

  (* --- sniff_query_kind: query-form detection ------------------------ *)
  check ~name:"sniff: bare SELECT" CQK_Select
    (sniff_query_kind "SELECT * WHERE { ?s ?p ?o }");
  check ~name:"sniff: bare ASK" CQK_Ask
    (sniff_query_kind "ASK { ?s ?p ?o }");
  check ~name:"sniff: bare CONSTRUCT" CQK_Construct
    (sniff_query_kind "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }");
  check ~name:"sniff: bare DESCRIBE" CQK_Describe
    (sniff_query_kind "DESCRIBE <http://example.org/x>");
  check ~name:"sniff: CONSTRUCT after a PREFIX prologue" CQK_Construct
    (sniff_query_kind
       "PREFIX ex: <http://example.org/> CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }");
  check ~name:"sniff: DESCRIBE after a BASE prologue" CQK_Describe
    (sniff_query_kind "BASE <http://example.org/> DESCRIBE <http://example.org/x>");
  check ~name:"sniff: multiple PREFIX decls before SELECT" CQK_Select
    (sniff_query_kind
       "PREFIX a: <http://a/> PREFIX b: <http://b/> SELECT * WHERE { ?s ?p ?o }");
  check ~name:"sniff: lower-case keyword still recognized" CQK_Ask
    (sniff_query_kind "ask { ?s ?p ?o }");
  check ~name:"sniff: unrecognizable text defaults to Select" CQK_Select
    (sniff_query_kind "");

  (* --- accept_header_for_kind: q-value biasing ----------------------- *)
  check ~name:"accept header: SELECT/ASK share the same ordering"
    (accept_header_for_kind CQK_Select) (accept_header_for_kind CQK_Ask);
  check ~name:"accept header: CONSTRUCT/DESCRIBE share the same ordering"
    (accept_header_for_kind CQK_Construct) (accept_header_for_kind CQK_Describe);
  check ~name:"accept header: SELECT ordering leads with sparql-results+json"
    true
    (let h = accept_header_for_kind CQK_Select in
     let want = "application/sparql-results+json" in
     let lw = String.length want in
     String.length h >= lw && String.sub h 0 lw = want);
  check ~name:"accept header: CONSTRUCT ordering leads with text/turtle"
    true
    (let h = accept_header_for_kind CQK_Construct in
     String.length h >= 11 && String.sub h 0 11 = "text/turtle");
  check ~name:"accept header: every media type present regardless of kind"
    true
    (let contains_all h =
       let has sub =
         let lh = String.length h and ls = String.length sub in
         let rec scan i = i + ls <= lh && (String.sub h i ls = sub || scan (i + 1)) in
         scan 0
       in
       has "application/sparql-results+json" && has "application/sparql-results+xml"
       && has "text/turtle" && has "application/n-triples"
     in
     contains_all (accept_header_for_kind CQK_Select)
     && contains_all (accept_header_for_kind CQK_Construct));

  (* --- build_get_request: query-via-GET (SPARQL 1.1 Protocol S2.1.1) - *)
  let accept_ask = accept_header_for_kind CQK_Ask in
  let req_get = build_get_request "example.org" "/sparql" "ASK{}" [] [] accept_ask in
  check ~name:"build_get_request: method is GET" "GET" req_get.rm_method;
  check ~name:"build_get_request: path preserved" "/sparql" req_get.rm_path;
  check ~name:"build_get_request: query string is query=<encoded>"
    "query=ASK%7B%7D" req_get.rm_query_str;
  check ~name:"build_get_request: empty body" "" req_get.rm_body;
  check ~name:"build_get_request: Accept header set"
    [("Accept", accept_ask)] req_get.rm_headers;
  check ~name:"build_get_request: no Content-Type header (GET has no body)"
    None (List.assoc_opt "Content-Type" req_get.rm_headers);

  let req_get_graphs =
    build_get_request "example.org" "/sparql" "ASK{}"
      ["urn:g1"] ["urn:g2"] accept_ask
  in
  check ~name:"build_get_request: default-graph-uri/named-graph-uri appended"
    "query=ASK%7B%7D&default-graph-uri=urn%3Ag1&named-graph-uri=urn%3Ag2"
    req_get_graphs.rm_query_str;

  (* --- build_post_direct_request: query-via-POST-direct (S2.1.2) ----- *)
  let req_post_direct =
    build_post_direct_request "example.org" "/sparql" "ASK {}" [] [] accept_ask
  in
  check ~name:"build_post_direct_request: method is POST" "POST" req_post_direct.rm_method;
  check ~name:"build_post_direct_request: body IS the raw query text"
    "ASK {}" req_post_direct.rm_body;
  check ~name:"build_post_direct_request: no query-string params (none given)"
    "" req_post_direct.rm_query_str;
  check ~name:"build_post_direct_request: Content-Type is application/sparql-query"
    (Some "application/sparql-query")
    (List.assoc_opt "Content-Type" req_post_direct.rm_headers);
  check ~name:"build_post_direct_request: Accept header still set"
    (Some accept_ask) (List.assoc_opt "Accept" req_post_direct.rm_headers);

  let req_post_direct_graphs =
    build_post_direct_request "example.org" "/sparql" "ASK{}"
      ["urn:g1"] [] accept_ask
  in
  check ~name:"build_post_direct_request: graph URIs travel as query-string params"
    "default-graph-uri=urn%3Ag1" req_post_direct_graphs.rm_query_str;

  (* --- build_post_form_request: query-via-URL-encoded-POST (S2.1.3) -- *)
  let req_post_form =
    build_post_form_request "example.org" "/sparql" "ASK{}" [] [] accept_ask
  in
  check ~name:"build_post_form_request: method is POST" "POST" req_post_form.rm_method;
  check ~name:"build_post_form_request: no query string (everything in body)"
    "" req_post_form.rm_query_str;
  check ~name:"build_post_form_request: body is query=<encoded>"
    "query=ASK%7B%7D" req_post_form.rm_body;
  check ~name:"build_post_form_request: Content-Type is x-www-form-urlencoded"
    (Some "application/x-www-form-urlencoded")
    (List.assoc_opt "Content-Type" req_post_form.rm_headers);

  let req_post_form_graphs =
    build_post_form_request "example.org" "/sparql" "ASK{}"
      ["urn:g1"] ["urn:g2"] accept_ask
  in
  check ~name:"build_post_form_request: graph URIs travel in the form body"
    "query=ASK%7B%7D&default-graph-uri=urn%3Ag1&named-graph-uri=urn%3Ag2"
    req_post_form_graphs.rm_body;

  (* --- build_query_request: dispatch-method selection + auto-sniff --- *)
  let req_auto_get =
    build_query_request CDM_Get "example.org" "/sparql" "SELECT * WHERE { ?s ?p ?o }" [] []
  in
  check ~name:"build_query_request: CDM_Get produces a GET" "GET" req_auto_get.rm_method;
  check ~name:"build_query_request: sniffed SELECT biases Accept toward json"
    true
    (match List.assoc_opt "Accept" req_auto_get.rm_headers with
     | Some h -> String.length h >= 5 && String.sub h 0 5 = "appli"
     | None -> false);

  let req_auto_post_direct =
    build_query_request CDM_PostDirect "example.org" "/sparql" "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }" [] []
  in
  check ~name:"build_query_request: CDM_PostDirect produces a direct POST"
    ("POST", "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }")
    (req_auto_post_direct.rm_method, req_auto_post_direct.rm_body);
  check ~name:"build_query_request: sniffed CONSTRUCT biases Accept toward turtle"
    true
    (match List.assoc_opt "Accept" req_auto_post_direct.rm_headers with
     | Some h -> String.length h >= 11 && String.sub h 0 11 = "text/turtle"
     | None -> false);

  let req_auto_post_form =
    build_query_request CDM_PostForm "example.org" "/sparql" "ASK{}" [] []
  in
  check ~name:"build_query_request: CDM_PostForm produces a form POST"
    ("POST", "query=ASK%7B%7D")
    (req_auto_post_form.rm_method, req_auto_post_form.rm_body);

  (* --- dispatch_body: Content-Type -> parser dispatch, one per format - *)
  check ~name:"dispatch_body RF_Json: boolean result"
    (CLR_Boolean true)
    (dispatch_body SPARQL_Protocol.RF_Json "{\"head\":{},\"boolean\":true}");
  check ~name:"dispatch_body RF_Json: bindings result"
    (CLR_Bindings (["x"], []))
    (dispatch_body SPARQL_Protocol.RF_Json
       "{\"head\":{\"vars\":[\"x\"]},\"results\":{\"bindings\":[]}}");
  check ~name:"dispatch_body RF_Json: malformed body -> parse error"
    true
    (match dispatch_body SPARQL_Protocol.RF_Json "not json at all" with
     | CLR_ParseError _ -> true | _ -> false);
  check ~name:"dispatch_body RF_Xml: boolean result"
    true
    (match dispatch_body SPARQL_Protocol.RF_Xml
       "<?xml version=\"1.0\"?><sparql xmlns=\"http://www.w3.org/2005/sparql-results#\"><head/><boolean>false</boolean></sparql>" with
     | CLR_Boolean false -> true | _ -> false);
  check ~name:"dispatch_body RF_Csv: bindings result"
    true
    (match dispatch_body SPARQL_Protocol.RF_Csv "x\r\nhello\r\n" with
     | CLR_Bindings (["x"], [ [ ("x", _) ] ]) -> true | _ -> false);
  check ~name:"dispatch_body RF_Tsv: bindings result"
    true
    (match dispatch_body SPARQL_Protocol.RF_Tsv "?x\n\"hello\"\n" with
     | CLR_Bindings (["x"], [ [ ("x", _) ] ]) -> true | _ -> false);
  check ~name:"dispatch_body RF_Turtle: graph result"
    true
    (match dispatch_body SPARQL_Protocol.RF_Turtle
       "<http://example.org/alice> <http://example.org/name> \"Alice\" ." with
     | CLR_Graph [ _ ] -> true | _ -> false);
  check ~name:"dispatch_body RF_NTriples: graph result (2 triples)"
    true
    (match dispatch_body SPARQL_Protocol.RF_NTriples
       "<http://example.org/alice> <http://example.org/name> \"Alice\" .\n\
        <http://example.org/bob> <http://example.org/name> \"Bob\" .\n" with
     | CLR_Graph [ _; _ ] -> true | _ -> false);
  check ~name:"dispatch_body RF_Text: never a valid SPARQL result"
    true
    (match dispatch_body SPARQL_Protocol.RF_Text "plain text body" with
     | CLR_ParseError _ -> true | _ -> false);

  (* --- handle_http_response: status + Content-Type dispatch ---------- *)
  let mk_resp status headers body : SPARQL_HTTP_Client.http_response =
    { rsp_version = "HTTP/1.1"; rsp_status = Z.of_int status; rsp_reason = "";
      rsp_headers = headers; rsp_body = body }
  in
  (* SPARQL_HTTP_Client.header_lookup_ci lower-cases the NEEDLE it is given
     but not the haystack keys -- it relies on `parse_http_response`
     (SPARQL_HTTP_Client.ml, real-response path) having already lower-cased
     every header name at parse time. Test fixtures must follow the same
     "already lower-case" convention a real parsed response guarantees, or
     the lookup silently misses -- pinned explicitly below alongside the
     normal-case tests so this contract doesn't regress unnoticed. *)
  check ~name:"handle_http_response: 200 + application/sparql-results+json -> Boolean"
    (CLR_Boolean true)
    (handle_http_response
       (mk_resp 200 [("content-type", "application/sparql-results+json")]
          "{\"head\":{},\"boolean\":true}"));
  check ~name:"handle_http_response: 200 + text/turtle; charset=utf-8 -> Graph"
    true
    (match handle_http_response
       (mk_resp 200 [("content-type", "text/turtle; charset=utf-8")]
          "<http://example.org/s> <http://example.org/p> \"o\" .") with
     | CLR_Graph [ _ ] -> true | _ -> false);
  check ~name:"handle_http_response: 400 -> HttpError, body preserved"
    (CLR_HttpError (Z.of_int 400, "bad query"))
    (handle_http_response (mk_resp 400 [] "bad query"));
  check ~name:"handle_http_response: 500 -> HttpError"
    true
    (match handle_http_response (mk_resp 500 [] "server error") with
     | CLR_HttpError (status, "server error") -> Z.equal status (Z.of_int 500) | _ -> false);
  check ~name:"handle_http_response: 200 but no Content-Type header -> UnknownContentType"
    (CLR_UnknownContentType ("", "some body"))
    (handle_http_response (mk_resp 200 [] "some body"));
  check ~name:"handle_http_response: 200 + unrecognized Content-Type -> UnknownContentType"
    (CLR_UnknownContentType ("application/x-nonsense", "??"))
    (handle_http_response (mk_resp 200 [("content-type", "application/x-nonsense")] "??"));
  check ~name:"handle_http_response: 201 (2xx boundary) still dispatches"
    (CLR_Boolean false)
    (handle_http_response
       (mk_resp 201 [("content-type", "application/sparql-results+json")]
          "{\"head\":{},\"boolean\":false}"));
  check ~name:"handle_http_response: 299 (2xx upper boundary) still dispatches"
    true
    (match handle_http_response
       (mk_resp 299 [("content-type", "application/n-triples")]
          "<http://example.org/s> <http://example.org/p> \"o\" .\n") with
     | CLR_Graph [ _ ] -> true | _ -> false);
  check ~name:"handle_http_response: 300 (just above 2xx) -> HttpError"
    true
    (match handle_http_response (mk_resp 300 [] "redirect") with
     | CLR_HttpError (status, _) -> Z.equal status (Z.of_int 300) | _ -> false);
  check ~name:"handle_http_response: mixed-case header key is NOT matched (pins the pre-lowercased-key contract)"
    (CLR_UnknownContentType ("", "body"))
    (handle_http_response
       (mk_resp 200 [("Content-Type", "application/sparql-results+json")] "body"));

  Printf.printf "sparql_protocol_client_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
