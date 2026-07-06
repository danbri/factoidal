(* sparql_service_wrap_unit.ml -- pins SPARQL.Service.Wrap, the
   "wrap+http(s):" virtual-sources SERVICE resolver added this session
   (docs/designissues/2026-07-06-virtual-sources-design.md, Part A
   Stages 1-2). The module is pure F* -- no socket I/O -- and this
   suite exercises exactly that pure surface: wrap+ IRI recognition,
   the control-fragment (#rml=/#mime=/#ttl=) parse, GET-request
   construction, response-format auto-detection, and the default
   Facade-X-equivalent JSON/CSV mapping via `resolve_wrap_response`
   fed fabricated response bytes directly (no network).

   The .fst file's own Part 8 carries compile-time `let _test_...`
   smoke checks; this suite is a superset run as an ordinary
   executable so a regression surfaces in `tests/unit/run-all.sh`. *)

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

open SPARQL_Service_Wrap

let () =
  (* --- parse_wrap_iri: scheme recognition ---------------------------- *)
  check ~name:"parse_wrap_iri: wrap+https with #rml= control fragment"
    true
    (match parse_wrap_iri "wrap+https://api.example.org/v1/users?id=42#rml=urn:mapping:users-api" with
     | Some wt ->
       wt.wt_transport = WT_Https
       && wt.wt_target = "api.example.org/v1/users?id=42"
       && wrap_target_rml_name wt = Some "urn:mapping:users-api"
     | None -> false);
  check ~name:"parse_wrap_iri: wrap+http, no control fragment"
    true
    (match parse_wrap_iri "wrap+http://internal.example.org/status" with
     | Some wt ->
       wt.wt_transport = WT_Http
       && wt.wt_target = "internal.example.org/status"
       && wrap_target_rml_name wt = None
       && wrap_target_mime_override wt = None
       && wrap_target_ttl wt = None
     | None -> false);
  check ~name:"parse_wrap_iri: #mime= control fragment"
    (Some "application/json")
    (match parse_wrap_iri "wrap+https://example.org/data#mime=application/json" with
     | Some wt -> wrap_target_mime_override wt
     | None -> None);
  check ~name:"parse_wrap_iri: #ttl= control fragment (parsed, v1 ignores semantically)"
    (Some "300")
    (match parse_wrap_iri "wrap+https://example.org/data#ttl=300" with
     | Some wt -> wrap_target_ttl wt
     | None -> None);
  check ~name:"parse_wrap_iri: multiple control-fragment keys, all recovered"
    true
    (match parse_wrap_iri "wrap+https://example.org/data#mime=text/csv&rml=urn:m&ttl=60" with
     | Some wt ->
       wrap_target_mime_override wt = Some "text/csv"
       && wrap_target_rml_name wt = Some "urn:m"
       && wrap_target_ttl wt = Some "60"
     | None -> false);
  check ~name:"parse_wrap_iri: rejects wrap+mcp: (out of scope this stage)"
    true (None = parse_wrap_iri "wrap+mcp:geocoder/geocode?x=1");
  check ~name:"parse_wrap_iri: rejects wrap+exec: (out of scope this stage)"
    true (None = parse_wrap_iri "wrap+exec:some-tool");
  check ~name:"parse_wrap_iri: rejects a plain http(s) IRI (no wrap+ prefix)"
    true (None = parse_wrap_iri "http://example.org/plain-service");
  check ~name:"parse_wrap_iri: rejects an entirely unrelated string"
    true (None = parse_wrap_iri "not a iri at all");

  (* --- wrap_target_url: fully-legible reconstitution ----------------- *)
  check ~name:"wrap_target_url: https round trip"
    (Some "https://127.0.0.1:8099/data.json")
    (match parse_wrap_iri "wrap+https://127.0.0.1:8099/data.json" with
     | Some wt -> Some (wrap_target_url wt) | None -> None);
  check ~name:"wrap_target_url: http round trip"
    (Some "http://example.org/x?y=1")
    (match parse_wrap_iri "wrap+http://example.org/x?y=1" with
     | Some wt -> Some (wrap_target_url wt) | None -> None);

  (* --- build_wrap_get_request: URL splitting + default ports --------- *)
  check ~name:"build_wrap_get_request: host/port/path/query split (explicit port)"
    true
    (match parse_wrap_iri "wrap+http://127.0.0.1:8099/data.json?x=1" with
     | Some wt ->
       let req = build_wrap_get_request wt in
       req.wr_host = "127.0.0.1" && Z.equal req.wr_port (Z.of_int 8099)
       && req.wr_msg.rm_path = "/data.json" && req.wr_msg.rm_query_str = "x=1"
       && req.wr_msg.rm_method = "GET"
     | None -> false);
  check ~name:"build_wrap_get_request: default https port is 443"
    true
    (match parse_wrap_iri "wrap+https://example.org/x" with
     | Some wt -> Z.equal (build_wrap_get_request wt).wr_port (Z.of_int 443)
     | None -> false);
  check ~name:"build_wrap_get_request: default http port is 80"
    true
    (match parse_wrap_iri "wrap+http://example.org/x" with
     | Some wt -> Z.equal (build_wrap_get_request wt).wr_port (Z.of_int 80)
     | None -> false);
  check ~name:"build_wrap_get_request: no path defaults to /"
    "/"
    (match parse_wrap_iri "wrap+http://example.org" with
     | Some wt -> (build_wrap_get_request wt).wr_msg.rm_path
     | None -> "<parse failed>");
  check ~name:"build_wrap_get_request: request is Accept: */* , Connection: close, no body"
    true
    (match parse_wrap_iri "wrap+http://example.org/x" with
     | Some wt ->
       let m = (build_wrap_get_request wt).wr_msg in
       m.rm_headers = [("Accept", "*/*"); ("Connection", "close")] && m.rm_body = ""
     | None -> false);

  (* --- detect_wrap_format: mime= override wins over Content-Type ----- *)
  check ~name:"detect_wrap_format: mime= override wins over Content-Type"
    WF_Json (detect_wrap_format (Some "text/plain") (Some "application/json"));
  check ~name:"detect_wrap_format: falls back to Content-Type, params stripped"
    WF_Csv (detect_wrap_format (Some "text/csv; charset=utf-8") None);
  check ~name:"detect_wrap_format: text/turtle"
    WF_Turtle (detect_wrap_format (Some "text/turtle") None);
  check ~name:"detect_wrap_format: application/x-turtle (alias)"
    WF_Turtle (detect_wrap_format (Some "application/x-turtle") None);
  check ~name:"detect_wrap_format: application/n-triples"
    WF_NTriples (detect_wrap_format (Some "application/n-triples") None);
  check ~name:"detect_wrap_format: application/n-quads"
    WF_NQuads (detect_wrap_format (Some "application/n-quads") None);
  check ~name:"detect_wrap_format: no Content-Type and no mime= -> plain-string fallback"
    WF_PlainString (detect_wrap_format None None);
  check ~name:"detect_wrap_format: unrecognized Content-Type -> plain-string fallback"
    WF_PlainString (detect_wrap_format (Some "application/octet-stream") None);

  (* --- resolve_wrap_response: default JSON/CSV mapping, small exact
     graphs (Stage 1, no rml= override) -------------------------------- *)
  check ~name:"resolve_wrap_response: flat JSON object -> one triple per field"
    2
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "application/json")] "{\"name\": \"Ada\", \"age\": 36}" None));
  check ~name:"resolve_wrap_response: nested JSON object adds a blank-node link triple"
    3 (* name + address-link + city *)
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "application/json")]
          "{\"name\": \"Ada\", \"address\": {\"city\": \"London\"}}" None));
  check ~name:"resolve_wrap_response: JSON array fans out as repeated triples, same predicate"
    3
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "application/json")] "{\"tag\": [\"a\", \"b\", \"c\"]}" None));
  check ~name:"resolve_wrap_response: CSV -- one blank-node subject per row, one triple per cell"
    4 (* 2 rows x 2 cells *)
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "text/csv")] "name,age\nAda,36\nGrace,85\n" None));
  check ~name:"resolve_wrap_response: Turtle passthrough (no default mapping applied)"
    1
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "text/turtle")]
          "<http://example.org/s> <http://example.org/p> \"o\" ." None));
  check ~name:"resolve_wrap_response: N-Triples passthrough (2 triples)"
    2
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "application/n-triples")]
          "<http://example.org/s> <http://example.org/p> \"a\" .\n\
           <http://example.org/s> <http://example.org/p2> \"b\" .\n" None));
  check ~name:"resolve_wrap_response: plain-string fallback (unrecognized content, no mime=)"
    1
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [] "just some bytes" None));

  (* --- resolve_wrap_response: non-2xx / unrecognized-IRI / malformed-
     body all yield the empty graph (never a partial/garbage graph) --- *)
  check ~name:"resolve_wrap_response: 404 status -> no triples"
    [] (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 404)
          [("content-type", "application/json")] "{}" None);
  check ~name:"resolve_wrap_response: 500 status -> no triples"
    [] (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 500)
          [("content-type", "application/json")] "{}" None);
  check ~name:"resolve_wrap_response: non-wrap+ IRI is never resolved, regardless of status/body"
    [] (resolve_wrap_response "http://example.org/plain-service" (Z.of_int 200) [] "irrelevant" None);
  check ~name:"resolve_wrap_response: malformed JSON body -> no triples (not a crash)"
    [] (resolve_wrap_response "wrap+http://127.0.0.1:8099/x" (Z.of_int 200)
          [("content-type", "application/json")] "{not valid json" None);

  (* --- mime= override changes dispatch even when Content-Type disagrees *)
  check ~name:"resolve_wrap_response: mime= override forces CSV mapping over a text/plain Content-Type"
    4
    (List.length
       (resolve_wrap_response "wrap+http://127.0.0.1:8099/x#mime=text/csv" (Z.of_int 200)
          [("content-type", "text/plain")] "name,age\nAda,36\nGrace,85\n" None));

  Printf.printf "sparql_service_wrap_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
