open Prims
type client_query_kind =
  | CQK_Select 
  | CQK_Ask 
  | CQK_Construct 
  | CQK_Describe 
let uu___is_CQK_Select (projectee : client_query_kind) : Prims.bool=
  match projectee with | CQK_Select -> true | uu___ -> false
let uu___is_CQK_Ask (projectee : client_query_kind) : Prims.bool=
  match projectee with | CQK_Ask -> true | uu___ -> false
let uu___is_CQK_Construct (projectee : client_query_kind) : Prims.bool=
  match projectee with | CQK_Construct -> true | uu___ -> false
let uu___is_CQK_Describe (projectee : client_query_kind) : Prims.bool=
  match projectee with | CQK_Describe -> true | uu___ -> false
type client_dispatch_method =
  | CDM_Get 
  | CDM_PostDirect 
  | CDM_PostForm 
let uu___is_CDM_Get (projectee : client_dispatch_method) : Prims.bool=
  match projectee with | CDM_Get -> true | uu___ -> false
let uu___is_CDM_PostDirect (projectee : client_dispatch_method) : Prims.bool=
  match projectee with | CDM_PostDirect -> true | uu___ -> false
let uu___is_CDM_PostForm (projectee : client_dispatch_method) : Prims.bool=
  match projectee with | CDM_PostForm -> true | uu___ -> false
type client_result =
  | CLR_Bindings of Prims.string Prims.list * (Prims.string *
  RDF_Term.rdf_term) Prims.list Prims.list 
  | CLR_Boolean of Prims.bool 
  | CLR_Graph of RDF_Triple.triple Prims.list 
  | CLR_HttpError of Prims.nat * Prims.string 
  | CLR_ParseError of Prims.string 
  | CLR_UnknownContentType of Prims.string * Prims.string 
let uu___is_CLR_Bindings (projectee : client_result) : Prims.bool=
  match projectee with | CLR_Bindings (vars, rows) -> true | uu___ -> false
let __proj__CLR_Bindings__item__vars (projectee : client_result) :
  Prims.string Prims.list=
  match projectee with | CLR_Bindings (vars, rows) -> vars
let __proj__CLR_Bindings__item__rows (projectee : client_result) :
  (Prims.string * RDF_Term.rdf_term) Prims.list Prims.list=
  match projectee with | CLR_Bindings (vars, rows) -> rows
let uu___is_CLR_Boolean (projectee : client_result) : Prims.bool=
  match projectee with | CLR_Boolean _0 -> true | uu___ -> false
let __proj__CLR_Boolean__item___0 (projectee : client_result) : Prims.bool=
  match projectee with | CLR_Boolean _0 -> _0
let uu___is_CLR_Graph (projectee : client_result) : Prims.bool=
  match projectee with | CLR_Graph _0 -> true | uu___ -> false
let __proj__CLR_Graph__item___0 (projectee : client_result) :
  RDF_Triple.triple Prims.list= match projectee with | CLR_Graph _0 -> _0
let uu___is_CLR_HttpError (projectee : client_result) : Prims.bool=
  match projectee with
  | CLR_HttpError (status, body) -> true
  | uu___ -> false
let __proj__CLR_HttpError__item__status (projectee : client_result) :
  Prims.nat= match projectee with | CLR_HttpError (status, body) -> status
let __proj__CLR_HttpError__item__body (projectee : client_result) :
  Prims.string= match projectee with | CLR_HttpError (status, body) -> body
let uu___is_CLR_ParseError (projectee : client_result) : Prims.bool=
  match projectee with | CLR_ParseError detail -> true | uu___ -> false
let __proj__CLR_ParseError__item__detail (projectee : client_result) :
  Prims.string= match projectee with | CLR_ParseError detail -> detail
let uu___is_CLR_UnknownContentType (projectee : client_result) : Prims.bool=
  match projectee with
  | CLR_UnknownContentType (content_type, body) -> true
  | uu___ -> false
let __proj__CLR_UnknownContentType__item__content_type
  (projectee : client_result) : Prims.string=
  match projectee with
  | CLR_UnknownContentType (content_type, body) -> content_type
let __proj__CLR_UnknownContentType__item__body (projectee : client_result) :
  Prims.string=
  match projectee with | CLR_UnknownContentType (content_type, body) -> body
let is_unreserved (c : FStar_Char.char) : Prims.bool=
  let cd = SPARQL_HTTP_Client.char_code c in
  (((((((cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x5A)))) ||
         ((cd >= (Prims.of_int (0x61))) && (cd <= (Prims.of_int (0x7A)))))
        || ((cd >= (Prims.of_int (0x30))) && (cd <= (Prims.of_int (0x39)))))
       || (cd = (Prims.of_int (0x2D))))
      || (cd = (Prims.of_int (0x2E))))
     || (cd = (Prims.of_int (0x5F))))
    || (cd = (Prims.of_int (0x7E)))
let hex_nibble_upper (n : Prims.nat) : FStar_Char.char=
  if n < (Prims.of_int (10))
  then FStar_Char.char_of_int ((Prims.of_int (0x30)) + n)
  else
    FStar_Char.char_of_int
      ((Prims.of_int (0x41)) + (n - (Prims.of_int (10))))
let byte_to_pct (b : Prims.nat) : Prims.string=
  let hi = b / (Prims.of_int (16)) in
  let lo = (mod) b (Prims.of_int (16)) in
  Prims.strcat "%"
    (Prims.strcat (SPARQL_Protocol.char_to_string (hex_nibble_upper hi))
       (SPARQL_Protocol.char_to_string (hex_nibble_upper lo)))
let codepoint_to_utf8_bytes (cp : Prims.nat) : Prims.nat Prims.list=
  if cp <= (Prims.of_int (0x7F))
  then [cp]
  else
    if cp <= (Prims.of_int (0x7FF))
    then
      [(Prims.of_int (0xC0)) + (cp / (Prims.of_int (64)));
      (Prims.of_int (0x80)) + ((mod) cp (Prims.of_int (64)))]
    else
      if cp <= (Prims.parse_int "0xFFFF")
      then
        [(Prims.of_int (0xE0)) + (cp / (Prims.of_int (4096)));
        (Prims.of_int (0x80)) +
          ((mod) (cp / (Prims.of_int (64))) (Prims.of_int (64)));
        (Prims.of_int (0x80)) + ((mod) cp (Prims.of_int (64)))]
      else
        (let cp' =
           if cp <= (Prims.parse_int "0x10FFFF")
           then cp
           else (Prims.parse_int "0x10FFFF") in
         [(Prims.of_int (0xF0)) + (cp' / (Prims.parse_int "262144"));
         (Prims.of_int (0x80)) +
           ((mod) (cp' / (Prims.of_int (4096))) (Prims.of_int (64)));
         (Prims.of_int (0x80)) +
           ((mod) (cp' / (Prims.of_int (64))) (Prims.of_int (64)));
         (Prims.of_int (0x80)) + ((mod) cp' (Prims.of_int (64)))])
let rec bytes_to_pct_chars (bs : Prims.nat Prims.list) : Prims.string=
  match bs with
  | [] -> ""
  | b::rest -> Prims.strcat (byte_to_pct b) (bytes_to_pct_chars rest)
let pct_encode_char (c : FStar_Char.char) : Prims.string=
  if is_unreserved c
  then SPARQL_Protocol.char_to_string c
  else
    bytes_to_pct_chars
      (codepoint_to_utf8_bytes (SPARQL_HTTP_Client.char_code c))
let rec pct_encode_chars (cs : FStar_Char.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest -> Prims.strcat (pct_encode_char c) (pct_encode_chars rest)
let pct_encode (s : Prims.string) : Prims.string=
  pct_encode_chars (FStar_String.list_of_string s)
let encode_pair (kv : (Prims.string * Prims.string)) : Prims.string=
  let uu___ = kv in
  match uu___ with
  | (k, v) -> Prims.strcat (pct_encode k) (Prims.strcat "=" (pct_encode v))
let rec join_amp (parts : Prims.string Prims.list) : Prims.string=
  match parts with
  | [] -> ""
  | p::[] -> p
  | p::rest -> Prims.strcat p (Prims.strcat "&" (join_amp rest))
let encode_pairs (pairs : (Prims.string * Prims.string) Prims.list) :
  Prims.string= join_amp (FStar_List_Tot_Base.map encode_pair pairs)
let graph_uri_pairs (default_graph_uris : Prims.string Prims.list)
  (named_graph_uris : Prims.string Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map (fun g -> ("default-graph-uri", g))
       default_graph_uris)
    (FStar_List_Tot_Base.map (fun g -> ("named-graph-uri", g))
       named_graph_uris)
let accept_header_for_kind (k : client_query_kind) : Prims.string=
  match k with
  | CQK_Select ->
      "application/sparql-results+json, application/sparql-results+xml;q=0.9, text/turtle;q=0.2, application/n-triples;q=0.1"
  | CQK_Ask ->
      "application/sparql-results+json, application/sparql-results+xml;q=0.9, text/turtle;q=0.2, application/n-triples;q=0.1"
  | CQK_Construct ->
      "text/turtle, application/n-triples;q=0.9, application/sparql-results+json;q=0.2, application/sparql-results+xml;q=0.1"
  | CQK_Describe ->
      "text/turtle, application/n-triples;q=0.9, application/sparql-results+json;q=0.2, application/sparql-results+xml;q=0.1"
let is_ascii_ws_char (c : FStar_Char.char) : Prims.bool=
  SPARQL_Protocol.is_ws_code (SPARQL_HTTP_Client.char_code c)
let ascii_upper_char (c : FStar_Char.char) : FStar_Char.char=
  let cd = SPARQL_HTTP_Client.char_code c in
  if (cd >= (Prims.of_int (0x61))) && (cd <= (Prims.of_int (0x7A)))
  then FStar_Char.char_of_int (cd - (Prims.of_int (32)))
  else c
let ascii_upper_string (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.map ascii_upper_char (FStar_String.list_of_string s))
let rec take_token_chars (xs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)=
  match xs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | c::rest ->
      if is_ascii_ws_char c
      then ((FStar_List_Tot_Base.rev acc), xs)
      else take_token_chars rest (c :: acc)
let next_token (cs : FStar_Char.char Prims.list) :
  (Prims.string * FStar_Char.char Prims.list)=
  let cs' = SPARQL_HTTP_Client.drop_ws_left cs in
  let uu___ = take_token_chars cs' [] in
  match uu___ with | (tok, rest) -> ((FStar_String.string_of_list tok), rest)
let rec sniff_loop (cs : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  client_query_kind=
  if fuel = Prims.int_zero
  then CQK_Select
  else
    (let uu___1 = next_token cs in
     match uu___1 with
     | (tok, rest) ->
         if (FStar_String.strlen tok) = Prims.int_zero
         then CQK_Select
         else
           (let up = ascii_upper_string tok in
            if up = "SELECT"
            then CQK_Select
            else
              if up = "ASK"
              then CQK_Ask
              else
                if up = "CONSTRUCT"
                then CQK_Construct
                else
                  if up = "DESCRIBE"
                  then CQK_Describe
                  else
                    if up = "PREFIX"
                    then
                      (let uu___7 = next_token rest in
                       match uu___7 with
                       | (uu___8, rest1) ->
                           let uu___9 = next_token rest1 in
                           (match uu___9 with
                            | (uu___10, rest2) ->
                                sniff_loop rest2 (fuel - Prims.int_one)))
                    else
                      if up = "BASE"
                      then
                        (let uu___8 = next_token rest in
                         match uu___8 with
                         | (uu___9, rest1) ->
                             sniff_loop rest1 (fuel - Prims.int_one))
                      else sniff_loop rest (fuel - Prims.int_one)))
let sniff_query_kind (query_text : Prims.string) : client_query_kind=
  sniff_loop (FStar_String.list_of_string query_text)
    ((FStar_String.strlen query_text) + Prims.int_one)
let build_get_request (host : Prims.string) (path : Prims.string)
  (query_text : Prims.string) (default_graph_uris : Prims.string Prims.list)
  (named_graph_uris : Prims.string Prims.list) (accept : Prims.string) :
  SPARQL_HTTP_Client.http_request_msg=
  let pairs = ("query", query_text) ::
    (graph_uri_pairs default_graph_uris named_graph_uris) in
  {
    SPARQL_HTTP_Client.rm_method = "GET";
    SPARQL_HTTP_Client.rm_path = path;
    SPARQL_HTTP_Client.rm_query_str = (encode_pairs pairs);
    SPARQL_HTTP_Client.rm_version = "HTTP/1.1";
    SPARQL_HTTP_Client.rm_host = host;
    SPARQL_HTTP_Client.rm_headers = [("Accept", accept)];
    SPARQL_HTTP_Client.rm_body = ""
  }
let build_post_direct_request (host : Prims.string) (path : Prims.string)
  (query_text : Prims.string) (default_graph_uris : Prims.string Prims.list)
  (named_graph_uris : Prims.string Prims.list) (accept : Prims.string) :
  SPARQL_HTTP_Client.http_request_msg=
  let pairs = graph_uri_pairs default_graph_uris named_graph_uris in
  {
    SPARQL_HTTP_Client.rm_method = "POST";
    SPARQL_HTTP_Client.rm_path = path;
    SPARQL_HTTP_Client.rm_query_str = (encode_pairs pairs);
    SPARQL_HTTP_Client.rm_version = "HTTP/1.1";
    SPARQL_HTTP_Client.rm_host = host;
    SPARQL_HTTP_Client.rm_headers =
      [("Accept", accept); ("Content-Type", "application/sparql-query")];
    SPARQL_HTTP_Client.rm_body = query_text
  }
let build_post_form_request (host : Prims.string) (path : Prims.string)
  (query_text : Prims.string) (default_graph_uris : Prims.string Prims.list)
  (named_graph_uris : Prims.string Prims.list) (accept : Prims.string) :
  SPARQL_HTTP_Client.http_request_msg=
  let pairs = ("query", query_text) ::
    (graph_uri_pairs default_graph_uris named_graph_uris) in
  {
    SPARQL_HTTP_Client.rm_method = "POST";
    SPARQL_HTTP_Client.rm_path = path;
    SPARQL_HTTP_Client.rm_query_str = "";
    SPARQL_HTTP_Client.rm_version = "HTTP/1.1";
    SPARQL_HTTP_Client.rm_host = host;
    SPARQL_HTTP_Client.rm_headers =
      [("Accept", accept);
      ("Content-Type", "application/x-www-form-urlencoded")];
    SPARQL_HTTP_Client.rm_body = (encode_pairs pairs)
  }
let build_query_request (method_ : client_dispatch_method)
  (host : Prims.string) (path : Prims.string) (query_text : Prims.string)
  (default_graph_uris : Prims.string Prims.list)
  (named_graph_uris : Prims.string Prims.list) :
  SPARQL_HTTP_Client.http_request_msg=
  let accept = accept_header_for_kind (sniff_query_kind query_text) in
  match method_ with
  | CDM_Get ->
      build_get_request host path query_text default_graph_uris
        named_graph_uris accept
  | CDM_PostDirect ->
      build_post_direct_request host path query_text default_graph_uris
        named_graph_uris accept
  | CDM_PostForm ->
      build_post_form_request host path query_text default_graph_uris
        named_graph_uris accept
let dispatch_body (fmt : SPARQL_Protocol.response_format)
  (body : Prims.string) : client_result=
  match fmt with
  | SPARQL_Protocol.RF_Json ->
      (match Parser_JSONResults.parse_srj_boolean body with
       | FStar_Pervasives_Native.Some b -> CLR_Boolean b
       | FStar_Pervasives_Native.None ->
           (match Parser_JSONResults.parse_srj_results body with
            | FStar_Pervasives_Native.Some (vars, rows) ->
                CLR_Bindings (vars, rows)
            | FStar_Pervasives_Native.None ->
                CLR_ParseError "invalid application/sparql-results+json body"))
  | SPARQL_Protocol.RF_Xml ->
      (match Parser_SRX.parse_srx_boolean body with
       | FStar_Pervasives_Native.Some b -> CLR_Boolean b
       | FStar_Pervasives_Native.None ->
           (match Parser_SRX.parse_srx_results body with
            | FStar_Pervasives_Native.Some (vars, rows) ->
                CLR_Bindings (vars, rows)
            | FStar_Pervasives_Native.None ->
                CLR_ParseError "invalid application/sparql-results+xml body"))
  | SPARQL_Protocol.RF_Csv ->
      (match Parser_CSVResults.parse_csv_to_solutions body with
       | FStar_Pervasives_Native.Some (vars, rows) ->
           CLR_Bindings (vars, rows)
       | FStar_Pervasives_Native.None ->
           CLR_ParseError "invalid text/csv results body")
  | SPARQL_Protocol.RF_Tsv ->
      (match Parser_CSVResults.parse_tsv_to_solutions body with
       | FStar_Pervasives_Native.Some (vars, rows) ->
           CLR_Bindings (vars, rows)
       | FStar_Pervasives_Native.None ->
           CLR_ParseError "invalid text/tab-separated-values results body")
  | SPARQL_Protocol.RF_Turtle ->
      (match Parser_Turtle.parse_turtle_strict body with
       | FStar_Pervasives_Native.Some ts -> CLR_Graph ts
       | FStar_Pervasives_Native.None ->
           CLR_ParseError "invalid text/turtle graph body")
  | SPARQL_Protocol.RF_NTriples ->
      (match Parser_NTriples.parse_ntriples_strict body with
       | FStar_Pervasives_Native.Some ts -> CLR_Graph ts
       | FStar_Pervasives_Native.None ->
           CLR_ParseError "invalid application/n-triples graph body")
  | SPARQL_Protocol.RF_Text ->
      CLR_ParseError "text/plain response body is not a SPARQL result"
let handle_http_response (resp : SPARQL_HTTP_Client.http_response) :
  client_result=
  if
    (resp.SPARQL_HTTP_Client.rsp_status < (Prims.of_int (200))) ||
      (resp.SPARQL_HTTP_Client.rsp_status >= (Prims.of_int (300)))
  then
    CLR_HttpError
      ((resp.SPARQL_HTTP_Client.rsp_status),
        (resp.SPARQL_HTTP_Client.rsp_body))
  else
    (match SPARQL_HTTP_Client.header_lookup_ci
             resp.SPARQL_HTTP_Client.rsp_headers "Content-Type"
     with
     | FStar_Pervasives_Native.None ->
         CLR_UnknownContentType ("", (resp.SPARQL_HTTP_Client.rsp_body))
     | FStar_Pervasives_Native.Some ct ->
         let base = SPARQL_Protocol.content_type_base ct in
         (match SPARQL_Protocol.media_type_to_format base with
          | FStar_Pervasives_Native.Some fmt ->
              dispatch_body fmt resp.SPARQL_HTTP_Client.rsp_body
          | FStar_Pervasives_Native.None ->
              CLR_UnknownContentType (ct, (resp.SPARQL_HTTP_Client.rsp_body))))
let _test_pct_ascii_passthrough : Prims.bool=
  (pct_encode "abcXYZ019-._~") = "abcXYZ019-._~"
let _test_pct_space : Prims.bool= (pct_encode "a b") = "a%20b"
let _test_pct_ask_query : Prims.bool=
  (pct_encode "ASK WHERE {}") = "ASK%20WHERE%20%7B%7D"
let _test_pct_colon_slash : Prims.bool= (pct_encode "urn:x") = "urn%3Ax"
let _test_encode_pairs : Prims.bool=
  (encode_pairs [("query", "ASK{}"); ("default-graph-uri", "urn:g")]) =
    "query=ASK%7B%7D&default-graph-uri=urn%3Ag"
let _test_sniff_select : Prims.bool=
  (sniff_query_kind "SELECT * WHERE { ?s ?p ?o }") = CQK_Select
let _test_sniff_ask : Prims.bool=
  (sniff_query_kind "ASK { ?s ?p ?o }") = CQK_Ask
let _test_sniff_construct_with_prefix : Prims.bool=
  (sniff_query_kind
     "PREFIX ex: <http://example.org/> CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }")
    = CQK_Construct
let _test_sniff_describe_with_base : Prims.bool=
  (sniff_query_kind
     "BASE <http://example.org/> DESCRIBE <http://example.org/x>")
    = CQK_Describe
let _test_accept_select : Prims.bool=
  (accept_header_for_kind CQK_Select) = (accept_header_for_kind CQK_Ask)
let _test_build_get_request : Prims.bool=
  let req =
    build_get_request "example.org" "/sparql" "ASK{}" [] []
      (accept_header_for_kind CQK_Ask) in
  (req.SPARQL_HTTP_Client.rm_method = "GET") &&
    (req.SPARQL_HTTP_Client.rm_query_str = "query=ASK%7B%7D")
let _test_build_post_direct_request : Prims.bool=
  let req =
    build_post_direct_request "example.org" "/sparql" "ASK {}" [] []
      (accept_header_for_kind CQK_Ask) in
  ((req.SPARQL_HTTP_Client.rm_method = "POST") &&
     (req.SPARQL_HTTP_Client.rm_body = "ASK {}"))
    && (req.SPARQL_HTTP_Client.rm_query_str = "")
let _test_build_post_form_request : Prims.bool=
  let req =
    build_post_form_request "example.org" "/sparql" "ASK{}" [] []
      (accept_header_for_kind CQK_Ask) in
  (req.SPARQL_HTTP_Client.rm_method = "POST") &&
    (req.SPARQL_HTTP_Client.rm_body = "query=ASK%7B%7D")
let _test_dispatch_json_boolean : Prims.bool=
  match dispatch_body SPARQL_Protocol.RF_Json
          "{\"head\":{},\"boolean\":true}"
  with
  | CLR_Boolean b -> b = true
  | uu___ -> false
let _test_dispatch_json_bindings : Prims.bool=
  match dispatch_body SPARQL_Protocol.RF_Json
          "{\"head\":{\"vars\":[\"x\"]},\"results\":{\"bindings\":[]}}"
  with
  | CLR_Bindings (vars, uu___) -> vars = ["x"]
  | uu___ -> false
let _test_dispatch_turtle_graph : Prims.bool=
  match dispatch_body SPARQL_Protocol.RF_Turtle
          "<http://example.org/alice> <http://example.org/name> \"Alice\" ."
  with
  | CLR_Graph ts -> (FStar_List_Tot_Base.length ts) = Prims.int_one
  | uu___ -> false
let _test_dispatch_ntriples_graph : Prims.bool=
  match dispatch_body SPARQL_Protocol.RF_NTriples
          "<http://example.org/alice> <http://example.org/name> \"Alice\" .\n<http://example.org/bob> <http://example.org/name> \"Bob\" .\n"
  with
  | CLR_Graph ts -> (FStar_List_Tot_Base.length ts) = (Prims.of_int (2))
  | uu___ -> false
let _test_handle_http_error : Prims.bool=
  let resp =
    {
      SPARQL_HTTP_Client.rsp_version = "HTTP/1.1";
      SPARQL_HTTP_Client.rsp_status = (Prims.of_int (400));
      SPARQL_HTTP_Client.rsp_reason = "Bad Request";
      SPARQL_HTTP_Client.rsp_headers = [];
      SPARQL_HTTP_Client.rsp_body = "bad query"
    } in
  match handle_http_response resp with
  | CLR_HttpError (status, body) ->
      (status = (Prims.of_int (400))) && (body = "bad query")
  | uu___ -> false
