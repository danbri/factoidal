open Prims
type http_request_msg =
  {
  rm_method: Prims.string ;
  rm_path: Prims.string ;
  rm_query_str: Prims.string ;
  rm_version: Prims.string ;
  rm_host: Prims.string ;
  rm_headers: (Prims.string * Prims.string) Prims.list ;
  rm_body: Prims.string }
let __proj__Mkhttp_request_msg__item__rm_method
  (projectee : http_request_msg) : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_method
let __proj__Mkhttp_request_msg__item__rm_path (projectee : http_request_msg)
  : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_path
let __proj__Mkhttp_request_msg__item__rm_query_str
  (projectee : http_request_msg) : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_query_str
let __proj__Mkhttp_request_msg__item__rm_version
  (projectee : http_request_msg) : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_version
let __proj__Mkhttp_request_msg__item__rm_host (projectee : http_request_msg)
  : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_host
let __proj__Mkhttp_request_msg__item__rm_headers
  (projectee : http_request_msg) : (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_headers
let __proj__Mkhttp_request_msg__item__rm_body (projectee : http_request_msg)
  : Prims.string=
  match projectee with
  | { rm_method; rm_path; rm_query_str; rm_version; rm_host; rm_headers;
      rm_body;_} -> rm_body
type http_response =
  {
  rsp_version: Prims.string ;
  rsp_status: Prims.nat ;
  rsp_reason: Prims.string ;
  rsp_headers: (Prims.string * Prims.string) Prims.list ;
  rsp_body: Prims.string }
let __proj__Mkhttp_response__item__rsp_version (projectee : http_response) :
  Prims.string=
  match projectee with
  | { rsp_version; rsp_status; rsp_reason; rsp_headers; rsp_body;_} ->
      rsp_version
let __proj__Mkhttp_response__item__rsp_status (projectee : http_response) :
  Prims.nat=
  match projectee with
  | { rsp_version; rsp_status; rsp_reason; rsp_headers; rsp_body;_} ->
      rsp_status
let __proj__Mkhttp_response__item__rsp_reason (projectee : http_response) :
  Prims.string=
  match projectee with
  | { rsp_version; rsp_status; rsp_reason; rsp_headers; rsp_body;_} ->
      rsp_reason
let __proj__Mkhttp_response__item__rsp_headers (projectee : http_response) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { rsp_version; rsp_status; rsp_reason; rsp_headers; rsp_body;_} ->
      rsp_headers
let __proj__Mkhttp_response__item__rsp_body (projectee : http_response) :
  Prims.string=
  match projectee with
  | { rsp_version; rsp_status; rsp_reason; rsp_headers; rsp_body;_} ->
      rsp_body
type http_client_error =
  | HCE_MalformedStatusLine 
  | HCE_MalformedHeader 
  | HCE_BadStatusCode 
  | HCE_HeadersTooLarge 
  | HCE_BodyTooLarge 
  | HCE_MissingCRLF 
  | HCE_BadResponse of Prims.string 
let uu___is_HCE_MalformedStatusLine (projectee : http_client_error) :
  Prims.bool=
  match projectee with | HCE_MalformedStatusLine -> true | uu___ -> false
let uu___is_HCE_MalformedHeader (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_MalformedHeader -> true | uu___ -> false
let uu___is_HCE_BadStatusCode (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_BadStatusCode -> true | uu___ -> false
let uu___is_HCE_HeadersTooLarge (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_HeadersTooLarge -> true | uu___ -> false
let uu___is_HCE_BodyTooLarge (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_BodyTooLarge -> true | uu___ -> false
let uu___is_HCE_MissingCRLF (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_MissingCRLF -> true | uu___ -> false
let uu___is_HCE_BadResponse (projectee : http_client_error) : Prims.bool=
  match projectee with | HCE_BadResponse _0 -> true | uu___ -> false
let __proj__HCE_BadResponse__item___0 (projectee : http_client_error) :
  Prims.string= match projectee with | HCE_BadResponse _0 -> _0
type 'a http_client_result = ('a, http_client_error) FStar_Pervasives.either
let char_code (c : FStar_Char.char) : Prims.nat= FStar_Char.int_of_char c
let is_ascii_ws (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let ascii_lower_char (c : FStar_Char.char) : FStar_Char.char=
  let cd = char_code c in
  if (cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (cd + (Prims.of_int (32)))
  else c
let ascii_lower_string (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.map ascii_lower_char (FStar_String.list_of_string s))
let rec drop_ws_left (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest -> if is_ascii_ws c then drop_ws_left rest else cs
let trim_ws_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  FStar_List_Tot_Base.rev
    (drop_ws_left (FStar_List_Tot_Base.rev (drop_ws_left cs)))
let trim_ws (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (trim_ws_chars (FStar_String.list_of_string s))
let safe_substring (s : Prims.string) (start : Prims.nat)
  (sub_len : Prims.nat) : Prims.string=
  let slen = FStar_String.strlen s in
  if start >= slen
  then ""
  else
    (let remaining = slen - start in
     let effective_len = if sub_len <= remaining then sub_len else remaining in
     FStar_String.sub s start effective_len)
let string_suffix (s : Prims.string) (start : Prims.nat) : Prims.string=
  let slen = FStar_String.strlen s in
  if start >= slen then "" else FStar_String.sub s start (slen - start)
let rec find_char (input : Prims.string) (pos : Prims.nat)
  (target : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then FStar_Pervasives_Native.None
     else
       (let c = char_code (FStar_String.index input pos) in
        if c = target
        then FStar_Pervasives_Native.Some pos
        else
          find_char input (pos + Prims.int_one) target (fuel - Prims.int_one)))
let rec find_2byte (input : Prims.string) (pos : Prims.nat) (b1 : Prims.nat)
  (b2 : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = FStar_String.strlen input in
     if (pos + Prims.int_one) >= len
     then FStar_Pervasives_Native.None
     else
       (let c1 = char_code (FStar_String.index input pos) in
        let c2 = char_code (FStar_String.index input (pos + Prims.int_one)) in
        if (c1 = b1) && (c2 = b2)
        then FStar_Pervasives_Native.Some pos
        else
          find_2byte input (pos + Prims.int_one) b1 b2 (fuel - Prims.int_one)))
let rec find_4byte (input : Prims.string) (pos : Prims.nat) (b1 : Prims.nat)
  (b2 : Prims.nat) (b3 : Prims.nat) (b4 : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let len = FStar_String.strlen input in
     if (pos + (Prims.of_int (3))) >= len
     then FStar_Pervasives_Native.None
     else
       (let c1 = char_code (FStar_String.index input pos) in
        let c2 = char_code (FStar_String.index input (pos + Prims.int_one)) in
        let c3 =
          char_code (FStar_String.index input (pos + (Prims.of_int (2)))) in
        let c4 =
          char_code (FStar_String.index input (pos + (Prims.of_int (3)))) in
        if (((c1 = b1) && (c2 = b2)) && (c3 = b3)) && (c4 = b4)
        then FStar_Pervasives_Native.Some pos
        else
          find_4byte input (pos + Prims.int_one) b1 b2 b3 b4
            (fuel - Prims.int_one)))
let rec contains_crlf_chars (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | c::rest ->
      let code = char_code c in
      if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
      then true
      else contains_crlf_chars rest
let contains_crlf (s : Prims.string) : Prims.bool=
  contains_crlf_chars (FStar_String.list_of_string s)
let rec header_lookup_ci_chars
  (hs : (Prims.string * Prims.string) Prims.list) (needle : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match hs with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = needle
      then FStar_Pervasives_Native.Some v
      else header_lookup_ci_chars rest needle
let header_lookup_ci (headers : (Prims.string * Prims.string) Prims.list)
  (name : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  header_lookup_ci_chars headers (ascii_lower_string name)
let rec parse_nat_chars (cs : FStar_Char.char Prims.list) (acc : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      let code = char_code c in
      if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
      then
        let d = code - (Prims.of_int (0x30)) in
        parse_nat_chars rest ((acc * (Prims.of_int (10))) + d)
      else FStar_Pervasives_Native.None
let parse_nat (s : Prims.string) : Prims.nat FStar_Pervasives_Native.option=
  let trimmed = trim_ws s in
  if (FStar_String.strlen trimmed) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else parse_nat_chars (FStar_String.list_of_string trimmed) Prims.int_zero
let rec nat_to_digits_acc (n : Prims.nat) (acc : FStar_Char.char Prims.list)
  : FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then acc
  else
    (let d = (mod) n (Prims.of_int (10)) in
     let rest = n / (Prims.of_int (10)) in
     let ch = FStar_Char.char_of_int ((Prims.of_int (0x30)) + d) in
     nat_to_digits_acc rest (ch :: acc))
let nat_to_string (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "0"
  else FStar_String.string_of_list (nat_to_digits_acc n [])
let has_header_ci (headers : (Prims.string * Prims.string) Prims.list)
  (name : Prims.string) : Prims.bool=
  match header_lookup_ci headers name with
  | FStar_Pervasives_Native.Some uu___ -> true
  | FStar_Pervasives_Native.None -> false
let crlf : Prims.string= "\r\n"
let sp : Prims.string= " "
let rec format_headers_acc
  (headers : (Prims.string * Prims.string) Prims.list) (acc : Prims.string) :
  Prims.string=
  match headers with
  | [] -> acc
  | (k, v)::rest ->
      let line = Prims.strcat k (Prims.strcat ": " (Prims.strcat v crlf)) in
      format_headers_acc rest (Prims.strcat acc line)
let format_request_headers
  (headers : (Prims.string * Prims.string) Prims.list) : Prims.string=
  format_headers_acc headers ""
let format_request_line (meth : Prims.string) (path : Prims.string)
  (qs : Prims.string) (ver : Prims.string) : Prims.string=
  let target =
    if (FStar_String.strlen qs) = Prims.int_zero
    then path
    else Prims.strcat path (Prims.strcat "?" qs) in
  Prims.strcat meth
    (Prims.strcat sp
       (Prims.strcat target (Prims.strcat sp (Prims.strcat ver crlf))))
let complete_headers (req : http_request_msg) :
  (Prims.string * Prims.string) Prims.list=
  let h0 = req.rm_headers in
  let h1 =
    if has_header_ci h0 "Host"
    then h0
    else FStar_List_Tot_Base.op_At h0 [("Host", (req.rm_host))] in
  let body_len = FStar_String.strlen req.rm_body in
  let h2 =
    if body_len = Prims.int_zero
    then h1
    else
      if has_header_ci h1 "Content-Length"
      then h1
      else
        FStar_List_Tot_Base.op_At h1
          [("Content-Length", (nat_to_string body_len))] in
  h2
let format_request (req : http_request_msg) : Prims.string=
  let rl =
    format_request_line req.rm_method req.rm_path req.rm_query_str
      req.rm_version in
  let hs = complete_headers req in
  let hblock = format_request_headers hs in
  Prims.strcat rl (Prims.strcat hblock (Prims.strcat crlf req.rm_body))
let parse_status_line (line : Prims.string) :
  (Prims.string * Prims.nat * Prims.string) http_client_result=
  if contains_crlf line
  then FStar_Pervasives.Inr HCE_MalformedStatusLine
  else
    (let len = FStar_String.strlen line in
     let fuel = len + Prims.int_one in
     match find_char line Prims.int_zero (Prims.of_int (0x20)) fuel with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives.Inr HCE_MalformedStatusLine
     | FStar_Pervasives_Native.Some i1 ->
         let ver = safe_substring line Prims.int_zero i1 in
         let rest_start = i1 + Prims.int_one in
         let rest_len =
           if rest_start <= len then len - rest_start else Prims.int_zero in
         let fuel2 = rest_len + Prims.int_one in
         (match find_char line rest_start (Prims.of_int (0x20)) fuel2 with
          | FStar_Pervasives_Native.None ->
              FStar_Pervasives.Inr HCE_MalformedStatusLine
          | FStar_Pervasives_Native.Some i2 ->
              if i2 <= rest_start
              then FStar_Pervasives.Inr HCE_MalformedStatusLine
              else
                (let code_len = i2 - rest_start in
                 let code_raw = safe_substring line rest_start code_len in
                 match parse_nat code_raw with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives.Inr HCE_BadStatusCode
                 | FStar_Pervasives_Native.Some code ->
                     let reason_start = i2 + Prims.int_one in
                     let reason = string_suffix line reason_start in
                     if (FStar_String.strlen ver) = Prims.int_zero
                     then FStar_Pervasives.Inr HCE_MalformedStatusLine
                     else FStar_Pervasives.Inl (ver, code, reason))))
let parse_response_header_line (line : Prims.string) :
  (Prims.string * Prims.string) http_client_result=
  if contains_crlf line
  then FStar_Pervasives.Inr HCE_MalformedHeader
  else
    (let len = FStar_String.strlen line in
     let fuel = len + Prims.int_one in
     match find_char line Prims.int_zero (Prims.of_int (0x3A)) fuel with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives.Inr HCE_MalformedHeader
     | FStar_Pervasives_Native.Some i ->
         let name_raw = safe_substring line Prims.int_zero i in
         let name = ascii_lower_string (trim_ws name_raw) in
         let value_start = i + Prims.int_one in
         let value_raw = string_suffix line value_start in
         let value = trim_ws value_raw in
         if (FStar_String.strlen name) = Prims.int_zero
         then FStar_Pervasives.Inr HCE_MalformedHeader
         else FStar_Pervasives.Inl (name, value))
let rec parse_response_header_lines (input : Prims.string) (pos : Prims.nat)
  (head_end : Prims.nat) (acc : (Prims.string * Prims.string) Prims.list)
  (fuel : Prims.nat) :
  (Prims.string * Prims.string) Prims.list http_client_result=
  if fuel = Prims.int_zero
  then FStar_Pervasives.Inl (FStar_List_Tot_Base.rev acc)
  else
    if pos >= head_end
    then FStar_Pervasives.Inl (FStar_List_Tot_Base.rev acc)
    else
      (let remaining =
         if head_end >= pos then head_end - pos else Prims.int_zero in
       let line_fuel = remaining + Prims.int_one in
       match find_2byte input pos (Prims.of_int (0x0D)) (Prims.of_int (0x0A))
               line_fuel
       with
       | FStar_Pervasives_Native.None ->
           let line = safe_substring input pos (head_end - pos) in
           if (FStar_String.strlen line) = Prims.int_zero
           then FStar_Pervasives.Inl (FStar_List_Tot_Base.rev acc)
           else
             (match parse_response_header_line line with
              | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
              | FStar_Pervasives.Inl kv ->
                  FStar_Pervasives.Inl (FStar_List_Tot_Base.rev (kv :: acc)))
       | FStar_Pervasives_Native.Some crlf_pos ->
           if crlf_pos > head_end
           then FStar_Pervasives.Inl (FStar_List_Tot_Base.rev acc)
           else
             if crlf_pos <= pos
             then FStar_Pervasives.Inl (FStar_List_Tot_Base.rev acc)
             else
               (let line_len = crlf_pos - pos in
                let line = safe_substring input pos line_len in
                match parse_response_header_line line with
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
                | FStar_Pervasives.Inl kv ->
                    let next_pos = crlf_pos + (Prims.of_int (2)) in
                    parse_response_header_lines input next_pos head_end (kv
                      :: acc) (fuel - Prims.int_one)))
let parse_http_response (raw : Prims.string) (max_header_bytes : Prims.nat)
  (max_body_bytes : Prims.nat) : http_response http_client_result=
  let raw_len = FStar_String.strlen raw in
  let head_scan_limit =
    if max_header_bytes < raw_len then max_header_bytes else raw_len in
  let head_scan_fuel = head_scan_limit + Prims.int_one in
  match find_4byte raw Prims.int_zero (Prims.of_int (0x0D))
          (Prims.of_int (0x0A)) (Prims.of_int (0x0D)) (Prims.of_int (0x0A))
          head_scan_fuel
  with
  | FStar_Pervasives_Native.None ->
      if raw_len >= max_header_bytes
      then FStar_Pervasives.Inr HCE_HeadersTooLarge
      else FStar_Pervasives.Inr HCE_MissingCRLF
  | FStar_Pervasives_Native.Some head_end ->
      if head_end > max_header_bytes
      then FStar_Pervasives.Inr HCE_HeadersTooLarge
      else
        (let sl_fuel = head_end + Prims.int_one in
         match find_2byte raw Prims.int_zero (Prims.of_int (0x0D))
                 (Prims.of_int (0x0A)) sl_fuel
         with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives.Inr HCE_MalformedStatusLine
         | FStar_Pervasives_Native.Some sl_end ->
             if sl_end > head_end
             then FStar_Pervasives.Inr HCE_MalformedStatusLine
             else
               (let status_line = safe_substring raw Prims.int_zero sl_end in
                match parse_status_line status_line with
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
                | FStar_Pervasives.Inl (ver, code, reason) ->
                    let headers_start = sl_end + (Prims.of_int (2)) in
                    let headers_end =
                      if head_end >= headers_start
                      then head_end
                      else headers_start in
                    let headers_len = headers_end - headers_start in
                    let hdr_fuel = headers_len + Prims.int_one in
                    (match parse_response_header_lines raw headers_start
                             headers_end [] hdr_fuel
                     with
                     | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
                     | FStar_Pervasives.Inl headers ->
                         let body_start = head_end + (Prims.of_int (4)) in
                         let available =
                           if raw_len >= body_start
                           then raw_len - body_start
                           else Prims.int_zero in
                         let body_len_opt =
                           match header_lookup_ci headers "content-length"
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.Some available
                           | FStar_Pervasives_Native.Some cl ->
                               (match parse_nat cl with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some n ->
                                    FStar_Pervasives_Native.Some n) in
                         (match body_len_opt with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives.Inr
                                (HCE_BadResponse "invalid Content-Length")
                          | FStar_Pervasives_Native.Some body_len ->
                              if body_len > max_body_bytes
                              then FStar_Pervasives.Inr HCE_BodyTooLarge
                              else
                                (let effective =
                                   if body_len <= available
                                   then body_len
                                   else available in
                                 let body =
                                   safe_substring raw body_start effective in
                                 FStar_Pervasives.Inl
                                   {
                                     rsp_version = ver;
                                     rsp_status = code;
                                     rsp_reason = reason;
                                     rsp_headers = headers;
                                     rsp_body = body
                                   })))))
let _test_nat_zero : Prims.bool= (nat_to_string Prims.int_zero) = "0"
let _test_nat_small : Prims.bool= (nat_to_string (Prims.of_int (7))) = "7"
let _test_nat_multi : Prims.bool=
  (nat_to_string (Prims.of_int (1234))) = "1234"
let _test_rl_no_qs : Prims.bool=
  (format_request_line "GET" "/sparql" "" "HTTP/1.1") =
    "GET /sparql HTTP/1.1\r\n"
let _test_rl_with_qs : Prims.bool=
  (format_request_line "POST" "/query" "default-graph-uri=urn%3Ax" "HTTP/1.1")
    = "POST /query?default-graph-uri=urn%3Ax HTTP/1.1\r\n"
let _test_headers_empty : Prims.bool= (format_request_headers []) = ""
let _test_headers_two : Prims.bool=
  (format_request_headers [("Accept", "application/json"); ("X-Foo", "bar")])
    = "Accept: application/json\r\nX-Foo: bar\r\n"
let _test_format_get : Prims.bool=
  let r =
    {
      rm_method = "GET";
      rm_path = "/sparql";
      rm_query_str = "query=ASK%20WHERE%20%7B%7D";
      rm_version = "HTTP/1.1";
      rm_host = "example.org";
      rm_headers = [("Accept", "application/sparql-results+json")];
      rm_body = ""
    } in
  (format_request r) =
    "GET /sparql?query=ASK%20WHERE%20%7B%7D HTTP/1.1\r\nAccept: application/sparql-results+json\r\nHost: example.org\r\n\r\n"
let _test_format_post : Prims.bool=
  let r =
    {
      rm_method = "POST";
      rm_path = "/sparql";
      rm_query_str = "";
      rm_version = "HTTP/1.1";
      rm_host = "example.org";
      rm_headers =
        [("Content-Type", "application/sparql-query");
        ("Accept", "application/sparql-results+json")];
      rm_body = "ASK {}"
    } in
  (format_request r) =
    "POST /sparql HTTP/1.1\r\nContent-Type: application/sparql-query\r\nAccept: application/sparql-results+json\r\nHost: example.org\r\nContent-Length: 6\r\n\r\nASK {}"
let _test_sl_ok : Prims.bool=
  match parse_status_line "HTTP/1.1 200 OK" with
  | FStar_Pervasives.Inl (v, c, r) ->
      ((v = "HTTP/1.1") && (c = (Prims.of_int (200)))) && (r = "OK")
  | FStar_Pervasives.Inr uu___ -> false
let _test_sl_reason_with_spaces : Prims.bool=
  match parse_status_line "HTTP/1.1 404 Not Found" with
  | FStar_Pervasives.Inl (v, c, r) ->
      ((v = "HTTP/1.1") && (c = (Prims.of_int (404)))) && (r = "Not Found")
  | FStar_Pervasives.Inr uu___ -> false
let _test_resp_header_ok : Prims.bool=
  match parse_response_header_line
          "Content-Type: application/sparql-results+json"
  with
  | FStar_Pervasives.Inl (n, v) ->
      (n = "content-type") && (v = "application/sparql-results+json")
  | FStar_Pervasives.Inr uu___ -> false
let _test_parse_response_cl : Prims.bool=
  let raw =
    "HTTP/1.1 200 OK\r\nContent-Type: application/sparql-results+json\r\nContent-Length: 13\r\n\r\n{\"ok\":true}\r\n" in
  match parse_http_response raw (Prims.of_int (8192))
          (Prims.parse_int "1048576")
  with
  | FStar_Pervasives.Inl r ->
      (((r.rsp_status = (Prims.of_int (200))) && (r.rsp_version = "HTTP/1.1"))
         && (r.rsp_reason = "OK"))
        && ((FStar_String.strlen r.rsp_body) = (Prims.of_int (13)))
  | FStar_Pervasives.Inr uu___ -> false
let _test_parse_response_no_cl : Prims.bool=
  let raw = "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nhello" in
  match parse_http_response raw (Prims.of_int (8192))
          (Prims.parse_int "1048576")
  with
  | FStar_Pervasives.Inl r ->
      (r.rsp_status = (Prims.of_int (200))) && (r.rsp_body = "hello")
  | FStar_Pervasives.Inr uu___ -> false
