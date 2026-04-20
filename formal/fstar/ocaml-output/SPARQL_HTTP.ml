open Prims
type http_request =
  {
  hr_method: Prims.string ;
  hr_path: Prims.string ;
  hr_query_str: Prims.string ;
  hr_version: Prims.string ;
  hr_headers: (Prims.string * Prims.string) Prims.list ;
  hr_body: Prims.string }
let __proj__Mkhttp_request__item__hr_method (projectee : http_request) :
  Prims.string=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_method
let __proj__Mkhttp_request__item__hr_path (projectee : http_request) :
  Prims.string=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_path
let __proj__Mkhttp_request__item__hr_query_str (projectee : http_request) :
  Prims.string=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_query_str
let __proj__Mkhttp_request__item__hr_version (projectee : http_request) :
  Prims.string=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_version
let __proj__Mkhttp_request__item__hr_headers (projectee : http_request) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_headers
let __proj__Mkhttp_request__item__hr_body (projectee : http_request) :
  Prims.string=
  match projectee with
  | { hr_method; hr_path; hr_query_str; hr_version; hr_headers; hr_body;_} ->
      hr_body
type http_error =
  | HE_MalformedRequestLine 
  | HE_MalformedHeader 
  | HE_BadRequest of Prims.string 
  | HE_BodyTooLarge 
  | HE_HeadersTooLarge 
  | HE_MissingCRLF 
let uu___is_HE_MalformedRequestLine (projectee : http_error) : Prims.bool=
  match projectee with | HE_MalformedRequestLine -> true | uu___ -> false
let uu___is_HE_MalformedHeader (projectee : http_error) : Prims.bool=
  match projectee with | HE_MalformedHeader -> true | uu___ -> false
let uu___is_HE_BadRequest (projectee : http_error) : Prims.bool=
  match projectee with | HE_BadRequest _0 -> true | uu___ -> false
let __proj__HE_BadRequest__item___0 (projectee : http_error) : Prims.string=
  match projectee with | HE_BadRequest _0 -> _0
let uu___is_HE_BodyTooLarge (projectee : http_error) : Prims.bool=
  match projectee with | HE_BodyTooLarge -> true | uu___ -> false
let uu___is_HE_HeadersTooLarge (projectee : http_error) : Prims.bool=
  match projectee with | HE_HeadersTooLarge -> true | uu___ -> false
let uu___is_HE_MissingCRLF (projectee : http_error) : Prims.bool=
  match projectee with | HE_MissingCRLF -> true | uu___ -> false
type 'a http_result = ('a, http_error) FStar_Pervasives.either
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
let split_path_and_query (uri : Prims.string) :
  (Prims.string * Prims.string)=
  let len = FStar_String.strlen uri in
  let fuel = len + Prims.int_one in
  match find_char uri Prims.int_zero (Prims.of_int (0x3F)) fuel with
  | FStar_Pervasives_Native.None -> (uri, "")
  | FStar_Pervasives_Native.Some i ->
      let path = safe_substring uri Prims.int_zero i in
      let qs_start = i + Prims.int_one in
      let qs = string_suffix uri qs_start in (path, qs)
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
let parse_request_line (line : Prims.string) :
  (Prims.string * Prims.string * Prims.string) http_result=
  if contains_crlf line
  then FStar_Pervasives.Inr HE_MalformedRequestLine
  else
    (let len = FStar_String.strlen line in
     let fuel = len + Prims.int_one in
     match find_char line Prims.int_zero (Prims.of_int (0x20)) fuel with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives.Inr HE_MalformedRequestLine
     | FStar_Pervasives_Native.Some i1 ->
         let meth = safe_substring line Prims.int_zero i1 in
         let rest_start = i1 + Prims.int_one in
         let rest_len =
           if rest_start <= len then len - rest_start else Prims.int_zero in
         let fuel2 = rest_len + Prims.int_one in
         (match find_char line rest_start (Prims.of_int (0x20)) fuel2 with
          | FStar_Pervasives_Native.None ->
              FStar_Pervasives.Inr HE_MalformedRequestLine
          | FStar_Pervasives_Native.Some i2 ->
              if i2 <= rest_start
              then FStar_Pervasives.Inr HE_MalformedRequestLine
              else
                (let uri_len = i2 - rest_start in
                 let uri = safe_substring line rest_start uri_len in
                 let ver_start = i2 + Prims.int_one in
                 let version = string_suffix line ver_start in
                 let fuel3 = (FStar_String.strlen version) + Prims.int_one in
                 match find_char version Prims.int_zero (Prims.of_int (0x20))
                         fuel3
                 with
                 | FStar_Pervasives_Native.Some uu___2 ->
                     FStar_Pervasives.Inr HE_MalformedRequestLine
                 | FStar_Pervasives_Native.None ->
                     if
                       (((FStar_String.strlen meth) = Prims.int_zero) ||
                          ((FStar_String.strlen uri) = Prims.int_zero))
                         || ((FStar_String.strlen version) = Prims.int_zero)
                     then FStar_Pervasives.Inr HE_MalformedRequestLine
                     else FStar_Pervasives.Inl (meth, uri, version))))
let parse_header_line (line : Prims.string) :
  (Prims.string * Prims.string) http_result=
  if contains_crlf line
  then FStar_Pervasives.Inr HE_MalformedHeader
  else
    (let len = FStar_String.strlen line in
     let fuel = len + Prims.int_one in
     match find_char line Prims.int_zero (Prims.of_int (0x3A)) fuel with
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives.Inr HE_MalformedHeader
     | FStar_Pervasives_Native.Some i ->
         let name_raw = safe_substring line Prims.int_zero i in
         let name = ascii_lower_string (trim_ws name_raw) in
         let value_start = i + Prims.int_one in
         let value_raw = string_suffix line value_start in
         let value = trim_ws value_raw in
         if (FStar_String.strlen name) = Prims.int_zero
         then FStar_Pervasives.Inr HE_MalformedHeader
         else FStar_Pervasives.Inl (name, value))
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
let rec parse_header_lines (input : Prims.string) (pos : Prims.nat)
  (head_end : Prims.nat) (acc : (Prims.string * Prims.string) Prims.list)
  (fuel : Prims.nat) : (Prims.string * Prims.string) Prims.list http_result=
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
             (match parse_header_line line with
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
                match parse_header_line line with
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
                | FStar_Pervasives.Inl kv ->
                    let next_pos = crlf_pos + (Prims.of_int (2)) in
                    parse_header_lines input next_pos head_end (kv :: acc)
                      (fuel - Prims.int_one)))
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
let parse_http_request (raw : Prims.string) (max_header_bytes : Prims.nat)
  (max_body_bytes : Prims.nat) : http_request http_result=
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
      then FStar_Pervasives.Inr HE_HeadersTooLarge
      else FStar_Pervasives.Inr HE_MissingCRLF
  | FStar_Pervasives_Native.Some head_end ->
      if head_end > max_header_bytes
      then FStar_Pervasives.Inr HE_HeadersTooLarge
      else
        (let rl_fuel = head_end + Prims.int_one in
         match find_2byte raw Prims.int_zero (Prims.of_int (0x0D))
                 (Prims.of_int (0x0A)) rl_fuel
         with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives.Inr HE_MalformedRequestLine
         | FStar_Pervasives_Native.Some rl_end ->
             if rl_end > head_end
             then FStar_Pervasives.Inr HE_MalformedRequestLine
             else
               (let req_line_len = rl_end in
                let req_line = safe_substring raw Prims.int_zero req_line_len in
                match parse_request_line req_line with
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
                | FStar_Pervasives.Inl (meth, uri, version) ->
                    let uu___2 = split_path_and_query uri in
                    (match uu___2 with
                     | (path, qs) ->
                         let headers_start = rl_end + (Prims.of_int (2)) in
                         let headers_end =
                           if head_end >= headers_start
                           then head_end
                           else headers_start in
                         let headers_len = headers_end - headers_start in
                         let hdr_fuel = headers_len + Prims.int_one in
                         (match parse_header_lines raw headers_start
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
                                match header_lookup_ci headers
                                        "content-length"
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.Some
                                      Prims.int_zero
                                | FStar_Pervasives_Native.Some cl ->
                                    (match parse_nat cl with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some n ->
                                         FStar_Pervasives_Native.Some n) in
                              (match body_len_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives.Inr
                                     (HE_BadRequest "invalid Content-Length")
                               | FStar_Pervasives_Native.Some body_len ->
                                   if body_len > max_body_bytes
                                   then FStar_Pervasives.Inr HE_BodyTooLarge
                                   else
                                     (let effective =
                                        if body_len <= available
                                        then body_len
                                        else available in
                                      let body =
                                        safe_substring raw body_start
                                          effective in
                                      FStar_Pervasives.Inl
                                        {
                                          hr_method = meth;
                                          hr_path = path;
                                          hr_query_str = qs;
                                          hr_version = version;
                                          hr_headers = headers;
                                          hr_body = body
                                        }))))))
let _test_rl_ok : Prims.bool=
  match parse_request_line "GET /query HTTP/1.1" with
  | FStar_Pervasives.Inl (m, u, v) ->
      ((m = "GET") && (u = "/query")) && (v = "HTTP/1.1")
  | FStar_Pervasives.Inr uu___ -> false
let _test_split_with_qs : Prims.bool=
  let uu___ = split_path_and_query "/query?a=1&b=2" in
  match uu___ with | (p, q) -> (p = "/query") && (q = "a=1&b=2")
let _test_split_no_qs : Prims.bool=
  let uu___ = split_path_and_query "/sparql" in
  match uu___ with | (p, q) -> (p = "/sparql") && (q = "")
let _test_header_ok : Prims.bool=
  match parse_header_line "Content-Type: application/sparql-query" with
  | FStar_Pervasives.Inl (n, v) ->
      (n = "content-type") && (v = "application/sparql-query")
  | FStar_Pervasives.Inr uu___ -> false
let _test_lookup_ci : Prims.bool=
  let hs = [("content-type", "application/json"); ("accept", "text/csv")] in
  match header_lookup_ci hs "Content-Type" with
  | FStar_Pervasives_Native.Some v -> v = "application/json"
  | FStar_Pervasives_Native.None -> false
