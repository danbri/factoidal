open Prims
let status_text (code : Prims.int) : Prims.string=
  if code = (Prims.of_int (200))
  then "OK"
  else
    if code = (Prims.of_int (204))
    then "No Content"
    else
      if code = (Prims.of_int (303))
      then "See Other"
      else
        if code = (Prims.of_int (400))
        then "Bad Request"
        else
          if code = (Prims.of_int (403))
          then "Forbidden"
          else
            if code = (Prims.of_int (404))
            then "Not Found"
            else
              if code = (Prims.of_int (405))
              then "Method Not Allowed"
              else
                if code = (Prims.of_int (413))
                then "Payload Too Large"
                else
                  if code = (Prims.of_int (500))
                  then "Internal Server Error"
                  else
                    if code = (Prims.of_int (501))
                    then "Not Implemented"
                    else
                      if code = (Prims.of_int (503))
                      then "Service Unavailable"
                      else
                        if code = (Prims.of_int (504))
                        then "Gateway Timeout"
                        else "Unknown"
type cors_policy =
  | CORS_Off 
  | CORS_Any 
  | CORS_List of Prims.string Prims.list 
let uu___is_CORS_Off (projectee : cors_policy) : Prims.bool=
  match projectee with | CORS_Off -> true | uu___ -> false
let uu___is_CORS_Any (projectee : cors_policy) : Prims.bool=
  match projectee with | CORS_Any -> true | uu___ -> false
let uu___is_CORS_List (projectee : cors_policy) : Prims.bool=
  match projectee with | CORS_List _0 -> true | uu___ -> false
let __proj__CORS_List__item___0 (projectee : cors_policy) :
  Prims.string Prims.list= match projectee with | CORS_List _0 -> _0
let common_cors_headers : Prims.string Prims.list=
  ["Access-Control-Allow-Methods: GET, POST, OPTIONS";
  "Access-Control-Allow-Headers: Content-Type, Authorization, Cf-Access-Jwt-Assertion, Cf-Access-Authenticated-User-Email, X-Authid";
  "Timing-Allow-Origin: *";
  "Access-Control-Max-Age: 86400"]
let rec string_mem (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | y::rest -> if x = y then true else string_mem x rest
let cors_headers (policy : cors_policy)
  (origin : Prims.string FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  match policy with
  | CORS_Off -> []
  | CORS_Any -> "Access-Control-Allow-Origin: *" :: common_cors_headers
  | CORS_List allowed ->
      (match origin with
       | FStar_Pervasives_Native.Some o ->
           if string_mem o allowed
           then (Prims.strcat "Access-Control-Allow-Origin: " o) ::
             "Vary: Origin" :: common_cors_headers
           else []
       | FStar_Pervasives_Native.None -> [])
let result_cap_response_body (cap : Prims.int) : Prims.string=
  FStar_String.concat ""
    ["{\"error\":\"result_cardinality_cap_exceeded\",\"cap\":";
    Prims.string_of_int cap;
    ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"]
let query_timeout_response_body (secs : Prims.int) : Prims.string=
  FStar_String.concat ""
    ["{\"error\":\"query_timeout\",\"seconds\":";
    Prims.string_of_int secs;
    ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"]
let is_ascii_ws (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n = (Prims.of_int (0x20))) || (n = (Prims.of_int (0x09)))) ||
     (n = (Prims.of_int (0x0A))))
    || (n = (Prims.of_int (0x0D)))
let rec drop_leading_ws (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest -> if is_ascii_ws c then drop_leading_ws rest else cs
let trim_ascii (s : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  let l = drop_leading_ws cs in
  let r =
    FStar_List_Tot_Base.rev (drop_leading_ws (FStar_List_Tot_Base.rev l)) in
  FStar_String.string_of_list r
let rec map_trim (xs : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with | [] -> [] | x::rest -> (trim_ascii x) :: (map_trim rest)
let rec drop_empty (xs : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> []
  | x::rest -> if x = "" then drop_empty rest else x :: (drop_empty rest)
let parse_cors_value (raw : Prims.string) : cors_policy=
  let v = trim_ascii raw in
  if v = "*"
  then CORS_Any
  else
    (let parts = drop_empty (map_trim (FStar_String.split [44] v)) in
     match parts with | [] -> CORS_Off | uu___1 -> CORS_List parts)
let rec join_with_comma_space (xs : Prims.string Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | x::[] -> x
  | x::rest ->
      Prims.strcat x (Prims.strcat ", " (join_with_comma_space rest))
let cors_mode_to_string (p : cors_policy) : Prims.string=
  match p with
  | CORS_Off -> "off (no Access-Control-* headers)"
  | CORS_Any -> "any origin (Access-Control-Allow-Origin: *)"
  | CORS_List origins ->
      Prims.strcat "allowlist ("
        (Prims.strcat (join_with_comma_space origins) ")")
let rec concat_header_lines (xs : Prims.string Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | h::rest ->
      Prims.strcat h (Prims.strcat "\r\n" (concat_header_lines rest))
let render_response_head (status : Prims.int) (content_type : Prims.string)
  (body_len : Prims.int) (extra_headers : Prims.string Prims.list) :
  Prims.string=
  let reason = status_text status in
  Prims.strcat "HTTP/1.1 "
    (Prims.strcat (Prims.string_of_int status)
       (Prims.strcat " "
          (Prims.strcat reason
             (Prims.strcat "\r\n"
                (Prims.strcat "Content-Type: "
                   (Prims.strcat content_type
                      (Prims.strcat "\r\n"
                         (Prims.strcat "Content-Length: "
                            (Prims.strcat (Prims.string_of_int body_len)
                               (Prims.strcat "\r\n"
                                  (Prims.strcat "Connection: close\r\n"
                                     (Prims.strcat
                                        (concat_header_lines extra_headers)
                                        "\r\n"))))))))))))
