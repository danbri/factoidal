open Prims
let (status_text : Prims.int -> Prims.string) =
  fun code ->
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
let (uu___is_CORS_Off : cors_policy -> Prims.bool) =
  fun projectee -> match projectee with | CORS_Off -> true | uu___ -> false
let (uu___is_CORS_Any : cors_policy -> Prims.bool) =
  fun projectee -> match projectee with | CORS_Any -> true | uu___ -> false
let (uu___is_CORS_List : cors_policy -> Prims.bool) =
  fun projectee ->
    match projectee with | CORS_List _0 -> true | uu___ -> false
let (__proj__CORS_List__item___0 : cors_policy -> Prims.string Prims.list) =
  fun projectee -> match projectee with | CORS_List _0 -> _0
let (common_cors_headers : Prims.string Prims.list) =
  ["Access-Control-Allow-Methods: GET, POST, OPTIONS";
  "Access-Control-Allow-Headers: Content-Type, Authorization, Cf-Access-Jwt-Assertion, Cf-Access-Authenticated-User-Email, X-Authid";
  "Timing-Allow-Origin: *";
  "Access-Control-Max-Age: 86400"]
let rec (string_mem : Prims.string -> Prims.string Prims.list -> Prims.bool)
  =
  fun x ->
    fun xs ->
      match xs with
      | [] -> false
      | y::rest -> if x = y then true else string_mem x rest
let (cors_headers :
  cors_policy ->
    Prims.string FStar_Pervasives_Native.option -> Prims.string Prims.list)
  =
  fun policy ->
    fun origin ->
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
let (result_cap_response_body : Prims.int -> Prims.string) =
  fun cap ->
    FStar_String.concat ""
      ["{\"error\":\"result_cardinality_cap_exceeded\",\"cap\":";
      Prims.string_of_int cap;
      ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"]
let (query_timeout_response_body : Prims.int -> Prims.string) =
  fun secs ->
    FStar_String.concat ""
      ["{\"error\":\"query_timeout\",\"seconds\":";
      Prims.string_of_int secs;
      ",\"hint\":\"Add LIMIT or bind more triple-pattern terms.\"}\n"]
