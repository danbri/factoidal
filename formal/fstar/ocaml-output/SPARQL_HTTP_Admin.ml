open Prims
let render_recent_query_json (started_at_str : Prims.string)
  (query_escaped : Prims.string) (form : Prims.string) (status : Prims.int)
  (rows : Prims.int) (body_bytes : Prims.int) (parse_ms_str : Prims.string)
  (eval_ms_str : Prims.string) (format_ms_str : Prims.string)
  (total_ms_str : Prims.string) : Prims.string=
  Prims.strcat "{\"started_at\":"
    (Prims.strcat started_at_str
       (Prims.strcat ",\"query\":\""
          (Prims.strcat query_escaped
             (Prims.strcat "\",\"form\":\""
                (Prims.strcat form
                   (Prims.strcat "\",\"status\":"
                      (Prims.strcat (Prims.string_of_int status)
                         (Prims.strcat ",\"rows\":"
                            (Prims.strcat (Prims.string_of_int rows)
                               (Prims.strcat ",\"body_bytes\":"
                                  (Prims.strcat
                                     (Prims.string_of_int body_bytes)
                                     (Prims.strcat ",\"parse_ms\":"
                                        (Prims.strcat parse_ms_str
                                           (Prims.strcat ",\"eval_ms\":"
                                              (Prims.strcat eval_ms_str
                                                 (Prims.strcat
                                                    ",\"format_ms\":"
                                                    (Prims.strcat
                                                       format_ms_str
                                                       (Prims.strcat
                                                          ",\"total_ms\":"
                                                          (Prims.strcat
                                                             total_ms_str "}")))))))))))))))))))
let rec join_array_elements (xs : Prims.string Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | x::[] -> x
  | x::rest -> Prims.strcat x (Prims.strcat "," (join_array_elements rest))
let render_recent_queries_envelope (total_queries_seen : Prims.int)
  (total_wall_ms_str : Prims.string) (status_2xx : Prims.int)
  (status_4xx : Prims.int) (status_5xx : Prims.int)
  (recent_jsons : Prims.string Prims.list) : Prims.string=
  Prims.strcat "{\"total_queries_seen\":"
    (Prims.strcat (Prims.string_of_int total_queries_seen)
       (Prims.strcat ",\"total_wall_ms\":"
          (Prims.strcat total_wall_ms_str
             (Prims.strcat ",\"status_2xx\":"
                (Prims.strcat (Prims.string_of_int status_2xx)
                   (Prims.strcat ",\"status_4xx\":"
                      (Prims.strcat (Prims.string_of_int status_4xx)
                         (Prims.strcat ",\"status_5xx\":"
                            (Prims.strcat (Prims.string_of_int status_5xx)
                               (Prims.strcat ",\"recent\":["
                                  (Prims.strcat
                                     (join_array_elements recent_jsons)
                                     "]}\n")))))))))))
let render_timing_log_line (form : Prims.string) (status : Prims.int)
  (rows : Prims.int) (body_bytes : Prims.int) (parse_ms_str : Prims.string)
  (eval_ms_str : Prims.string) (format_ms_str : Prims.string)
  (total_ms_str : Prims.string) (q_summary : Prims.string) : Prims.string=
  Prims.strcat "[timing] form="
    (Prims.strcat form
       (Prims.strcat " status="
          (Prims.strcat (Prims.string_of_int status)
             (Prims.strcat " rows="
                (Prims.strcat (Prims.string_of_int rows)
                   (Prims.strcat " body="
                      (Prims.strcat (Prims.string_of_int body_bytes)
                         (Prims.strcat "B"
                            (Prims.strcat " parse="
                               (Prims.strcat parse_ms_str
                                  (Prims.strcat "ms"
                                     (Prims.strcat " eval="
                                        (Prims.strcat eval_ms_str
                                           (Prims.strcat "ms"
                                              (Prims.strcat " format="
                                                 (Prims.strcat format_ms_str
                                                    (Prims.strcat "ms"
                                                       (Prims.strcat
                                                          " total="
                                                          (Prims.strcat
                                                             total_ms_str
                                                             (Prims.strcat
                                                                "ms"
                                                                (Prims.strcat
                                                                   " q="
                                                                   q_summary)))))))))))))))))))))
let render_timing_response_header (parse_ms_str : Prims.string)
  (eval_ms_str : Prims.string) (format_ms_str : Prims.string)
  (total_ms_str : Prims.string) : Prims.string=
  Prims.strcat "Server-Timing: parse;dur="
    (Prims.strcat parse_ms_str
       (Prims.strcat ", eval;dur="
          (Prims.strcat eval_ms_str
             (Prims.strcat ", format;dur="
                (Prims.strcat format_ms_str
                   (Prims.strcat ", total;dur=" total_ms_str))))))
let truncate_for_log (s : Prims.string) (n : Prims.nat) : Prims.string=
  let len = FStar_String.strlen s in
  if len <= n
  then s
  else Prims.strcat (FStar_String.sub s Prims.int_zero n) "..."
