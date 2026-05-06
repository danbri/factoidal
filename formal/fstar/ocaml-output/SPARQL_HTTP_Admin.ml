open Prims
let (render_recent_query_json :
  Prims.string ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          Prims.int ->
            Prims.int ->
              Prims.string ->
                Prims.string -> Prims.string -> Prims.string -> Prims.string)
  =
  fun started_at_str ->
    fun query_escaped ->
      fun form ->
        fun status ->
          fun rows ->
            fun body_bytes ->
              fun parse_ms_str ->
                fun eval_ms_str ->
                  fun format_ms_str ->
                    fun total_ms_str ->
                      Prims.strcat "{\"started_at\":"
                        (Prims.strcat started_at_str
                           (Prims.strcat ",\"query\":\""
                              (Prims.strcat query_escaped
                                 (Prims.strcat "\",\"form\":\""
                                    (Prims.strcat form
                                       (Prims.strcat "\",\"status\":"
                                          (Prims.strcat
                                             (Prims.string_of_int status)
                                             (Prims.strcat ",\"rows\":"
                                                (Prims.strcat
                                                   (Prims.string_of_int rows)
                                                   (Prims.strcat
                                                      ",\"body_bytes\":"
                                                      (Prims.strcat
                                                         (Prims.string_of_int
                                                            body_bytes)
                                                         (Prims.strcat
                                                            ",\"parse_ms\":"
                                                            (Prims.strcat
                                                               parse_ms_str
                                                               (Prims.strcat
                                                                  ",\"eval_ms\":"
                                                                  (Prims.strcat
                                                                    eval_ms_str
                                                                    (Prims.strcat
                                                                    ",\"format_ms\":"
                                                                    (Prims.strcat
                                                                    format_ms_str
                                                                    (Prims.strcat
                                                                    ",\"total_ms\":"
                                                                    (Prims.strcat
                                                                    total_ms_str
                                                                    "}")))))))))))))))))))
let rec (join_array_elements : Prims.string Prims.list -> Prims.string) =
  fun xs ->
    match xs with
    | [] -> ""
    | x::[] -> x
    | x::rest -> Prims.strcat x (Prims.strcat "," (join_array_elements rest))
let (render_recent_queries_envelope :
  Prims.int ->
    Prims.string ->
      Prims.int ->
        Prims.int -> Prims.int -> Prims.string Prims.list -> Prims.string)
  =
  fun total_queries_seen ->
    fun total_wall_ms_str ->
      fun status_2xx ->
        fun status_4xx ->
          fun status_5xx ->
            fun recent_jsons ->
              Prims.strcat "{\"total_queries_seen\":"
                (Prims.strcat (Prims.string_of_int total_queries_seen)
                   (Prims.strcat ",\"total_wall_ms\":"
                      (Prims.strcat total_wall_ms_str
                         (Prims.strcat ",\"status_2xx\":"
                            (Prims.strcat (Prims.string_of_int status_2xx)
                               (Prims.strcat ",\"status_4xx\":"
                                  (Prims.strcat
                                     (Prims.string_of_int status_4xx)
                                     (Prims.strcat ",\"status_5xx\":"
                                        (Prims.strcat
                                           (Prims.string_of_int status_5xx)
                                           (Prims.strcat ",\"recent\":["
                                              (Prims.strcat
                                                 (join_array_elements
                                                    recent_jsons) "]}\n")))))))))))
