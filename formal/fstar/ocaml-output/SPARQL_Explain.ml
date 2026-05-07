open Prims
type bound_status =
  | BS_Var of Prims.string 
  | BS_Hit of Prims.string 
  | BS_Miss of Prims.string 
  | BS_Other of Prims.string 
let (uu___is_BS_Var : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Var _0 -> true | uu___ -> false
let (__proj__BS_Var__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Var _0 -> _0
let (uu___is_BS_Hit : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Hit _0 -> true | uu___ -> false
let (__proj__BS_Hit__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Hit _0 -> _0
let (uu___is_BS_Miss : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Miss _0 -> true | uu___ -> false
let (__proj__BS_Miss__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Miss _0 -> _0
let (uu___is_BS_Other : bound_status -> Prims.bool) =
  fun projectee ->
    match projectee with | BS_Other _0 -> true | uu___ -> false
let (__proj__BS_Other__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Other _0 -> _0
let (bs_string : bound_status -> Prims.string) =
  fun b ->
    match b with
    | BS_Var v -> Prims.strcat "?" (Prims.strcat v " (free)")
    | BS_Hit s -> Prims.strcat s " [hit]"
    | BS_Miss s ->
        Prims.strcat s
          " [MISS \226\128\148 term not in dictionary; result definitely empty]"
    | BS_Other s -> Prims.strcat s " [non-encodable]"
let (bs_json : bound_status -> Prims.string) =
  fun bs ->
    match bs with
    | BS_Var v ->
        Prims.strcat "{\"kind\":\"var\",\"name\":\""
          (Prims.strcat (SPARQL_JSON_Escape.json_escape v) "\"}")
    | BS_Hit s ->
        Prims.strcat "{\"kind\":\"hit\",\"term\":\""
          (Prims.strcat (SPARQL_JSON_Escape.json_escape s) "\"}")
    | BS_Miss s ->
        Prims.strcat "{\"kind\":\"miss\",\"term\":\""
          (Prims.strcat (SPARQL_JSON_Escape.json_escape s) "\"}")
    | BS_Other s ->
        Prims.strcat "{\"kind\":\"other\",\"term\":\""
          (Prims.strcat (SPARQL_JSON_Escape.json_escape s) "\"}")
type tp_explain =
  {
  tpx_label: Prims.string ;
  tpx_tp: SPARQL11_Algebra.triple_pattern ;
  tpx_s_status: bound_status ;
  tpx_p_status: bound_status ;
  tpx_o_status: bound_status ;
  tpx_bound_built: Prims.bool ;
  tpx_pred_present: Prims.bool FStar_Pervasives_Native.option ;
  tpx_estimate: Prims.int }
let (__proj__Mktp_explain__item__tpx_label : tp_explain -> Prims.string) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_label
let (__proj__Mktp_explain__item__tpx_tp :
  tp_explain -> SPARQL11_Algebra.triple_pattern) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_tp
let (__proj__Mktp_explain__item__tpx_s_status : tp_explain -> bound_status) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_s_status
let (__proj__Mktp_explain__item__tpx_p_status : tp_explain -> bound_status) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_p_status
let (__proj__Mktp_explain__item__tpx_o_status : tp_explain -> bound_status) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_o_status
let (__proj__Mktp_explain__item__tpx_bound_built : tp_explain -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_bound_built
let (__proj__Mktp_explain__item__tpx_pred_present :
  tp_explain -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} ->
        tpx_pred_present
let (__proj__Mktp_explain__item__tpx_estimate : tp_explain -> Prims.int) =
  fun projectee ->
    match projectee with
    | { tpx_label; tpx_tp; tpx_s_status; tpx_p_status; tpx_o_status;
        tpx_bound_built; tpx_pred_present; tpx_estimate;_} -> tpx_estimate
let (opt_bool_json :
  Prims.bool FStar_Pervasives_Native.option -> Prims.string) =
  fun ob ->
    match ob with
    | FStar_Pervasives_Native.None -> "null"
    | FStar_Pervasives_Native.Some (true) -> "true"
    | FStar_Pervasives_Native.Some (false) -> "false"
let (tpx_json : tp_explain -> Prims.string) =
  fun tpx ->
    Prims.strcat "{\"label\":\""
      (Prims.strcat (SPARQL_JSON_Escape.json_escape tpx.tpx_label)
         (Prims.strcat "\",\"pattern\":\""
            (Prims.strcat
               (SPARQL_JSON_Escape.json_escape
                  (RDF_Pretty.triple_pattern_short_explain tpx.tpx_tp))
               (Prims.strcat "\",\"s\":"
                  (Prims.strcat (bs_json tpx.tpx_s_status)
                     (Prims.strcat ",\"p\":"
                        (Prims.strcat (bs_json tpx.tpx_p_status)
                           (Prims.strcat ",\"o\":"
                              (Prims.strcat (bs_json tpx.tpx_o_status)
                                 (Prims.strcat ",\"bound_built\":"
                                    (Prims.strcat
                                       (if tpx.tpx_bound_built
                                        then "true"
                                        else "false")
                                       (Prims.strcat
                                          ",\"predicate_present\":"
                                          (Prims.strcat
                                             (opt_bool_json
                                                tpx.tpx_pred_present)
                                             (Prims.strcat ",\"estimate\":"
                                                (Prims.strcat
                                                   (Prims.string_of_int
                                                      tpx.tpx_estimate) "}")))))))))))))))
