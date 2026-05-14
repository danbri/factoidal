open Prims
let parse_error_status : Prims.nat= (Prims.of_int (400))
let eval_error_status : Prims.nat= (Prims.of_int (500))
let success_status : Prims.nat= (Prims.of_int (200))
let parse_error_body (msg : Prims.string) : Prims.string=
  Prims.strcat "SPARQL parse error: " (Prims.strcat msg "\n")
let eval_error_body (msg : Prims.string) (backtrace : Prims.string) :
  Prims.string=
  Prims.strcat "Query evaluation error: "
    (Prims.strcat msg
       (Prims.strcat "\n" (Prims.strcat "Backtrace:\n" backtrace)))
let parse_error_content_type : Prims.string= "text/plain; charset=utf-8"
let eval_error_content_type : Prims.string= "text/plain; charset=utf-8"
type serialiser_strategy =
  | SS_BooleanJson 
  | SS_BooleanXml 
  | SS_RowsJson 
  | SS_RowsXml 
  | SS_RowsCsv 
  | SS_RowsTsv 
let uu___is_SS_BooleanJson (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_BooleanJson -> true | uu___ -> false
let uu___is_SS_BooleanXml (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_BooleanXml -> true | uu___ -> false
let uu___is_SS_RowsJson (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_RowsJson -> true | uu___ -> false
let uu___is_SS_RowsXml (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_RowsXml -> true | uu___ -> false
let uu___is_SS_RowsCsv (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_RowsCsv -> true | uu___ -> false
let uu___is_SS_RowsTsv (projectee : serialiser_strategy) : Prims.bool=
  match projectee with | SS_RowsTsv -> true | uu___ -> false
let serialiser_strategy_for_ask (fmt : SPARQL_Protocol.response_format) :
  (serialiser_strategy * Prims.string)=
  match fmt with
  | SPARQL_Protocol.RF_Xml ->
      (SS_BooleanXml,
        (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Xml))
  | uu___ ->
      (SS_BooleanJson,
        (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Json))
let serialiser_strategy_for_select (fmt : SPARQL_Protocol.response_format) :
  (serialiser_strategy * Prims.string)=
  match fmt with
  | SPARQL_Protocol.RF_Xml ->
      (SS_RowsXml, (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Xml))
  | SPARQL_Protocol.RF_Csv ->
      (SS_RowsCsv, (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Csv))
  | SPARQL_Protocol.RF_Tsv ->
      (SS_RowsTsv, (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Tsv))
  | uu___ ->
      (SS_RowsJson,
        (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Json))
let serialiser_strategy_for_construct_describe
  (fmt : SPARQL_Protocol.response_format) :
  (serialiser_strategy * Prims.string)=
  match fmt with
  | SPARQL_Protocol.RF_Xml ->
      (SS_RowsXml, (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Xml))
  | uu___ ->
      (SS_RowsJson,
        (SPARQL_Protocol.content_type_for SPARQL_Protocol.RF_Json))
let make_parse_error_response (msg : Prims.string) :
  SPARQL_HTTP_Response.response_body=
  {
    SPARQL_HTTP_Response.rb_status = parse_error_status;
    SPARQL_HTTP_Response.rb_content_type = parse_error_content_type;
    SPARQL_HTTP_Response.rb_body = (parse_error_body msg)
  }
let make_eval_error_response (msg : Prims.string) (backtrace : Prims.string)
  : SPARQL_HTTP_Response.response_body=
  {
    SPARQL_HTTP_Response.rb_status = eval_error_status;
    SPARQL_HTTP_Response.rb_content_type = eval_error_content_type;
    SPARQL_HTTP_Response.rb_body = (eval_error_body msg backtrace)
  }
let row_count_overflows (max_rows : Prims.nat)
  (rows : SPARQL_Protocol.binding_row Prims.list) : Prims.bool=
  let strict_cap = SPARQL_Eval_Limits.mk_cap (max_rows + Prims.int_one) in
  SPARQL_Eval_Limits.cap_reached strict_cap (FStar_List_Tot_Base.length rows)
let make_result_cap_response (max_rows : Prims.nat) :
  SPARQL_HTTP_Response.response_body=
  {
    SPARQL_HTTP_Response.rb_status = (Prims.of_int (413));
    SPARQL_HTTP_Response.rb_content_type = "application/json; charset=utf-8";
    SPARQL_HTTP_Response.rb_body =
      (SPARQL_HTTP_Response.result_cap_response_body max_rows)
  }
let body_for_ask_strategy (strat : serialiser_strategy) (b : Prims.bool) :
  Prims.string=
  match strat with
  | SS_BooleanXml -> SPARQL_Protocol.serialise_response_boolean_xml b
  | uu___ -> SPARQL_Protocol.serialise_response_boolean_json b
let body_for_rows_strategy (strat : serialiser_strategy)
  (vars : Prims.string Prims.list)
  (rows : SPARQL_Protocol.binding_row Prims.list) : Prims.string=
  match strat with
  | SS_RowsXml -> SPARQL_Protocol.serialise_response_xml vars rows
  | SS_RowsCsv -> SPARQL_Protocol.serialise_response_csv vars rows
  | SS_RowsTsv -> SPARQL_Protocol.serialise_response_tsv vars rows
  | uu___ -> SPARQL_Protocol.serialise_response_json vars rows
let run_query (qform : SPARQL11_Algebra.query_form)
  (fmt : SPARQL_Protocol.response_format) (max_rows : Prims.nat)
  (vars : Prims.string Prims.list)
  (ask_result : Prims.bool FStar_Pervasives_Native.option)
  (rows_result :
    SPARQL_Protocol.binding_row Prims.list FStar_Pervasives_Native.option)
  : SPARQL_HTTP_Response.response_body=
  match qform with
  | SPARQL11_Algebra.QF_Ask ->
      let b =
        match ask_result with
        | FStar_Pervasives_Native.Some v -> v
        | FStar_Pervasives_Native.None -> false in
      let uu___ = serialiser_strategy_for_ask fmt in
      (match uu___ with
       | (strat, ct) ->
           {
             SPARQL_HTTP_Response.rb_status = success_status;
             SPARQL_HTTP_Response.rb_content_type = ct;
             SPARQL_HTTP_Response.rb_body = (body_for_ask_strategy strat b)
           })
  | SPARQL11_Algebra.QF_Select uu___ ->
      let rows =
        match rows_result with
        | FStar_Pervasives_Native.Some r -> r
        | FStar_Pervasives_Native.None -> [] in
      if row_count_overflows max_rows rows
      then make_result_cap_response max_rows
      else
        (let uu___2 = serialiser_strategy_for_select fmt in
         match uu___2 with
         | (strat, ct) ->
             {
               SPARQL_HTTP_Response.rb_status = success_status;
               SPARQL_HTTP_Response.rb_content_type = ct;
               SPARQL_HTTP_Response.rb_body =
                 (body_for_rows_strategy strat vars rows)
             })
  | SPARQL11_Algebra.QF_Construct uu___ ->
      let rows =
        match rows_result with
        | FStar_Pervasives_Native.Some r -> r
        | FStar_Pervasives_Native.None -> [] in
      if row_count_overflows max_rows rows
      then make_result_cap_response max_rows
      else
        (let uu___2 = serialiser_strategy_for_construct_describe fmt in
         match uu___2 with
         | (strat, ct) ->
             {
               SPARQL_HTTP_Response.rb_status = success_status;
               SPARQL_HTTP_Response.rb_content_type = ct;
               SPARQL_HTTP_Response.rb_body =
                 (body_for_rows_strategy strat vars rows)
             })
  | SPARQL11_Algebra.QF_Describe uu___ ->
      let rows =
        match rows_result with
        | FStar_Pervasives_Native.Some r -> r
        | FStar_Pervasives_Native.None -> [] in
      if row_count_overflows max_rows rows
      then make_result_cap_response max_rows
      else
        (let uu___2 = serialiser_strategy_for_construct_describe fmt in
         match uu___2 with
         | (strat, ct) ->
             {
               SPARQL_HTTP_Response.rb_status = success_status;
               SPARQL_HTTP_Response.rb_content_type = ct;
               SPARQL_HTTP_Response.rb_body =
                 (body_for_rows_strategy strat vars rows)
             })
