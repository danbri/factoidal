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
