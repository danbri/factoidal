(* Sparql_query_bridge: Thin wrapper providing parse_query via the
   F*-extracted SPARQL11_Parser module.

   The F*-extracted SPARQL parser (SPARQL11.Parser.fst) currently has
   assume val stubs for the core parse functions (parse_expr,
   parse_group_graph_pattern, parse_select_query). Until those are
   implemented in F*, this bridge raises Unsupported for all queries.

   This module provides the Sparql_parser interface that w3c_runner expects:
   - parse_query : string -> SPARQL11_Algebra.query
   - exception Parse_error of string
   - exception Unsupported of string
*)

exception Parse_error of string
exception Unsupported of string

let parse_query (_input : string) : SPARQL11_Algebra.query =
  raise (Unsupported "SPARQL query parser not yet implemented in F* (assume val stubs)")
