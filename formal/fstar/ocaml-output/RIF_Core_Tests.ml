open Prims
let default_fuel : Prims.nat= (Prims.of_int (100))
let saturate_with_program (rif_xml : Prims.string)
  (premise : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_graph FStar_Pervasives_Native.option=
  match Parser_RIFXML.parse_rif_program rif_xml with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some program ->
      FStar_Pervasives_Native.Some
        (RIF_Core_Eval.fixpoint premise program fuel)
let parse_rif_imports (rif_xml : Prims.string) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match Parser_RIFXML.parse_rif_program_with_imports rif_xml with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (imports, uu___) ->
      FStar_Pervasives_Native.Some imports
let run_rif_ask_triple (rif_xml : Prims.string)
  (premise : RDF_Graph_Executable.rdf_graph)
  (conclusion : RDF_Graph_Executable.triple) : Prims.bool=
  match saturate_with_program rif_xml premise default_fuel with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some sat ->
      RDF_Graph_Executable.mem_triple conclusion sat
let run_rif_ask_with (rif_xml : Prims.string)
  (premise : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  (check : RDF_Graph_Executable.rdf_graph -> Prims.bool) : Prims.bool=
  match saturate_with_program rif_xml premise fuel with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some sat -> check sat
let rec run_rif_select_rows (rif_xml : Prims.string)
  (premise : RDF_Graph_Executable.rdf_graph) (fuel : Prims.nat)
  (rows : RDF_Graph_Executable.triple Prims.list) : Prims.bool=
  match rows with
  | [] -> true
  | row::rest ->
      if
        run_rif_ask_with rif_xml premise fuel
          (fun g -> RDF_Graph_Executable.mem_triple row g)
      then run_rif_select_rows rif_xml premise fuel rest
      else false
let run_rif_entailment_check (rif_xml : Prims.string)
  (premise : RDF_Graph_Executable.rdf_graph)
  (rows : RDF_Graph_Executable.triple Prims.list) : Prims.bool=
  run_rif_select_rows rif_xml premise default_fuel rows
