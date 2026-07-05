open Prims
let csvw_ns : Prims.string= "http://www.w3.org/ns/csvw#"
let csvw_TableGroup : RDF_Term.wf_iri= Prims.strcat csvw_ns "TableGroup"
let csvw_Table : RDF_Term.wf_iri= Prims.strcat csvw_ns "Table"
let csvw_Row : RDF_Term.wf_iri= Prims.strcat csvw_ns "Row"
let csvw_table_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "table"
let csvw_row_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "row"
let csvw_rownum : RDF_Term.wf_iri= Prims.strcat csvw_ns "rownum"
let csvw_url_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "url"
let csvw_describes : RDF_Term.wf_iri= Prims.strcat csvw_ns "describes"
let csvw_base_name_to_iri (n : Prims.string) : Prims.string=
  if n = "html"
  then "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"
  else
    if n = "xml"
    then "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
    else
      if n = "json"
      then Prims.strcat csvw_ns "JSON"
      else Prims.strcat "http://www.w3.org/2001/XMLSchema#" n
let csvw_datatype_iri
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  Prims.string=
  match dt with
  | FStar_Pervasives_Native.None -> RDF_Term.xsd_string
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Named n) ->
      csvw_base_name_to_iri n
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Object
      (base_opt, uu___, uu___1, uu___2, uu___3)) ->
      (match base_opt with
       | FStar_Pervasives_Native.Some n -> csvw_base_name_to_iri n
       | FStar_Pervasives_Native.None -> RDF_Term.xsd_string)
let csvw_build_literal (lex : Prims.string) (dt : Prims.string) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if RDF_Term.is_iri dt
  then
    let l =
      {
        RDF_Term.lexical_form = lex;
        RDF_Term.datatype = dt;
        RDF_Term.lang_tag = FStar_Pervasives_Native.None
      } in
    (if RDF_Term.literal_wf l
     then FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
type csvw_col_spec =
  {
  cs_name: Prims.string ;
  cs_virtual: Prims.bool ;
  cs_suppress: Prims.bool ;
  cs_datatype: CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option ;
  cs_about_url: Prims.string FStar_Pervasives_Native.option ;
  cs_property_url: Prims.string FStar_Pervasives_Native.option ;
  cs_value_url: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcsvw_col_spec__item__cs_name (projectee : csvw_col_spec) :
  Prims.string=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_name
let __proj__Mkcsvw_col_spec__item__cs_virtual (projectee : csvw_col_spec) :
  Prims.bool=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_virtual
let __proj__Mkcsvw_col_spec__item__cs_suppress (projectee : csvw_col_spec) :
  Prims.bool=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_suppress
let __proj__Mkcsvw_col_spec__item__cs_datatype (projectee : csvw_col_spec) :
  CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_datatype
let __proj__Mkcsvw_col_spec__item__cs_about_url (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_about_url
let __proj__Mkcsvw_col_spec__item__cs_property_url
  (projectee : csvw_col_spec) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_property_url
let __proj__Mkcsvw_col_spec__item__cs_value_url (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url;_} -> cs_value_url
let csvw_opt_bool (o : Prims.bool FStar_Pervasives_Native.option) :
  Prims.bool=
  match o with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let csvw_col_spec_of_column (ts : CSVW_Metadata.csvw_table_schema)
  (c : CSVW_Metadata.csvw_column) : csvw_col_spec=
  {
    cs_name =
      (match c.CSVW_Metadata.col_name with
       | FStar_Pervasives_Native.Some n -> n
       | FStar_Pervasives_Native.None ->
           (match c.CSVW_Metadata.col_titles with | t::uu___ -> t | [] -> ""));
    cs_virtual = (csvw_opt_bool c.CSVW_Metadata.col_virtual);
    cs_suppress = (csvw_opt_bool c.CSVW_Metadata.col_suppress_output);
    cs_datatype = (c.CSVW_Metadata.col_datatype);
    cs_about_url =
      (match c.CSVW_Metadata.col_about_url with
       | FStar_Pervasives_Native.Some a -> FStar_Pervasives_Native.Some a
       | FStar_Pervasives_Native.None -> ts.CSVW_Metadata.ts_about_url);
    cs_property_url =
      (match c.CSVW_Metadata.col_property_url with
       | FStar_Pervasives_Native.Some p -> FStar_Pervasives_Native.Some p
       | FStar_Pervasives_Native.None -> ts.CSVW_Metadata.ts_property_url);
    cs_value_url =
      (match c.CSVW_Metadata.col_value_url with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> ts.CSVW_Metadata.ts_value_url)
  }
let csvw_positional_name (i : Prims.int) : Prims.string=
  Prims.strcat "_col." (Prims.string_of_int (i + Prims.int_one))
let csvw_col_specs_from_header (header_cells : Prims.string Prims.list) :
  csvw_col_spec Prims.list=
  FStar_List_Tot_Base.mapi
    (fun i h ->
       {
         cs_name = (if h = "" then csvw_positional_name i else h);
         cs_virtual = false;
         cs_suppress = false;
         cs_datatype = FStar_Pervasives_Native.None;
         cs_about_url = FStar_Pervasives_Native.None;
         cs_property_url = FStar_Pervasives_Native.None;
         cs_value_url = FStar_Pervasives_Native.None
       }) header_cells
let csvw_build_col_specs
  (ts_opt : CSVW_Metadata.csvw_table_schema FStar_Pervasives_Native.option)
  (header_cells : Prims.string Prims.list) : csvw_col_spec Prims.list=
  match ts_opt with
  | FStar_Pervasives_Native.Some ts ->
      if Prims.uu___is_Cons ts.CSVW_Metadata.ts_columns
      then
        FStar_List_Tot_Base.map (csvw_col_spec_of_column ts)
          ts.CSVW_Metadata.ts_columns
      else csvw_col_specs_from_header header_cells
  | FStar_Pervasives_Native.None -> csvw_col_specs_from_header header_cells
let csvw_header_row_count
  (dia_opt : CSVW_Metadata.csvw_dialect FStar_Pervasives_Native.option) :
  Prims.nat=
  match dia_opt with
  | FStar_Pervasives_Native.None -> Prims.int_one
  | FStar_Pervasives_Native.Some dia ->
      (match dia.CSVW_Metadata.dia_header_row_count with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero then n else Prims.int_one
       | FStar_Pervasives_Native.None ->
           (match dia.CSVW_Metadata.dia_header with
            | FStar_Pervasives_Native.Some false -> Prims.int_zero
            | uu___ -> Prims.int_one))
let csvw_skip_rows_count
  (dia_opt : CSVW_Metadata.csvw_dialect FStar_Pervasives_Native.option) :
  Prims.nat=
  match dia_opt with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some dia ->
      (match dia.CSVW_Metadata.dia_skip_rows with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero then n else Prims.int_zero
       | FStar_Pervasives_Native.None -> Prims.int_zero)
let rec csvw_drop : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then l
    else
      (match l with
       | [] -> []
       | uu___1::tl -> csvw_drop (n - Prims.int_one) tl)
let rec csvw_index_from :
  'a . Prims.nat -> 'a Prims.list -> (Prims.nat * 'a) Prims.list =
  fun n l ->
    match l with
    | [] -> []
    | hd::tl -> (n, hd) :: (csvw_index_from (n + Prims.int_one) tl)
let rec csvw_zip_specs_cells (specs : csvw_col_spec Prims.list)
  (cells : Prims.string Prims.list) :
  (csvw_col_spec * Prims.string) Prims.list=
  match (specs, cells) with
  | (s::srest, c::crest) -> (s, c) :: (csvw_zip_specs_cells srest crest)
  | (uu___, uu___1) -> []
let csvw_effective_table_url (base_iri : Prims.string)
  (fallback_url : Prims.string) (tbl : CSVW_Metadata.csvw_table) :
  Prims.string=
  let raw =
    match tbl.CSVW_Metadata.tbl_url with
    | FStar_Pervasives_Native.Some u -> u
    | FStar_Pervasives_Native.None -> fallback_url in
  RDF_IRI.resolve_iri_v2 base_iri raw
let csvw_row_lookup
  (phys_bindings : (Prims.string * Prims.string) Prims.list)
  (row_num : Prims.nat) (source_row_num : Prims.nat) (v : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if v = "_row"
  then FStar_Pervasives_Native.Some (Prims.string_of_int row_num)
  else
    if v = "_sourceRow"
    then FStar_Pervasives_Native.Some (Prims.string_of_int source_row_num)
    else FStar_List_Tot_Base.assoc v phys_bindings
let csvw_term_of_subject (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let csvw_cell_object (table_url_resolved : Prims.string)
  (spec : csvw_col_spec)
  (cell_text : Prims.string FStar_Pervasives_Native.option)
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match spec.cs_value_url with
  | FStar_Pervasives_Native.Some tmpl ->
      let raw = CSVW_URITemplate.csvw_expand_template lookup tmpl in
      let resolved = RDF_IRI.resolve_iri_v2 table_url_resolved raw in
      if RDF_Term.is_iri resolved
      then FStar_Pervasives_Native.Some (RDF_Term.T_IRI resolved)
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None ->
      (match cell_text with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some txt ->
           if txt = ""
           then FStar_Pervasives_Native.None
           else csvw_build_literal txt (csvw_datatype_iri spec.cs_datatype))
let csvw_process_cell (table_url_resolved : Prims.string)
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (default_subject : RDF_Term.subject) (spec : csvw_col_spec)
  (cell_text : Prims.string FStar_Pervasives_Native.option) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  if spec.cs_suppress
  then (default_subject, [])
  else
    (let cur_lookup v =
       if v = "_name"
       then FStar_Pervasives_Native.Some (spec.cs_name)
       else lookup v in
     let subj =
       match spec.cs_about_url with
       | FStar_Pervasives_Native.Some tmpl ->
           let raw = CSVW_URITemplate.csvw_expand_template cur_lookup tmpl in
           let resolved = RDF_IRI.resolve_iri_v2 table_url_resolved raw in
           if RDF_Term.is_iri resolved
           then RDF_Term.S_IRI resolved
           else default_subject
       | FStar_Pervasives_Native.None -> default_subject in
     let raw =
       match spec.cs_property_url with
       | FStar_Pervasives_Native.Some tmpl ->
           RDF_IRI.resolve_iri_v2 table_url_resolved
             (CSVW_URITemplate.csvw_expand_template cur_lookup tmpl)
       | FStar_Pervasives_Native.None ->
           Prims.strcat table_url_resolved
             (Prims.strcat "#"
                (SPARQL11_Algebra.string_encode_uri spec.cs_name)) in
     let pred_valid =
       if RDF_Term.is_iri raw
       then FStar_Pervasives_Native.Some raw
       else FStar_Pervasives_Native.None in
     match pred_valid with
     | FStar_Pervasives_Native.None -> (subj, [])
     | FStar_Pervasives_Native.Some pred_str ->
         (match csvw_cell_object table_url_resolved spec cell_text cur_lookup
          with
          | FStar_Pervasives_Native.None -> (subj, [])
          | FStar_Pervasives_Native.Some obj ->
              (subj,
                [{
                   RDF_Triple.s = subj;
                   RDF_Triple.p = pred_str;
                   RDF_Triple.o = obj
                 }])))
let csvw_row_cell_results (table_url_resolved : Prims.string)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list) Prims.list=
  let phys_specs =
    FStar_List_Tot_Base.filter (fun s -> Prims.op_Negation s.cs_virtual)
      col_specs in
  let virt_specs =
    FStar_List_Tot_Base.filter (fun s -> s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let phys_bindings =
    FStar_List_Tot_Base.map
      (fun p ->
         (((FStar_Pervasives_Native.fst p).cs_name),
           (FStar_Pervasives_Native.snd p))) phys_pairs in
  let lookup = csvw_row_lookup phys_bindings row_num source_row_num in
  let default_subject =
    RDF_Term.S_BNode
      (Prims.strcat "csvwrow_"
         (Prims.strcat
            (SPARQL11_Algebra.string_encode_uri table_url_resolved)
            (Prims.strcat "_" (Prims.string_of_int source_row_num)))) in
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map
       (fun p ->
          csvw_process_cell table_url_resolved lookup default_subject
            (FStar_Pervasives_Native.fst p)
            (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.snd p)))
       phys_pairs)
    (FStar_List_Tot_Base.map
       (fun s ->
          csvw_process_cell table_url_resolved lookup default_subject s
            FStar_Pervasives_Native.None) virt_specs)
let csvw_row_triples_minimal (table_url_resolved : Prims.string)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd
    (csvw_row_cell_results table_url_resolved col_specs row_num
       source_row_num cells)
let csvw_convert_table_minimal (base_iri : Prims.string)
  (fallback_url : Prims.string) (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  RDF_Triple.triple Prims.list=
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_n = (csvw_skip_rows_count dia) + (csvw_header_row_count dia) in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let header_cells =
    if (csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else [] in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let col_specs =
    csvw_build_col_specs tbl.CSVW_Metadata.tbl_table_schema header_cells in
  let indexed = csvw_index_from Prims.int_zero data_rows in
  FStar_List_Tot_Base.concatMap
    (fun p ->
       let uu___ = p in
       match uu___ with
       | (i, cells) ->
           csvw_row_triples_minimal table_url_resolved col_specs
             (i + Prims.int_one) ((skip_n + i) + Prims.int_one) cells)
    indexed
let csvw_row_url (table_url_resolved : Prims.string)
  (source_row_num : Prims.nat) : Prims.string=
  Prims.strcat table_url_resolved
    (Prims.strcat "#row=" (Prims.string_of_int source_row_num))
let csvw_row_triples_standard (table_url_resolved : Prims.string)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  let per_col =
    csvw_row_cell_results table_url_resolved col_specs row_num source_row_num
      cells in
  let row_node =
    RDF_Term.S_BNode
      (Prims.strcat "csvwR_"
         (Prims.strcat
            (SPARQL11_Algebra.string_encode_uri table_url_resolved)
            (Prims.strcat "_" (Prims.string_of_int source_row_num)))) in
  let row_url = csvw_row_url table_url_resolved source_row_num in
  let row_meta =
    FStar_List_Tot_Base.op_At
      [{
         RDF_Triple.s = row_node;
         RDF_Triple.p = RDFS_Closure.rdf_type;
         RDF_Triple.o = (RDF_Term.T_IRI csvw_Row)
       };
      {
        RDF_Triple.s = row_node;
        RDF_Triple.p = csvw_rownum;
        RDF_Triple.o =
          (RDF_Term.T_Literal
             {
               RDF_Term.lexical_form = (Prims.string_of_int row_num);
               RDF_Term.datatype = RDF_Term.xsd_integer;
               RDF_Term.lang_tag = FStar_Pervasives_Native.None
             })
      }]
      (if RDF_Term.is_iri row_url
       then
         [{
            RDF_Triple.s = row_node;
            RDF_Triple.p = csvw_url_pred;
            RDF_Triple.o = (RDF_Term.T_IRI row_url)
          }]
       else []) in
  let describes =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         let uu___ = r in
         match uu___ with
         | (subj, ts) ->
             if Prims.uu___is_Nil ts
             then []
             else
               [{
                  RDF_Triple.s = row_node;
                  RDF_Triple.p = csvw_describes;
                  RDF_Triple.o = (csvw_term_of_subject subj)
                }]) per_col in
  let cell_triples =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd per_col in
  (row_node,
    (FStar_List_Tot_Base.op_At row_meta
       (FStar_List_Tot_Base.op_At describes cell_triples)))
let csvw_convert_table_standard (base_iri : Prims.string)
  (fallback_url : Prims.string) (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_n = (csvw_skip_rows_count dia) + (csvw_header_row_count dia) in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let header_cells =
    if (csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else [] in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let col_specs =
    csvw_build_col_specs tbl.CSVW_Metadata.tbl_table_schema header_cells in
  let indexed = csvw_index_from Prims.int_zero data_rows in
  let row_results =
    FStar_List_Tot_Base.map
      (fun p ->
         let uu___ = p in
         match uu___ with
         | (i, cells) ->
             csvw_row_triples_standard table_url_resolved col_specs
               (i + Prims.int_one) ((skip_n + i) + Prims.int_one) cells)
      indexed in
  let t_node =
    RDF_Term.S_BNode
      (Prims.strcat "csvwT_"
         (SPARQL11_Algebra.string_encode_uri table_url_resolved)) in
  let row_links =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         [{
            RDF_Triple.s = t_node;
            RDF_Triple.p = csvw_row_pred;
            RDF_Triple.o =
              (csvw_term_of_subject (FStar_Pervasives_Native.fst r))
          }]) row_results in
  let row_all =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd row_results in
  let t_meta =
    FStar_List_Tot_Base.op_At
      [{
         RDF_Triple.s = t_node;
         RDF_Triple.p = RDFS_Closure.rdf_type;
         RDF_Triple.o = (RDF_Term.T_IRI csvw_Table)
       }]
      (if RDF_Term.is_iri table_url_resolved
       then
         [{
            RDF_Triple.s = t_node;
            RDF_Triple.p = csvw_url_pred;
            RDF_Triple.o = (RDF_Term.T_IRI table_url_resolved)
          }]
       else []) in
  (t_node,
    (FStar_List_Tot_Base.op_At t_meta
       (FStar_List_Tot_Base.op_At row_links row_all)))
let csvw_convert_document_minimal (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       let uu___ = t in
       match uu___ with
       | (tbl, fallback_url, rows) ->
           csvw_convert_table_minimal base_iri fallback_url tbl rows)
    tables_with_rows
let csvw_group_node : RDF_Term.subject= RDF_Term.S_BNode "csvwG"
let csvw_convert_document_standard (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : RDF_Triple.triple Prims.list=
  let table_results =
    FStar_List_Tot_Base.map
      (fun t ->
         let uu___ = t in
         match uu___ with
         | (tbl, fallback_url, rows) ->
             csvw_convert_table_standard base_iri fallback_url tbl rows)
      tables_with_rows in
  let g_meta =
    [{
       RDF_Triple.s = csvw_group_node;
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI csvw_TableGroup)
     }] in
  let table_links =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         [{
            RDF_Triple.s = csvw_group_node;
            RDF_Triple.p = csvw_table_pred;
            RDF_Triple.o =
              (csvw_term_of_subject (FStar_Pervasives_Native.fst r))
          }]) table_results in
  let table_all =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd table_results in
  FStar_List_Tot_Base.op_At g_meta
    (FStar_List_Tot_Base.op_At table_links table_all)
let csvw_no_metadata_table : CSVW_Metadata.csvw_table=
  {
    CSVW_Metadata.tbl_url = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_dialect = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_table_schema = FStar_Pervasives_Native.None
  }
