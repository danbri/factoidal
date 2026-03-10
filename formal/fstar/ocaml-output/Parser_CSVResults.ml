open Prims
let mk_literal (lexical : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    let lit =
      {
        RDF_Graph_Executable.lexical_form = lexical;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = lang
      } in
    (if RDF_Graph_Executable.literal_wf lit
     then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal lit)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let rec split_lines_acc (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) : FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] -> [FStar_List_Tot_Base.rev acc]
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if code = (Prims.of_int (0x0A))
      then (FStar_List_Tot_Base.rev acc) :: (split_lines_acc rest [])
      else
        if code = (Prims.of_int (0x0D))
        then
          (match rest with
           | c2::rest2 ->
               if (FStar_Char.int_of_char c2) = (Prims.of_int (0x0A))
               then (FStar_List_Tot_Base.rev acc) ::
                 (split_lines_acc rest2 [])
               else (FStar_List_Tot_Base.rev acc) ::
                 (split_lines_acc rest [])
           | [] -> [FStar_List_Tot_Base.rev acc])
        else split_lines_acc rest (c :: acc)
let split_lines (s : Prims.string) : Prims.string Prims.list=
  let char_lists = split_lines_acc (FStar_String.list_of_string s) [] in
  FStar_List_Tot_Base.map FStar_String.string_of_list char_lists
let rec remove_trailing_empty (lines : Prims.string Prims.list) :
  Prims.string Prims.list=
  match lines with
  | [] -> []
  | uu___ ->
      let rev = FStar_List_Tot_Base.rev lines in
      (match rev with
       | [] -> []
       | last::rest ->
           if (FStar_String.strlen last) = Prims.int_zero
           then remove_trailing_empty (FStar_List_Tot_Base.rev rest)
           else lines)
let rec csv_split_fields_acc (cs : FStar_Char.char Prims.list)
  (sep : FStar_Char.char) (in_quote : Prims.bool)
  (acc : FStar_Char.char Prims.list) : Prims.string Prims.list=
  match cs with
  | [] -> [FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)]
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if in_quote
      then
        (if code = (Prims.of_int (0x22))
         then
           match rest with
           | c2::rest2 ->
               (if (FStar_Char.int_of_char c2) = (Prims.of_int (0x22))
                then csv_split_fields_acc rest2 sep true (c :: acc)
                else csv_split_fields_acc rest sep false acc)
           | [] ->
               [FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)]
         else csv_split_fields_acc rest sep true (c :: acc))
      else
        if c = sep
        then (FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)) ::
          (csv_split_fields_acc rest sep false [])
        else
          if code = (Prims.of_int (0x22))
          then csv_split_fields_acc rest sep true acc
          else csv_split_fields_acc rest sep false (c :: acc)
let csv_split_fields (line : Prims.string) (sep : FStar_Char.char) :
  Prims.string Prims.list=
  csv_split_fields_acc (FStar_String.list_of_string line) sep false []
let rec tsv_split_fields_acc (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) : Prims.string Prims.list=
  match cs with
  | [] -> [FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)]
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x09))
      then (FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)) ::
        (tsv_split_fields_acc rest [])
      else tsv_split_fields_acc rest (c :: acc)
let tsv_split_fields (line : Prims.string) : Prims.string Prims.list=
  tsv_split_fields_acc (FStar_String.list_of_string line) []
let parse_csv_header (line : Prims.string) :
  RDF_Graph_Executable.var_name Prims.list FStar_Pervasives_Native.option=
  let fields =
    csv_split_fields line (FStar_Char.char_of_int (Prims.of_int (0x2C))) in
  if (FStar_List_Tot_Base.length fields) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.Some fields
let strip_question_mark (s : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  match cs with
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x3F))
      then FStar_String.string_of_list rest
      else s
  | [] -> s
let parse_tsv_header (line : Prims.string) :
  RDF_Graph_Executable.var_name Prims.list FStar_Pervasives_Native.option=
  let fields = tsv_split_fields line in
  if (FStar_List_Tot_Base.length fields) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    FStar_Pervasives_Native.Some
      (FStar_List_Tot_Base.map strip_question_mark fields)
let is_blank_node_str (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  match cs with
  | c1::c2::uu___ ->
      ((FStar_Char.int_of_char c1) = (Prims.of_int (0x5F))) &&
        ((FStar_Char.int_of_char c2) = (Prims.of_int (0x3A)))
  | uu___ -> false
let bnode_label (s : Prims.string) : Prims.string=
  if (FStar_String.strlen s) > (Prims.of_int (2))
  then
    FStar_String.sub s (Prims.of_int (2))
      ((FStar_String.strlen s) - (Prims.of_int (2)))
  else ""
let is_ascii_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let rec all_digits (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest -> (is_ascii_digit c) && (all_digits rest)
let is_numeric_str (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then false
  else
    (match cs with
     | c::uu___1 ->
         let code = FStar_Char.int_of_char c in
         (((is_ascii_digit c) || (code = (Prims.of_int (0x2D)))) ||
            (code = (Prims.of_int (0x2B))))
           ||
           ((code = (Prims.of_int (0x2E))) &&
              ((match cs with
                | uu___2::c2::uu___3 -> is_ascii_digit c2
                | uu___2 -> false)))
     | [] -> false)
let looks_like_iri (s : Prims.string) : Prims.bool=
  RDF_Graph_Executable.is_iri s
let parse_csv_value (field : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if (FStar_String.strlen field) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if is_blank_node_str field
    then
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_BNode (bnode_label field))
    else
      if looks_like_iri field
      then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI field)
      else
        mk_literal field RDF_Graph_Executable.xsd_string
          FStar_Pervasives_Native.None
let parse_csv_row (line : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list=
  let fields =
    csv_split_fields line (FStar_Char.char_of_int (Prims.of_int (0x2C))) in
  FStar_List_Tot_Base.map parse_csv_value fields
let parse_tsv_iri (s : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  let len = FStar_String.strlen s in
  if len >= (Prims.of_int (2))
  then
    match cs with
    | c::uu___ ->
        (if (FStar_Char.int_of_char c) = (Prims.of_int (0x3C))
         then
           let last_chars = FStar_String.list_of_string s in
           let rev = FStar_List_Tot_Base.rev last_chars in
           match rev with
           | cl::uu___1 ->
               (if (FStar_Char.int_of_char cl) = (Prims.of_int (0x3E))
                then
                  let inner =
                    FStar_String.sub s Prims.int_one
                      (len - (Prims.of_int (2))) in
                  (if RDF_Graph_Executable.is_iri inner
                   then
                     FStar_Pervasives_Native.Some
                       (RDF_Graph_Executable.T_IRI inner)
                   else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None)
           | [] -> FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.None)
    | [] -> FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.None
let rec find_double_caret (cs : FStar_Char.char Prims.list) (idx : Prims.nat)
  : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c1::rest ->
      if (FStar_Char.int_of_char c1) = (Prims.of_int (0x5E))
      then
        (match rest with
         | c2::uu___ ->
             if (FStar_Char.int_of_char c2) = (Prims.of_int (0x5E))
             then FStar_Pervasives_Native.Some idx
             else find_double_caret rest (idx + Prims.int_one)
         | [] -> FStar_Pervasives_Native.None)
      else find_double_caret rest (idx + Prims.int_one)
let rec find_last_at (cs : FStar_Char.char Prims.list) (idx : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      let sub_result = find_last_at rest (idx + Prims.int_one) in
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x40))
      then
        (match sub_result with
         | FStar_Pervasives_Native.Some uu___ -> sub_result
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some idx)
      else sub_result
let strip_quotes (s : Prims.string) : Prims.string=
  let len = FStar_String.strlen s in
  if len >= (Prims.of_int (2))
  then
    let cs = FStar_String.list_of_string s in
    match cs with
    | c::uu___ ->
        (if (FStar_Char.int_of_char c) = (Prims.of_int (0x22))
         then
           let rev = FStar_List_Tot_Base.rev cs in
           match rev with
           | cl::uu___1 ->
               (if (FStar_Char.int_of_char cl) = (Prims.of_int (0x22))
                then
                  FStar_String.sub s Prims.int_one (len - (Prims.of_int (2)))
                else s)
           | [] -> s
         else s)
    | [] -> s
  else s
let starts_with_quote (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  match cs with
  | c::uu___ -> (FStar_Char.int_of_char c) = (Prims.of_int (0x22))
  | [] -> false
let extract_angle_iri (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len >= (Prims.of_int (2))
  then
    let cs = FStar_String.list_of_string s in
    match cs with
    | c::uu___ ->
        (if (FStar_Char.int_of_char c) = (Prims.of_int (0x3C))
         then
           let rev = FStar_List_Tot_Base.rev cs in
           match rev with
           | cl::uu___1 ->
               (if (FStar_Char.int_of_char cl) = (Prims.of_int (0x3E))
                then
                  FStar_Pervasives_Native.Some
                    (FStar_String.sub s Prims.int_one
                       (len - (Prims.of_int (2))))
                else FStar_Pervasives_Native.None)
           | [] -> FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.None)
    | [] -> FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.None
let parse_tsv_quoted_literal (s : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (2))
  then FStar_Pervasives_Native.None
  else
    (let caret_pos = find_double_caret cs Prims.int_zero in
     match caret_pos with
     | FStar_Pervasives_Native.Some cp ->
         if (cp >= (Prims.of_int (2))) && (cp <= len)
         then
           let quoted_part = FStar_String.sub s Prims.int_zero cp in
           let lexical = strip_quotes quoted_part in
           let rest_str =
             if (cp + (Prims.of_int (2))) < len
             then
               FStar_String.sub s (cp + (Prims.of_int (2)))
                 ((len - cp) - (Prims.of_int (2)))
             else "" in
           (match extract_angle_iri rest_str with
            | FStar_Pervasives_Native.Some dt_str ->
                if RDF_Graph_Executable.is_iri dt_str
                then mk_literal lexical dt_str FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         else FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.None ->
         let at_pos = find_last_at cs Prims.int_zero in
         (match at_pos with
          | FStar_Pervasives_Native.Some ap ->
              if (ap >= (Prims.of_int (2))) && (ap < len)
              then
                let prev_char = FStar_String.index s (ap - Prims.int_one) in
                (if
                   (FStar_Char.int_of_char prev_char) = (Prims.of_int (0x22))
                 then
                   let quoted_part = FStar_String.sub s Prims.int_zero ap in
                   let lexical = strip_quotes quoted_part in
                   let lang =
                     if (ap + Prims.int_one) < len
                     then
                       FStar_String.sub s (ap + Prims.int_one)
                         ((len - ap) - Prims.int_one)
                     else "" in
                   mk_literal lexical RDF_Graph_Executable.rdf_lang_string
                     (FStar_Pervasives_Native.Some lang)
                 else
                   (let lexical = strip_quotes s in
                    mk_literal lexical RDF_Graph_Executable.xsd_string
                      FStar_Pervasives_Native.None))
              else
                (let lexical = strip_quotes s in
                 mk_literal lexical RDF_Graph_Executable.xsd_string
                   FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.None ->
              let lexical = strip_quotes s in
              mk_literal lexical RDF_Graph_Executable.xsd_string
                FStar_Pervasives_Native.None))
let rec is_all_digits (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest -> (is_ascii_digit c) && (is_all_digits rest)
let is_integer_str (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  match cs with
  | [] -> false
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if (code = (Prims.of_int (0x2D))) || (code = (Prims.of_int (0x2B)))
      then
        ((FStar_List_Tot_Base.length rest) > Prims.int_zero) &&
          (is_all_digits rest)
      else (is_ascii_digit c) && (is_all_digits rest)
let rec has_dot (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | c::rest ->
      ((FStar_Char.int_of_char c) = (Prims.of_int (0x2E))) || (has_dot rest)
let is_decimal_str (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then false
  else
    (let sign_stripped =
       match cs with
       | c::rest ->
           let code = FStar_Char.int_of_char c in
           if
             (code = (Prims.of_int (0x2D))) || (code = (Prims.of_int (0x2B)))
           then rest
           else cs
       | [] -> cs in
     (has_dot sign_stripped) &&
       (let rec all_digit_or_dot l =
          match l with
          | [] -> true
          | c::rest ->
              ((is_ascii_digit c) ||
                 ((FStar_Char.int_of_char c) = (Prims.of_int (0x2E))))
                && (all_digit_or_dot rest) in
        all_digit_or_dot sign_stripped))
let rec has_exponent (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      ((code = (Prims.of_int (0x65))) || (code = (Prims.of_int (0x45)))) ||
        (has_exponent rest)
let is_double_str (s : Prims.string) : Prims.bool=
  has_exponent (FStar_String.list_of_string s)
let parse_tsv_value (field : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if (FStar_String.strlen field) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let cs = FStar_String.list_of_string field in
     match cs with
     | c::uu___1 ->
         let code = FStar_Char.int_of_char c in
         if code = (Prims.of_int (0x3C))
         then parse_tsv_iri field
         else
           if code = (Prims.of_int (0x22))
           then parse_tsv_quoted_literal field
           else
             if code = (Prims.of_int (0x5F))
             then
               (if is_blank_node_str field
                then
                  FStar_Pervasives_Native.Some
                    (RDF_Graph_Executable.T_BNode (bnode_label field))
                else
                  mk_literal field RDF_Graph_Executable.xsd_string
                    FStar_Pervasives_Native.None)
             else
               if is_integer_str field
               then
                 mk_literal field RDF_Graph_Executable.xsd_integer
                   FStar_Pervasives_Native.None
               else
                 if is_double_str field
                 then
                   mk_literal field RDF_Graph_Executable.xsd_double
                     FStar_Pervasives_Native.None
                 else
                   if is_decimal_str field
                   then
                     mk_literal field RDF_Graph_Executable.xsd_decimal
                       FStar_Pervasives_Native.None
                   else
                     mk_literal field RDF_Graph_Executable.xsd_string
                       FStar_Pervasives_Native.None
     | [] -> FStar_Pervasives_Native.None)
let parse_tsv_row (line : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list=
  let fields = tsv_split_fields line in
  FStar_List_Tot_Base.map parse_tsv_value fields
let rec pad_row
  (row :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list)
  (n : Prims.nat) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list=
  if n = Prims.int_zero
  then []
  else
    (match row with
     | [] -> FStar_Pervasives_Native.None :: (pad_row [] (n - Prims.int_one))
     | v::rest -> v :: (pad_row rest (n - Prims.int_one)))
let parse_csv_results (input : Prims.string) :
  (RDF_Graph_Executable.var_name Prims.list * RDF_Graph_Executable.rdf_term
    FStar_Pervasives_Native.option Prims.list Prims.list)
    FStar_Pervasives_Native.option=
  let lines = remove_trailing_empty (split_lines input) in
  match lines with
  | [] -> FStar_Pervasives_Native.None
  | header_line::data_lines ->
      (match parse_csv_header header_line with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some vars ->
           let nvars = FStar_List_Tot_Base.length vars in
           let rows =
             FStar_List_Tot_Base.map
               (fun line -> let raw = parse_csv_row line in pad_row raw nvars)
               data_lines in
           FStar_Pervasives_Native.Some (vars, rows))
let parse_tsv_results (input : Prims.string) :
  (RDF_Graph_Executable.var_name Prims.list * RDF_Graph_Executable.rdf_term
    FStar_Pervasives_Native.option Prims.list Prims.list)
    FStar_Pervasives_Native.option=
  let lines = remove_trailing_empty (split_lines input) in
  match lines with
  | [] -> FStar_Pervasives_Native.None
  | header_line::data_lines ->
      (match parse_tsv_header header_line with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some vars ->
           let nvars = FStar_List_Tot_Base.length vars in
           let rows =
             FStar_List_Tot_Base.map
               (fun line -> let raw = parse_tsv_row line in pad_row raw nvars)
               data_lines in
           FStar_Pervasives_Native.Some (vars, rows))
let rec build_solution_mapping
  (vars : RDF_Graph_Executable.var_name Prims.list)
  (vals :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list)
  : RDF_Graph_Executable.solution_mapping=
  match (vars, vals) with
  | ([], uu___) -> []
  | (uu___::uu___1, []) -> []
  | (v::vrest, oval::orest) ->
      (match oval with
       | FStar_Pervasives_Native.Some term -> (v, term) ::
           (build_solution_mapping vrest orest)
       | FStar_Pervasives_Native.None -> build_solution_mapping vrest orest)
let results_to_solution_mappings
  (vars : RDF_Graph_Executable.var_name Prims.list)
  (rows :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
      Prims.list)
  : RDF_Graph_Executable.solution_mapping Prims.list=
  FStar_List_Tot_Base.map (build_solution_mapping vars) rows
let parse_csv_to_solutions (input : Prims.string) :
  (RDF_Graph_Executable.var_name Prims.list *
    RDF_Graph_Executable.solution_mapping Prims.list)
    FStar_Pervasives_Native.option=
  match parse_csv_results input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (vars, rows) ->
      FStar_Pervasives_Native.Some
        (vars, (results_to_solution_mappings vars rows))
let parse_tsv_to_solutions (input : Prims.string) :
  (RDF_Graph_Executable.var_name Prims.list *
    RDF_Graph_Executable.solution_mapping Prims.list)
    FStar_Pervasives_Native.option=
  match parse_tsv_results input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (vars, rows) ->
      FStar_Pervasives_Native.Some
        (vars, (results_to_solution_mappings vars rows))
