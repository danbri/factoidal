open Prims
let rif_ns : Prims.string= "http://www.w3.org/2007/rif#"
let rdf_ns : Prims.string= "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rec find_last_colon_aux (cs : FStar_Char.char Prims.list)
  (idx : Prims.nat) (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
      then
        find_last_colon_aux rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_colon_aux rest (idx + Prims.int_one) last
let find_last_colon (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  find_last_colon_aux (FStar_String.list_of_string s) Prims.int_zero
    FStar_Pervasives_Native.None
let local_name (tag : Prims.string) : Prims.string=
  match find_last_colon tag with
  | FStar_Pervasives_Native.None -> tag
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen tag in
      if (pos + Prims.int_one) >= len
      then ""
      else
        FStar_String.sub tag (pos + Prims.int_one)
          ((len - pos) - Prims.int_one)
let tag_is (expected : Prims.string) (tag : Prims.string) : Prims.bool=
  (local_name tag) = expected
let rec first_child_with_local_name (name : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match children with
  | [] -> FStar_Pervasives_Native.None
  | hd::rest ->
      (match hd with
       | Parser_XML.XElement (t, uu___, uu___1) ->
           if tag_is name t
           then FStar_Pervasives_Native.Some hd
           else first_child_with_local_name name rest
       | uu___ -> first_child_with_local_name name rest)
let rec children_with_local_name (name : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  match children with
  | [] -> []
  | hd::rest ->
      (match hd with
       | Parser_XML.XElement (t, uu___, uu___1) ->
           if tag_is name t
           then hd :: (children_with_local_name name rest)
           else children_with_local_name name rest
       | uu___ -> children_with_local_name name rest)
let rec child_elements_only (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  match children with
  | [] -> []
  | hd::rest ->
      (match hd with
       | Parser_XML.XElement (uu___, uu___1, uu___2) -> hd ::
           (child_elements_only rest)
       | uu___ -> child_elements_only rest)
let rec collect_leaf_text (children : Parser_XML.xml_node Prims.list) :
  Prims.string=
  match children with
  | [] -> ""
  | hd::rest ->
      let here =
        match hd with
        | Parser_XML.XText t -> t
        | Parser_XML.XCDATA t -> t
        | uu___ -> "" in
      FStar_String.concat "" [here; collect_leaf_text rest]
let element_text (n : Parser_XML.xml_node) : Prims.string=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      collect_leaf_text children
  | uu___ -> ""
let trim_ws (s : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  let rec drop_left xs =
    match xs with
    | [] -> []
    | c::rest ->
        let code = FStar_Char.int_of_char c in
        if
          (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09))))
             || (code = (Prims.of_int (0x0A))))
            || (code = (Prims.of_int (0x0D)))
        then drop_left rest
        else xs in
  let trimmed = drop_left cs in
  let reversed = FStar_List_Tot_Base.rev trimmed in
  let trimmed_back = drop_left reversed in
  FStar_String.string_of_list (FStar_List_Tot_Base.rev trimmed_back)
let is_iri_type_marker (ty : Prims.string) : Prims.bool=
  ((ty = (FStar_String.concat "" [rif_ns; "iri"])) || (ty = "iri")) ||
    ((local_name ty) = "iri")
let is_local_type_marker (ty : Prims.string) : Prims.bool=
  ((ty = (FStar_String.concat "" [rif_ns; "local"])) || (ty = "local")) ||
    ((local_name ty) = "local")
let local_to_iri (lex : Prims.string) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  let urn_iri = FStar_String.concat "" ["urn:rif-local:"; lex] in
  if RDF_Graph_Executable.is_iri urn_iri
  then
    FStar_Pervasives_Native.Some
      (RIF_Core_Syntax.mk_const (RDF_Graph_Executable.T_IRI urn_iri))
  else FStar_Pervasives_Native.None
let typed_literal_const (ty : Prims.string) (lex : Prims.string) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  if
    (RDF_Graph_Executable.is_iri ty) &&
      (ty <> RDF_Graph_Executable.rdf_lang_string)
  then
    FStar_Pervasives_Native.Some
      (RIF_Core_Syntax.mk_const
         (RDF_Graph_Executable.T_Literal
            {
              RDF_Graph_Executable.lexical_form = lex;
              RDF_Graph_Executable.datatype = ty;
              RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
            }))
  else FStar_Pervasives_Native.None
let is_plain_literal_type_marker (ty : Prims.string) : Prims.bool=
  ((ty = (FStar_String.concat "" [rdf_ns; "PlainLiteral"])) ||
     (ty = "PlainLiteral"))
    || ((local_name ty) = "PlainLiteral")
let rec find_last_at_aux (cs : FStar_Char.char Prims.list) (idx : Prims.nat)
  (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x40))
      then
        find_last_at_aux rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_at_aux rest (idx + Prims.int_one) last
let find_last_at (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  find_last_at_aux (FStar_String.list_of_string s) Prims.int_zero
    FStar_Pervasives_Native.None
let plain_literal_const (lex : Prims.string) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  match find_last_at lex with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen lex in
      if pos >= len
      then FStar_Pervasives_Native.None
      else
        (let text = FStar_String.sub lex Prims.int_zero pos in
         let lang =
           FStar_String.sub lex (pos + Prims.int_one)
             ((len - pos) - Prims.int_one) in
         if (FStar_String.strlen lang) = Prims.int_zero
         then
           FStar_Pervasives_Native.Some
             (RIF_Core_Syntax.mk_const
                (RDF_Graph_Executable.T_Literal
                   {
                     RDF_Graph_Executable.lexical_form = text;
                     RDF_Graph_Executable.datatype =
                       RDF_Graph_Executable.xsd_string;
                     RDF_Graph_Executable.lang_tag =
                       FStar_Pervasives_Native.None
                   }))
         else
           FStar_Pervasives_Native.Some
             (RIF_Core_Syntax.mk_const
                (RDF_Graph_Executable.T_Literal
                   {
                     RDF_Graph_Executable.lexical_form = text;
                     RDF_Graph_Executable.datatype =
                       RDF_Graph_Executable.rdf_lang_string;
                     RDF_Graph_Executable.lang_tag =
                       (FStar_Pervasives_Native.Some lang)
                   })))
let const_from_type (ty : Prims.string) (lex : Prims.string) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  if is_iri_type_marker ty
  then
    (if RDF_Graph_Executable.is_iri lex
     then
       FStar_Pervasives_Native.Some
         (RIF_Core_Syntax.mk_const (RDF_Graph_Executable.T_IRI lex))
     else FStar_Pervasives_Native.None)
  else
    if is_local_type_marker ty
    then local_to_iri lex
    else
      if is_plain_literal_type_marker ty
      then plain_literal_const lex
      else typed_literal_const ty lex
let parse_const (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, attrs, children) ->
      let ty_opt = Parser_XML.find_attr "type" attrs in
      let lex = trim_ws (collect_leaf_text children) in
      (match ty_opt with
       | FStar_Pervasives_Native.Some ty -> const_from_type ty lex
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some
             (RIF_Core_Syntax.mk_const
                (RDF_Graph_Executable.T_Literal
                   {
                     RDF_Graph_Executable.lexical_form = lex;
                     RDF_Graph_Executable.datatype =
                       RDF_Graph_Executable.xsd_string;
                     RDF_Graph_Executable.lang_tag =
                       FStar_Pervasives_Native.None
                   })))
  | uu___ -> FStar_Pervasives_Native.None
let parse_var (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let raw = trim_ws (collect_leaf_text children) in
      if (FStar_String.strlen raw) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (RIF_Core_Syntax.mk_var raw)
  | uu___ -> FStar_Pervasives_Native.None
let rec list_collect_some :
  'a .
    'a FStar_Pervasives_Native.option Prims.list ->
      'a Prims.list FStar_Pervasives_Native.option
  =
  fun xs ->
    match xs with
    | [] -> FStar_Pervasives_Native.Some []
    | (FStar_Pervasives_Native.None)::uu___ -> FStar_Pervasives_Native.None
    | (FStar_Pervasives_Native.Some x)::rest ->
        (match list_collect_some rest with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ys ->
             FStar_Pervasives_Native.Some (x :: ys))
let rec parse_term_fuel (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if tag_is "Const" tag
         then parse_const n
         else
           if tag_is "Var" tag
           then parse_var n
           else
             if tag_is "External" tag
             then
               (match first_child_with_local_name "content" children with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some content_node ->
                    (match content_node with
                     | Parser_XML.XElement (uu___4, uu___5, cchildren) ->
                         (match child_elements_only cchildren with
                          | inner::[] ->
                              (match inner with
                               | Parser_XML.XElement (itag, uu___6, uu___7)
                                   ->
                                   if tag_is "Expr" itag
                                   then
                                     (match parse_op_and_args_fuel inner
                                              (fuel - Prims.int_one)
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          (op, args) ->
                                          FStar_Pervasives_Native.Some
                                            (RIF_Core_Syntax.RIF_TermExternal
                                               (op, args)))
                                   else FStar_Pervasives_Native.None
                               | uu___6 -> FStar_Pervasives_Native.None)
                          | uu___6 -> FStar_Pervasives_Native.None)
                     | uu___4 -> FStar_Pervasives_Native.None))
             else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
and parse_op_and_args_fuel (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  (RDF_Graph_Executable.wf_iri * RIF_Core_Syntax.rif_term Prims.list)
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (uu___1, uu___2, children) ->
         let op_n = first_child_with_local_name "op" children in
         let args_n = first_child_with_local_name "args" children in
         (match op_n with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some op_node ->
              (match parse_term_host_fuel op_node (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.Some (RIF_Core_Syntax.RIF_Const
                   (RDF_Graph_Executable.T_IRI pi)) ->
                   let arg_terms =
                     match args_n with
                     | FStar_Pervasives_Native.None -> []
                     | FStar_Pervasives_Native.Some args_node ->
                         FStar_List_Tot_Base.fold_right
                           (fun c acc ->
                              match c with
                              | Parser_XML.XElement (uu___3, uu___4, uu___5)
                                  ->
                                  (parse_term_fuel c (fuel - Prims.int_one))
                                  :: acc
                              | uu___3 -> acc)
                           (Parser_XML.element_children args_node) [] in
                   (match list_collect_some arg_terms with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some args ->
                        FStar_Pervasives_Native.Some (pi, args))
               | uu___3 -> FStar_Pervasives_Native.None))
     | uu___1 -> FStar_Pervasives_Native.None)
and parse_term_host_fuel (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (uu___1, uu___2, children) ->
         (match child_elements_only children with
          | [] -> FStar_Pervasives_Native.None
          | first::uu___3 -> parse_term_fuel first (fuel - Prims.int_one))
     | uu___1 -> FStar_Pervasives_Native.None)
let parse_term (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  parse_term_fuel n (Prims.of_int (1000))
let parse_term_host (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_term FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match child_elements_only children with
       | [] -> FStar_Pervasives_Native.None
       | first::uu___2 -> parse_term first)
  | uu___ -> FStar_Pervasives_Native.None
let parse_atom_element (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_atom FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let op_n = first_child_with_local_name "op" children in
      let args_n = first_child_with_local_name "args" children in
      (match op_n with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some op_node ->
           (match parse_term_host op_node with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some pred ->
                let arg_terms =
                  match args_n with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some args_node ->
                      FStar_List_Tot_Base.fold_right
                        (fun c acc ->
                           match c with
                           | Parser_XML.XElement (uu___2, uu___3, uu___4) ->
                               (parse_term c) :: acc
                           | uu___2 -> acc)
                        (Parser_XML.element_children args_node) [] in
                (match arg_terms with
                 | [] ->
                     FStar_Pervasives_Native.Some
                       (RIF_Core_Syntax.RIF_Uniterm (pred, []))
                 | (FStar_Pervasives_Native.Some a)::[] ->
                     FStar_Pervasives_Native.Some
                       (RIF_Core_Syntax.RIF_Uniterm (pred, [a]))
                 | (FStar_Pervasives_Native.Some
                     s)::(FStar_Pervasives_Native.Some o)::[] ->
                     FStar_Pervasives_Native.Some
                       (RIF_Core_Syntax.RIF_Triple (s, pred, o))
                 | uu___2 -> FStar_Pervasives_Native.None)))
  | uu___ -> FStar_Pervasives_Native.None
let parse_slot_pair (slot : Parser_XML.xml_node)
  (obj : RIF_Core_Syntax.rif_term) :
  RIF_Core_Syntax.rif_atom FStar_Pervasives_Native.option=
  match slot with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match child_elements_only children with
       | k::v::[] ->
           (match ((parse_term k), (parse_term v)) with
            | (FStar_Pervasives_Native.Some kt, FStar_Pervasives_Native.Some
               vt) ->
                FStar_Pervasives_Native.Some
                  (RIF_Core_Syntax.RIF_Frame (obj, kt, vt))
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
       | uu___2 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let parse_frame_element (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_atom Prims.list FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let obj_n = first_child_with_local_name "object" children in
      let slots = children_with_local_name "slot" children in
      (match obj_n with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some obj_node ->
           (match parse_term_host obj_node with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some obj ->
                let slot_atoms =
                  FStar_List_Tot_Base.map (fun s -> parse_slot_pair s obj)
                    slots in
                list_collect_some slot_atoms))
  | uu___ -> FStar_Pervasives_Native.None
let parse_member_element (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_atom FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let inst_n = first_child_with_local_name "instance" children in
      let cls_n = first_child_with_local_name "class" children in
      (match (inst_n, cls_n) with
       | (FStar_Pervasives_Native.Some i_node, FStar_Pervasives_Native.Some
          c_node) ->
           (match ((parse_term_host i_node), (parse_term_host c_node)) with
            | (FStar_Pervasives_Native.Some i, FStar_Pervasives_Native.Some
               c) ->
                FStar_Pervasives_Native.Some
                  (RIF_Core_Syntax.RIF_Member (i, c))
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let parse_subclass_element (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_atom FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      let sub_n = first_child_with_local_name "sub" children in
      let sup_n = first_child_with_local_name "super" children in
      (match (sub_n, sup_n) with
       | (FStar_Pervasives_Native.Some s_node, FStar_Pervasives_Native.Some
          u_node) ->
           (match ((parse_term_host s_node), (parse_term_host u_node)) with
            | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.Some
               su) ->
                FStar_Pervasives_Native.Some
                  (RIF_Core_Syntax.RIF_Sub (sb, su))
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let parse_atom_node (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_atom Prims.list FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (tag, uu___, uu___1) ->
      if tag_is "Atom" tag
      then
        (match parse_atom_element n with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some a -> FStar_Pervasives_Native.Some [a])
      else
        if tag_is "Frame" tag
        then parse_frame_element n
        else
          if tag_is "Member" tag
          then
            (match parse_member_element n with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some a ->
                 FStar_Pervasives_Native.Some [a])
          else
            if tag_is "Subclass" tag
            then
              (match parse_subclass_element n with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some a ->
                   FStar_Pervasives_Native.Some [a])
            else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let is_body_wrapper_tag (tag : Prims.string) : Prims.bool=
  ((tag_is "if" tag) || (tag_is "body" tag)) || (tag_is "formula" tag)
let is_atom_tag (tag : Prims.string) : Prims.bool=
  (((tag_is "Atom" tag) || (tag_is "Frame" tag)) || (tag_is "Member" tag)) ||
    (tag_is "Subclass" tag)
let rec parse_body_node (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_body FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if tag_is "And" tag
         then
           let kids = child_elements_only children in
           let bodies = parse_body_list kids (fuel - Prims.int_one) in
           (match bodies with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some bs ->
                FStar_Pervasives_Native.Some (RIF_Core_Syntax.RIF_BodyAnd bs))
         else
           if is_body_wrapper_tag tag
           then
             (match child_elements_only children with
              | [] -> FStar_Pervasives_Native.None
              | first::uu___3 -> parse_body_node first (fuel - Prims.int_one))
           else
             if tag_is "External" tag
             then
               (match first_child_with_local_name "content" children with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some content_node ->
                    (match content_node with
                     | Parser_XML.XElement (uu___4, uu___5, cchildren) ->
                         (match child_elements_only cchildren with
                          | inner::[] ->
                              (match inner with
                               | Parser_XML.XElement (itag, uu___6, uu___7)
                                   ->
                                   if tag_is "Atom" itag
                                   then
                                     (match parse_op_and_args_fuel inner
                                              (fuel - Prims.int_one)
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          (op, args) ->
                                          FStar_Pervasives_Native.Some
                                            (RIF_Core_Syntax.RIF_BodyExternal
                                               (op, args)))
                                   else FStar_Pervasives_Native.None
                               | uu___6 -> FStar_Pervasives_Native.None)
                          | uu___6 -> FStar_Pervasives_Native.None)
                     | uu___4 -> FStar_Pervasives_Native.None))
             else
               if tag_is "Equal" tag
               then
                 (match ((first_child_with_local_name "left" children),
                          (first_child_with_local_name "right" children))
                  with
                  | (FStar_Pervasives_Native.Some l_node,
                     FStar_Pervasives_Native.Some r_node) ->
                      (match ((parse_term_host l_node),
                               (parse_term_host r_node))
                       with
                       | (FStar_Pervasives_Native.Some l,
                          FStar_Pervasives_Native.Some r) ->
                           FStar_Pervasives_Native.Some
                             (RIF_Core_Syntax.RIF_BodyEqual (l, r))
                       | (uu___5, uu___6) -> FStar_Pervasives_Native.None)
                  | (uu___5, uu___6) -> FStar_Pervasives_Native.None)
               else
                 if is_atom_tag tag
                 then
                   (match parse_atom_node n with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (a::[]) ->
                        FStar_Pervasives_Native.Some
                          (RIF_Core_Syntax.RIF_BodyAtom a)
                    | FStar_Pervasives_Native.Some atoms ->
                        FStar_Pervasives_Native.Some
                          (RIF_Core_Syntax.RIF_BodyAnd
                             (FStar_List_Tot_Base.map
                                (fun a -> RIF_Core_Syntax.RIF_BodyAtom a)
                                atoms)))
                 else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
and parse_body_list (xs : Parser_XML.xml_node Prims.list) (fuel : Prims.nat)
  : RIF_Core_Syntax.rif_body Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match xs with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::rest ->
         (match parse_body_node hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some b ->
              (match parse_body_list rest (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some bs ->
                   FStar_Pervasives_Native.Some (b :: bs))))
let is_head_wrapper_tag (tag : Prims.string) : Prims.bool=
  ((tag_is "then" tag) || (tag_is "head" tag)) || (tag_is "formula" tag)
let rec unwrap_head_node (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if is_atom_tag tag
         then FStar_Pervasives_Native.Some n
         else
           if is_head_wrapper_tag tag
           then
             (match child_elements_only children with
              | [] -> FStar_Pervasives_Native.None
              | first::uu___3 ->
                  unwrap_head_node first (fuel - Prims.int_one))
           else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
let parse_head_node (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_atom FStar_Pervasives_Native.option=
  match unwrap_head_node n fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some atom_node ->
      (match parse_atom_node atom_node with
       | FStar_Pervasives_Native.Some (a::[]) ->
           FStar_Pervasives_Native.Some a
       | uu___ -> FStar_Pervasives_Native.None)
let find_first_named (names : Prims.string Prims.list)
  (children : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  let rec go ns =
    match ns with
    | [] -> FStar_Pervasives_Native.None
    | name::rest ->
        (match first_child_with_local_name name children with
         | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n
         | FStar_Pervasives_Native.None -> go rest) in
  go names
let parse_implies (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_rule FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (uu___1, uu___2, children) ->
         let if_node = find_first_named ["if"; "body"] children in
         let then_node = find_first_named ["then"; "head"] children in
         (match (if_node, then_node) with
          | (FStar_Pervasives_Native.Some i, FStar_Pervasives_Native.Some t)
              ->
              (match ((parse_body_node i fuel), (parse_head_node t fuel))
               with
               | (FStar_Pervasives_Native.Some body_,
                  FStar_Pervasives_Native.Some head_) ->
                   FStar_Pervasives_Native.Some
                     (RIF_Core_Syntax.mk_rule head_ body_)
               | (uu___3, uu___4) -> FStar_Pervasives_Native.None)
          | (uu___3, uu___4) -> FStar_Pervasives_Native.None)
     | uu___1 -> FStar_Pervasives_Native.None)
let parse_fact_atom (n : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_rule FStar_Pervasives_Native.option=
  match parse_atom_node n with
  | FStar_Pervasives_Native.Some (a::[]) ->
      FStar_Pervasives_Native.Some
        (RIF_Core_Syntax.mk_rule a (RIF_Core_Syntax.RIF_BodyAnd []))
  | FStar_Pervasives_Native.Some _atoms -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec parse_sentence_content (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_rule Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if tag_is "Forall" tag
         then
           (match first_child_with_local_name "formula" children with
            | FStar_Pervasives_Native.None ->
                (match first_child_with_local_name "Implies" children with
                 | FStar_Pervasives_Native.Some imp_node ->
                     (match parse_implies imp_node fuel with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rule_ ->
                          FStar_Pervasives_Native.Some [rule_])
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.Some f_node ->
                parse_sentence_content f_node (fuel - Prims.int_one))
         else
           if tag_is "Implies" tag
           then
             (match parse_implies n fuel with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some rule_ ->
                  FStar_Pervasives_Native.Some [rule_])
           else
             if tag_is "formula" tag
             then
               (match child_elements_only children with
                | [] -> FStar_Pervasives_Native.None
                | first::uu___4 ->
                    parse_sentence_content first (fuel - Prims.int_one))
             else
               if tag_is "sentence" tag
               then
                 (match child_elements_only children with
                  | [] -> FStar_Pervasives_Native.None
                  | first::uu___5 ->
                      parse_sentence_content first (fuel - Prims.int_one))
               else
                 if tag_is "And" tag
                 then
                   parse_sentence_conjuncts (child_elements_only children)
                     (fuel - Prims.int_one)
                 else
                   if is_atom_tag tag
                   then
                     (match parse_atom_node n with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (a::[]) ->
                          FStar_Pervasives_Native.Some
                            [RIF_Core_Syntax.mk_rule a
                               (RIF_Core_Syntax.RIF_BodyAnd [])]
                      | FStar_Pervasives_Native.Some atoms ->
                          FStar_Pervasives_Native.Some
                            (FStar_List_Tot_Base.map
                               (fun a ->
                                  RIF_Core_Syntax.mk_rule a
                                    (RIF_Core_Syntax.RIF_BodyAnd [])) atoms))
                   else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
and parse_sentence_conjuncts (xs : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_rule Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match xs with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::rest ->
         (match parse_sentence_content hd (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some these ->
              (match parse_sentence_conjuncts rest (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some more ->
                   FStar_Pervasives_Native.Some
                     (FStar_List_Tot_Base.op_At these more))))
let rec parse_group_children (xs : Parser_XML.xml_node Prims.list)
  (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_rule Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match xs with
     | [] -> FStar_Pervasives_Native.Some []
     | hd::rest ->
         (match hd with
          | Parser_XML.XElement (tag, uu___1, children) ->
              if tag_is "sentence" tag
              then
                (match child_elements_only children with
                 | [] -> parse_group_children rest (fuel - Prims.int_one)
                 | first::uu___2 ->
                     if
                       (match first with
                        | Parser_XML.XElement (t, uu___3, uu___4) ->
                            tag_is "Group" t
                        | uu___3 -> false)
                     then
                       (match parse_group_node first (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some these ->
                            (match parse_group_children rest
                                     (fuel - Prims.int_one)
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some more ->
                                 FStar_Pervasives_Native.Some
                                   (FStar_List_Tot_Base.op_At these more)))
                     else
                       (match parse_sentence_content first
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some these ->
                            (match parse_group_children rest
                                     (fuel - Prims.int_one)
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some more ->
                                 FStar_Pervasives_Native.Some
                                   (FStar_List_Tot_Base.op_At these more))))
              else
                if tag_is "Group" tag
                then
                  (match parse_group_node hd (fuel - Prims.int_one) with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some these ->
                       (match parse_group_children rest
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some more ->
                            FStar_Pervasives_Native.Some
                              (FStar_List_Tot_Base.op_At these more)))
                else parse_group_children rest (fuel - Prims.int_one)
          | uu___1 -> parse_group_children rest (fuel - Prims.int_one)))
and parse_group_node (n : Parser_XML.xml_node) (fuel : Prims.nat) :
  RIF_Core_Syntax.rif_rule Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match n with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if tag_is "Group" tag
         then parse_group_children children (fuel - Prims.int_one)
         else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
let extract_group_from_doc (root : Parser_XML.xml_node) (fuel : Prims.nat) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match root with
     | Parser_XML.XElement (tag, uu___1, children) ->
         if tag_is "Document" tag
         then
           (match first_child_with_local_name "payload" children with
            | FStar_Pervasives_Native.Some payload_node ->
                (match payload_node with
                 | Parser_XML.XElement (uu___2, uu___3, pchildren) ->
                     first_child_with_local_name "Group" pchildren
                 | uu___2 -> FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None ->
                first_child_with_local_name "Group" children)
         else
           if tag_is "Group" tag
           then FStar_Pervasives_Native.Some root
           else
             if tag_is "payload" tag
             then first_child_with_local_name "Group" children
             else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
let parse_rif_document (root : Parser_XML.xml_node) :
  RIF_Core_Syntax.rif_program FStar_Pervasives_Native.option=
  let fuel = (Prims.of_int (1000)) in
  match extract_group_from_doc root fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some group_node ->
      (match parse_group_node group_node fuel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some rules_ ->
           FStar_Pervasives_Native.Some
             (RIF_Core_Syntax.program_of_rules rules_))
let parse_rif_program (input : Prims.string) :
  RIF_Core_Syntax.rif_program FStar_Pervasives_Native.option=
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root -> parse_rif_document root
let parse_import_location (import_node : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match import_node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match first_child_with_local_name "location" children with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some loc_node ->
           let raw = trim_ws (element_text loc_node) in
           if (FStar_String.strlen raw) = Prims.int_zero
           then FStar_Pervasives_Native.None
           else FStar_Pervasives_Native.Some raw)
  | uu___ -> FStar_Pervasives_Native.None
let parse_directive_import (directive_node : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match directive_node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      (match first_child_with_local_name "Import" children with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some imp_node ->
           parse_import_location imp_node)
  | uu___ -> FStar_Pervasives_Native.None
let rec extract_imports_from_directives
  (children : Parser_XML.xml_node Prims.list) : Prims.string Prims.list=
  match children with
  | [] -> []
  | hd::rest ->
      (match hd with
       | Parser_XML.XElement (t, uu___, uu___1) ->
           if tag_is "directive" t
           then
             (match parse_directive_import hd with
              | FStar_Pervasives_Native.None ->
                  extract_imports_from_directives rest
              | FStar_Pervasives_Native.Some url -> url ::
                  (extract_imports_from_directives rest))
           else extract_imports_from_directives rest
       | uu___ -> extract_imports_from_directives rest)
let extract_document_imports (root : Parser_XML.xml_node) :
  Prims.string Prims.list=
  match root with
  | Parser_XML.XElement (tag, uu___, children) ->
      if tag_is "Document" tag
      then extract_imports_from_directives children
      else []
  | uu___ -> []
let parse_rif_program_with_imports (input : Prims.string) :
  (Prims.string Prims.list * RIF_Core_Syntax.rif_program)
    FStar_Pervasives_Native.option=
  match Parser_XML.parse_xml_document input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      (match parse_rif_document root with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some prog ->
           FStar_Pervasives_Native.Some
             ((extract_document_imports root), prog))
