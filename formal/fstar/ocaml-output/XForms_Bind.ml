open Prims
type xf_mip_type =
  | MipTypeNone 
  | MipTypeString 
  | MipTypeBoolean 
  | MipTypeInteger 
  | MipTypeDecimal 
  | MipTypeFloat 
  | MipTypeDouble 
  | MipTypeUnsupported 
let uu___is_MipTypeNone (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeNone -> true | uu___ -> false
let uu___is_MipTypeString (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeString -> true | uu___ -> false
let uu___is_MipTypeBoolean (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeBoolean -> true | uu___ -> false
let uu___is_MipTypeInteger (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeInteger -> true | uu___ -> false
let uu___is_MipTypeDecimal (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeDecimal -> true | uu___ -> false
let uu___is_MipTypeFloat (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeFloat -> true | uu___ -> false
let uu___is_MipTypeDouble (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeDouble -> true | uu___ -> false
let uu___is_MipTypeUnsupported (projectee : xf_mip_type) : Prims.bool=
  match projectee with | MipTypeUnsupported -> true | uu___ -> false
let mip_type_of_qname (q : Prims.string) : xf_mip_type=
  if q = ""
  then MipTypeNone
  else
    if (q = "xsd:string") || (q = "xs:string")
    then MipTypeString
    else
      if (q = "xsd:boolean") || (q = "xs:boolean")
      then MipTypeBoolean
      else
        if (q = "xsd:integer") || (q = "xs:integer")
        then MipTypeInteger
        else
          if (q = "xsd:decimal") || (q = "xs:decimal")
          then MipTypeDecimal
          else
            if (q = "xsd:float") || (q = "xs:float")
            then MipTypeFloat
            else
              if (q = "xsd:double") || (q = "xs:double")
              then MipTypeDouble
              else MipTypeUnsupported
let type_wellformed (t : xf_mip_type) (lex : Prims.string) : Prims.bool=
  match t with
  | MipTypeNone -> true
  | MipTypeString -> true
  | MipTypeBoolean ->
      (((lex = "true") || (lex = "false")) || (lex = "0")) || (lex = "1")
  | MipTypeInteger -> XSD_Datatypes.is_integer_lexical lex
  | MipTypeDecimal -> XSD_Datatypes.is_decimal_lexical lex
  | MipTypeFloat -> XSD_Datatypes.is_float_lexical lex
  | MipTypeDouble -> XSD_Datatypes.is_float_lexical lex
  | MipTypeUnsupported -> false
type xf_bind =
  {
  bind_id: Prims.string ;
  bind_target: Prims.string ;
  bind_calculate: Prims.string FStar_Pervasives_Native.option ;
  bind_constraint: Prims.string FStar_Pervasives_Native.option ;
  bind_relevant: Prims.string FStar_Pervasives_Native.option ;
  bind_required: Prims.string FStar_Pervasives_Native.option ;
  bind_readonly: Prims.string FStar_Pervasives_Native.option ;
  bind_type: xf_mip_type }
let __proj__Mkxf_bind__item__bind_id (projectee : xf_bind) : Prims.string=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_id
let __proj__Mkxf_bind__item__bind_target (projectee : xf_bind) :
  Prims.string=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_target
let __proj__Mkxf_bind__item__bind_calculate (projectee : xf_bind) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_calculate
let __proj__Mkxf_bind__item__bind_constraint (projectee : xf_bind) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_constraint
let __proj__Mkxf_bind__item__bind_relevant (projectee : xf_bind) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_relevant
let __proj__Mkxf_bind__item__bind_required (projectee : xf_bind) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_required
let __proj__Mkxf_bind__item__bind_readonly (projectee : xf_bind) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_readonly
let __proj__Mkxf_bind__item__bind_type (projectee : xf_bind) : xf_mip_type=
  match projectee with
  | { bind_id; bind_target; bind_calculate; bind_constraint; bind_relevant;
      bind_required; bind_readonly; bind_type;_} -> bind_type
let find_leaf (root : Parser_XML.xml_node) (name : Prims.string) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  Parser_XML.child_element name root
let get_leaf_text (root : Parser_XML.xml_node) (name : Prims.string) :
  Prims.string=
  match find_leaf root name with
  | FStar_Pervasives_Native.Some n -> Parser_XML.text_content n
  | FStar_Pervasives_Native.None -> ""
let rec set_child_text (children : Parser_XML.xml_node Prims.list)
  (name : Prims.string) (v : Prims.string) : Parser_XML.xml_node Prims.list=
  match children with
  | [] -> []
  | h::rest ->
      (match h with
       | Parser_XML.XElement (t, a, uu___) ->
           if t = name
           then (Parser_XML.XElement (t, a, [Parser_XML.XText v])) :: rest
           else h :: (set_child_text rest name v)
       | uu___ -> h :: (set_child_text rest name v))
let set_leaf_text (root : Parser_XML.xml_node) (name : Prims.string)
  (v : Prims.string) : Parser_XML.xml_node=
  match root with
  | Parser_XML.XElement (tag, attrs, children) ->
      Parser_XML.XElement (tag, attrs, (set_child_text children name v))
  | other -> other
let eval_mip_value (root : Parser_XML.xml_node) (target : Prims.string)
  (expr : Prims.string) : XPath_Eval.xp_value FStar_Pervasives_Native.option=
  match find_leaf root target with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some leaf ->
      XPath_Eval.eval_xpath_from_item [root] leaf [] expr
let rec names_expr (e : Parser_XPath.xp_expr) : Prims.string Prims.list=
  match e with
  | Parser_XPath.XE_Path (uu___, steps) -> names_steps steps
  | Parser_XPath.XE_FilterPath (p, preds, steps) ->
      FStar_List_Tot_Base.op_At (names_expr p)
        (FStar_List_Tot_Base.op_At (names_exprs preds) (names_steps steps))
  | Parser_XPath.XE_Union (a, b) ->
      FStar_List_Tot_Base.op_At (names_expr a) (names_expr b)
  | Parser_XPath.XE_Or (a, b) ->
      FStar_List_Tot_Base.op_At (names_expr a) (names_expr b)
  | Parser_XPath.XE_And (a, b) ->
      FStar_List_Tot_Base.op_At (names_expr a) (names_expr b)
  | Parser_XPath.XE_Compare (uu___, a, b) ->
      FStar_List_Tot_Base.op_At (names_expr a) (names_expr b)
  | Parser_XPath.XE_Arith (uu___, a, b) ->
      FStar_List_Tot_Base.op_At (names_expr a) (names_expr b)
  | Parser_XPath.XE_Neg a -> names_expr a
  | Parser_XPath.XE_FunCall (uu___, args) -> names_exprs args
  | Parser_XPath.XE_Number (uu___, uu___1) -> []
  | Parser_XPath.XE_Literal uu___ -> []
  | Parser_XPath.XE_VarRef uu___ -> []
and names_exprs (es : Parser_XPath.xp_expr Prims.list) :
  Prims.string Prims.list=
  match es with
  | [] -> []
  | h::t -> FStar_List_Tot_Base.op_At (names_expr h) (names_exprs t)
and names_steps (ss : Parser_XPath.xp_step Prims.list) :
  Prims.string Prims.list=
  match ss with
  | [] -> []
  | s::t ->
      let here =
        match s.Parser_XPath.step_test with
        | Parser_XPath.NT_Name n -> [n]
        | uu___ -> [] in
      FStar_List_Tot_Base.op_At here
        (FStar_List_Tot_Base.op_At (names_exprs s.Parser_XPath.step_preds)
           (names_steps t))
let all_targets (bs : xf_bind Prims.list) : Prims.string Prims.list=
  FStar_List_Tot_Base.map (fun b -> b.bind_target) bs
let calc_names (b : xf_bind) : Prims.string Prims.list=
  match b.bind_calculate with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some c ->
      (match Parser_XPath.parse_xpath c with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some e -> names_expr e)
let preds_of (bs : xf_bind Prims.list) (b : xf_bind) :
  Prims.string Prims.list=
  let tgts = all_targets bs in
  FStar_List_Tot_Base.filter (fun n -> FStar_List_Tot_Base.mem n tgts)
    (calc_names b)
type graph_node = {
  gn_bind: xf_bind ;
  gn_preds: Prims.string Prims.list }
let __proj__Mkgraph_node__item__gn_bind (projectee : graph_node) : xf_bind=
  match projectee with | { gn_bind; gn_preds;_} -> gn_bind
let __proj__Mkgraph_node__item__gn_preds (projectee : graph_node) :
  Prims.string Prims.list=
  match projectee with | { gn_bind; gn_preds;_} -> gn_preds
let build_graph (bs : xf_bind Prims.list) : graph_node Prims.list=
  FStar_List_Tot_Base.map
    (fun b -> { gn_bind = b; gn_preds = (preds_of bs b) }) bs
let node_ready (emitted : Prims.string Prims.list) (g : graph_node) :
  Prims.bool=
  FStar_List_Tot_Base.for_all (fun p -> FStar_List_Tot_Base.mem p emitted)
    g.gn_preds
let rec topo_pass (remaining : graph_node Prims.list)
  (emitted : Prims.string Prims.list) :
  xf_bind Prims.list FStar_Pervasives_Native.option=
  match remaining with
  | [] -> FStar_Pervasives_Native.Some []
  | uu___ ->
      let rdy = node_ready emitted in
      let ready = FStar_List_Tot_Base.filter rdy remaining in
      let notready =
        FStar_List_Tot_Base.filter (fun g -> Prims.op_Negation (rdy g))
          remaining in
      (match ready with
       | [] -> FStar_Pervasives_Native.None
       | uu___1::uu___2 ->
           let new_emitted =
             FStar_List_Tot_Base.op_At emitted
               (FStar_List_Tot_Base.map (fun g -> (g.gn_bind).bind_target)
                  ready) in
           (match topo_pass notready new_emitted with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.op_At
                     (FStar_List_Tot_Base.map (fun g -> g.gn_bind) ready)
                     rest)))
let topo_sort (bs : xf_bind Prims.list) :
  xf_bind Prims.list FStar_Pervasives_Native.option=
  topo_pass (build_graph bs) []
let rec apply_calcs (sorted : xf_bind Prims.list)
  (xdoc : Parser_XML.xml_node) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match sorted with
  | [] -> FStar_Pervasives_Native.Some xdoc
  | b::rest ->
      (match b.bind_calculate with
       | FStar_Pervasives_Native.None -> apply_calcs rest xdoc
       | FStar_Pervasives_Native.Some c ->
           (match eval_mip_value xdoc b.bind_target c with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some v ->
                apply_calcs rest
                  (set_leaf_text xdoc b.bind_target
                     (XPath_Eval.to_string_val v))))
type node_validity =
  {
  nv_target: Prims.string ;
  nv_value: Prims.string ;
  nv_type_valid: Prims.bool ;
  nv_constraint: Prims.bool ;
  nv_relevant: Prims.bool ;
  nv_required: Prims.bool ;
  nv_readonly: Prims.bool ;
  nv_valid: Prims.bool }
let __proj__Mknode_validity__item__nv_target (projectee : node_validity) :
  Prims.string=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_target
let __proj__Mknode_validity__item__nv_value (projectee : node_validity) :
  Prims.string=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_value
let __proj__Mknode_validity__item__nv_type_valid (projectee : node_validity)
  : Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_type_valid
let __proj__Mknode_validity__item__nv_constraint (projectee : node_validity)
  : Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_constraint
let __proj__Mknode_validity__item__nv_relevant (projectee : node_validity) :
  Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_relevant
let __proj__Mknode_validity__item__nv_required (projectee : node_validity) :
  Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_required
let __proj__Mknode_validity__item__nv_readonly (projectee : node_validity) :
  Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_readonly
let __proj__Mknode_validity__item__nv_valid (projectee : node_validity) :
  Prims.bool=
  match projectee with
  | { nv_target; nv_value; nv_type_valid; nv_constraint; nv_relevant;
      nv_required; nv_readonly; nv_valid;_} -> nv_valid
let eval_bool_mip (root : Parser_XML.xml_node) (target : Prims.string)
  (eo : Prims.string FStar_Pervasives_Native.option) (dflt : Prims.bool) :
  Prims.bool=
  match eo with
  | FStar_Pervasives_Native.None -> dflt
  | FStar_Pervasives_Native.Some e ->
      (match eval_mip_value root target e with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some v -> XPath_Eval.to_bool_val v)
let build_validity (root : Parser_XML.xml_node) (b : xf_bind) :
  node_validity=
  let value = get_leaf_text root b.bind_target in
  let tv = type_wellformed b.bind_type value in
  let cons = eval_bool_mip root b.bind_target b.bind_constraint true in
  let rel = eval_bool_mip root b.bind_target b.bind_relevant true in
  let req = eval_bool_mip root b.bind_target b.bind_required false in
  let ro = eval_bool_mip root b.bind_target b.bind_readonly false in
  let required_ok =
    (Prims.op_Negation req) || ((FStar_String.strlen value) > Prims.int_zero) in
  let valid = (Prims.op_Negation rel) || ((tv && cons) && required_ok) in
  {
    nv_target = (b.bind_target);
    nv_value = value;
    nv_type_valid = tv;
    nv_constraint = cons;
    nv_relevant = rel;
    nv_required = req;
    nv_readonly = ro;
    nv_valid = valid
  }
let recalculate (binds : xf_bind Prims.list) (xdoc : Parser_XML.xml_node) :
  (Parser_XML.xml_node * node_validity Prims.list)
    FStar_Pervasives_Native.option=
  match topo_sort binds with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some sorted ->
      (match apply_calcs sorted xdoc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some inst2 ->
           FStar_Pervasives_Native.Some
             (inst2, (FStar_List_Tot_Base.map (build_validity inst2) binds)))
let apply_edit (binds : xf_bind Prims.list) (xdoc : Parser_XML.xml_node)
  (edit_target : Prims.string) (edit_value : Prims.string) :
  (Parser_XML.xml_node * node_validity Prims.list)
    FStar_Pervasives_Native.option=
  recalculate binds (set_leaf_text xdoc edit_target edit_value)
let mk_bind_from (attrs : Parser_XML.xml_attribute Prims.list)
  (tgt : Prims.string) : xf_bind=
  {
    bind_id =
      (match Parser_XML.find_attr "id" attrs with
       | FStar_Pervasives_Native.Some i -> i
       | FStar_Pervasives_Native.None -> "");
    bind_target = tgt;
    bind_calculate = (Parser_XML.find_attr "calculate" attrs);
    bind_constraint = (Parser_XML.find_attr "constraint" attrs);
    bind_relevant = (Parser_XML.find_attr "relevant" attrs);
    bind_required = (Parser_XML.find_attr "required" attrs);
    bind_readonly = (Parser_XML.find_attr "readonly" attrs);
    bind_type =
      (match Parser_XML.find_attr "type" attrs with
       | FStar_Pervasives_Native.Some q -> mip_type_of_qname q
       | FStar_Pervasives_Native.None -> MipTypeNone)
  }
let decode_bind (el : Parser_XML.xml_node) :
  xf_bind FStar_Pervasives_Native.option=
  let attrs = Parser_XML.element_attrs el in
  match Parser_XML.find_attr "nodeset" attrs with
  | FStar_Pervasives_Native.Some tgt ->
      FStar_Pervasives_Native.Some (mk_bind_from attrs tgt)
  | FStar_Pervasives_Native.None ->
      (match Parser_XML.find_attr "ref" attrs with
       | FStar_Pervasives_Native.Some tgt ->
           FStar_Pervasives_Native.Some (mk_bind_from attrs tgt)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec decode_binds_list (nodes : Parser_XML.xml_node Prims.list) :
  xf_bind Prims.list=
  match nodes with
  | [] -> []
  | h::t ->
      (match h with
       | Parser_XML.XElement (uu___, uu___1, uu___2) ->
           (match decode_bind h with
            | FStar_Pervasives_Native.Some b -> b :: (decode_binds_list t)
            | FStar_Pervasives_Native.None -> decode_binds_list t)
       | uu___ -> decode_binds_list t)
let decode_binds (container : Parser_XML.xml_node) : xf_bind Prims.list=
  decode_binds_list (Parser_XML.element_children container)
