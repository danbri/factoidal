open Prims
let soc (c : FStar_String.char) : Prims.string= FStar_String.string_of_char c
let chars_of (s : Prims.string) : FStar_String.char Prims.list=
  FStar_String.list_of_string s
let str_of_chars (cs : FStar_String.char Prims.list) : Prims.string=
  FStar_String.string_of_list cs
let is_space_char (c : FStar_String.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let rec drop_leading_ws (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | [] -> []
  | c::rest -> if is_space_char c then drop_leading_ws rest else cs
let trim_chars (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  FStar_List_Tot_Base.rev
    (drop_leading_ws (FStar_List_Tot_Base.rev (drop_leading_ws cs)))
let trim_str (s : Prims.string) : Prims.string=
  str_of_chars (trim_chars (chars_of s))
let rec all_ws_chars (cs : FStar_String.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest -> if is_space_char c then all_ws_chars rest else false
let is_all_ws (s : Prims.string) : Prims.bool= all_ws_chars (chars_of s)
let rec starts_with_chars (pre : FStar_String.char Prims.list)
  (cs : FStar_String.char Prims.list) : Prims.bool=
  match (pre, cs) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (p::pr, c::cr) -> if p = c then starts_with_chars pr cr else false
let starts_with (pre : Prims.string) (s : Prims.string) : Prims.bool=
  starts_with_chars (chars_of pre) (chars_of s)
let rec split_on_char_acc (d : FStar_String.char)
  (cs : FStar_String.char Prims.list) (cur : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list Prims.list) :
  FStar_String.char Prims.list Prims.list=
  match cs with
  | [] -> FStar_List_Tot_Base.rev ((FStar_List_Tot_Base.rev cur) :: acc)
  | c::rest ->
      if c = d
      then split_on_char_acc d rest [] ((FStar_List_Tot_Base.rev cur) :: acc)
      else split_on_char_acc d rest (c :: cur) acc
let split_on_char (d : FStar_String.char) (s : Prims.string) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.map str_of_chars
    (split_on_char_acc d (chars_of s) [] [])
let rec has_double_slash (cs : FStar_String.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | c0::rest ->
      (match rest with
       | c1::uu___ ->
           if (c0 = 47) && (c1 = 47) then true else has_double_slash rest
       | [] -> false)
let contains_double_slash (s : Prims.string) : Prims.bool=
  has_double_slash (chars_of s)
let rec has_char (d : FStar_String.char) (cs : FStar_String.char Prims.list)
  : Prims.bool=
  match cs with
  | [] -> false
  | c::rest -> if c = d then true else has_char d rest
let contains_char (d : FStar_String.char) (s : Prims.string) : Prims.bool=
  has_char d (chars_of s)
let local_name (tag : Prims.string) : Prims.string=
  match split_on_char 58 tag with
  | uu___::local::uu___1 -> local
  | uu___ -> tag
let rec drop_prefix_chars (cs : FStar_String.char Prims.list) (n : Prims.nat)
  : FStar_String.char Prims.list=
  if n = Prims.int_zero
  then cs
  else
    (match cs with
     | [] -> []
     | uu___1::rest -> drop_prefix_chars rest (n - Prims.int_one))
let name_prefix (tag : Prims.string) : Prims.string=
  match split_on_char 58 tag with | pfx::uu___::uu___1 -> pfx | uu___ -> ""
let ns_decl_prefix (name : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if name = "xmlns"
  then FStar_Pervasives_Native.Some ""
  else
    if starts_with "xmlns:" name
    then
      FStar_Pervasives_Native.Some
        (str_of_chars (drop_prefix_chars (chars_of name) (Prims.of_int (6))))
    else FStar_Pervasives_Native.None
let is_ns_decl (a : Parser_XML.xml_attribute) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some
    (ns_decl_prefix a.Parser_XML.attr_name)
let rec mem_str (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with | [] -> false | h::t -> if h = x then true else mem_str x t
let rec ns_add (acc : Parser_XML.xml_attribute Prims.list)
  (seen : Prims.string Prims.list)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (Parser_XML.xml_attribute Prims.list * Prims.string Prims.list)=
  match attrs with
  | [] -> (acc, seen)
  | a::rest ->
      (match ns_decl_prefix a.Parser_XML.attr_name with
       | FStar_Pervasives_Native.Some pfx ->
           if mem_str pfx seen
           then ns_add acc seen rest
           else ns_add (FStar_List_Tot_Base.op_At acc [a]) (pfx :: seen) rest
       | FStar_Pervasives_Native.None -> ns_add acc seen rest)
let rec inscope_ns (acc : Parser_XML.xml_attribute Prims.list)
  (seen : Prims.string Prims.list) (nodes : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_attribute Prims.list=
  match nodes with
  | [] -> acc
  | n::rest ->
      let uu___ = ns_add acc seen (Parser_XML.element_attrs n) in
      (match uu___ with | (acc', seen') -> inscope_ns acc' seen' rest)
let rec char_list_cmp (a : FStar_String.char Prims.list)
  (b : FStar_String.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      let cx = FStar_Char.int_of_char x in
      let cy = FStar_Char.int_of_char y in
      if cx < cy
      then (Prims.of_int (-1))
      else if cx > cy then Prims.int_one else char_list_cmp xs ys
let attr_name_cmp (a : Parser_XML.xml_attribute)
  (b : Parser_XML.xml_attribute) : Prims.int=
  match ((ns_decl_prefix a.Parser_XML.attr_name),
          (ns_decl_prefix b.Parser_XML.attr_name))
  with
  | (FStar_Pervasives_Native.Some pa, FStar_Pervasives_Native.Some pb) ->
      if (pa = "") && (pb <> "")
      then Prims.int_one
      else
        if (pa <> "") && (pb = "")
        then (Prims.of_int (-1))
        else char_list_cmp (chars_of pa) (chars_of pb)
  | (uu___, uu___1) ->
      char_list_cmp (chars_of a.Parser_XML.attr_name)
        (chars_of b.Parser_XML.attr_name)
type rnode =
  | R_Node of Parser_XML.xml_node 
  | R_Attr of Parser_XML.xml_attribute 
let uu___is_R_Node (projectee : rnode) : Prims.bool=
  match projectee with | R_Node _0 -> true | uu___ -> false
let __proj__R_Node__item___0 (projectee : rnode) : Parser_XML.xml_node=
  match projectee with | R_Node _0 -> _0
let uu___is_R_Attr (projectee : rnode) : Prims.bool=
  match projectee with | R_Attr _0 -> true | uu___ -> false
let __proj__R_Attr__item___0 (projectee : rnode) : Parser_XML.xml_attribute=
  match projectee with | R_Attr _0 -> _0
let rec split_rnodes (rs : rnode Prims.list)
  (as_acc : Parser_XML.xml_attribute Prims.list)
  (ns_acc : Parser_XML.xml_node Prims.list) :
  (Parser_XML.xml_attribute Prims.list * Parser_XML.xml_node Prims.list)=
  match rs with
  | [] ->
      ((FStar_List_Tot_Base.rev as_acc), (FStar_List_Tot_Base.rev ns_acc))
  | (R_Attr a)::rest -> split_rnodes rest (a :: as_acc) ns_acc
  | (R_Node n)::rest -> split_rnodes rest as_acc (n :: ns_acc)
let build_element (tag : Prims.string)
  (extra_attrs : Parser_XML.xml_attribute Prims.list)
  (body : rnode Prims.list) : Parser_XML.xml_node=
  let uu___ = split_rnodes body [] [] in
  match uu___ with
  | (attrs, nodes) ->
      Parser_XML.XElement
        (tag, (FStar_List_Tot_Base.op_At extra_attrs attrs), nodes)
let rec rnodes_text (rs : rnode Prims.list) : Prims.string=
  match rs with
  | [] -> ""
  | (R_Node (Parser_XML.XText t))::rest -> Prims.strcat t (rnodes_text rest)
  | (R_Node (Parser_XML.XCDATA t))::rest -> Prims.strcat t (rnodes_text rest)
  | uu___::rest -> rnodes_text rest
let only_nodes (rs : rnode Prims.list) : Parser_XML.xml_node Prims.list=
  let uu___ = split_rnodes rs [] [] in
  match uu___ with | (uu___1, nodes) -> nodes
let rec raw_text (children : Parser_XML.xml_node Prims.list) : Prims.string=
  match children with
  | [] -> ""
  | (Parser_XML.XText t)::rest -> Prims.strcat t (raw_text rest)
  | (Parser_XML.XCDATA t)::rest -> Prims.strcat t (raw_text rest)
  | uu___::rest -> raw_text rest
let item_to_rnode (it : XPath_Eval.xctx_item) : rnode=
  match it with
  | XPath_Eval.CI_Elem (uu___, uu___1, n) -> R_Node n
  | XPath_Eval.CI_Text (uu___, uu___1, uu___2, t) ->
      R_Node (Parser_XML.XText t)
  | XPath_Eval.CI_Comment (uu___, uu___1, uu___2, t) ->
      R_Node (Parser_XML.XComment t)
  | XPath_Eval.CI_PI (uu___, uu___1, uu___2, tg, d) ->
      R_Node (Parser_XML.XPI (tg, d))
  | XPath_Eval.CI_Attr (uu___, uu___1, uu___2, a) -> R_Attr a
type dnode =
  | D_Doc of Parser_XML.xml_node * Parser_XML.xml_node Prims.list 
  | D_Item of XPath_Eval.xctx_item 
let uu___is_D_Doc (projectee : dnode) : Prims.bool=
  match projectee with | D_Doc (_0, _1) -> true | uu___ -> false
let __proj__D_Doc__item___0 (projectee : dnode) : Parser_XML.xml_node=
  match projectee with | D_Doc (_0, _1) -> _0
let __proj__D_Doc__item___1 (projectee : dnode) :
  Parser_XML.xml_node Prims.list= match projectee with | D_Doc (_0, _1) -> _1
let uu___is_D_Item (projectee : dnode) : Prims.bool=
  match projectee with | D_Item _0 -> true | uu___ -> false
let __proj__D_Item__item___0 (projectee : dnode) : XPath_Eval.xctx_item=
  match projectee with | D_Item _0 -> _0
let doc_has_misc (doc_kids : Parser_XML.xml_node Prims.list) : Prims.bool=
  match doc_kids with | [] -> false | uu___::[] -> false | uu___ -> true
let dnode_ci (nd : dnode) : XPath_Eval.xctx_item=
  match nd with
  | D_Doc (root, uu___) -> XPath_Eval.CI_Elem ([], [], root)
  | D_Item it -> it
let dnode_children (nd : dnode) : dnode Prims.list=
  match nd with
  | D_Doc (root, doc_kids) ->
      if doc_has_misc doc_kids
      then
        FStar_List_Tot_Base.map (fun it -> D_Item it)
          (XPath_Eval.doc_child_items doc_kids)
      else [D_Item (XPath_Eval.CI_Elem ([], [], root))]
  | D_Item (XPath_Eval.CI_Elem (p, anc, n)) ->
      FStar_List_Tot_Base.map (fun it -> D_Item it)
        (XPath_Eval.child_items p anc n)
  | D_Item uu___ -> []
let dnode_attrs_and_kids (nd : dnode) :
  (XPath_Eval.xctx_item Prims.list * XPath_Eval.xctx_item Prims.list)=
  match nd with
  | D_Doc (root, doc_kids) ->
      if doc_has_misc doc_kids
      then ([], (XPath_Eval.doc_child_items doc_kids))
      else ([], [XPath_Eval.CI_Elem ([], [], root)])
  | D_Item (XPath_Eval.CI_Elem (p, anc, n)) ->
      ((XPath_Eval.attribute_items p anc n),
        (XPath_Eval.child_items p anc n))
  | D_Item uu___ -> ([], [])
type template =
  {
  tpl_match: Prims.string ;
  tpl_name: Prims.string ;
  tpl_mode: Prims.string ;
  tpl_prio: Prims.int FStar_Pervasives_Native.option ;
  tpl_body: Parser_XML.xml_node Prims.list }
let __proj__Mktemplate__item__tpl_match (projectee : template) :
  Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body;_} -> tpl_match
let __proj__Mktemplate__item__tpl_name (projectee : template) : Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body;_} -> tpl_name
let __proj__Mktemplate__item__tpl_mode (projectee : template) : Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body;_} -> tpl_mode
let __proj__Mktemplate__item__tpl_prio (projectee : template) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body;_} -> tpl_prio
let __proj__Mktemplate__item__tpl_body (projectee : template) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body;_} -> tpl_body
type xstyle =
  {
  xs_pfx: Prims.string ;
  xs_templates: template Prims.list ;
  xs_method: Prims.string ;
  xs_globals: (Prims.string * XPath_Eval.xp_value) Prims.list ;
  xs_nsscope: Parser_XML.xml_attribute Prims.list ;
  xs_nsctx: (Prims.string * Prims.string) Prims.list }
let __proj__Mkxstyle__item__xs_pfx (projectee : xstyle) : Prims.string=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_pfx
let __proj__Mkxstyle__item__xs_templates (projectee : xstyle) :
  template Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_templates
let __proj__Mkxstyle__item__xs_method (projectee : xstyle) : Prims.string=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_method
let __proj__Mkxstyle__item__xs_globals (projectee : xstyle) :
  (Prims.string * XPath_Eval.xp_value) Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_globals
let __proj__Mkxstyle__item__xs_nsscope (projectee : xstyle) :
  Parser_XML.xml_attribute Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_nsscope
let __proj__Mkxstyle__item__xs_nsctx (projectee : xstyle) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_method; xs_globals; xs_nsscope; xs_nsctx;_} ->
      xs_nsctx
let xslt_ns : Prims.string= "http://www.w3.org/1999/XSL/Transform"
let copy_of_item (it : XPath_Eval.xctx_item) : rnode=
  match it with
  | XPath_Eval.CI_Elem (uu___, anc, Parser_XML.XElement (t, attrs, kids)) ->
      let uu___1 = ns_add [] [] attrs in
      (match uu___1 with
       | (uu___2, own_seen) ->
           let inherited =
             FStar_List_Tot_Base.filter
               (fun a -> a.Parser_XML.attr_value <> xslt_ns)
               (inscope_ns [] own_seen anc) in
           R_Node
             (Parser_XML.XElement
                (t, (FStar_List_Tot_Base.append inherited attrs), kids)))
  | uu___ -> item_to_rnode it
let rec strip_ns_node (n : Parser_XML.xml_node) : Parser_XML.xml_node=
  match n with
  | Parser_XML.XElement (tag, attrs, kids) ->
      let attrs' =
        FStar_List_Tot_Base.filter
          (fun a -> Prims.op_Negation (is_ns_decl a)) attrs in
      Parser_XML.XElement (tag, attrs', (strip_ns_nodes kids))
  | other -> other
and strip_ns_nodes (ns : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node Prims.list=
  match ns with
  | [] -> []
  | hd::tl -> (strip_ns_node hd) :: (strip_ns_nodes tl)
let rnode_strip_ns (r : rnode) : rnode=
  match r with | R_Node n -> R_Node (strip_ns_node n) | uu___ -> r
let copy_of_item_no_ns (it : XPath_Eval.xctx_item) : rnode=
  rnode_strip_ns (copy_of_item it)
let rec find_xsl_prefix (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match attrs with
  | [] -> FStar_Pervasives_Native.None
  | a::rest ->
      if
        (a.Parser_XML.attr_value = xslt_ns) &&
          (starts_with "xmlns:" a.Parser_XML.attr_name)
      then
        FStar_Pervasives_Native.Some
          (str_of_chars
             (drop_prefix_chars (chars_of a.Parser_XML.attr_name)
                (Prims.of_int (6))))
      else find_xsl_prefix rest
let xsl_prefix_of (root : Parser_XML.xml_node) : Prims.string=
  match find_xsl_prefix (Parser_XML.element_attrs root) with
  | FStar_Pervasives_Native.Some p -> p
  | FStar_Pervasives_Native.None -> "xsl"
let is_xsl (pfx : Prims.string) (tag : Prims.string) : Prims.bool=
  starts_with (Prims.strcat pfx ":") tag
let xsl_instr (pfx : Prims.string) (tag : Prims.string) : Prims.string=
  local_name tag
let attr_opt (name : Prims.string)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  Parser_XML.find_attr name attrs
let attr_or (name : Prims.string) (dflt : Prims.string)
  (attrs : Parser_XML.xml_attribute Prims.list) : Prims.string=
  match Parser_XML.find_attr name attrs with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None -> dflt
let eval_val (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : XPath_Eval.xp_value=
  match Parser_XPath.parse_xpath expr_text with
  | FStar_Pervasives_Native.None -> XPath_Eval.XV_Str ""
  | FStar_Pervasives_Native.Some e ->
      let doc_nodes = XPath_Eval.xml_node_count (XPath_Eval.root_of_item ctx) in
      let fuel = XPath_Eval.initial_eval_fuel e doc_nodes in
      let env =
        {
          XPath_Eval.env_item = ctx;
          XPath_Eval.env_pos = pos;
          XPath_Eval.env_size = size;
          XPath_Eval.env_vars = vars;
          XPath_Eval.env_nsctx = nsctx;
          XPath_Eval.env_doc_kids = []
        } in
      XPath_Eval.eval_expr fuel env e
let eval_string (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : Prims.string=
  XPath_Eval.to_string_val (eval_val ctx pos size vars nsctx expr_text)
let eval_bool (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : Prims.bool=
  XPath_Eval.to_bool_val (eval_val ctx pos size vars nsctx expr_text)
let is_pi_alt (s : Prims.string) : Prims.bool=
  (trim_str s) = "processing-instruction()"
let drop_pi_alts (sel : Prims.string) : Prims.string=
  let alts = split_on_char 124 sel in
  let kept =
    FStar_List_Tot_Base.filter (fun a -> Prims.op_Negation (is_pi_alt a))
      alts in
  match kept with
  | [] -> "self::processing-instruction()"
  | uu___ -> FStar_String.concat "|" kept
let eval_nodeset (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (sel : Prims.string) :
  XPath_Eval.xctx_item Prims.list=
  match eval_val ctx pos size vars nsctx (drop_pi_alts sel) with
  | XPath_Eval.XV_Nodes items -> items
  | uu___ -> []
let rec force_abs (e : Parser_XPath.xp_expr) : Parser_XPath.xp_expr=
  match e with
  | Parser_XPath.XE_Path (false, steps) -> Parser_XPath.XE_Path (true, steps)
  | Parser_XPath.XE_Union (a, b) ->
      Parser_XPath.XE_Union ((force_abs a), (force_abs b))
  | uu___ -> e
let eval_val_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : XPath_Eval.xp_value=
  match ctx with
  | D_Item it -> eval_val it pos size vars nsctx expr_text
  | D_Doc (root, doc_kids) ->
      (match Parser_XPath.parse_xpath expr_text with
       | FStar_Pervasives_Native.None -> XPath_Eval.XV_Str ""
       | FStar_Pervasives_Native.Some e ->
           let e2 = force_abs e in
           let doc_nodes = XPath_Eval.xml_node_count root in
           let fuel = XPath_Eval.initial_eval_fuel e2 doc_nodes in
           let env =
             {
               XPath_Eval.env_item = (XPath_Eval.CI_Elem ([], [], root));
               XPath_Eval.env_pos = pos;
               XPath_Eval.env_size = size;
               XPath_Eval.env_vars = vars;
               XPath_Eval.env_nsctx = nsctx;
               XPath_Eval.env_doc_kids = doc_kids
             } in
           XPath_Eval.eval_expr fuel env e2)
let eval_string_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : Prims.string=
  XPath_Eval.to_string_val (eval_val_dn ctx pos size vars nsctx expr_text)
let eval_bool_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : Prims.bool=
  XPath_Eval.to_bool_val (eval_val_dn ctx pos size vars nsctx expr_text)
let eval_nodeset_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (sel : Prims.string) :
  XPath_Eval.xctx_item Prims.list=
  match eval_val_dn ctx pos size vars nsctx (drop_pi_alts sel) with
  | XPath_Eval.XV_Nodes items -> items
  | uu___ -> []
let rec read_until_brace (cs : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | 125::rest -> ((FStar_List_Tot_Base.rev acc), rest)
  | c::rest -> read_until_brace rest (c :: acc)
let rec expand_avt_chars (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (cs : FStar_String.char Prims.list) (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match cs with
     | [] -> ""
     | 123::123::rest ->
         Prims.strcat "{"
           (expand_avt_chars ctx pos size vars nsctx rest
              (fuel - Prims.int_one))
     | 125::125::rest ->
         Prims.strcat "}"
           (expand_avt_chars ctx pos size vars nsctx rest
              (fuel - Prims.int_one))
     | 123::rest ->
         let uu___1 = read_until_brace rest [] in
         (match uu___1 with
          | (expr_cs, after) ->
              let v =
                eval_string ctx pos size vars nsctx (str_of_chars expr_cs) in
              Prims.strcat v
                (expand_avt_chars ctx pos size vars nsctx after
                   (fuel - Prims.int_one)))
     | c::rest ->
         Prims.strcat (soc c)
           (expand_avt_chars ctx pos size vars nsctx rest
              (fuel - Prims.int_one)))
let expand_avt (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (s : Prims.string) :
  Prims.string=
  let cs = chars_of s in
  if contains_char 123 s
  then
    expand_avt_chars ctx pos size vars nsctx cs
      ((FStar_List_Tot_Base.length cs) + Prims.int_one)
  else s
let step_ok (stp : Prims.string) (tag : Prims.string) : Prims.bool=
  let s = trim_str stp in (s = "*") || (s = tag)
let rec match_chain (rsteps : Prims.string Prims.list)
  (tags : Prims.string Prims.list) : Prims.bool=
  match rsteps with
  | [] -> true
  | s::rest ->
      (match tags with
       | [] -> false
       | tg::trest -> if step_ok s tg then match_chain rest trest else false)
let rec any_tag_matches (stp : Prims.string) (tags : Prims.string Prims.list)
  : Prims.bool=
  match tags with
  | [] -> false
  | tg::rest -> if step_ok stp tg then true else any_tag_matches stp rest
let split_predicate (alt : Prims.string) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option)=
  match split_on_char 91 alt with
  | namep::predp::uu___ ->
      let pc = chars_of predp in
      let pc' = FStar_List_Tot_Base.rev pc in
      let pc'' =
        match pc' with | 93::r -> FStar_List_Tot_Base.rev r | uu___1 -> pc in
      ((trim_str namep), (FStar_Pervasives_Native.Some (str_of_chars pc'')))
  | uu___ -> (alt, FStar_Pervasives_Native.None)
let ancestor_tags_of (it : XPath_Eval.xctx_item) : Prims.string Prims.list=
  FStar_List_Tot_Base.choose (fun m -> Parser_XML.element_tag m)
    (XPath_Eval.item_ancestors it)
let pstep_ok (nsctx : (Prims.string * Prims.string) Prims.list)
  (nm : Prims.string) (n : Parser_XML.xml_node)
  (anc : Parser_XML.xml_node Prims.list) : Prims.bool=
  let nm' = trim_str nm in
  if nm' = "*"
  then true
  else
    (match Parser_XML.element_tag n with
     | FStar_Pervasives_Native.Some tag ->
         let tpfx = XPath_Eval.prefix_of nm' in
         if ((XPath_Eval.local_name_of nm') = "*") && (tpfx <> "")
         then
           XPath_Eval.prefix_test_matches_elem nsctx tpfx
             (Parser_XML.element_attrs n) anc tag
         else
           XPath_Eval.name_test_matches_elem nsctx nm'
             (Parser_XML.element_attrs n) anc tag
     | FStar_Pervasives_Native.None -> false)
type pconn =
  | PC_Child 
  | PC_Desc 
let uu___is_PC_Child (projectee : pconn) : Prims.bool=
  match projectee with | PC_Child -> true | uu___ -> false
let uu___is_PC_Desc (projectee : pconn) : Prims.bool=
  match projectee with | PC_Desc -> true | uu___ -> false
let norm_pstep (s : Prims.string) : Prims.string=
  let s0 = trim_str s in
  if starts_with "child::" s0
  then str_of_chars (drop_prefix_chars (chars_of s0) (Prims.of_int (7)))
  else s0
let rec build_psteps (toks : Prims.string Prims.list) (pending : pconn) :
  (pconn * Prims.string) Prims.list=
  match toks with
  | [] -> []
  | t::rest ->
      if (trim_str t) = ""
      then build_psteps rest PC_Desc
      else (pending, (norm_pstep t)) :: (build_psteps rest PC_Child)
let parse_psteps (a : Prims.string) :
  (Prims.bool * (pconn * Prims.string) Prims.list)=
  let toks = split_on_char 47 a in
  match toks with
  | first::t2::rest ->
      if (trim_str first) = ""
      then
        (if (trim_str t2) = ""
         then (false, (build_psteps rest PC_Desc))
         else (true, (build_psteps (t2 :: rest) PC_Child)))
      else (false, (build_psteps toks PC_Child))
  | uu___ -> (false, (build_psteps toks PC_Child))
let rec match_up (nsctx : (Prims.string * Prims.string) Prims.list)
  (anchored : Prims.bool) (rsteps : (pconn * Prims.string) Prims.list)
  (childconn : pconn) (anc : Parser_XML.xml_node Prims.list) : Prims.bool=
  match rsteps with
  | [] -> if anchored then Prims.uu___is_Nil anc else true
  | (c, nm)::rest ->
      (match childconn with
       | PC_Child ->
           (match anc with
            | [] -> false
            | a::az ->
                (pstep_ok nsctx nm a az) &&
                  (match_up nsctx anchored rest c az))
       | PC_Desc -> match_desc nsctx anchored nm rest c anc)
and match_desc (nsctx : (Prims.string * Prims.string) Prims.list)
  (anchored : Prims.bool) (nm : Prims.string)
  (rest : (pconn * Prims.string) Prims.list) (c : pconn)
  (anc : Parser_XML.xml_node Prims.list) : Prims.bool=
  match anc with
  | [] -> false
  | a::az ->
      ((pstep_ok nsctx nm a az) && (match_up nsctx anchored rest c az)) ||
        (match_desc nsctx anchored nm rest c az)
let alt_matches_elem (nsctx : (Prims.string * Prims.string) Prims.list)
  (a : Prims.string) (n : Parser_XML.xml_node)
  (anc : Parser_XML.xml_node Prims.list) : Prims.bool=
  let uu___ = parse_psteps a in
  match uu___ with
  | (anchored, steps) ->
      (match FStar_List_Tot_Base.rev steps with
       | [] -> false
       | (ck, nk)::rrest ->
           if Prims.op_Negation (pstep_ok nsctx nk n anc)
           then false
           else match_up nsctx anchored rrest ck anc)
let strip_quotes (s : Prims.string) : Prims.string=
  let t = trim_str s in
  match chars_of t with
  | q::rest ->
      if (q = 39) || (q = 34)
      then
        (match FStar_List_Tot_Base.rev rest with
         | q2::mid ->
             if q2 = q then str_of_chars (FStar_List_Tot_Base.rev mid) else t
         | [] -> t)
      else t
  | [] -> t
let pi_test_target (a : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match split_on_char 40 a with
  | uu___::rest::uu___1 ->
      let before_close =
        match split_on_char 41 rest with | x::uu___2 -> x | [] -> rest in
      let t = trim_str before_close in
      if t = ""
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (strip_quotes t)
  | uu___ -> FStar_Pervasives_Native.None
let alt_matches_core (nsctx : (Prims.string * Prims.string) Prims.list)
  (alt : Prims.string) (nd : dnode) : Prims.bool=
  let a = trim_str alt in
  if a = "/"
  then match nd with | D_Doc (uu___, uu___1) -> true | uu___ -> false
  else
    if a = "*"
    then
      (match nd with
       | D_Item (XPath_Eval.CI_Elem (uu___1, uu___2, uu___3)) -> true
       | uu___1 -> false)
    else
      if a = "@*"
      then
        (match nd with
         | D_Item (XPath_Eval.CI_Attr (uu___2, uu___3, uu___4, uu___5)) ->
             true
         | uu___2 -> false)
      else
        if a = "text()"
        then
          (match nd with
           | D_Item (XPath_Eval.CI_Text (uu___3, uu___4, uu___5, uu___6)) ->
               true
           | uu___3 -> false)
        else
          if a = "comment()"
          then
            (match nd with
             | D_Item (XPath_Eval.CI_Comment
                 (uu___4, uu___5, uu___6, uu___7)) -> true
             | uu___4 -> false)
          else
            if a = "node()"
            then
              (match nd with
               | D_Item (XPath_Eval.CI_Elem (uu___5, uu___6, uu___7)) -> true
               | D_Item (XPath_Eval.CI_Text (uu___5, uu___6, uu___7, uu___8))
                   -> true
               | D_Item (XPath_Eval.CI_Comment
                   (uu___5, uu___6, uu___7, uu___8)) -> true
               | D_Item (XPath_Eval.CI_PI
                   (uu___5, uu___6, uu___7, uu___8, uu___9)) -> true
               | uu___5 -> false)
            else
              if a = "processing-instruction()"
              then
                (match nd with
                 | D_Item (XPath_Eval.CI_PI
                     (uu___6, uu___7, uu___8, uu___9, uu___10)) -> true
                 | uu___6 -> false)
              else
                if starts_with "processing-instruction(" a
                then
                  (match nd with
                   | D_Item (XPath_Eval.CI_PI
                       (uu___7, uu___8, uu___9, tgt, uu___10)) ->
                       (match pi_test_target a with
                        | FStar_Pervasives_Native.None -> true
                        | FStar_Pervasives_Native.Some want -> tgt = want)
                   | uu___7 -> false)
                else
                  if starts_with "@" a
                  then
                    (match nd with
                     | D_Item (XPath_Eval.CI_Attr (uu___8, anc, owner, att))
                         ->
                         let nm =
                           str_of_chars
                             (drop_prefix_chars (chars_of a) Prims.int_one) in
                         let tpfx = XPath_Eval.prefix_of nm in
                         if
                           ((XPath_Eval.local_name_of nm) = "*") &&
                             (tpfx <> "")
                         then
                           (match XPath_Eval.lookup_nsctx nsctx tpfx with
                            | FStar_Pervasives_Native.None ->
                                XPath_Eval.string_starts_with
                                  att.Parser_XML.attr_name
                                  (Prims.strcat tpfx ":")
                            | FStar_Pervasives_Native.Some turi ->
                                let apfx =
                                  XPath_Eval.prefix_of
                                    att.Parser_XML.attr_name in
                                (apfx <> "") &&
                                  (XPath_Eval.ns_uri_eq
                                     (XPath_Eval.resolve_ns_uri apfx
                                        (Parser_XML.element_attrs owner) anc)
                                     (FStar_Pervasives_Native.Some turi)))
                         else att.Parser_XML.attr_name = nm
                     | uu___8 -> false)
                  else
                    if a = "attribute::*"
                    then
                      (match nd with
                       | D_Item (XPath_Eval.CI_Attr
                           (uu___9, uu___10, uu___11, uu___12)) -> true
                       | uu___9 -> false)
                    else
                      if starts_with "attribute::" a
                      then
                        (match nd with
                         | D_Item (XPath_Eval.CI_Attr
                             (uu___10, uu___11, uu___12, att)) ->
                             att.Parser_XML.attr_name =
                               (str_of_chars
                                  (drop_prefix_chars (chars_of a)
                                     (Prims.of_int (11))))
                         | uu___10 -> false)
                      else
                        (match nd with
                         | D_Item (XPath_Eval.CI_Elem (uu___11, anc, n)) ->
                             alt_matches_elem nsctx a n anc
                         | uu___11 -> false)
let rec has_double_colon_chars (cs : FStar_String.char Prims.list) :
  Prims.bool=
  match cs with
  | [] -> false
  | c0::rest ->
      (match rest with
       | c1::uu___ ->
           if (c0 = 58) && (c1 = 58)
           then true
           else has_double_colon_chars rest
       | [] -> false)
let contains_double_colon (s : Prims.string) : Prims.bool=
  has_double_colon_chars (chars_of s)
let is_child_union_alt (alt : Prims.string) : Prims.bool=
  let a = trim_str alt in
  if
    (((((a = "*") || (a = "@*")) || (a = "text()")) || (a = "comment()")) ||
       (a = "node()"))
      || (a = "processing-instruction()")
  then true
  else
    if starts_with "@" a
    then
      Prims.op_Negation
        (((contains_char 47 a) || (contains_char 91 a)) ||
           (contains_char 40 a))
    else
      ((((((a <> "") && (Prims.op_Negation (starts_with "." a))) &&
            (Prims.op_Negation (starts_with "$" a)))
           && (Prims.op_Negation (contains_char 47 a)))
          && (Prims.op_Negation (contains_char 91 a)))
         && (Prims.op_Negation (contains_char 40 a)))
        && (Prims.op_Negation (contains_double_colon a))
let rec all_child_union_alts (alts : Prims.string Prims.list) : Prims.bool=
  match alts with
  | [] -> true
  | a::rest ->
      if is_child_union_alt a then all_child_union_alts rest else false
let is_simple_child_union (sel : Prims.string) : Prims.bool=
  let alts = split_on_char 124 sel in
  match alts with | [] -> false | uu___ -> all_child_union_alts alts
let rec any_core_matches (nsctx : (Prims.string * Prims.string) Prims.list)
  (alts : Prims.string Prims.list) (it : XPath_Eval.xctx_item) : Prims.bool=
  match alts with
  | [] -> false
  | a::rest ->
      if alt_matches_core nsctx a (D_Item it)
      then true
      else any_core_matches nsctx rest it
let select_child_union (nsctx : (Prims.string * Prims.string) Prims.list)
  (nd : dnode) (alts : Prims.string Prims.list) :
  XPath_Eval.xctx_item Prims.list=
  let uu___ = dnode_attrs_and_kids nd in
  match uu___ with
  | (attrs, kids) ->
      let sel_attrs =
        FStar_List_Tot_Base.filter (fun it -> any_core_matches nsctx alts it)
          attrs in
      let sel_kids =
        FStar_List_Tot_Base.filter (fun it -> any_core_matches nsctx alts it)
          kids in
      FStar_List_Tot_Base.op_At sel_attrs sel_kids
let select_nodes (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (sel : Prims.string) :
  XPath_Eval.xctx_item Prims.list=
  if is_simple_child_union sel
  then select_child_union nsctx ctx (split_on_char 124 sel)
  else eval_nodeset_dn ctx pos size vars nsctx sel
let match_proximity (nsctx : (Prims.string * Prims.string) Prims.list)
  (namepart : Prims.string) (it : XPath_Eval.xctx_item) :
  (Prims.nat * Prims.nat)=
  let sibs = XPath_Eval.siblings_of it in
  if Prims.uu___is_Nil sibs
  then (Prims.int_one, Prims.int_one)
  else
    (let matching =
       FStar_List_Tot_Base.filter
         (fun s -> alt_matches_core nsctx namepart (D_Item s)) sibs in
     let p = XPath_Eval.item_path it in
     let before =
       FStar_List_Tot_Base.filter
         (fun s ->
            (XPath_Eval.path_compare (XPath_Eval.item_path s) p) <
              Prims.int_zero) matching in
     (((FStar_List_Tot_Base.length before) + Prims.int_one),
       (FStar_List_Tot_Base.length matching)))
let alt_matches (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (alt : Prims.string)
  (nd : dnode) : Prims.bool=
  let uu___ = split_predicate alt in
  match uu___ with
  | (namepart, predopt) ->
      (match predopt with
       | FStar_Pervasives_Native.None -> alt_matches_core nsctx alt nd
       | FStar_Pervasives_Native.Some pred ->
           if Prims.op_Negation (alt_matches_core nsctx namepart nd)
           then false
           else
             (match nd with
              | D_Doc (uu___2, uu___3) ->
                  eval_bool (dnode_ci nd) Prims.int_one Prims.int_one vars
                    nsctx pred
              | D_Item it ->
                  let uu___2 = match_proximity nsctx namepart it in
                  (match uu___2 with
                   | (p, s) -> eval_bool it p s vars nsctx pred)))
let rec any_alt_matches
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (alts : Prims.string Prims.list) (nd : dnode) : Prims.bool=
  match alts with
  | [] -> false
  | a::rest ->
      if alt_matches vars nsctx a nd
      then true
      else any_alt_matches vars nsctx rest nd
let template_matches (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (tpl : template)
  (nd : dnode) : Prims.bool=
  if tpl.tpl_match = ""
  then false
  else any_alt_matches vars nsctx (split_on_char 124 tpl.tpl_match) nd
let alt_priority (alt : Prims.string) : Prims.int=
  let a = trim_str alt in
  if
    ((((((a = "*") || (a = "@*")) || (a = "node()")) || (a = "text()")) ||
        (a = "comment()"))
       || (a = "processing-instruction()"))
      || (a = "attribute::*")
  then (Prims.of_int (-5))
  else
    if (contains_char 47 a) || (contains_char 91 a)
    then (Prims.of_int (5))
    else
      (let core =
         if starts_with "@" a
         then str_of_chars (drop_prefix_chars (chars_of a) Prims.int_one)
         else a in
       if
         ((XPath_Eval.local_name_of core) = "*") &&
           ((XPath_Eval.prefix_of core) <> "")
       then (Prims.of_int (-2))
       else Prims.int_zero)
let rec max_alt_priority (alts : Prims.string Prims.list) (cur : Prims.int) :
  Prims.int=
  match alts with
  | [] -> cur
  | a::rest ->
      let p = alt_priority a in
      max_alt_priority rest (if p > cur then p else cur)
let template_priority (tpl : template) : Prims.int=
  match tpl.tpl_prio with
  | FStar_Pervasives_Native.Some p -> p
  | FStar_Pervasives_Native.None ->
      max_alt_priority (split_on_char 124 tpl.tpl_match)
        (Prims.of_int (-100))
let rec pick_template
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (mode : Prims.string)
  (tpls : template Prims.list) (nd : dnode)
  (best : template FStar_Pervasives_Native.option) :
  template FStar_Pervasives_Native.option=
  match tpls with
  | [] -> best
  | t::rest ->
      let best' =
        if (t.tpl_mode = mode) && (template_matches vars nsctx t nd)
        then
          match best with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some t
          | FStar_Pervasives_Native.Some b ->
              (if (template_priority t) >= (template_priority b)
               then FStar_Pervasives_Native.Some t
               else best)
        else best in
      pick_template vars nsctx mode rest nd best'
let rec find_named_template (tpls : template Prims.list) (nm : Prims.string)
  : template FStar_Pervasives_Native.option=
  match tpls with
  | [] -> FStar_Pervasives_Native.None
  | t::rest ->
      if (t.tpl_name = nm) && (nm <> "")
      then FStar_Pervasives_Native.Some t
      else find_named_template rest nm
let escape_text_char (c : FStar_String.char) : Prims.string=
  if c = 38
  then "&amp;"
  else if c = 60 then "&lt;" else if c = 62 then "&gt;" else soc c
let escape_attr_char (c : FStar_String.char) : Prims.string=
  if c = 38
  then "&amp;"
  else
    if c = 60
    then "&lt;"
    else if c = 34 then "&quot;" else if c = 62 then "&gt;" else soc c
let rec escape_with (f : FStar_String.char -> Prims.string)
  (cs : FStar_String.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest -> Prims.strcat (f c) (escape_with f rest)
let escape_text (s : Prims.string) : Prims.string=
  escape_with escape_text_char (chars_of s)
let escape_attr (s : Prims.string) : Prims.string=
  escape_with escape_attr_char (chars_of s)
let serialize_attr (a : Parser_XML.xml_attribute) : Prims.string=
  FStar_String.concat ""
    [" ";
    a.Parser_XML.attr_name;
    "=\"";
    escape_attr a.Parser_XML.attr_value;
    "\""]
let rec serialize_attrs (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string=
  match attrs with
  | [] -> ""
  | a::rest -> Prims.strcat (serialize_attr a) (serialize_attrs rest)
let rec lookup_ns (scope : (Prims.string * Prims.string) Prims.list)
  (pfx : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match scope with
  | [] -> FStar_Pervasives_Native.None
  | (p, u)::rest ->
      if p = pfx then FStar_Pervasives_Native.Some u else lookup_ns rest pfx
let rec emit_ns_decls (scope : (Prims.string * Prims.string) Prims.list)
  (decls : Parser_XML.xml_attribute Prims.list) :
  (Prims.string * (Prims.string * Prims.string) Prims.list)=
  match decls with
  | [] -> ("", scope)
  | a::rest ->
      (match ns_decl_prefix a.Parser_XML.attr_name with
       | FStar_Pervasives_Native.None -> emit_ns_decls scope rest
       | FStar_Pervasives_Native.Some pfx ->
           let cur = lookup_ns scope pfx in
           let redundant =
             (cur = (FStar_Pervasives_Native.Some (a.Parser_XML.attr_value)))
               ||
               ((a.Parser_XML.attr_value = "") &&
                  (cur = FStar_Pervasives_Native.None)) in
           let scope' =
             if redundant
             then scope
             else (pfx, (a.Parser_XML.attr_value)) :: scope in
           let uu___ = emit_ns_decls scope' rest in
           (match uu___ with
            | (s_rest, scope'') ->
                let here = if redundant then "" else serialize_attr a in
                ((Prims.strcat here s_rest), scope'')))
let rec serialize_node (scope : (Prims.string * Prims.string) Prims.list)
  (n : Parser_XML.xml_node) : Prims.string=
  match n with
  | Parser_XML.XText t -> escape_text t
  | Parser_XML.XCDATA t -> escape_text t
  | Parser_XML.XComment t -> FStar_String.concat "" ["<!--"; t; "-->"]
  | Parser_XML.XPI (tg, d) -> FStar_String.concat "" ["<?"; tg; " "; d; "?>"]
  | Parser_XML.XElement (tag, attrs, children) ->
      let uu___ = FStar_List_Tot_Base.partition is_ns_decl attrs in
      (match uu___ with
       | (decls, normal) ->
           let uu___1 = emit_ns_decls scope decls in
           (match uu___1 with
            | (ns_str, scope') ->
                let a = Prims.strcat ns_str (serialize_attrs normal) in
                let inner = serialize_nodes scope' children in
                if inner = ""
                then FStar_String.concat "" ["<"; tag; a; "/>"]
                else
                  FStar_String.concat ""
                    ["<"; tag; a; ">"; inner; "</"; tag; ">"]))
and serialize_nodes (scope : (Prims.string * Prims.string) Prims.list)
  (ns : Parser_XML.xml_node Prims.list) : Prims.string=
  match ns with
  | [] -> ""
  | hd::tl ->
      Prims.strcat (serialize_node scope hd) (serialize_nodes scope tl)
let serialize_result (n : Parser_XML.xml_node) : Prims.string=
  serialize_node [] n
let rec text_value_node (n : Parser_XML.xml_node) : Prims.string=
  match n with
  | Parser_XML.XText t -> t
  | Parser_XML.XCDATA t -> t
  | Parser_XML.XComment uu___ -> ""
  | Parser_XML.XPI (uu___, uu___1) -> ""
  | Parser_XML.XElement (uu___, uu___1, children) ->
      text_value_nodes children
and text_value_nodes (ns : Parser_XML.xml_node Prims.list) : Prims.string=
  match ns with
  | [] -> ""
  | hd::tl -> Prims.strcat (text_value_node hd) (text_value_nodes tl)
let ascii_lower_char (c : FStar_String.char) : FStar_String.char=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (0x41))) && (n <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (n + (Prims.of_int (0x20)))
  else c
let is_ascii_lower (c : FStar_String.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (0x61))) && (n <= (Prims.of_int (0x7A)))
let rec cmp_chars_ci (a : FStar_String.char Prims.list)
  (b : FStar_String.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      let lx = FStar_Char.int_of_char (ascii_lower_char x) in
      let ly = FStar_Char.int_of_char (ascii_lower_char y) in
      if lx = ly
      then cmp_chars_ci xs ys
      else if lx < ly then (Prims.of_int (-1)) else Prims.int_one
let rec cmp_chars_case (lower_first : Prims.bool)
  (a : FStar_String.char Prims.list) (b : FStar_String.char Prims.list) :
  Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      if x = y
      then cmp_chars_case lower_first xs ys
      else
        (let x_is_lower = is_ascii_lower x in
         if lower_first
         then (if x_is_lower then (Prims.of_int (-1)) else Prims.int_one)
         else if x_is_lower then Prims.int_one else (Prims.of_int (-1)))
let cmp_text_caseorder (lower_first : Prims.bool) (a : Prims.string)
  (b : Prims.string) : Prims.int=
  let ca = chars_of a in
  let cb = chars_of b in
  let prim = cmp_chars_ci ca cb in
  if prim <> Prims.int_zero then prim else cmp_chars_case lower_first ca cb
type sortspec =
  {
  so_select: Prims.string ;
  so_numeric: Prims.bool ;
  so_descending: Prims.bool ;
  so_case_order: Prims.int }
let __proj__Mksortspec__item__so_select (projectee : sortspec) :
  Prims.string=
  match projectee with
  | { so_select; so_numeric; so_descending; so_case_order;_} -> so_select
let __proj__Mksortspec__item__so_numeric (projectee : sortspec) : Prims.bool=
  match projectee with
  | { so_select; so_numeric; so_descending; so_case_order;_} -> so_numeric
let __proj__Mksortspec__item__so_descending (projectee : sortspec) :
  Prims.bool=
  match projectee with
  | { so_select; so_numeric; so_descending; so_case_order;_} -> so_descending
let __proj__Mksortspec__item__so_case_order (projectee : sortspec) :
  Prims.int=
  match projectee with
  | { so_select; so_numeric; so_descending; so_case_order;_} -> so_case_order
let parse_sort (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (pfx : Prims.string)
  (n : Parser_XML.xml_node) : sortspec FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "sort")
      then
        let dt =
          expand_avt ctx pos size vars nsctx
            (attr_or "data-type" "text" attrs) in
        let od =
          expand_avt ctx pos size vars nsctx
            (attr_or "order" "ascending" attrs) in
        let co =
          expand_avt ctx pos size vars nsctx (attr_or "case-order" "" attrs) in
        FStar_Pervasives_Native.Some
          {
            so_select = (attr_or "select" "." attrs);
            so_numeric = (dt = "number");
            so_descending = (od = "descending");
            so_case_order =
              ((if co = "lower-first"
                then Prims.int_one
                else
                  if co = "upper-first"
                  then (Prims.of_int (2))
                  else Prims.int_zero))
          }
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec collect_sorts (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) (pfx : Prims.string)
  (body : Parser_XML.xml_node Prims.list) : sortspec Prims.list=
  match body with
  | [] -> []
  | hd::tl ->
      (match parse_sort ctx pos size vars nsctx pfx hd with
       | FStar_Pervasives_Native.Some s -> s ::
           (collect_sorts ctx pos size vars nsctx pfx tl)
       | FStar_Pervasives_Native.None ->
           (match hd with
            | Parser_XML.XText t ->
                if is_all_ws t
                then collect_sorts ctx pos size vars nsctx pfx tl
                else []
            | Parser_XML.XComment uu___ ->
                collect_sorts ctx pos size vars nsctx pfx tl
            | uu___ -> []))
let rec eval_sort_keys (specs : sortspec Prims.list)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (it : XPath_Eval.xctx_item) (pos : Prims.nat) (size : Prims.nat) :
  Prims.string Prims.list=
  match specs with
  | [] -> []
  | s::rest -> (eval_string it pos size vars nsctx s.so_select) ::
      (eval_sort_keys rest vars nsctx it pos size)
let rec annotate_items (specs : sortspec Prims.list)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (items : XPath_Eval.xctx_item Prims.list) (pos : Prims.nat)
  (size : Prims.nat) :
  (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list=
  match items with
  | [] -> []
  | it::tl -> (it, (eval_sort_keys specs vars nsctx it pos size)) ::
      (annotate_items specs vars nsctx tl (pos + Prims.int_one) size)
let rec cmp_sort_keys (specs : sortspec Prims.list)
  (ka : Prims.string Prims.list) (kb : Prims.string Prims.list) : Prims.int=
  match (specs, ka, kb) with
  | (s::sr, a::ar, b::br) ->
      let raw =
        if s.so_numeric
        then
          let na = XPath_Eval.string_to_xn a in
          let nb = XPath_Eval.string_to_xn b in
          match XPath_Eval.xn_compare na nb with
          | FStar_Pervasives_Native.Some c -> c
          | FStar_Pervasives_Native.None ->
              let a_nan =
                match na with | XPath_Eval.XN_NaN -> true | uu___ -> false in
              let b_nan =
                match nb with | XPath_Eval.XN_NaN -> true | uu___ -> false in
              (if a_nan && b_nan
               then Prims.int_zero
               else if a_nan then (Prims.of_int (-1)) else Prims.int_one)
        else
          if s.so_case_order = Prims.int_zero
          then FStar_String.compare a b
          else cmp_text_caseorder (s.so_case_order = Prims.int_one) a b in
      let signed = if s.so_descending then Prims.int_zero - raw else raw in
      if signed <> Prims.int_zero then signed else cmp_sort_keys sr ar br
  | (uu___, uu___1, uu___2) -> Prims.int_zero
let rec sort_insert (specs : sortspec Prims.list)
  (x : (XPath_Eval.xctx_item * Prims.string Prims.list))
  (l : (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list) :
  (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list=
  match l with
  | [] -> [x]
  | y::ys ->
      if
        (cmp_sort_keys specs (FStar_Pervasives_Native.snd x)
           (FStar_Pervasives_Native.snd y))
          <= Prims.int_zero
      then x :: l
      else y :: (sort_insert specs x ys)
let rec sort_items (specs : sortspec Prims.list)
  (l : (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list) :
  (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list=
  match l with
  | [] -> []
  | x::xs -> sort_insert specs x (sort_items specs xs)
let sort_maybe (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (pfx : Prims.string)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (body : Parser_XML.xml_node Prims.list)
  (items : XPath_Eval.xctx_item Prims.list) :
  XPath_Eval.xctx_item Prims.list=
  match collect_sorts ctx pos size vars nsctx pfx body with
  | [] -> items
  | specs ->
      let n = FStar_List_Tot_Base.length items in
      FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
        (sort_items specs
           (annotate_items specs vars nsctx items Prims.int_one n))
let rtf_var_name (sel : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let s = trim_str sel in
  if starts_with "$" s
  then
    FStar_Pervasives_Native.Some
      (str_of_chars (drop_prefix_chars (chars_of s) Prims.int_one))
  else FStar_Pervasives_Native.None
let rec rtf_find (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (nm : Prims.string) : rnode Prims.list FStar_Pervasives_Native.option=
  match rtf with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = nm then FStar_Pervasives_Native.Some v else rtf_find rest nm
let rec dispatch (fuel : Prims.nat) (st : xstyle) (nd : dnode)
  (pos : Prims.nat) (size : Prims.nat) (mode : Prims.string) :
  rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match pick_template st.xs_globals st.xs_nsctx mode st.xs_templates nd
             FStar_Pervasives_Native.None
     with
     | FStar_Pervasives_Native.Some tpl ->
         instantiate_seq (fuel - Prims.int_one) st nd pos size st.xs_globals
           [] tpl.tpl_body
     | FStar_Pervasives_Native.None ->
         builtin_rule (fuel - Prims.int_one) st nd mode)
and builtin_rule (fuel : Prims.nat) (st : xstyle) (nd : dnode)
  (mode : Prims.string) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match nd with
     | D_Doc (uu___1, uu___2) ->
         let kids = dnode_children nd in
         apply_list (fuel - Prims.int_one) st kids Prims.int_one
           (FStar_List_Tot_Base.length kids) mode
     | D_Item (XPath_Eval.CI_Elem (uu___1, uu___2, uu___3)) ->
         let kids = dnode_children nd in
         apply_list (fuel - Prims.int_one) st kids Prims.int_one
           (FStar_List_Tot_Base.length kids) mode
     | D_Item (XPath_Eval.CI_Text (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XText t)]
     | D_Item (XPath_Eval.CI_Attr (uu___1, uu___2, uu___3, a)) ->
         [R_Node (Parser_XML.XText (a.Parser_XML.attr_value))]
     | D_Item (XPath_Eval.CI_Comment (uu___1, uu___2, uu___3, uu___4)) -> []
     | D_Item (XPath_Eval.CI_PI (uu___1, uu___2, uu___3, uu___4, uu___5)) ->
         [])
and apply_list (fuel : Prims.nat) (st : xstyle) (nodes : dnode Prims.list)
  (pos : Prims.nat) (size : Prims.nat) (mode : Prims.string) :
  rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match nodes with
     | [] -> []
     | hd::tl ->
         let here = dispatch (fuel - Prims.int_one) st hd pos size mode in
         FStar_List_Tot_Base.op_At here
           (apply_list (fuel - Prims.int_one) st tl (pos + Prims.int_one)
              size mode))
and instantiate_seq (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (nodes : Parser_XML.xml_node Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match nodes with
     | [] -> []
     | hd::tl ->
         (match hd with
          | Parser_XML.XElement (tag, attrs, children) ->
              if
                (is_xsl st.xs_pfx tag) &&
                  (let ln = xsl_instr st.xs_pfx tag in
                   (ln = "variable") || (ln = "param"))
              then
                let nm = attr_or "name" "" attrs in
                let already =
                  ((xsl_instr st.xs_pfx tag) = "param") &&
                    (FStar_Pervasives_Native.uu___is_Some
                       (XPath_Eval.lookup_var vars nm)) in
                (if already
                 then
                   instantiate_seq (fuel - Prims.int_one) st ctx pos size
                     vars rtf tl
                 else
                   (match attr_opt "select" attrs with
                    | FStar_Pervasives_Native.Some sel ->
                        let v = eval_val_dn ctx pos size vars st.xs_nsctx sel in
                        instantiate_seq (fuel - Prims.int_one) st ctx pos
                          size ((nm, v) :: vars) rtf tl
                    | FStar_Pervasives_Native.None ->
                        let frag =
                          instantiate_seq (fuel - Prims.int_one) st ctx pos
                            size vars rtf children in
                        let sval = text_value_nodes (only_nodes frag) in
                        instantiate_seq (fuel - Prims.int_one) st ctx pos
                          size ((nm, (XPath_Eval.XV_Str sval)) :: vars)
                          ((nm, frag) :: rtf) tl))
              else
                (let here =
                   instantiate_one (fuel - Prims.int_one) st ctx pos size
                     vars rtf hd in
                 FStar_List_Tot_Base.op_At here
                   (instantiate_seq (fuel - Prims.int_one) st ctx pos size
                      vars rtf tl))
          | uu___1 ->
              let here =
                instantiate_one (fuel - Prims.int_one) st ctx pos size vars
                  rtf hd in
              FStar_List_Tot_Base.op_At here
                (instantiate_seq (fuel - Prims.int_one) st ctx pos size vars
                   rtf tl)))
and bind_with_params (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (children : Parser_XML.xml_node Prims.list) :
  ((Prims.string * XPath_Eval.xp_value) Prims.list * (Prims.string * rnode
    Prims.list) Prims.list)=
  if fuel = Prims.int_zero
  then (vars, rtf)
  else
    (match children with
     | [] -> (vars, rtf)
     | hd::tl ->
         (match hd with
          | Parser_XML.XElement (tag, attrs, pchildren) ->
              if
                (is_xsl st.xs_pfx tag) &&
                  ((xsl_instr st.xs_pfx tag) = "with-param")
              then
                let nm = attr_or "name" "" attrs in
                (match attr_opt "select" attrs with
                 | FStar_Pervasives_Native.Some sel ->
                     let v = eval_val_dn ctx pos size vars st.xs_nsctx sel in
                     bind_with_params (fuel - Prims.int_one) st ctx pos size
                       ((nm, v) :: vars) rtf tl
                 | FStar_Pervasives_Native.None ->
                     let frag =
                       instantiate_seq (fuel - Prims.int_one) st ctx pos size
                         vars rtf pchildren in
                     let sval = text_value_nodes (only_nodes frag) in
                     bind_with_params (fuel - Prims.int_one) st ctx pos size
                       ((nm, (XPath_Eval.XV_Str sval)) :: vars) ((nm, frag)
                       :: rtf) tl)
              else
                bind_with_params (fuel - Prims.int_one) st ctx pos size vars
                  rtf tl
          | uu___1 ->
              bind_with_params (fuel - Prims.int_one) st ctx pos size vars
                rtf tl))
and instantiate_one (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (node : Parser_XML.xml_node) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match node with
     | Parser_XML.XText t ->
         if is_all_ws t then [] else [R_Node (Parser_XML.XText t)]
     | Parser_XML.XComment uu___1 -> []
     | Parser_XML.XPI (tg, d) -> [R_Node (Parser_XML.XPI (tg, d))]
     | Parser_XML.XCDATA t -> [R_Node (Parser_XML.XText t)]
     | Parser_XML.XElement (tag, attrs, children) ->
         if is_xsl st.xs_pfx tag
         then
           let ln = xsl_instr st.xs_pfx tag in
           (if ln = "value-of"
            then
              [R_Node
                 (Parser_XML.XText
                    (eval_string_dn ctx pos size vars st.xs_nsctx
                       (attr_or "select" "." attrs)))]
            else
              if ln = "text"
              then [R_Node (Parser_XML.XText (raw_text children))]
              else
                if ln = "if"
                then
                  (if
                     eval_bool_dn ctx pos size vars st.xs_nsctx
                       (attr_or "test" "false()" attrs)
                   then
                     instantiate_seq (fuel - Prims.int_one) st ctx pos size
                       vars rtf children
                   else [])
                else
                  if ln = "choose"
                  then
                    instantiate_choose (fuel - Prims.int_one) st ctx pos size
                      vars rtf children
                  else
                    if ln = "for-each"
                    then
                      (let sel = attr_or "select" "." attrs in
                       let items0 =
                         XPath_Eval.doc_sort_dedup
                           (select_nodes ctx pos size vars st.xs_nsctx sel) in
                       let items =
                         sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars
                           st.xs_nsctx children items0 in
                       for_each_items (fuel - Prims.int_one) st children vars
                         rtf items Prims.int_one
                         (FStar_List_Tot_Base.length items))
                    else
                      if ln = "apply-templates"
                      then
                        (let amode = attr_or "mode" "" attrs in
                         match attr_opt "select" attrs with
                         | FStar_Pervasives_Native.Some sel ->
                             let items0 =
                               XPath_Eval.doc_sort_dedup
                                 (select_nodes ctx pos size vars st.xs_nsctx
                                    sel) in
                             let items =
                               sort_maybe (dnode_ci ctx) pos size st.xs_pfx
                                 vars st.xs_nsctx children items0 in
                             let dns =
                               FStar_List_Tot_Base.map (fun it -> D_Item it)
                                 items in
                             apply_list (fuel - Prims.int_one) st dns
                               Prims.int_one
                               (FStar_List_Tot_Base.length items) amode
                         | FStar_Pervasives_Native.None ->
                             let kids0 = dnode_children ctx in
                             let items0 =
                               FStar_List_Tot_Base.map dnode_ci kids0 in
                             let items =
                               sort_maybe (dnode_ci ctx) pos size st.xs_pfx
                                 vars st.xs_nsctx children items0 in
                             let dns =
                               FStar_List_Tot_Base.map (fun it -> D_Item it)
                                 items in
                             apply_list (fuel - Prims.int_one) st dns
                               Prims.int_one
                               (FStar_List_Tot_Base.length items) amode)
                      else
                        if ln = "call-template"
                        then
                          (let nm = attr_or "name" "" attrs in
                           match find_named_template st.xs_templates nm with
                           | FStar_Pervasives_Native.Some tpl ->
                               let uu___7 =
                                 bind_with_params (fuel - Prims.int_one) st
                                   ctx pos size st.xs_globals [] children in
                               (match uu___7 with
                                | (cvars, crtf) ->
                                    instantiate_seq (fuel - Prims.int_one) st
                                      ctx pos size cvars crtf tpl.tpl_body)
                           | FStar_Pervasives_Native.None -> [])
                        else
                          if ln = "copy-of"
                          then
                            (let sel = attr_or "select" "." attrs in
                             let no_ns =
                               (attr_or "copy-namespaces" "yes" attrs) = "no" in
                             let mk =
                               if no_ns
                               then copy_of_item_no_ns
                               else copy_of_item in
                             match rtf_var_name sel with
                             | FStar_Pervasives_Native.Some nm ->
                                 (match rtf_find rtf nm with
                                  | FStar_Pervasives_Native.Some frag ->
                                      if no_ns
                                      then
                                        FStar_List_Tot_Base.map
                                          rnode_strip_ns frag
                                      else frag
                                  | FStar_Pervasives_Native.None ->
                                      FStar_List_Tot_Base.map mk
                                        (select_nodes ctx pos size vars
                                           st.xs_nsctx sel))
                             | FStar_Pervasives_Native.None ->
                                 FStar_List_Tot_Base.map mk
                                   (select_nodes ctx pos size vars
                                      st.xs_nsctx sel))
                          else
                            if ln = "copy"
                            then
                              instantiate_copy (fuel - Prims.int_one) st ctx
                                pos size vars rtf children
                            else
                              if ln = "element"
                              then
                                (let nm =
                                   expand_avt (dnode_ci ctx) pos size vars
                                     st.xs_nsctx (attr_or "name" "" attrs) in
                                 let epfx = name_prefix nm in
                                 let nsdecls =
                                   match attr_opt "namespace" attrs with
                                   | FStar_Pervasives_Native.Some nsraw ->
                                       let u =
                                         expand_avt (dnode_ci ctx) pos size
                                           vars st.xs_nsctx nsraw in
                                       if epfx = ""
                                       then
                                         [{
                                            Parser_XML.attr_name = "xmlns";
                                            Parser_XML.attr_value = u
                                          }]
                                       else
                                         if u = ""
                                         then []
                                         else
                                           [{
                                              Parser_XML.attr_name =
                                                (Prims.strcat "xmlns:" epfx);
                                              Parser_XML.attr_value = u
                                            }]
                                   | FStar_Pervasives_Native.None ->
                                       if epfx = ""
                                       then
                                         (match XPath_Eval.lookup_nsctx
                                                  st.xs_nsctx ""
                                          with
                                          | FStar_Pervasives_Native.Some u ->
                                              [{
                                                 Parser_XML.attr_name =
                                                   "xmlns";
                                                 Parser_XML.attr_value = u
                                               }]
                                          | FStar_Pervasives_Native.None ->
                                              [{
                                                 Parser_XML.attr_name =
                                                   "xmlns";
                                                 Parser_XML.attr_value = ""
                                               }])
                                       else
                                         (match XPath_Eval.lookup_nsctx
                                                  st.xs_nsctx epfx
                                          with
                                          | FStar_Pervasives_Native.Some u ->
                                              [{
                                                 Parser_XML.attr_name =
                                                   (Prims.strcat "xmlns:"
                                                      epfx);
                                                 Parser_XML.attr_value = u
                                               }]
                                          | FStar_Pervasives_Native.None ->
                                              []) in
                                 let body =
                                   instantiate_seq (fuel - Prims.int_one) st
                                     ctx pos size vars rtf children in
                                 [R_Node (build_element nm nsdecls body)])
                              else
                                if ln = "attribute"
                                then
                                  (let nm =
                                     expand_avt (dnode_ci ctx) pos size vars
                                       st.xs_nsctx (attr_or "name" "" attrs) in
                                   let body =
                                     instantiate_seq (fuel - Prims.int_one)
                                       st ctx pos size vars rtf children in
                                   [R_Attr
                                      {
                                        Parser_XML.attr_name = nm;
                                        Parser_XML.attr_value =
                                          (rnodes_text body)
                                      }])
                                else
                                  if ln = "comment"
                                  then
                                    (let body =
                                       instantiate_seq (fuel - Prims.int_one)
                                         st ctx pos size vars rtf children in
                                     [R_Node
                                        (Parser_XML.XComment
                                           (rnodes_text body))])
                                  else [])
         else
           (let kept =
              FStar_List_Tot_Base.filter
                (fun a ->
                   (Prims.op_Negation
                      (starts_with (Prims.strcat st.xs_pfx ":")
                         a.Parser_XML.attr_name))
                     &&
                     (Prims.op_Negation
                        ((is_ns_decl a) &&
                           (a.Parser_XML.attr_value = xslt_ns)))) attrs in
            let out_attrs =
              FStar_List_Tot_Base.map
                (fun a ->
                   {
                     Parser_XML.attr_name = (a.Parser_XML.attr_name);
                     Parser_XML.attr_value =
                       (expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx
                          a.Parser_XML.attr_value)
                   }) kept in
            let body =
              instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
                children in
            [R_Node
               (build_element tag
                  (FStar_List_Tot_Base.op_At st.xs_nsscope out_attrs) body)]))
and instantiate_choose (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (branches : Parser_XML.xml_node Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match branches with
     | [] -> []
     | hd::tl ->
         (match hd with
          | Parser_XML.XElement (tag, attrs, children) ->
              if is_xsl st.xs_pfx tag
              then
                let ln = xsl_instr st.xs_pfx tag in
                (if ln = "when"
                 then
                   (if
                      eval_bool_dn ctx pos size vars st.xs_nsctx
                        (attr_or "test" "false()" attrs)
                    then
                      instantiate_seq (fuel - Prims.int_one) st ctx pos size
                        vars rtf children
                    else
                      instantiate_choose (fuel - Prims.int_one) st ctx pos
                        size vars rtf tl)
                 else
                   if ln = "otherwise"
                   then
                     instantiate_seq (fuel - Prims.int_one) st ctx pos size
                       vars rtf children
                   else
                     instantiate_choose (fuel - Prims.int_one) st ctx pos
                       size vars rtf tl)
              else
                instantiate_choose (fuel - Prims.int_one) st ctx pos size
                  vars rtf tl
          | uu___1 ->
              instantiate_choose (fuel - Prims.int_one) st ctx pos size vars
                rtf tl))
and instantiate_copy (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (children : Parser_XML.xml_node Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match ctx with
     | D_Doc (uu___1, uu___2) ->
         instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
           children
     | D_Item (XPath_Eval.CI_Elem (uu___1, anc, n)) ->
         (match n with
          | Parser_XML.XElement (t, uu___2, uu___3) ->
              let body =
                instantiate_seq (fuel - Prims.int_one) st ctx pos size vars
                  rtf children in
              let nsnodes =
                FStar_List_Tot_Base.filter
                  (fun a -> a.Parser_XML.attr_value <> xslt_ns)
                  (inscope_ns [] [] (n :: anc)) in
              [R_Node (build_element t nsnodes body)]
          | uu___2 ->
              instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
                children)
     | D_Item (XPath_Eval.CI_Text (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XText t)]
     | D_Item (XPath_Eval.CI_Comment (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XComment t)]
     | D_Item (XPath_Eval.CI_PI (uu___1, uu___2, uu___3, tg, d)) ->
         [R_Node (Parser_XML.XPI (tg, d))]
     | D_Item (XPath_Eval.CI_Attr (uu___1, uu___2, uu___3, a)) -> [R_Attr a])
and for_each_items (fuel : Prims.nat) (st : xstyle)
  (body : Parser_XML.xml_node Prims.list)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (items : XPath_Eval.xctx_item Prims.list) (pos : Prims.nat)
  (size : Prims.nat) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | it::rest ->
         let here =
           instantiate_seq (fuel - Prims.int_one) st (D_Item it) pos size
             vars rtf body in
         FStar_List_Tot_Base.op_At here
           (for_each_items (fuel - Prims.int_one) st body vars rtf rest
              (pos + Prims.int_one) size))
let rec digits_to_int (cs : FStar_String.char Prims.list) (acc : Prims.int) :
  Prims.int FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      let d = (FStar_Char.int_of_char c) - (Prims.of_int (0x30)) in
      if (d >= Prims.int_zero) && (d <= (Prims.of_int (9)))
      then digits_to_int rest ((acc * (Prims.of_int (10))) + d)
      else FStar_Pervasives_Native.None
let parse_priority (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match chars_of (trim_str s) with
  | [] -> FStar_Pervasives_Native.None
  | 45::rest ->
      (match digits_to_int rest Prims.int_zero with
       | FStar_Pervasives_Native.Some n ->
           FStar_Pervasives_Native.Some
             ((Prims.int_zero - n) * (Prims.of_int (10)))
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | cs ->
      (match digits_to_int cs Prims.int_zero with
       | FStar_Pervasives_Native.Some n ->
           FStar_Pervasives_Native.Some (n * (Prims.of_int (10)))
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec collect_templates (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : template Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, body) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "template")
           then
             let m = attr_or "match" "" attrs in
             let nm = attr_or "name" "" attrs in
             (if (m = "") && (nm = "")
              then collect_templates pfx tl
              else
                (let t =
                   {
                     tpl_match = m;
                     tpl_name = nm;
                     tpl_mode = (attr_or "mode" "" attrs);
                     tpl_prio =
                       (match attr_opt "priority" attrs with
                        | FStar_Pervasives_Native.Some p -> parse_priority p
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None);
                     tpl_body = body
                   } in
                 t :: (collect_templates pfx tl)))
           else collect_templates pfx tl
       | uu___ -> collect_templates pfx tl)
let rec find_output_method (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : Prims.string=
  match children with
  | [] -> "xml"
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "output")
           then attr_or "method" "xml" attrs
           else find_output_method pfx tl
       | uu___ -> find_output_method pfx tl)
let rec build_nsctx (attrs : Parser_XML.xml_attribute Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      (match ns_decl_prefix a.Parser_XML.attr_name with
       | FStar_Pervasives_Native.Some pfx -> (pfx, (a.Parser_XML.attr_value))
           :: (build_nsctx rest)
       | FStar_Pervasives_Native.None -> build_nsctx rest)
let rec collect_globals (pfx : Prims.string)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (children : Parser_XML.xml_node Prims.list) (source : Parser_XML.xml_node)
  (doc_kids : Parser_XML.xml_node Prims.list) :
  (Prims.string * XPath_Eval.xp_value) Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if
             (is_xsl pfx tag) &&
               (let ln = xsl_instr pfx tag in
                (ln = "variable") || (ln = "param"))
           then
             (match ((attr_opt "select" attrs), (attr_opt "name" attrs)) with
              | (FStar_Pervasives_Native.Some sel,
                 FStar_Pervasives_Native.Some nm) ->
                  let v =
                    eval_val_dn (D_Doc (source, doc_kids)) Prims.int_one
                      Prims.int_one [] nsctx sel in
                  (nm, v) :: (collect_globals pfx nsctx tl source doc_kids)
              | (uu___1, uu___2) ->
                  collect_globals pfx nsctx tl source doc_kids)
           else collect_globals pfx nsctx tl source doc_kids
       | uu___ -> collect_globals pfx nsctx tl source doc_kids)
let parse_prefix_list (s : Prims.string) : Prims.string Prims.list=
  FStar_List_Tot_Base.map (fun p -> if p = "#default" then "" else p)
    (FStar_List_Tot_Base.filter (fun p -> p <> "")
       (FStar_List_Tot_Base.map trim_str (split_on_char 32 s)))
let build_nsscope (attrs : Parser_XML.xml_attribute Prims.list) :
  Parser_XML.xml_attribute Prims.list=
  let excluded =
    parse_prefix_list (attr_or "exclude-result-prefixes" "" attrs) in
  FStar_List_Tot_Base.sortWith attr_name_cmp
    (FStar_List_Tot_Base.filter
       (fun a ->
          match ns_decl_prefix a.Parser_XML.attr_name with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some pfx ->
              (a.Parser_XML.attr_value <> xslt_ns) &&
                (Prims.op_Negation (mem_str pfx excluded))) attrs)
let build_style (stylesheet : Parser_XML.xml_node)
  (source : Parser_XML.xml_node) (doc_kids : Parser_XML.xml_node Prims.list)
  : xstyle=
  match stylesheet with
  | Parser_XML.XElement (tag, attrs, children) ->
      let pfx = xsl_prefix_of stylesheet in
      if
        (is_xsl pfx tag) &&
          (let ln = xsl_instr pfx tag in
           (ln = "stylesheet") || (ln = "transform"))
      then
        let nsctx = build_nsctx attrs in
        {
          xs_pfx = pfx;
          xs_templates = (collect_templates pfx children);
          xs_method = (find_output_method pfx children);
          xs_globals = (collect_globals pfx nsctx children source doc_kids);
          xs_nsscope = (build_nsscope attrs);
          xs_nsctx = nsctx
        }
      else
        {
          xs_pfx = pfx;
          xs_templates =
            [{
               tpl_match = "/";
               tpl_name = "";
               tpl_mode = "";
               tpl_prio = FStar_Pervasives_Native.None;
               tpl_body = [stylesheet]
             }];
          xs_method = "xml";
          xs_globals = [];
          xs_nsscope = [];
          xs_nsctx = (build_nsctx attrs)
        }
  | uu___ ->
      {
        xs_pfx = "xsl";
        xs_templates = [];
        xs_method = "xml";
        xs_globals = [];
        xs_nsscope = [];
        xs_nsctx = []
      }
let rec doc_root_elem (doc_kids : Parser_XML.xml_node Prims.list) :
  Parser_XML.xml_node FStar_Pervasives_Native.option=
  match doc_kids with
  | [] -> FStar_Pervasives_Native.None
  | (Parser_XML.XElement (t, a, c))::uu___ ->
      FStar_Pervasives_Native.Some (Parser_XML.XElement (t, a, c))
  | uu___::tl -> doc_root_elem tl
let rec xml_nodes_count_sum (ns : Parser_XML.xml_node Prims.list) :
  Prims.nat=
  match ns with
  | [] -> Prims.int_zero
  | hd::tl -> (XPath_Eval.xml_node_count hd) + (xml_nodes_count_sum tl)
let transform (stylesheet : Parser_XML.xml_node)
  (source : Parser_XML.xml_node) : Prims.string=
  let st = build_style stylesheet source [source] in
  let sz =
    (XPath_Eval.xml_node_count stylesheet) +
      (XPath_Eval.xml_node_count source) in
  let fuel =
    ((sz + Prims.int_one) * (Prims.of_int (256))) +
      (Prims.parse_int "100000") in
  let result =
    dispatch fuel st (D_Doc (source, [source])) Prims.int_one Prims.int_one
      "" in
  let nodes = only_nodes result in
  if st.xs_method = "text"
  then text_value_nodes nodes
  else serialize_nodes [] nodes
let transform_doc (stylesheet : Parser_XML.xml_node)
  (source_kids : Parser_XML.xml_node Prims.list) : Prims.string=
  match doc_root_elem source_kids with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some root ->
      let st = build_style stylesheet root source_kids in
      let sz =
        (XPath_Eval.xml_node_count stylesheet) +
          (xml_nodes_count_sum source_kids) in
      let fuel =
        ((sz + Prims.int_one) * (Prims.of_int (256))) +
          (Prims.parse_int "100000") in
      let result =
        dispatch fuel st (D_Doc (root, source_kids)) Prims.int_one
          Prims.int_one "" in
      let nodes = only_nodes result in
      if st.xs_method = "text"
      then text_value_nodes nodes
      else serialize_nodes [] nodes
