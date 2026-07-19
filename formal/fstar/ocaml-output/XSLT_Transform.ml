open Prims
let soc (c : FStar_String.char) : Prims.string=
  FStar_String.string_of_list [c]
let chars_of (s : Prims.string) : FStar_String.char Prims.list=
  FStar_String.list_of_string s
let str_of_chars (cs : FStar_String.char Prims.list) : Prims.string=
  FStar_String.string_of_list cs
let ascii_lower_char (c : FStar_String.char) : FStar_String.char=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (0x41))) && (n <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (n + (Prims.of_int (0x20)))
  else c
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
let rec attrs_upsert (acc : Parser_XML.xml_attribute Prims.list)
  (a : Parser_XML.xml_attribute) : Parser_XML.xml_attribute Prims.list=
  match acc with
  | [] -> [a]
  | hd::tl ->
      if hd.Parser_XML.attr_name = a.Parser_XML.attr_name
      then a :: tl
      else hd :: (attrs_upsert tl a)
let rec merge_attrs_override (base : Parser_XML.xml_attribute Prims.list)
  (overrides : Parser_XML.xml_attribute Prims.list) :
  Parser_XML.xml_attribute Prims.list=
  match overrides with
  | [] -> base
  | hd::tl -> merge_attrs_override (attrs_upsert base hd) tl
let only_attrs (rs : rnode Prims.list) : Parser_XML.xml_attribute Prims.list=
  let uu___ = split_rnodes rs [] [] in
  match uu___ with | (attrs, uu___1) -> attrs
let build_element (tag : Prims.string)
  (extra_attrs : Parser_XML.xml_attribute Prims.list)
  (body : rnode Prims.list) : Parser_XML.xml_node=
  let uu___ = split_rnodes body [] [] in
  match uu___ with
  | (attrs, nodes) ->
      Parser_XML.XElement
        (tag, (merge_attrs_override extra_attrs attrs), nodes)
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
  | XPath_Eval.CI_Namespace (uu___, uu___1, uu___2, pfx, uri) ->
      R_Attr
        {
          Parser_XML.attr_name =
            (if pfx = "" then "xmlns" else Prims.strcat "xmlns:" pfx);
          Parser_XML.attr_value = uri
        }
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
  tpl_body: Parser_XML.xml_node Prims.list ;
  tpl_import_prec: Prims.int }
let __proj__Mktemplate__item__tpl_match (projectee : template) :
  Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_match
let __proj__Mktemplate__item__tpl_name (projectee : template) : Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_name
let __proj__Mktemplate__item__tpl_mode (projectee : template) : Prims.string=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_mode
let __proj__Mktemplate__item__tpl_prio (projectee : template) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_prio
let __proj__Mktemplate__item__tpl_body (projectee : template) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_body
let __proj__Mktemplate__item__tpl_import_prec (projectee : template) :
  Prims.int=
  match projectee with
  | { tpl_match; tpl_name; tpl_mode; tpl_prio; tpl_body; tpl_import_prec;_}
      -> tpl_import_prec
type attrset_entry =
  {
  ase_name: Prims.string ;
  ase_deps: Prims.string Prims.list ;
  ase_own: Parser_XML.xml_node Prims.list }
let __proj__Mkattrset_entry__item__ase_name (projectee : attrset_entry) :
  Prims.string=
  match projectee with | { ase_name; ase_deps; ase_own;_} -> ase_name
let __proj__Mkattrset_entry__item__ase_deps (projectee : attrset_entry) :
  Prims.string Prims.list=
  match projectee with | { ase_name; ase_deps; ase_own;_} -> ase_deps
let __proj__Mkattrset_entry__item__ase_own (projectee : attrset_entry) :
  Parser_XML.xml_node Prims.list=
  match projectee with | { ase_name; ase_deps; ase_own;_} -> ase_own
let rec find_attrset_entry (entries : attrset_entry Prims.list)
  (nm : Prims.string) : attrset_entry FStar_Pervasives_Native.option=
  match entries with
  | [] -> FStar_Pervasives_Native.None
  | e::rest ->
      if e.ase_name = nm
      then FStar_Pervasives_Native.Some e
      else find_attrset_entry rest nm
let parse_qname_list (s : Prims.string) : Prims.string Prims.list=
  FStar_List_Tot_Base.filter (fun p -> p <> "")
    (FStar_List_Tot_Base.map trim_str (split_on_char 32 s))
type output_settings =
  {
  os_method_raw: Prims.string ;
  os_omit_decl: Prims.bool ;
  os_standalone: Prims.string ;
  os_indent_raw: Prims.string ;
  os_encoding: Prims.string ;
  os_version: Prims.string ;
  os_doctype_public: Prims.string ;
  os_doctype_system: Prims.string ;
  os_cdata:
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list }
let __proj__Mkoutput_settings__item__os_method_raw
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_method_raw
let __proj__Mkoutput_settings__item__os_omit_decl
  (projectee : output_settings) : Prims.bool=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_omit_decl
let __proj__Mkoutput_settings__item__os_standalone
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_standalone
let __proj__Mkoutput_settings__item__os_indent_raw
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_indent_raw
let __proj__Mkoutput_settings__item__os_encoding
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_encoding
let __proj__Mkoutput_settings__item__os_version (projectee : output_settings)
  : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_version
let __proj__Mkoutput_settings__item__os_doctype_public
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_doctype_public
let __proj__Mkoutput_settings__item__os_doctype_system
  (projectee : output_settings) : Prims.string=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_doctype_system
let __proj__Mkoutput_settings__item__os_cdata (projectee : output_settings) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list=
  match projectee with
  | { os_method_raw; os_omit_decl; os_standalone; os_indent_raw; os_encoding;
      os_version; os_doctype_public; os_doctype_system; os_cdata;_} ->
      os_cdata
let default_output_settings : output_settings=
  {
    os_method_raw = "";
    os_omit_decl = false;
    os_standalone = "";
    os_indent_raw = "";
    os_encoding = "UTF-8";
    os_version = "1.0";
    os_doctype_public = "";
    os_doctype_system = "";
    os_cdata = []
  }
type xstyle =
  {
  xs_pfx: Prims.string ;
  xs_templates: template Prims.list ;
  xs_attrsets: attrset_entry Prims.list ;
  xs_method: Prims.string ;
  xs_output_present: Prims.bool ;
  xs_output: output_settings ;
  xs_globals: (Prims.string * XPath_Eval.xp_value) Prims.list ;
  xs_nsscope: Parser_XML.xml_attribute Prims.list ;
  xs_nsctx: (Prims.string * Prims.string) Prims.list ;
  xs_id_attrs: (Prims.string * Prims.string) Prims.list ;
  xs_style_root: Parser_XML.xml_node ;
  xs_decfmts: XPath_Eval.decimal_format_symbols Prims.list ;
  xs_key_table: XPath_Eval.key_entry Prims.list }
let __proj__Mkxstyle__item__xs_pfx (projectee : xstyle) : Prims.string=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_pfx
let __proj__Mkxstyle__item__xs_templates (projectee : xstyle) :
  template Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_templates
let __proj__Mkxstyle__item__xs_attrsets (projectee : xstyle) :
  attrset_entry Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_attrsets
let __proj__Mkxstyle__item__xs_method (projectee : xstyle) : Prims.string=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_method
let __proj__Mkxstyle__item__xs_output_present (projectee : xstyle) :
  Prims.bool=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_output_present
let __proj__Mkxstyle__item__xs_output (projectee : xstyle) : output_settings=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_output
let __proj__Mkxstyle__item__xs_globals (projectee : xstyle) :
  (Prims.string * XPath_Eval.xp_value) Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_globals
let __proj__Mkxstyle__item__xs_nsscope (projectee : xstyle) :
  Parser_XML.xml_attribute Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_nsscope
let __proj__Mkxstyle__item__xs_nsctx (projectee : xstyle) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_nsctx
let __proj__Mkxstyle__item__xs_id_attrs (projectee : xstyle) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_id_attrs
let __proj__Mkxstyle__item__xs_style_root (projectee : xstyle) :
  Parser_XML.xml_node=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_style_root
let __proj__Mkxstyle__item__xs_decfmts (projectee : xstyle) :
  XPath_Eval.decimal_format_symbols Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_decfmts
let __proj__Mkxstyle__item__xs_key_table (projectee : xstyle) :
  XPath_Eval.key_entry Prims.list=
  match projectee with
  | { xs_pfx; xs_templates; xs_attrsets; xs_method; xs_output_present;
      xs_output; xs_globals; xs_nsscope; xs_nsctx; xs_id_attrs;
      xs_style_root; xs_decfmts; xs_key_table;_} -> xs_key_table
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
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  XPath_Eval.xp_value=
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
          XPath_Eval.env_doc_kids = [];
          XPath_Eval.env_id_attrs = id_attrs;
          XPath_Eval.env_style_root = style_root;
          XPath_Eval.env_decimal_formats = decfmts;
          XPath_Eval.env_key_table = key_table
        } in
      XPath_Eval.eval_expr fuel env e
let eval_string (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (expr_text : Prims.string) : Prims.string=
  XPath_Eval.to_string_val
    (eval_val ctx pos size vars nsctx [] XPath_Eval.xnode_none [] []
       expr_text)
let eval_string_kv (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  Prims.string=
  XPath_Eval.to_string_val
    (eval_val ctx pos size vars nsctx id_attrs style_root decfmts key_table
       expr_text)
let eval_bool (ctx : XPath_Eval.xctx_item) (pos : Prims.nat)
  (size : Prims.nat) (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  Prims.bool=
  match eval_val ctx pos size vars nsctx id_attrs style_root decfmts
          key_table expr_text
  with
  | XPath_Eval.XV_Num n ->
      (match XPath_Eval.xn_finite_int (XPath_Eval.xn_round n) with
       | FStar_Pervasives_Native.Some k -> k = pos
       | FStar_Pervasives_Native.None -> false)
  | v -> XPath_Eval.to_bool_val v
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
  match eval_val ctx pos size vars nsctx [] XPath_Eval.xnode_none [] []
          (drop_pi_alts sel)
  with
  | XPath_Eval.XV_Nodes items -> items
  | uu___ -> []
let rec force_abs (e : Parser_XPath.xp_expr) : Parser_XPath.xp_expr=
  match e with
  | Parser_XPath.XE_Path (false, steps) -> Parser_XPath.XE_Path (true, steps)
  | Parser_XPath.XE_Path (true, steps) -> Parser_XPath.XE_Path (true, steps)
  | Parser_XPath.XE_FilterPath (primary, preds, steps) ->
      Parser_XPath.XE_FilterPath ((force_abs primary), preds, steps)
  | Parser_XPath.XE_Union (a, b) ->
      Parser_XPath.XE_Union ((force_abs a), (force_abs b))
  | Parser_XPath.XE_Or (a, b) ->
      Parser_XPath.XE_Or ((force_abs a), (force_abs b))
  | Parser_XPath.XE_And (a, b) ->
      Parser_XPath.XE_And ((force_abs a), (force_abs b))
  | Parser_XPath.XE_Compare (op, a, b) ->
      Parser_XPath.XE_Compare (op, (force_abs a), (force_abs b))
  | Parser_XPath.XE_Arith (op, a, b) ->
      Parser_XPath.XE_Arith (op, (force_abs a), (force_abs b))
  | Parser_XPath.XE_Neg a -> Parser_XPath.XE_Neg (force_abs a)
  | Parser_XPath.XE_FunCall (name, args) ->
      Parser_XPath.XE_FunCall (name, (force_abs_list args))
  | uu___ -> e
and force_abs_list (es : Parser_XPath.xp_expr Prims.list) :
  Parser_XPath.xp_expr Prims.list=
  match es with | [] -> [] | h::t -> (force_abs h) :: (force_abs_list t)
let eval_val_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  XPath_Eval.xp_value=
  match ctx with
  | D_Item it ->
      eval_val it pos size vars nsctx id_attrs style_root decfmts key_table
        expr_text
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
               XPath_Eval.env_doc_kids = doc_kids;
               XPath_Eval.env_id_attrs = id_attrs;
               XPath_Eval.env_style_root = style_root;
               XPath_Eval.env_decimal_formats = decfmts;
               XPath_Eval.env_key_table = key_table
             } in
           XPath_Eval.eval_expr fuel env e2)
let eval_string_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  Prims.string=
  XPath_Eval.to_string_val
    (eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts
       key_table expr_text)
let eval_bool_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (expr_text : Prims.string) :
  Prims.bool=
  XPath_Eval.to_bool_val
    (eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts
       key_table expr_text)
let eval_nodeset_dn (ctx : dnode) (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (sel : Prims.string) :
  XPath_Eval.xctx_item Prims.list=
  match eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts
          key_table (drop_pi_alts sel)
  with
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
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (sel : Prims.string) :
  XPath_Eval.xctx_item Prims.list=
  if is_simple_child_union sel
  then select_child_union nsctx ctx (split_on_char 124 sel)
  else
    eval_nodeset_dn ctx pos size vars nsctx id_attrs style_root decfmts
      key_table sel
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
let match_expr_pattern
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (pat : Prims.string)
  (it : XPath_Eval.xctx_item) : Prims.bool=
  match Parser_XPath.parse_xpath pat with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some e ->
      let root = XPath_Eval.root_of_item it in
      let fuel =
        XPath_Eval.initial_eval_fuel e (XPath_Eval.xml_node_count root) in
      let env =
        {
          XPath_Eval.env_item = (XPath_Eval.CI_Elem ([], [], root));
          XPath_Eval.env_pos = Prims.int_one;
          XPath_Eval.env_size = Prims.int_one;
          XPath_Eval.env_vars = vars;
          XPath_Eval.env_nsctx = nsctx;
          XPath_Eval.env_doc_kids = [];
          XPath_Eval.env_id_attrs = id_attrs;
          XPath_Eval.env_style_root = style_root;
          XPath_Eval.env_decimal_formats = decfmts;
          XPath_Eval.env_key_table = key_table
        } in
      let same_node s =
        match (s, it) with
        | (XPath_Eval.CI_Elem (uu___, sanc, sn), XPath_Eval.CI_Elem
           (uu___1, ianc, inode)) -> (sn = inode) && (sanc = ianc)
        | (uu___, uu___1) ->
            (XPath_Eval.item_path s) = (XPath_Eval.item_path it) in
      (match XPath_Eval.eval_expr fuel env e with
       | XPath_Eval.XV_Nodes items ->
           FStar_List_Tot_Base.existsb same_node items
       | uu___ -> false)
let is_idkey_pattern (alt : Prims.string) : Prims.bool=
  let a = trim_str alt in (starts_with "id(" a) || (starts_with "key(" a)
let alt_matches (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (alt : Prims.string)
  (nd : dnode) : Prims.bool=
  if is_idkey_pattern alt
  then
    match nd with
    | D_Item it ->
        match_expr_pattern vars nsctx id_attrs style_root decfmts key_table
          (trim_str alt) it
    | uu___ -> false
  else
    (let uu___1 = split_predicate alt in
     match uu___1 with
     | (namepart, predopt) ->
         (match predopt with
          | FStar_Pervasives_Native.None -> alt_matches_core nsctx alt nd
          | FStar_Pervasives_Native.Some pred ->
              if Prims.op_Negation (alt_matches_core nsctx namepart nd)
              then false
              else
                (match nd with
                 | D_Doc (uu___3, uu___4) ->
                     eval_bool (dnode_ci nd) Prims.int_one Prims.int_one vars
                       nsctx id_attrs style_root decfmts key_table pred
                 | D_Item it ->
                     let uu___3 = match_proximity nsctx namepart it in
                     (match uu___3 with
                      | (p, s) ->
                          eval_bool it p s vars nsctx id_attrs style_root
                            decfmts key_table pred))))
let rec any_alt_matches
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list)
  (alts : Prims.string Prims.list) (nd : dnode) : Prims.bool=
  match alts with
  | [] -> false
  | a::rest ->
      if alt_matches vars nsctx id_attrs style_root decfmts key_table a nd
      then true
      else
        any_alt_matches vars nsctx id_attrs style_root decfmts key_table rest
          nd
let template_matches (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (tpl : template) (nd : dnode)
  : Prims.bool=
  if tpl.tpl_match = ""
  then false
  else
    any_alt_matches vars nsctx id_attrs style_root decfmts key_table
      (split_on_char 124 tpl.tpl_match) nd
let rec parse_nat_chars (cs : FStar_String.char Prims.list) (acc : Prims.nat)
  : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      let d = (FStar_Char.int_of_char c) - (Prims.of_int (0x30)) in
      if (d >= Prims.int_zero) && (d <= (Prims.of_int (9)))
      then parse_nat_chars rest ((acc * (Prims.of_int (10))) + d)
      else FStar_Pervasives_Native.None
let default_count_pattern (it : XPath_Eval.xctx_item) : Prims.string=
  match it with
  | XPath_Eval.CI_Elem (uu___, uu___1, n) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> "*")
  | XPath_Eval.CI_Text (uu___, uu___1, uu___2, uu___3) -> "text()"
  | XPath_Eval.CI_Comment (uu___, uu___1, uu___2, uu___3) -> "comment()"
  | XPath_Eval.CI_PI (uu___, uu___1, uu___2, uu___3, uu___4) ->
      "processing-instruction()"
  | XPath_Eval.CI_Attr (uu___, uu___1, uu___2, a) ->
      Prims.strcat "@" a.Parser_XML.attr_name
  | XPath_Eval.CI_Namespace (uu___, uu___1, uu___2, uu___3, uu___4) -> "*"
let count_matches (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (pat : Prims.string)
  (node : XPath_Eval.xctx_item) : Prims.bool=
  any_alt_matches vars nsctx id_attrs style_root decfmts key_table
    (split_on_char 124 pat) (D_Item node)
let count_with_preceding
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (node : XPath_Eval.xctx_item) : Prims.nat=
  Prims.int_one +
    (FStar_List_Tot_Base.length
       (FStar_List_Tot_Base.filter
          (count_matches vars nsctx id_attrs style_root decfmts key_table
             count_pat) (XPath_Eval.preceding_sibling_axis node)))
let rec find_level_single
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (chain : XPath_Eval.xctx_item Prims.list) :
  XPath_Eval.xctx_item FStar_Pervasives_Native.option=
  match chain with
  | [] -> FStar_Pervasives_Native.None
  | node::rest ->
      if
        count_matches vars nsctx id_attrs style_root decfmts key_table
          count_pat node
      then FStar_Pervasives_Native.Some node
      else
        if
          (from_pat <> "") &&
            (count_matches vars nsctx id_attrs style_root decfmts key_table
               from_pat node)
        then FStar_Pervasives_Native.None
        else
          find_level_single vars nsctx id_attrs style_root decfmts key_table
            count_pat from_pat rest
let level_single_numbers
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (self : XPath_Eval.xctx_item) :
  Prims.nat Prims.list=
  let chain = self :: (XPath_Eval.ancestor_axis self) in
  match find_level_single vars nsctx id_attrs style_root decfmts key_table
          count_pat from_pat chain
  with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some c ->
      [count_with_preceding vars nsctx id_attrs style_root decfmts key_table
         count_pat c]
let rec multiple_numbers
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (chain : XPath_Eval.xctx_item Prims.list) :
  Prims.nat Prims.list=
  match chain with
  | [] -> []
  | node::rest ->
      if
        (from_pat <> "") &&
          (count_matches vars nsctx id_attrs style_root decfmts key_table
             from_pat node)
      then []
      else
        (let tail =
           multiple_numbers vars nsctx id_attrs style_root decfmts key_table
             count_pat from_pat rest in
         if
           count_matches vars nsctx id_attrs style_root decfmts key_table
             count_pat node
         then
           FStar_List_Tot_Base.op_At tail
             [count_with_preceding vars nsctx id_attrs style_root decfmts
                key_table count_pat node]
         else tail)
let level_multiple_numbers
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (self : XPath_Eval.xctx_item) :
  Prims.nat Prims.list=
  multiple_numbers vars nsctx id_attrs style_root decfmts key_table count_pat
    from_pat (self :: (XPath_Eval.ancestor_axis self))
let rec merge_desc_items (xs : XPath_Eval.xctx_item Prims.list)
  (ys : XPath_Eval.xctx_item Prims.list) : XPath_Eval.xctx_item Prims.list=
  match (xs, ys) with
  | ([], uu___) -> ys
  | (uu___, []) -> xs
  | (x::xs', y::ys') ->
      if
        (XPath_Eval.path_compare (XPath_Eval.item_path x)
           (XPath_Eval.item_path y))
          >= Prims.int_zero
      then x :: (merge_desc_items xs' ys)
      else y :: (merge_desc_items xs ys')
let rec scan_any_from_reset
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (nodes : XPath_Eval.xctx_item Prims.list) :
  Prims.nat=
  match nodes with
  | [] -> Prims.int_zero
  | n::rest ->
      if
        (from_pat <> "") &&
          (count_matches vars nsctx id_attrs style_root decfmts key_table
             from_pat n)
      then Prims.int_zero
      else
        (let here =
           if
             count_matches vars nsctx id_attrs style_root decfmts key_table
               count_pat n
           then Prims.int_one
           else Prims.int_zero in
         here +
           (scan_any_from_reset vars nsctx id_attrs style_root decfmts
              key_table count_pat from_pat rest))
let level_any_numbers
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (count_pat : Prims.string)
  (from_pat : Prims.string) (self : XPath_Eval.xctx_item) :
  Prims.nat Prims.list=
  let neighborhood =
    merge_desc_items (XPath_Eval.ancestor_axis self)
      (XPath_Eval.preceding_axis self) in
  [scan_any_from_reset vars nsctx id_attrs style_root decfmts key_table
     count_pat from_pat (self :: neighborhood)]
let level_numbers (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (level : Prims.string)
  (count_raw : Prims.string) (from_pat : Prims.string)
  (self : XPath_Eval.xctx_item) : Prims.nat Prims.list=
  let count_pat =
    if count_raw = "" then default_count_pattern self else count_raw in
  if level = "multiple"
  then
    level_multiple_numbers vars nsctx id_attrs style_root decfmts key_table
      count_pat from_pat self
  else
    if level = "any"
    then
      level_any_numbers vars nsctx id_attrs style_root decfmts key_table
        count_pat from_pat self
    else
      level_single_numbers vars nsctx id_attrs style_root decfmts key_table
        count_pat from_pat self
let alpha_digit_char (upper : Prims.bool) (d : Prims.nat) :
  FStar_String.char=
  let base = if upper then (Prims.of_int (0x41)) else (Prims.of_int (0x61)) in
  FStar_Char.char_of_int
    (base + (if d < (Prims.of_int (26)) then d else (Prims.of_int (25))))
let rec alpha_digits (upper : Prims.bool) (n : Prims.nat) (fuel : Prims.nat)
  : FStar_String.char Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    if n = Prims.int_zero
    then []
    else
      (let n0 = n - Prims.int_one in
       let d = (mod) n0 (Prims.of_int (26)) in
       let rest = n0 / (Prims.of_int (26)) in
       FStar_List_Tot_Base.op_At
         (alpha_digits upper rest (fuel - Prims.int_one))
         [alpha_digit_char upper d])
let render_alpha (upper : Prims.bool) (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "0"
  else str_of_chars (alpha_digits upper n (n + Prims.int_one))
let roman_table : (Prims.nat * Prims.string) Prims.list=
  [((Prims.of_int (1000)), "M");
  ((Prims.of_int (900)), "CM");
  ((Prims.of_int (500)), "D");
  ((Prims.of_int (400)), "CD");
  ((Prims.of_int (100)), "C");
  ((Prims.of_int (90)), "XC");
  ((Prims.of_int (50)), "L");
  ((Prims.of_int (40)), "XL");
  ((Prims.of_int (10)), "X");
  ((Prims.of_int (9)), "IX");
  ((Prims.of_int (5)), "V");
  ((Prims.of_int (4)), "IV");
  (Prims.int_one, "I")]
let rec roman_pick (n : Prims.nat)
  (table : (Prims.nat * Prims.string) Prims.list) :
  (Prims.nat * Prims.string) FStar_Pervasives_Native.option=
  match table with
  | [] -> FStar_Pervasives_Native.None
  | (v, s)::rest ->
      if (v > Prims.int_zero) && (v <= n)
      then FStar_Pervasives_Native.Some (v, s)
      else roman_pick n rest
let rec roman_digits_fuel (n : Prims.nat) (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    if n = Prims.int_zero
    then ""
    else
      (match roman_pick n roman_table with
       | FStar_Pervasives_Native.None -> ""
       | FStar_Pervasives_Native.Some (v, s) ->
           Prims.strcat s
             (roman_digits_fuel (if n >= v then n - v else Prims.int_zero)
                (fuel - Prims.int_one)))
let roman_digits (n : Prims.nat) : Prims.string=
  roman_digits_fuel n (n + Prims.int_one)
let rec nat_to_digits (n : Prims.nat) (fuel : Prims.nat) :
  FStar_String.char Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    if n = Prims.int_zero
    then []
    else
      (let d = (mod) n (Prims.of_int (10)) in
       let rest = n / (Prims.of_int (10)) in
       FStar_List_Tot_Base.op_At (nat_to_digits rest (fuel - Prims.int_one))
         [FStar_Char.char_of_int ((Prims.of_int (0x30)) + d)])
let digits_of_nat (n : Prims.nat) : FStar_String.char Prims.list=
  if n = Prims.int_zero then [48] else nat_to_digits n (n + Prims.int_one)
let rec replicate_char (c : FStar_String.char) (k : Prims.nat) :
  FStar_String.char Prims.list=
  if k = Prims.int_zero
  then []
  else c :: (replicate_char c (k - Prims.int_one))
let pad_left_zeros (cs : FStar_String.char Prims.list) (want : Prims.nat) :
  FStar_String.char Prims.list=
  let len = FStar_List_Tot_Base.length cs in
  if want <= len
  then cs
  else FStar_List_Tot_Base.op_At (replicate_char 48 (want - len)) cs
let rec group_rev (rev_ds : FStar_String.char Prims.list)
  (sep_rev : FStar_String.char Prims.list) (gsize : Prims.nat)
  (i : Prims.nat) : FStar_String.char Prims.list=
  match rev_ds with
  | [] -> []
  | c::rest ->
      let tail = group_rev rest sep_rev gsize (i + Prims.int_one) in
      if
        ((gsize > Prims.int_zero) &&
           (((mod) (i + Prims.int_one) gsize) = Prims.int_zero))
          && (Prims.uu___is_Cons rest)
      then c :: (FStar_List_Tot_Base.op_At sep_rev tail)
      else c :: tail
let apply_grouping (digits : FStar_String.char Prims.list)
  (gsep : Prims.string) (gsize : Prims.nat) : FStar_String.char Prims.list=
  if (gsep = "") || (gsize = Prims.int_zero)
  then digits
  else
    FStar_List_Tot_Base.rev
      (group_rev (FStar_List_Tot_Base.rev digits)
         (FStar_List_Tot_Base.rev (chars_of gsep)) gsize Prims.int_zero)
type numfmt_style =
  | NF_Decimal of Prims.nat 
  | NF_UpperAlpha 
  | NF_LowerAlpha 
  | NF_UpperRoman 
  | NF_LowerRoman 
let uu___is_NF_Decimal (projectee : numfmt_style) : Prims.bool=
  match projectee with | NF_Decimal _0 -> true | uu___ -> false
let __proj__NF_Decimal__item___0 (projectee : numfmt_style) : Prims.nat=
  match projectee with | NF_Decimal _0 -> _0
let uu___is_NF_UpperAlpha (projectee : numfmt_style) : Prims.bool=
  match projectee with | NF_UpperAlpha -> true | uu___ -> false
let uu___is_NF_LowerAlpha (projectee : numfmt_style) : Prims.bool=
  match projectee with | NF_LowerAlpha -> true | uu___ -> false
let uu___is_NF_UpperRoman (projectee : numfmt_style) : Prims.bool=
  match projectee with | NF_UpperRoman -> true | uu___ -> false
let uu___is_NF_LowerRoman (projectee : numfmt_style) : Prims.bool=
  match projectee with | NF_LowerRoman -> true | uu___ -> false
let render_num_styled (n : Prims.nat) (style : numfmt_style)
  (gsep : Prims.string) (gsize : Prims.nat) : Prims.string=
  match style with
  | NF_Decimal minw ->
      str_of_chars
        (apply_grouping (pad_left_zeros (digits_of_nat n) minw) gsep gsize)
  | NF_UpperAlpha -> render_alpha true n
  | NF_LowerAlpha -> render_alpha false n
  | NF_UpperRoman -> roman_digits n
  | NF_LowerRoman ->
      str_of_chars
        (FStar_List_Tot_Base.map ascii_lower_char (chars_of (roman_digits n)))
let is_alnum_fmt_char (c : FStar_String.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
      ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))))
     || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
    || (code >= (Prims.of_int (0x80)))
let rec run_alnum (cs : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)=
  match cs with
  | c::rest ->
      if is_alnum_fmt_char c
      then run_alnum rest (c :: acc)
      else ((FStar_List_Tot_Base.rev acc), cs)
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
let rec run_sep (cs : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)=
  match cs with
  | c::rest ->
      if Prims.op_Negation (is_alnum_fmt_char c)
      then run_sep rest (c :: acc)
      else ((FStar_List_Tot_Base.rev acc), cs)
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
type frun =
  | FR_Alnum of FStar_String.char Prims.list 
  | FR_Sep of FStar_String.char Prims.list 
let uu___is_FR_Alnum (projectee : frun) : Prims.bool=
  match projectee with | FR_Alnum _0 -> true | uu___ -> false
let __proj__FR_Alnum__item___0 (projectee : frun) :
  FStar_String.char Prims.list= match projectee with | FR_Alnum _0 -> _0
let uu___is_FR_Sep (projectee : frun) : Prims.bool=
  match projectee with | FR_Sep _0 -> true | uu___ -> false
let __proj__FR_Sep__item___0 (projectee : frun) :
  FStar_String.char Prims.list= match projectee with | FR_Sep _0 -> _0
let rec tokenize_runs (cs : FStar_String.char Prims.list) (fuel : Prims.nat)
  : frun Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::uu___1 ->
         if is_alnum_fmt_char c
         then
           let uu___2 = run_alnum cs [] in
           (match uu___2 with
            | (run, rest) -> (FR_Alnum run) ::
                (tokenize_runs rest (fuel - Prims.int_one)))
         else
           (let uu___3 = run_sep cs [] in
            match uu___3 with
            | (run, rest) -> (FR_Sep run) ::
                (tokenize_runs rest (fuel - Prims.int_one))))
let classify_token (t : FStar_String.char Prims.list) : numfmt_style=
  match t with
  | [] -> NF_Decimal Prims.int_one
  | c::uu___ ->
      if c = 65
      then NF_UpperAlpha
      else
        if c = 97
        then NF_LowerAlpha
        else
          if c = 73
          then NF_UpperRoman
          else
            if c = 105
            then NF_LowerRoman
            else NF_Decimal (FStar_List_Tot_Base.length t)
let rec split_tokens (rest : frun Prims.list) :
  (numfmt_style Prims.list * Prims.string Prims.list * Prims.string)=
  match rest with
  | [] -> ([], [], "")
  | (FR_Alnum t)::[] -> ([classify_token t], [], "")
  | (FR_Alnum t)::(FR_Sep s)::[] ->
      ([classify_token t], [], (str_of_chars s))
  | (FR_Alnum t)::(FR_Sep s)::more ->
      let uu___ = split_tokens more in
      (match uu___ with
       | (toks, seps, suf) ->
           (((classify_token t) :: toks), ((str_of_chars s) :: seps), suf))
  | (FR_Alnum t)::more ->
      let uu___ = split_tokens more in
      (match uu___ with
       | (toks, seps, suf) -> (((classify_token t) :: toks), seps, suf))
  | (FR_Sep uu___)::more -> split_tokens more
let parsed_format (fmt : Prims.string) :
  (Prims.string * numfmt_style Prims.list * Prims.string Prims.list *
    Prims.string)=
  let cs = chars_of fmt in
  match tokenize_runs cs ((FStar_List_Tot_Base.length cs) + Prims.int_one)
  with
  | [] -> ("", [NF_Decimal Prims.int_one], [], "")
  | (FR_Sep s)::rest ->
      let uu___ = split_tokens rest in
      (match uu___ with
       | (toks, seps, suf) ->
           (match toks with
            | [] -> ((str_of_chars s), [NF_Decimal Prims.int_one], [], "")
            | uu___1 -> ((str_of_chars s), toks, seps, suf)))
  | runs ->
      let uu___ = split_tokens runs in
      (match uu___ with | (toks, seps, suf) -> ("", toks, seps, suf))
let rec pick_style (toks : numfmt_style Prims.list) (i : Prims.nat) :
  numfmt_style=
  match toks with
  | [] -> NF_Decimal Prims.int_one
  | t::[] -> t
  | t::rest ->
      if i = Prims.int_zero then t else pick_style rest (i - Prims.int_one)
let rec pick_sep (seps : Prims.string Prims.list) (i : Prims.nat) :
  Prims.string=
  match seps with
  | [] -> "."
  | s::[] -> s
  | s::rest ->
      if i = Prims.int_zero then s else pick_sep rest (i - Prims.int_one)
let rec render_numbered (ns : Prims.nat Prims.list)
  (toks : numfmt_style Prims.list) (seps : Prims.string Prims.list)
  (suffix : Prims.string) (gsep : Prims.string) (gsize : Prims.nat)
  (i : Prims.nat) : Prims.string=
  match ns with
  | [] -> ""
  | n::[] ->
      Prims.strcat (render_num_styled n (pick_style toks i) gsep gsize)
        suffix
  | n::rest ->
      Prims.strcat
        (Prims.strcat (render_num_styled n (pick_style toks i) gsep gsize)
           (pick_sep seps i))
        (render_numbered rest toks seps suffix gsep gsize (i + Prims.int_one))
let render_number_list (numbers : Prims.nat Prims.list) (fmt : Prims.string)
  (gsep : Prims.string) (gsize_s : Prims.string) : Prims.string=
  let uu___ = parsed_format fmt in
  match uu___ with
  | (lead, toks, seps, suffix) ->
      (match numbers with
       | [] -> ""
       | uu___1 ->
           let gsize =
             match parse_nat_chars (chars_of (trim_str gsize_s))
                     Prims.int_zero
             with
             | FStar_Pervasives_Native.Some n -> n
             | FStar_Pervasives_Native.None -> Prims.int_zero in
           Prims.strcat lead
             (render_numbered numbers toks seps suffix gsep gsize
                Prims.int_zero))
let value_bypass (n : XPath_Eval.xpath_number) :
  Prims.string FStar_Pervasives_Native.option=
  match XPath_Eval.xn_round n with
  | XPath_Eval.XN_Finite (v, uu___) when uu___ = Prims.int_zero ->
      if v < Prims.int_one
      then FStar_Pervasives_Native.Some (Prims.string_of_int v)
      else FStar_Pervasives_Native.None
  | XPath_Eval.XN_Finite (uu___, uu___1) -> FStar_Pervasives_Native.None
  | other -> FStar_Pervasives_Native.Some (XPath_Eval.xn_to_string other)
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
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (mode : Prims.string)
  (tpls : template Prims.list) (nd : dnode)
  (best : template FStar_Pervasives_Native.option) :
  template FStar_Pervasives_Native.option=
  match tpls with
  | [] -> best
  | t::rest ->
      let best' =
        if
          (t.tpl_mode = mode) &&
            (template_matches vars nsctx id_attrs style_root decfmts
               key_table t nd)
        then
          match best with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some t
          | FStar_Pervasives_Native.Some b ->
              (if t.tpl_import_prec > b.tpl_import_prec
               then FStar_Pervasives_Native.Some t
               else
                 if t.tpl_import_prec < b.tpl_import_prec
                 then best
                 else
                   if (template_priority t) >= (template_priority b)
                   then FStar_Pervasives_Native.Some t
                   else best)
        else best in
      pick_template vars nsctx id_attrs style_root decfmts key_table mode
        rest nd best'
let rec pick_template_below
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (mode : Prims.string)
  (below : Prims.int) (tpls : template Prims.list) (nd : dnode)
  (best : template FStar_Pervasives_Native.option) :
  template FStar_Pervasives_Native.option=
  match tpls with
  | [] -> best
  | t::rest ->
      let best' =
        if
          ((t.tpl_mode = mode) && (t.tpl_import_prec < below)) &&
            (template_matches vars nsctx id_attrs style_root decfmts
               key_table t nd)
        then
          match best with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some t
          | FStar_Pervasives_Native.Some b ->
              (if (template_priority t) >= (template_priority b)
               then FStar_Pervasives_Native.Some t
               else best)
        else best in
      pick_template_below vars nsctx id_attrs style_root decfmts key_table
        mode below rest nd best'
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
let ascii_lower_str (s : Prims.string) : Prims.string=
  str_of_chars (FStar_List_Tot_Base.map ascii_lower_char (chars_of s))
let html_void_elems : Prims.string Prims.list=
  ["area";
  "base";
  "basefont";
  "br";
  "col";
  "frame";
  "hr";
  "img";
  "input";
  "isindex";
  "link";
  "meta";
  "param"]
let is_html_void_elem (local : Prims.string) : Prims.bool=
  mem_str (ascii_lower_str local) html_void_elems
let html_boolean_attrs : Prims.string Prims.list=
  ["checked";
  "compact";
  "declare";
  "defer";
  "disabled";
  "ismap";
  "multiple";
  "noresize";
  "noshade";
  "nowrap";
  "readonly";
  "selected"]
let is_html_boolean_attr (name : Prims.string) : Prims.bool=
  mem_str (ascii_lower_str name) html_boolean_attrs
let html_latin1_entities : (Prims.int * Prims.string) Prims.list=
  [((Prims.of_int (0xA0)), "nbsp");
  ((Prims.of_int (0xA1)), "iexcl");
  ((Prims.of_int (0xA2)), "cent");
  ((Prims.of_int (0xA3)), "pound");
  ((Prims.of_int (0xA4)), "curren");
  ((Prims.of_int (0xA5)), "yen");
  ((Prims.of_int (0xA6)), "brvbar");
  ((Prims.of_int (0xA7)), "sect");
  ((Prims.of_int (0xA8)), "uml");
  ((Prims.of_int (0xA9)), "copy");
  ((Prims.of_int (0xAA)), "ordf");
  ((Prims.of_int (0xAB)), "laquo");
  ((Prims.of_int (0xAC)), "not");
  ((Prims.of_int (0xAD)), "shy");
  ((Prims.of_int (0xAE)), "reg");
  ((Prims.of_int (0xAF)), "macr");
  ((Prims.of_int (0xB0)), "deg");
  ((Prims.of_int (0xB1)), "plusmn");
  ((Prims.of_int (0xB2)), "sup2");
  ((Prims.of_int (0xB3)), "sup3");
  ((Prims.of_int (0xB4)), "acute");
  ((Prims.of_int (0xB5)), "micro");
  ((Prims.of_int (0xB6)), "para");
  ((Prims.of_int (0xB7)), "middot");
  ((Prims.of_int (0xB8)), "cedil");
  ((Prims.of_int (0xB9)), "sup1");
  ((Prims.of_int (0xBA)), "ordm");
  ((Prims.of_int (0xBB)), "raquo");
  ((Prims.of_int (0xBC)), "frac14");
  ((Prims.of_int (0xBD)), "frac12");
  ((Prims.of_int (0xBE)), "frac34");
  ((Prims.of_int (0xBF)), "iquest");
  ((Prims.of_int (0xC0)), "Agrave");
  ((Prims.of_int (0xC1)), "Aacute");
  ((Prims.of_int (0xC2)), "Acirc");
  ((Prims.of_int (0xC3)), "Atilde");
  ((Prims.of_int (0xC4)), "Auml");
  ((Prims.of_int (0xC5)), "Aring");
  ((Prims.of_int (0xC6)), "AElig");
  ((Prims.of_int (0xC7)), "Ccedil");
  ((Prims.of_int (0xC8)), "Egrave");
  ((Prims.of_int (0xC9)), "Eacute");
  ((Prims.of_int (0xCA)), "Ecirc");
  ((Prims.of_int (0xCB)), "Euml");
  ((Prims.of_int (0xCC)), "Igrave");
  ((Prims.of_int (0xCD)), "Iacute");
  ((Prims.of_int (0xCE)), "Icirc");
  ((Prims.of_int (0xCF)), "Iuml");
  ((Prims.of_int (0xD0)), "ETH");
  ((Prims.of_int (0xD1)), "Ntilde");
  ((Prims.of_int (0xD2)), "Ograve");
  ((Prims.of_int (0xD3)), "Oacute");
  ((Prims.of_int (0xD4)), "Ocirc");
  ((Prims.of_int (0xD5)), "Otilde");
  ((Prims.of_int (0xD6)), "Ouml");
  ((Prims.of_int (0xD7)), "times");
  ((Prims.of_int (0xD8)), "Oslash");
  ((Prims.of_int (0xD9)), "Ugrave");
  ((Prims.of_int (0xDA)), "Uacute");
  ((Prims.of_int (0xDB)), "Ucirc");
  ((Prims.of_int (0xDC)), "Uuml");
  ((Prims.of_int (0xDD)), "Yacute");
  ((Prims.of_int (0xDE)), "THORN");
  ((Prims.of_int (0xDF)), "szlig");
  ((Prims.of_int (0xE0)), "agrave");
  ((Prims.of_int (0xE1)), "aacute");
  ((Prims.of_int (0xE2)), "acirc");
  ((Prims.of_int (0xE3)), "atilde");
  ((Prims.of_int (0xE4)), "auml");
  ((Prims.of_int (0xE5)), "aring");
  ((Prims.of_int (0xE6)), "aelig");
  ((Prims.of_int (0xE7)), "ccedil");
  ((Prims.of_int (0xE8)), "egrave");
  ((Prims.of_int (0xE9)), "eacute");
  ((Prims.of_int (0xEA)), "ecirc");
  ((Prims.of_int (0xEB)), "euml");
  ((Prims.of_int (0xEC)), "igrave");
  ((Prims.of_int (0xED)), "iacute");
  ((Prims.of_int (0xEE)), "icirc");
  ((Prims.of_int (0xEF)), "iuml");
  ((Prims.of_int (0xF0)), "eth");
  ((Prims.of_int (0xF1)), "ntilde");
  ((Prims.of_int (0xF2)), "ograve");
  ((Prims.of_int (0xF3)), "oacute");
  ((Prims.of_int (0xF4)), "ocirc");
  ((Prims.of_int (0xF5)), "otilde");
  ((Prims.of_int (0xF6)), "ouml");
  ((Prims.of_int (0xF7)), "divide");
  ((Prims.of_int (0xF8)), "oslash");
  ((Prims.of_int (0xF9)), "ugrave");
  ((Prims.of_int (0xFA)), "uacute");
  ((Prims.of_int (0xFB)), "ucirc");
  ((Prims.of_int (0xFC)), "uuml");
  ((Prims.of_int (0xFD)), "yacute");
  ((Prims.of_int (0xFE)), "thorn");
  ((Prims.of_int (0xFF)), "yuml")]
let html_named_entity (cp : Prims.int) :
  Prims.string FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun p -> (FStar_Pervasives_Native.fst p) = cp)
          html_latin1_entities
  with
  | FStar_Pervasives_Native.Some (uu___, nm) ->
      FStar_Pervasives_Native.Some nm
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let html_char_ref (c : FStar_String.char) : Prims.string=
  match html_named_entity (FStar_Char.int_of_char c) with
  | FStar_Pervasives_Native.Some nm -> FStar_String.concat "" ["&"; nm; ";"]
  | FStar_Pervasives_Native.None -> soc c
let escape_html_text_char (c : FStar_String.char) : Prims.string=
  if c = 38 then "&amp;" else if c = 60 then "&lt;" else html_char_ref c
let escape_html_attr_char (c : FStar_String.char) : Prims.string=
  if c = 38 then "&amp;" else if c = 34 then "&quot;" else html_char_ref c
let escape_html_text (s : Prims.string) : Prims.string=
  escape_with escape_html_text_char (chars_of s)
let escape_html_attr (s : Prims.string) : Prims.string=
  escape_with escape_html_attr_char (chars_of s)
let serialize_attr (a : Parser_XML.xml_attribute) : Prims.string=
  FStar_String.concat ""
    [" ";
    a.Parser_XML.attr_name;
    "=\"";
    escape_attr a.Parser_XML.attr_value;
    "\""]
let serialize_attr_html (a : Parser_XML.xml_attribute) : Prims.string=
  if
    (is_html_boolean_attr a.Parser_XML.attr_name) &&
      ((ascii_lower_str a.Parser_XML.attr_value) =
         (ascii_lower_str a.Parser_XML.attr_name))
  then FStar_String.concat "" [" "; a.Parser_XML.attr_name]
  else
    FStar_String.concat ""
      [" ";
      a.Parser_XML.attr_name;
      "=\"";
      escape_html_attr a.Parser_XML.attr_value;
      "\""]
let rec serialize_attrs_html (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string=
  match attrs with
  | [] -> ""
  | a::rest ->
      Prims.strcat (serialize_attr_html a) (serialize_attrs_html rest)
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
type ser_settings =
  {
  ser_cdata:
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list ;
  ser_indent: Prims.bool ;
  ser_encoding: Prims.string ;
  ser_html: Prims.bool }
let __proj__Mkser_settings__item__ser_cdata (projectee : ser_settings) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list=
  match projectee with
  | { ser_cdata; ser_indent; ser_encoding; ser_html;_} -> ser_cdata
let __proj__Mkser_settings__item__ser_indent (projectee : ser_settings) :
  Prims.bool=
  match projectee with
  | { ser_cdata; ser_indent; ser_encoding; ser_html;_} -> ser_indent
let __proj__Mkser_settings__item__ser_encoding (projectee : ser_settings) :
  Prims.string=
  match projectee with
  | { ser_cdata; ser_indent; ser_encoding; ser_html;_} -> ser_encoding
let __proj__Mkser_settings__item__ser_html (projectee : ser_settings) :
  Prims.bool=
  match projectee with
  | { ser_cdata; ser_indent; ser_encoding; ser_html;_} -> ser_html
let default_ser_settings : ser_settings=
  {
    ser_cdata = [];
    ser_indent = false;
    ser_encoding = "UTF-8";
    ser_html = false
  }
let is_text_node (n : Parser_XML.xml_node) : Prims.bool=
  match n with
  | Parser_XML.XText uu___ -> true
  | Parser_XML.XCDATA uu___ -> true
  | uu___ -> false
let rec has_text_node (ns : Parser_XML.xml_node Prims.list) : Prims.bool=
  match ns with
  | [] -> false
  | hd::tl -> if is_text_node hd then true else has_text_node tl
let matches_cdata_name
  (targets :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  (ns_uri : Prims.string FStar_Pervasives_Native.option)
  (local : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun uu___ ->
       match uu___ with
       | (tu, tl) -> (tl = local) && (XPath_Eval.ns_uri_eq tu ns_uri))
    targets
let is_representable (encoding : Prims.string) (cp : Prims.int) : Prims.bool=
  if (encoding = "US-ASCII") || (encoding = "ASCII")
  then cp < (Prims.of_int (128))
  else
    if (encoding = "ISO-8859-1") || (encoding = "Latin1")
    then cp < (Prims.of_int (256))
    else true
let charref (c : FStar_String.char) : Prims.string=
  FStar_String.concat ""
    ["&#"; Prims.string_of_int (FStar_Char.int_of_char c); ";"]
let rec replace_cdata_end_chars (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | 93::93::62::rest ->
      FStar_List_Tot_Base.append
        [93; 93; 93; 93; 62; 60; 33; 91; 67; 68; 65; 84; 65; 91; 62]
        (replace_cdata_end_chars rest)
  | c::rest -> c :: (replace_cdata_end_chars rest)
  | [] -> []
type crun =
  | Run_Text of FStar_String.char Prims.list 
  | Run_Escape of FStar_String.char 
let uu___is_Run_Text (projectee : crun) : Prims.bool=
  match projectee with | Run_Text _0 -> true | uu___ -> false
let __proj__Run_Text__item___0 (projectee : crun) :
  FStar_String.char Prims.list= match projectee with | Run_Text _0 -> _0
let uu___is_Run_Escape (projectee : crun) : Prims.bool=
  match projectee with | Run_Escape _0 -> true | uu___ -> false
let __proj__Run_Escape__item___0 (projectee : crun) : FStar_String.char=
  match projectee with | Run_Escape _0 -> _0
let rec build_cdata_runs (encoding : Prims.string)
  (cs : FStar_String.char Prims.list) (cur : FStar_String.char Prims.list) :
  crun Prims.list=
  match cs with
  | [] ->
      if Prims.uu___is_Nil cur
      then []
      else [Run_Text (FStar_List_Tot_Base.rev cur)]
  | c::rest ->
      if is_representable encoding (FStar_Char.int_of_char c)
      then build_cdata_runs encoding rest (c :: cur)
      else
        (let before =
           if Prims.uu___is_Nil cur
           then []
           else [Run_Text (FStar_List_Tot_Base.rev cur)] in
         FStar_List_Tot_Base.append before ((Run_Escape c) ::
           (build_cdata_runs encoding rest [])))
let render_crun (r : crun) : Prims.string=
  match r with
  | Run_Text [] -> ""
  | Run_Text cs ->
      FStar_String.concat ""
        ["<![CDATA["; str_of_chars (replace_cdata_end_chars cs); "]]>"]
  | Run_Escape c -> charref c
let cdata_wrap_text (encoding : Prims.string) (t : Prims.string) :
  Prims.string=
  FStar_String.concat ""
    (FStar_List_Tot_Base.map render_crun
       (build_cdata_runs encoding (chars_of t) []))
type text_mode =
  | TM_Xml 
  | TM_Html 
  | TM_Cdata 
  | TM_Raw 
let uu___is_TM_Xml (projectee : text_mode) : Prims.bool=
  match projectee with | TM_Xml -> true | uu___ -> false
let uu___is_TM_Html (projectee : text_mode) : Prims.bool=
  match projectee with | TM_Html -> true | uu___ -> false
let uu___is_TM_Cdata (projectee : text_mode) : Prims.bool=
  match projectee with | TM_Cdata -> true | uu___ -> false
let uu___is_TM_Raw (projectee : text_mode) : Prims.bool=
  match projectee with | TM_Raw -> true | uu___ -> false
let rec serialize_node (cfg : ser_settings)
  (scope : (Prims.string * Prims.string) Prims.list)
  (n : Parser_XML.xml_node) : Prims.string=
  match n with
  | Parser_XML.XText t ->
      if cfg.ser_html then escape_html_text t else escape_text t
  | Parser_XML.XCDATA t ->
      if cfg.ser_html then escape_html_text t else escape_text t
  | Parser_XML.XComment t -> FStar_String.concat "" ["<!--"; t; "-->"]
  | Parser_XML.XPI (tg, d) ->
      if cfg.ser_html
      then FStar_String.concat "" ["<?"; tg; " "; d; ">"]
      else FStar_String.concat "" ["<?"; tg; " "; d; "?>"]
  | Parser_XML.XElement (tag, attrs, children) ->
      let uu___ = FStar_List_Tot_Base.partition is_ns_decl attrs in
      (match uu___ with
       | (decls, normal) ->
           let uu___1 = emit_ns_decls scope decls in
           (match uu___1 with
            | (ns_str, scope') ->
                let elem_ns = lookup_ns scope' (XPath_Eval.prefix_of tag) in
                let is_html_here =
                  cfg.ser_html &&
                    (FStar_Pervasives_Native.uu___is_None elem_ns) in
                let loc = XPath_Eval.local_name_of tag in
                let loc_lc = ascii_lower_str loc in
                let a =
                  Prims.strcat ns_str
                    (if is_html_here
                     then serialize_attrs_html normal
                     else serialize_attrs normal) in
                let is_cdata_elem =
                  matches_cdata_name cfg.ser_cdata elem_ns loc in
                let tmode =
                  if
                    is_html_here &&
                      ((loc_lc = "script") || (loc_lc = "style"))
                  then TM_Raw
                  else
                    if is_cdata_elem
                    then TM_Cdata
                    else if is_html_here then TM_Html else TM_Xml in
                let parts = serialize_children cfg scope' tmode children in
                let do_indent =
                  (cfg.ser_indent && (Prims.uu___is_Cons children)) &&
                    (Prims.op_Negation (has_text_node children)) in
                let inner =
                  if Prims.uu___is_Nil parts
                  then ""
                  else
                    if do_indent
                    then
                      Prims.strcat "\n"
                        (Prims.strcat (FStar_String.concat "\n" parts) "\n")
                    else FStar_String.concat "" parts in
                if is_html_here && (is_html_void_elem loc)
                then FStar_String.concat "" ["<"; tag; a; ">"]
                else
                  if inner = ""
                  then
                    (if is_html_here
                     then
                       FStar_String.concat "" ["<"; tag; a; "></"; tag; ">"]
                     else FStar_String.concat "" ["<"; tag; a; "/>"])
                  else
                    FStar_String.concat ""
                      ["<"; tag; a; ">"; inner; "</"; tag; ">"]))
and serialize_children (cfg : ser_settings)
  (scope : (Prims.string * Prims.string) Prims.list) (tmode : text_mode)
  (ns : Parser_XML.xml_node Prims.list) : Prims.string Prims.list=
  match ns with
  | [] -> []
  | hd::tl ->
      let s =
        match hd with
        | Parser_XML.XText t ->
            (match tmode with
             | TM_Raw -> t
             | TM_Cdata -> cdata_wrap_text cfg.ser_encoding t
             | TM_Html -> escape_html_text t
             | TM_Xml -> escape_text t)
        | Parser_XML.XCDATA t ->
            (match tmode with
             | TM_Raw -> t
             | TM_Cdata -> cdata_wrap_text cfg.ser_encoding t
             | TM_Html -> escape_html_text t
             | TM_Xml -> escape_text t)
        | uu___ -> serialize_node cfg scope hd in
      s :: (serialize_children cfg scope tmode tl)
let serialize_nodes (cfg : ser_settings)
  (scope : (Prims.string * Prims.string) Prims.list)
  (ns : Parser_XML.xml_node Prims.list) : Prims.string=
  FStar_String.concat ""
    (serialize_children cfg scope (if cfg.ser_html then TM_Html else TM_Xml)
       ns)
let serialize_result (n : Parser_XML.xml_node) : Prims.string=
  serialize_node default_ser_settings [] n
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
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list) (it : XPath_Eval.xctx_item)
  (pos : Prims.nat) (size : Prims.nat) : Prims.string Prims.list=
  match specs with
  | [] -> []
  | s::rest ->
      (eval_string_kv it pos size vars nsctx id_attrs style_root decfmts
         key_table s.so_select)
      ::
      (eval_sort_keys rest vars nsctx id_attrs style_root decfmts key_table
         it pos size)
let rec annotate_items (specs : sortspec Prims.list)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list)
  (items : XPath_Eval.xctx_item Prims.list) (pos : Prims.nat)
  (size : Prims.nat) :
  (XPath_Eval.xctx_item * Prims.string Prims.list) Prims.list=
  match items with
  | [] -> []
  | it::tl ->
      (it,
        (eval_sort_keys specs vars nsctx id_attrs style_root decfmts
           key_table it pos size))
      ::
      (annotate_items specs vars nsctx id_attrs style_root decfmts key_table
         tl (pos + Prims.int_one) size)
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
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (key_table : XPath_Eval.key_entry Prims.list)
  (body : Parser_XML.xml_node Prims.list)
  (items : XPath_Eval.xctx_item Prims.list) :
  XPath_Eval.xctx_item Prims.list=
  match collect_sorts ctx pos size vars nsctx pfx body with
  | [] -> items
  | specs ->
      let n = FStar_List_Tot_Base.length items in
      FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
        (sort_items specs
           (annotate_items specs vars nsctx id_attrs style_root decfmts
              key_table items Prims.int_one n))
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
  (pos : Prims.nat) (size : Prims.nat) (mode : Prims.string)
  (svars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (srtf : (Prims.string * rnode Prims.list) Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match pick_template st.xs_globals st.xs_nsctx st.xs_id_attrs
             st.xs_style_root st.xs_decfmts st.xs_key_table mode
             st.xs_templates nd FStar_Pervasives_Native.None
     with
     | FStar_Pervasives_Native.Some tpl ->
         instantiate_seq (fuel - Prims.int_one) st nd pos size svars srtf
           mode tpl.tpl_import_prec tpl.tpl_body
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
           (FStar_List_Tot_Base.length kids) mode st.xs_globals []
     | D_Item (XPath_Eval.CI_Elem (uu___1, uu___2, uu___3)) ->
         let kids = dnode_children nd in
         apply_list (fuel - Prims.int_one) st kids Prims.int_one
           (FStar_List_Tot_Base.length kids) mode st.xs_globals []
     | D_Item (XPath_Eval.CI_Text (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XText t)]
     | D_Item (XPath_Eval.CI_Attr (uu___1, uu___2, uu___3, a)) ->
         [R_Node (Parser_XML.XText (a.Parser_XML.attr_value))]
     | D_Item (XPath_Eval.CI_Comment (uu___1, uu___2, uu___3, uu___4)) -> []
     | D_Item (XPath_Eval.CI_PI (uu___1, uu___2, uu___3, uu___4, uu___5)) ->
         []
     | D_Item (XPath_Eval.CI_Namespace
         (uu___1, uu___2, uu___3, uu___4, uu___5)) -> [])
and apply_list (fuel : Prims.nat) (st : xstyle) (nodes : dnode Prims.list)
  (pos : Prims.nat) (size : Prims.nat) (mode : Prims.string)
  (svars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (srtf : (Prims.string * rnode Prims.list) Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match nodes with
     | [] -> []
     | hd::tl ->
         let here =
           dispatch (fuel - Prims.int_one) st hd pos size mode svars srtf in
         FStar_List_Tot_Base.op_At here
           (apply_list (fuel - Prims.int_one) st tl (pos + Prims.int_one)
              size mode svars srtf))
and instantiate_seq (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
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
                     vars rtf cur_mode cur_prec tl
                 else
                   (match attr_opt "select" attrs with
                    | FStar_Pervasives_Native.Some sel ->
                        let v =
                          eval_val_dn ctx pos size vars st.xs_nsctx
                            st.xs_id_attrs st.xs_style_root st.xs_decfmts
                            st.xs_key_table sel in
                        instantiate_seq (fuel - Prims.int_one) st ctx pos
                          size ((nm, v) :: vars) rtf cur_mode cur_prec tl
                    | FStar_Pervasives_Native.None ->
                        let frag =
                          instantiate_seq (fuel - Prims.int_one) st ctx pos
                            size vars rtf cur_mode cur_prec children in
                        let sval = text_value_nodes (only_nodes frag) in
                        instantiate_seq (fuel - Prims.int_one) st ctx pos
                          size ((nm, (XPath_Eval.XV_Str sval)) :: vars)
                          ((nm, frag) :: rtf) cur_mode cur_prec tl))
              else
                (let here =
                   instantiate_one (fuel - Prims.int_one) st ctx pos size
                     vars rtf cur_mode cur_prec hd in
                 FStar_List_Tot_Base.op_At here
                   (instantiate_seq (fuel - Prims.int_one) st ctx pos size
                      vars rtf cur_mode cur_prec tl))
          | uu___1 ->
              let here =
                instantiate_one (fuel - Prims.int_one) st ctx pos size vars
                  rtf cur_mode cur_prec hd in
              FStar_List_Tot_Base.op_At here
                (instantiate_seq (fuel - Prims.int_one) st ctx pos size vars
                   rtf cur_mode cur_prec tl)))
and bind_with_params_scoped (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (evars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (ertf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
  (svars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (srtf : (Prims.string * rnode Prims.list) Prims.list)
  (children : Parser_XML.xml_node Prims.list) :
  ((Prims.string * XPath_Eval.xp_value) Prims.list * (Prims.string * rnode
    Prims.list) Prims.list)=
  if fuel = Prims.int_zero
  then (svars, srtf)
  else
    (match children with
     | [] -> (svars, srtf)
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
                     let v =
                       eval_val_dn ctx pos size evars st.xs_nsctx
                         st.xs_id_attrs st.xs_style_root st.xs_decfmts
                         st.xs_key_table sel in
                     bind_with_params_scoped (fuel - Prims.int_one) st ctx
                       pos size evars ertf cur_mode cur_prec ((nm, v) ::
                       svars) srtf tl
                 | FStar_Pervasives_Native.None ->
                     let frag =
                       instantiate_seq (fuel - Prims.int_one) st ctx pos size
                         evars ertf cur_mode cur_prec pchildren in
                     let sval = text_value_nodes (only_nodes frag) in
                     bind_with_params_scoped (fuel - Prims.int_one) st ctx
                       pos size evars ertf cur_mode cur_prec
                       ((nm, (XPath_Eval.XV_Str sval)) :: svars) ((nm, frag)
                       :: srtf) tl)
              else
                bind_with_params_scoped (fuel - Prims.int_one) st ctx pos
                  size evars ertf cur_mode cur_prec svars srtf tl
          | uu___1 ->
              bind_with_params_scoped (fuel - Prims.int_one) st ctx pos size
                evars ertf cur_mode cur_prec svars srtf tl))
and instantiate_one (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
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
                       st.xs_id_attrs st.xs_style_root st.xs_decfmts
                       st.xs_key_table (attr_or "select" "." attrs)))]
            else
              if ln = "text"
              then [R_Node (Parser_XML.XText (raw_text children))]
              else
                if ln = "if"
                then
                  (if
                     eval_bool_dn ctx pos size vars st.xs_nsctx
                       st.xs_id_attrs st.xs_style_root st.xs_decfmts
                       st.xs_key_table (attr_or "test" "false()" attrs)
                   then
                     instantiate_seq (fuel - Prims.int_one) st ctx pos size
                       vars rtf cur_mode cur_prec children
                   else [])
                else
                  if ln = "choose"
                  then
                    instantiate_choose (fuel - Prims.int_one) st ctx pos size
                      vars rtf cur_mode cur_prec children
                  else
                    if ln = "for-each"
                    then
                      (let sel = attr_or "select" "." attrs in
                       let items0 =
                         XPath_Eval.doc_sort_dedup
                           (select_nodes ctx pos size vars st.xs_nsctx
                              st.xs_id_attrs st.xs_style_root st.xs_decfmts
                              st.xs_key_table sel) in
                       let items =
                         sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars
                           st.xs_nsctx st.xs_id_attrs st.xs_style_root
                           st.xs_decfmts st.xs_key_table children items0 in
                       for_each_items (fuel - Prims.int_one) st children vars
                         rtf cur_mode cur_prec items Prims.int_one
                         (FStar_List_Tot_Base.length items))
                    else
                      if ln = "apply-templates"
                      then
                        (let amode = attr_or "mode" "" attrs in
                         let uu___6 =
                           bind_with_params_scoped (fuel - Prims.int_one) st
                             ctx pos size vars rtf cur_mode cur_prec
                             st.xs_globals [] children in
                         match uu___6 with
                         | (pvars, prtf) ->
                             (match attr_opt "select" attrs with
                              | FStar_Pervasives_Native.Some sel ->
                                  let items0 =
                                    XPath_Eval.doc_sort_dedup
                                      (select_nodes ctx pos size vars
                                         st.xs_nsctx st.xs_id_attrs
                                         st.xs_style_root st.xs_decfmts
                                         st.xs_key_table sel) in
                                  let items =
                                    sort_maybe (dnode_ci ctx) pos size
                                      st.xs_pfx vars st.xs_nsctx
                                      st.xs_id_attrs st.xs_style_root
                                      st.xs_decfmts st.xs_key_table children
                                      items0 in
                                  let dns =
                                    FStar_List_Tot_Base.map
                                      (fun it -> D_Item it) items in
                                  apply_list (fuel - Prims.int_one) st dns
                                    Prims.int_one
                                    (FStar_List_Tot_Base.length items) amode
                                    pvars prtf
                              | FStar_Pervasives_Native.None ->
                                  let kids0 = dnode_children ctx in
                                  let items0 =
                                    FStar_List_Tot_Base.map dnode_ci kids0 in
                                  let items =
                                    sort_maybe (dnode_ci ctx) pos size
                                      st.xs_pfx vars st.xs_nsctx
                                      st.xs_id_attrs st.xs_style_root
                                      st.xs_decfmts st.xs_key_table children
                                      items0 in
                                  let dns =
                                    FStar_List_Tot_Base.map
                                      (fun it -> D_Item it) items in
                                  apply_list (fuel - Prims.int_one) st dns
                                    Prims.int_one
                                    (FStar_List_Tot_Base.length items) amode
                                    pvars prtf))
                      else
                        if ln = "apply-imports"
                        then
                          (match pick_template_below st.xs_globals
                                   st.xs_nsctx st.xs_id_attrs
                                   st.xs_style_root st.xs_decfmts
                                   st.xs_key_table cur_mode cur_prec
                                   st.xs_templates ctx
                                   FStar_Pervasives_Native.None
                           with
                           | FStar_Pervasives_Native.Some tpl ->
                               instantiate_seq (fuel - Prims.int_one) st ctx
                                 pos size st.xs_globals [] cur_mode
                                 tpl.tpl_import_prec tpl.tpl_body
                           | FStar_Pervasives_Native.None ->
                               builtin_rule (fuel - Prims.int_one) st ctx
                                 cur_mode)
                        else
                          if ln = "call-template"
                          then
                            (let nm = attr_or "name" "" attrs in
                             match find_named_template st.xs_templates nm
                             with
                             | FStar_Pervasives_Native.Some tpl ->
                                 let uu___8 =
                                   bind_with_params_scoped
                                     (fuel - Prims.int_one) st ctx pos size
                                     vars rtf cur_mode cur_prec st.xs_globals
                                     [] children in
                                 (match uu___8 with
                                  | (cvars, crtf) ->
                                      instantiate_seq (fuel - Prims.int_one)
                                        st ctx pos size cvars crtf cur_mode
                                        tpl.tpl_import_prec tpl.tpl_body)
                             | FStar_Pervasives_Native.None -> [])
                          else
                            if ln = "copy-of"
                            then
                              (let sel = attr_or "select" "." attrs in
                               let no_ns =
                                 (attr_or "copy-namespaces" "yes" attrs) =
                                   "no" in
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
                                             st.xs_nsctx st.xs_id_attrs
                                             st.xs_style_root st.xs_decfmts
                                             st.xs_key_table sel))
                               | FStar_Pervasives_Native.None ->
                                   FStar_List_Tot_Base.map mk
                                     (select_nodes ctx pos size vars
                                        st.xs_nsctx st.xs_id_attrs
                                        st.xs_style_root st.xs_decfmts
                                        st.xs_key_table sel))
                            else
                              if ln = "copy"
                              then
                                (let use_attrs =
                                   expand_attrset_names
                                     (fuel - Prims.int_one) st ctx pos size
                                     vars rtf cur_mode cur_prec []
                                     (parse_qname_list
                                        (attr_or "use-attribute-sets" ""
                                           attrs)) in
                                 instantiate_copy (fuel - Prims.int_one) st
                                   ctx pos size vars rtf cur_mode cur_prec
                                   use_attrs children)
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
                                            | FStar_Pervasives_Native.Some u
                                                ->
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
                                            | FStar_Pervasives_Native.Some u
                                                ->
                                                [{
                                                   Parser_XML.attr_name =
                                                     (Prims.strcat "xmlns:"
                                                        epfx);
                                                   Parser_XML.attr_value = u
                                                 }]
                                            | FStar_Pervasives_Native.None ->
                                                []) in
                                   let use_attrs =
                                     expand_attrset_names
                                       (fuel - Prims.int_one) st ctx pos size
                                       vars rtf cur_mode cur_prec []
                                       (parse_qname_list
                                          (attr_or "use-attribute-sets" ""
                                             attrs)) in
                                   let body =
                                     instantiate_seq (fuel - Prims.int_one)
                                       st ctx pos size vars rtf cur_mode
                                       cur_prec children in
                                   [R_Node
                                      (build_element nm
                                         (FStar_List_Tot_Base.append
                                            use_attrs nsdecls) body)])
                                else
                                  if ln = "attribute"
                                  then
                                    (let nm =
                                       expand_avt (dnode_ci ctx) pos size
                                         vars st.xs_nsctx
                                         (attr_or "name" "" attrs) in
                                     let body =
                                       instantiate_seq (fuel - Prims.int_one)
                                         st ctx pos size vars rtf cur_mode
                                         cur_prec children in
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
                                         instantiate_seq
                                           (fuel - Prims.int_one) st ctx pos
                                           size vars rtf cur_mode cur_prec
                                           children in
                                       [R_Node
                                          (Parser_XML.XComment
                                             (rnodes_text body))])
                                    else
                                      if ln = "number"
                                      then
                                        (let dctx = dnode_ci ctx in
                                         let level =
                                           expand_avt dctx pos size vars
                                             st.xs_nsctx
                                             (attr_or "level" "single" attrs) in
                                         let count_pat =
                                           attr_or "count" "" attrs in
                                         let from_pat =
                                           attr_or "from" "" attrs in
                                         let fmt =
                                           expand_avt dctx pos size vars
                                             st.xs_nsctx
                                             (attr_or "format" "1" attrs) in
                                         let gsep =
                                           expand_avt dctx pos size vars
                                             st.xs_nsctx
                                             (attr_or "grouping-separator" ""
                                                attrs) in
                                         let gsize_s =
                                           expand_avt dctx pos size vars
                                             st.xs_nsctx
                                             (attr_or "grouping-size" ""
                                                attrs) in
                                         let text =
                                           match attr_opt "value" attrs with
                                           | FStar_Pervasives_Native.Some
                                               vexpr ->
                                               let n =
                                                 XPath_Eval.to_number_val
                                                   (eval_val_dn ctx pos size
                                                      vars st.xs_nsctx
                                                      st.xs_id_attrs
                                                      st.xs_style_root
                                                      st.xs_decfmts
                                                      st.xs_key_table vexpr) in
                                               (match value_bypass n with
                                                | FStar_Pervasives_Native.Some
                                                    s -> s
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (match XPath_Eval.xn_finite_int
                                                             (XPath_Eval.xn_round
                                                                n)
                                                     with
                                                     | FStar_Pervasives_Native.Some
                                                         v ->
                                                         render_number_list
                                                           [v] fmt gsep
                                                           gsize_s
                                                     | FStar_Pervasives_Native.None
                                                         -> ""))
                                           | FStar_Pervasives_Native.None ->
                                               (match ctx with
                                                | D_Item it ->
                                                    render_number_list
                                                      (level_numbers vars
                                                         st.xs_nsctx
                                                         st.xs_id_attrs
                                                         st.xs_style_root
                                                         st.xs_decfmts
                                                         st.xs_key_table
                                                         level count_pat
                                                         from_pat it) fmt
                                                      gsep gsize_s
                                                | D_Doc (uu___14, uu___15) ->
                                                    "") in
                                         [R_Node (Parser_XML.XText text)])
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
            let use_attrs =
              expand_attrset_names (fuel - Prims.int_one) st ctx pos size
                vars rtf cur_mode cur_prec []
                (parse_qname_list
                   (attr_or (Prims.strcat st.xs_pfx ":use-attribute-sets") ""
                      attrs)) in
            let literal_attrs = merge_attrs_override use_attrs out_attrs in
            let body =
              instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
                cur_mode cur_prec children in
            let default_ns_fixup =
              if contains_char 58 tag
              then []
              else
                if
                  (FStar_List_Tot_Base.existsb
                     (fun a -> a.Parser_XML.attr_name = "xmlns") kept)
                    ||
                    (FStar_List_Tot_Base.existsb
                       (fun a -> a.Parser_XML.attr_name = "xmlns")
                       st.xs_nsscope)
                then []
                else
                  (match XPath_Eval.lookup_nsctx st.xs_nsctx "" with
                   | FStar_Pervasives_Native.Some u ->
                       if u <> ""
                       then
                         [{
                            Parser_XML.attr_name = "xmlns";
                            Parser_XML.attr_value = u
                          }]
                       else []
                   | FStar_Pervasives_Native.None -> []) in
            [R_Node
               (build_element tag
                  (FStar_List_Tot_Base.op_At default_ns_fixup
                     (FStar_List_Tot_Base.op_At st.xs_nsscope literal_attrs))
                  body)]))
and instantiate_choose (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
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
                        st.xs_id_attrs st.xs_style_root st.xs_decfmts
                        st.xs_key_table (attr_or "test" "false()" attrs)
                    then
                      instantiate_seq (fuel - Prims.int_one) st ctx pos size
                        vars rtf cur_mode cur_prec children
                    else
                      instantiate_choose (fuel - Prims.int_one) st ctx pos
                        size vars rtf cur_mode cur_prec tl)
                 else
                   if ln = "otherwise"
                   then
                     instantiate_seq (fuel - Prims.int_one) st ctx pos size
                       vars rtf cur_mode cur_prec children
                   else
                     instantiate_choose (fuel - Prims.int_one) st ctx pos
                       size vars rtf cur_mode cur_prec tl)
              else
                instantiate_choose (fuel - Prims.int_one) st ctx pos size
                  vars rtf cur_mode cur_prec tl
          | uu___1 ->
              instantiate_choose (fuel - Prims.int_one) st ctx pos size vars
                rtf cur_mode cur_prec tl))
and instantiate_copy (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
  (use_attrs : Parser_XML.xml_attribute Prims.list)
  (children : Parser_XML.xml_node Prims.list) : rnode Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match ctx with
     | D_Doc (uu___1, uu___2) ->
         instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
           cur_mode cur_prec children
     | D_Item (XPath_Eval.CI_Elem (uu___1, anc, n)) ->
         (match n with
          | Parser_XML.XElement (t, uu___2, uu___3) ->
              let body =
                instantiate_seq (fuel - Prims.int_one) st ctx pos size vars
                  rtf cur_mode cur_prec children in
              let nsnodes = inscope_ns [] [] (n :: anc) in
              [R_Node
                 (build_element t
                    (FStar_List_Tot_Base.append nsnodes use_attrs) body)]
          | uu___2 ->
              instantiate_seq (fuel - Prims.int_one) st ctx pos size vars rtf
                cur_mode cur_prec children)
     | D_Item (XPath_Eval.CI_Text (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XText t)]
     | D_Item (XPath_Eval.CI_Comment (uu___1, uu___2, uu___3, t)) ->
         [R_Node (Parser_XML.XComment t)]
     | D_Item (XPath_Eval.CI_PI (uu___1, uu___2, uu___3, tg, d)) ->
         [R_Node (Parser_XML.XPI (tg, d))]
     | D_Item (XPath_Eval.CI_Attr (uu___1, uu___2, uu___3, a)) -> [R_Attr a]
     | D_Item (XPath_Eval.CI_Namespace (uu___1, uu___2, uu___3, pfx, uri)) ->
         [R_Attr
            {
              Parser_XML.attr_name =
                (if pfx = "" then "xmlns" else Prims.strcat "xmlns:" pfx);
              Parser_XML.attr_value = uri
            }])
and expand_attrset_name (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
  (visited : Prims.string Prims.list) (name : Prims.string) :
  Parser_XML.xml_attribute Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    if mem_str name visited
    then []
    else
      (match find_attrset_entry st.xs_attrsets name with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some e ->
           let deps_expanded =
             expand_attrset_names (fuel - Prims.int_one) st ctx pos size vars
               rtf cur_mode cur_prec (name :: visited) e.ase_deps in
           let own_attrs =
             only_attrs
               (instantiate_seq (fuel - Prims.int_one) st ctx pos size vars
                  rtf cur_mode cur_prec e.ase_own) in
           merge_attrs_override deps_expanded own_attrs)
and expand_attrset_names (fuel : Prims.nat) (st : xstyle) (ctx : dnode)
  (pos : Prims.nat) (size : Prims.nat)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
  (visited : Prims.string Prims.list) (names : Prims.string Prims.list) :
  Parser_XML.xml_attribute Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match names with
     | [] -> []
     | hd::tl ->
         let a =
           expand_attrset_name (fuel - Prims.int_one) st ctx pos size vars
             rtf cur_mode cur_prec visited hd in
         let b =
           expand_attrset_names (fuel - Prims.int_one) st ctx pos size vars
             rtf cur_mode cur_prec visited tl in
         merge_attrs_override a b)
and for_each_items (fuel : Prims.nat) (st : xstyle)
  (body : Parser_XML.xml_node Prims.list)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (rtf : (Prims.string * rnode Prims.list) Prims.list)
  (cur_mode : Prims.string) (cur_prec : Prims.int)
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
             vars rtf cur_mode cur_prec body in
         FStar_List_Tot_Base.op_At here
           (for_each_items (fuel - Prims.int_one) st body vars rtf cur_mode
              cur_prec rest (pos + Prims.int_one) size))
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
let rec collect_templates_prec (pfx : Prims.string) (prec : Prims.int)
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
              then collect_templates_prec pfx prec tl
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
                     tpl_body = body;
                     tpl_import_prec = prec
                   } in
                 t :: (collect_templates_prec pfx prec tl)))
           else collect_templates_prec pfx prec tl
       | uu___ -> collect_templates_prec pfx prec tl)
let collect_templates (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : template Prims.list=
  collect_templates_prec pfx Prims.int_zero children
let first_char_or (dflt : FStar_String.char) (s : Prims.string) :
  FStar_String.char= match chars_of s with | c::uu___ -> c | [] -> dflt
let char_attr (attrs : Parser_XML.xml_attribute Prims.list)
  (name : Prims.string) (dflt : FStar_String.char) : FStar_String.char=
  match attr_opt name attrs with
  | FStar_Pervasives_Native.Some s -> first_char_or dflt s
  | FStar_Pervasives_Native.None -> dflt
let string_attr (attrs : Parser_XML.xml_attribute Prims.list)
  (name : Prims.string) (dflt : Prims.string) : Prims.string=
  match attr_opt name attrs with
  | FStar_Pervasives_Native.Some s -> s
  | FStar_Pervasives_Native.None -> dflt
let decimal_format_of_attrs (attrs : Parser_XML.xml_attribute Prims.list) :
  XPath_Eval.decimal_format_symbols=
  {
    XPath_Eval.dfs_name = (attr_or "name" "" attrs);
    XPath_Eval.dfs_decimal_sep =
      (char_attr attrs "decimal-separator"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_decimal_sep);
    XPath_Eval.dfs_grouping_sep =
      (char_attr attrs "grouping-separator"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_grouping_sep);
    XPath_Eval.dfs_infinity =
      (string_attr attrs "infinity"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_infinity);
    XPath_Eval.dfs_minus_sign =
      (char_attr attrs "minus-sign"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_minus_sign);
    XPath_Eval.dfs_nan =
      (string_attr attrs "NaN"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_nan);
    XPath_Eval.dfs_percent =
      (char_attr attrs "percent"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_percent);
    XPath_Eval.dfs_per_mille =
      (char_attr attrs "per-mille"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_per_mille);
    XPath_Eval.dfs_zero_digit =
      (char_attr attrs "zero-digit"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_zero_digit);
    XPath_Eval.dfs_digit =
      (char_attr attrs "digit"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_digit);
    XPath_Eval.dfs_pattern_sep =
      (char_attr attrs "pattern-separator"
         XPath_Eval.default_decimal_format_symbols.XPath_Eval.dfs_pattern_sep)
  }
let rec collect_decimal_formats (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  XPath_Eval.decimal_format_symbols Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "decimal-format")
           then (decimal_format_of_attrs attrs) ::
             (collect_decimal_formats pfx tl)
           else collect_decimal_formats pfx tl
       | uu___ -> collect_decimal_formats pfx tl)
type key_decl =
  {
  kd_name: Prims.string ;
  kd_match: Prims.string ;
  kd_use: Prims.string }
let __proj__Mkkey_decl__item__kd_name (projectee : key_decl) : Prims.string=
  match projectee with | { kd_name; kd_match; kd_use;_} -> kd_name
let __proj__Mkkey_decl__item__kd_match (projectee : key_decl) : Prims.string=
  match projectee with | { kd_name; kd_match; kd_use;_} -> kd_match
let __proj__Mkkey_decl__item__kd_use (projectee : key_decl) : Prims.string=
  match projectee with | { kd_name; kd_match; kd_use;_} -> kd_use
let rec collect_keys (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : key_decl Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "key")
           then
             (match ((attr_opt "name" attrs), (attr_opt "match" attrs),
                      (attr_opt "use" attrs))
              with
              | (FStar_Pervasives_Native.Some nm,
                 FStar_Pervasives_Native.Some m, FStar_Pervasives_Native.Some
                 u) -> { kd_name = nm; kd_match = m; kd_use = u } ::
                  (collect_keys pfx tl)
              | (uu___1, uu___2, uu___3) -> collect_keys pfx tl)
           else collect_keys pfx tl
       | uu___ -> collect_keys pfx tl)
let key_entries_for_use (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (kname : (Prims.string FStar_Pervasives_Native.option * Prims.string))
  (it : XPath_Eval.xctx_item) (use_expr : Prims.string) :
  XPath_Eval.key_entry Prims.list=
  match eval_val it Prims.int_one Prims.int_one [] nsctx id_attrs style_root
          decfmts [] use_expr
  with
  | XPath_Eval.XV_Nodes ns ->
      FStar_List_Tot_Base.map
        (fun n -> (kname, (XPath_Eval.item_string_value n), it)) ns
  | other -> [(kname, (XPath_Eval.to_string_val other), it)]
let rec key_entries_for_decl
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (kname : (Prims.string FStar_Pervasives_Native.option * Prims.string))
  (match_alts : Prims.string Prims.list) (use_expr : Prims.string)
  (items : XPath_Eval.xctx_item Prims.list) :
  XPath_Eval.key_entry Prims.list=
  match items with
  | [] -> []
  | it::rest ->
      let here =
        if
          any_alt_matches [] nsctx id_attrs style_root decfmts [] match_alts
            (D_Item it)
        then
          key_entries_for_use nsctx id_attrs style_root decfmts kname it
            use_expr
        else [] in
      FStar_List_Tot_Base.op_At here
        (key_entries_for_decl nsctx id_attrs style_root decfmts kname
           match_alts use_expr rest)
let rec build_key_table (nsctx : (Prims.string * Prims.string) Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list)
  (style_root : Parser_XML.xml_node)
  (decfmts : XPath_Eval.decimal_format_symbols Prims.list)
  (decls : key_decl Prims.list) (items : XPath_Eval.xctx_item Prims.list) :
  XPath_Eval.key_entry Prims.list=
  match decls with
  | [] -> []
  | kd::rest ->
      let kname = XPath_Eval.resolve_key_qname nsctx kd.kd_name in
      let alts = split_on_char 124 kd.kd_match in
      FStar_List_Tot_Base.append
        (key_entries_for_decl nsctx id_attrs style_root decfmts kname alts
           kd.kd_use items)
        (build_key_table nsctx id_attrs style_root decfmts rest items)
let resolve_qname_ns (nsctx : (Prims.string * Prims.string) Prims.list)
  (qn : Prims.string) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string)=
  ((XPath_Eval.lookup_nsctx nsctx (XPath_Eval.prefix_of qn)),
    (XPath_Eval.local_name_of qn))
let merge_one_output (nsctx : (Prims.string * Prims.string) Prims.list)
  (cfg : output_settings) (attrs : Parser_XML.xml_attribute Prims.list) :
  output_settings=
  {
    os_method_raw =
      (match attr_opt "method" attrs with
       | FStar_Pervasives_Native.Some m -> m
       | FStar_Pervasives_Native.None -> cfg.os_method_raw);
    os_omit_decl =
      (match attr_opt "omit-xml-declaration" attrs with
       | FStar_Pervasives_Native.Some v -> v = "yes"
       | FStar_Pervasives_Native.None -> cfg.os_omit_decl);
    os_standalone =
      (match attr_opt "standalone" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_standalone);
    os_indent_raw =
      (match attr_opt "indent" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_indent_raw);
    os_encoding =
      (match attr_opt "encoding" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_encoding);
    os_version =
      (match attr_opt "version" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_version);
    os_doctype_public =
      (match attr_opt "doctype-public" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_doctype_public);
    os_doctype_system =
      (match attr_opt "doctype-system" attrs with
       | FStar_Pervasives_Native.Some v -> v
       | FStar_Pervasives_Native.None -> cfg.os_doctype_system);
    os_cdata =
      (FStar_List_Tot_Base.append cfg.os_cdata
         (match attr_opt "cdata-section-elements" attrs with
          | FStar_Pervasives_Native.Some v ->
              FStar_List_Tot_Base.map (resolve_qname_ns nsctx)
                (parse_qname_list v)
          | FStar_Pervasives_Native.None -> []))
  }
let rec collect_output_settings (pfx : Prims.string)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (children : Parser_XML.xml_node Prims.list) (cfg : output_settings) :
  output_settings=
  match children with
  | [] -> cfg
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "output")
           then
             collect_output_settings pfx nsctx tl
               (merge_one_output nsctx cfg attrs)
           else collect_output_settings pfx nsctx tl cfg
       | uu___ -> collect_output_settings pfx nsctx tl cfg)
let rec any_output_decl (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : Prims.bool=
  match children with
  | [] -> false
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, uu___, uu___1) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "output")
           then true
           else any_output_decl pfx tl
       | uu___ -> any_output_decl pfx tl)
let rec attrset_upsert_append (entries : attrset_entry Prims.list)
  (nm : Prims.string) (deps : Prims.string Prims.list)
  (own : Parser_XML.xml_node Prims.list) : attrset_entry Prims.list=
  match entries with
  | [] -> [{ ase_name = nm; ase_deps = deps; ase_own = own }]
  | e::rest ->
      if e.ase_name = nm
      then
        {
          ase_name = (e.ase_name);
          ase_deps = (FStar_List_Tot_Base.append e.ase_deps deps);
          ase_own = (FStar_List_Tot_Base.append e.ase_own own)
        } :: rest
      else e :: (attrset_upsert_append rest nm deps own)
let rec collect_attribute_sets (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) : attrset_entry Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      let rest = collect_attribute_sets pfx tl in
      (match hd with
       | Parser_XML.XElement (tag, attrs, body) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "attribute-set")
           then
             let nm = attr_or "name" "" attrs in
             (if nm = ""
              then rest
              else
                (let deps =
                   parse_qname_list (attr_or "use-attribute-sets" "" attrs) in
                 attrset_upsert_append rest nm deps body))
           else rest
       | uu___ -> rest)
let rec build_nsctx (attrs : Parser_XML.xml_attribute Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      (match ns_decl_prefix a.Parser_XML.attr_name with
       | FStar_Pervasives_Native.Some pfx -> (pfx, (a.Parser_XML.attr_value))
           :: (build_nsctx rest)
       | FStar_Pervasives_Native.None -> build_nsctx rest)
let text_or_cdata (n : Parser_XML.xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match n with
  | Parser_XML.XText s -> FStar_Pervasives_Native.Some s
  | Parser_XML.XCDATA s -> FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let rec run_is_all_ws (nodes : Parser_XML.xml_node Prims.list) : Prims.bool=
  match nodes with
  | [] -> true
  | hd::tl ->
      (match text_or_cdata hd with
       | FStar_Pervasives_Native.Some s ->
           (is_all_ws s) && (run_is_all_ws tl)
       | FStar_Pervasives_Native.None -> true)
let xml_space_here (attrs : Parser_XML.xml_attribute Prims.list)
  (inherited : Prims.bool) : Prims.bool=
  match Parser_XML.find_attr "xml:space" attrs with
  | FStar_Pervasives_Native.Some "preserve" -> true
  | FStar_Pervasives_Native.Some "default" -> false
  | FStar_Pervasives_Native.Some uu___ -> inherited
  | FStar_Pervasives_Native.None -> inherited
type ws_name_test =
  | WNT_Star 
  | WNT_NsStar of Prims.string FStar_Pervasives_Native.option 
  | WNT_Qual of Prims.string FStar_Pervasives_Native.option * Prims.string 
let uu___is_WNT_Star (projectee : ws_name_test) : Prims.bool=
  match projectee with | WNT_Star -> true | uu___ -> false
let uu___is_WNT_NsStar (projectee : ws_name_test) : Prims.bool=
  match projectee with | WNT_NsStar _0 -> true | uu___ -> false
let __proj__WNT_NsStar__item___0 (projectee : ws_name_test) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | WNT_NsStar _0 -> _0
let uu___is_WNT_Qual (projectee : ws_name_test) : Prims.bool=
  match projectee with | WNT_Qual (_0, _1) -> true | uu___ -> false
let __proj__WNT_Qual__item___0 (projectee : ws_name_test) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | WNT_Qual (_0, _1) -> _0
let __proj__WNT_Qual__item___1 (projectee : ws_name_test) : Prims.string=
  match projectee with | WNT_Qual (_0, _1) -> _1
type ws_decl = {
  wsd_test: ws_name_test ;
  wsd_strip: Prims.bool }
let __proj__Mkws_decl__item__wsd_test (projectee : ws_decl) : ws_name_test=
  match projectee with | { wsd_test; wsd_strip;_} -> wsd_test
let __proj__Mkws_decl__item__wsd_strip (projectee : ws_decl) : Prims.bool=
  match projectee with | { wsd_test; wsd_strip;_} -> wsd_strip
let parse_ws_name_test (nsctx : (Prims.string * Prims.string) Prims.list)
  (tok : Prims.string) : ws_name_test=
  if tok = "*"
  then WNT_Star
  else
    (match split_on_char 58 tok with
     | pfx::"*"::[] -> WNT_NsStar (XPath_Eval.lookup_nsctx nsctx pfx)
     | pfx::local::[] ->
         WNT_Qual ((XPath_Eval.lookup_nsctx nsctx pfx), local)
     | uu___1 -> WNT_Qual (FStar_Pervasives_Native.None, tok))
let rec ws_decls_of_tokens (strip : Prims.bool)
  (tests : Prims.string Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list) : ws_decl Prims.list=
  match tests with
  | [] -> []
  | t::rest -> { wsd_test = (parse_ws_name_test nsctx t); wsd_strip = strip }
      :: (ws_decls_of_tokens strip rest nsctx)
let rec collect_ws_decls (pfx : Prims.string)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (children : Parser_XML.xml_node Prims.list) : ws_decl Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           let instr = if is_xsl pfx tag then xsl_instr pfx tag else "" in
           if (instr = "strip-space") || (instr = "preserve-space")
           then
             (match attr_opt "elements" attrs with
              | FStar_Pervasives_Native.Some v ->
                  FStar_List_Tot_Base.append
                    (ws_decls_of_tokens (instr = "strip-space")
                       (parse_qname_list v) nsctx)
                    (collect_ws_decls pfx nsctx tl)
              | FStar_Pervasives_Native.None -> collect_ws_decls pfx nsctx tl)
           else collect_ws_decls pfx nsctx tl
       | uu___ -> collect_ws_decls pfx nsctx tl)
let wnt_specificity (t : ws_name_test) : Prims.int=
  match t with
  | WNT_Star -> Prims.int_zero
  | WNT_NsStar uu___ -> Prims.int_one
  | WNT_Qual (uu___, uu___1) -> (Prims.of_int (2))
let wnt_matches (elem_ns : Prims.string FStar_Pervasives_Native.option)
  (elem_local : Prims.string) (t : ws_name_test) : Prims.bool=
  match t with
  | WNT_Star -> true
  | WNT_NsStar ns ->
      (FStar_Pervasives_Native.uu___is_Some ns) && (ns = elem_ns)
  | WNT_Qual (ns, local) -> (ns = elem_ns) && (local = elem_local)
let rec resolve_ws_strip (decls : ws_decl Prims.list)
  (elem_ns : Prims.string FStar_Pervasives_Native.option)
  (elem_local : Prims.string)
  (best : (Prims.int * Prims.bool) FStar_Pervasives_Native.option) :
  Prims.bool=
  match decls with
  | [] ->
      (match best with
       | FStar_Pervasives_Native.Some (uu___, s) -> s
       | FStar_Pervasives_Native.None -> false)
  | d::rest ->
      if wnt_matches elem_ns elem_local d.wsd_test
      then
        let sp = wnt_specificity d.wsd_test in
        let best' =
          match best with
          | FStar_Pervasives_Native.None ->
              FStar_Pervasives_Native.Some (sp, (d.wsd_strip))
          | FStar_Pervasives_Native.Some (bsp, uu___) ->
              if sp >= bsp
              then FStar_Pervasives_Native.Some (sp, (d.wsd_strip))
              else best in
        resolve_ws_strip rest elem_ns elem_local best'
      else resolve_ws_strip rest elem_ns elem_local best
let source_elem_identity (nsctx : (Prims.string * Prims.string) Prims.list)
  (tag : Prims.string) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string)=
  ((XPath_Eval.lookup_nsctx nsctx (name_prefix tag)), (local_name tag))
let rec strip_ws_source_node (decls : ws_decl Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (space_here : Prims.bool) (n : Parser_XML.xml_node) : Parser_XML.xml_node=
  match n with
  | Parser_XML.XElement (tag, attrs, kids) ->
      let nsctx' = FStar_List_Tot_Base.append (build_nsctx attrs) nsctx in
      let space' = xml_space_here attrs space_here in
      let uu___ = source_elem_identity nsctx' tag in
      (match uu___ with
       | (ns, local) ->
           let strip_here =
             resolve_ws_strip decls ns local FStar_Pervasives_Native.None in
           Parser_XML.XElement
             (tag, attrs,
               (strip_ws_source_nodes decls nsctx' space' strip_here kids)))
  | other -> other
and strip_ws_source_nodes (decls : ws_decl Prims.list)
  (nsctx : (Prims.string * Prims.string) Prims.list)
  (space_here : Prims.bool) (strip_here : Prims.bool)
  (nodes : Parser_XML.xml_node Prims.list) : Parser_XML.xml_node Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      (match text_or_cdata hd with
       | FStar_Pervasives_Native.Some uu___ ->
           if
             (strip_here && (Prims.op_Negation space_here)) &&
               (run_is_all_ws nodes)
           then strip_ws_source_nodes decls nsctx space_here strip_here tl
           else hd ::
             (strip_ws_source_nodes decls nsctx space_here strip_here tl)
       | FStar_Pervasives_Native.None ->
           ((match hd with
             | Parser_XML.XElement (uu___, uu___1, uu___2) ->
                 strip_ws_source_node decls nsctx space_here hd
             | other -> other))
           :: (strip_ws_source_nodes decls nsctx space_here strip_here tl))
let strip_source_whitespace_simple (stylesheet : Parser_XML.xml_node)
  (root : Parser_XML.xml_node) : Parser_XML.xml_node=
  match stylesheet with
  | Parser_XML.XElement (tag, attrs, children) ->
      let pfx = xsl_prefix_of stylesheet in
      if
        (is_xsl pfx tag) &&
          (let ln = xsl_instr pfx tag in
           (ln = "stylesheet") || (ln = "transform"))
      then
        (match collect_ws_decls pfx (build_nsctx attrs) children with
         | [] -> root
         | decls -> strip_ws_source_node decls [] false root)
      else root
  | uu___ -> root
let strip_source_whitespace_units
  (units : (Prims.int * Parser_XML.xml_node Prims.list) Prims.list)
  (root_pfx : Prims.string)
  (root_attrs : Parser_XML.xml_attribute Prims.list)
  (root : Parser_XML.xml_node) : Parser_XML.xml_node=
  let all_children_desc =
    FStar_List_Tot_Base.flatten
      (FStar_List_Tot_Base.map FStar_Pervasives_Native.snd
         (FStar_List_Tot_Base.rev units)) in
  match collect_ws_decls root_pfx (build_nsctx root_attrs) all_children_desc
  with
  | [] -> root
  | decls -> strip_ws_source_node decls [] false root
let rec replace_doc_root (kids : Parser_XML.xml_node Prims.list)
  (new_root : Parser_XML.xml_node) : Parser_XML.xml_node Prims.list=
  match kids with
  | [] -> []
  | (Parser_XML.XElement (uu___, uu___1, uu___2))::tl -> new_root :: tl
  | hd::tl -> hd :: (replace_doc_root tl new_root)
let rec collect_globals (fuel : Prims.nat) (st : xstyle)
  (children : Parser_XML.xml_node Prims.list) (source : Parser_XML.xml_node)
  (doc_kids : Parser_XML.xml_node Prims.list) :
  (Prims.string * XPath_Eval.xp_value) Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match children with
     | [] -> []
     | hd::tl ->
         (match hd with
          | Parser_XML.XElement (tag, attrs, body) ->
              if
                (is_xsl st.xs_pfx tag) &&
                  (let ln = xsl_instr st.xs_pfx tag in
                   (ln = "variable") || (ln = "param"))
              then
                (match ((attr_opt "select" attrs), (attr_opt "name" attrs))
                 with
                 | (FStar_Pervasives_Native.Some sel,
                    FStar_Pervasives_Native.Some nm) ->
                     let v =
                       eval_val_dn (D_Doc (source, doc_kids)) Prims.int_one
                         Prims.int_one [] st.xs_nsctx st.xs_id_attrs
                         XPath_Eval.xnode_none st.xs_decfmts [] sel in
                     (nm, v) ::
                       (collect_globals (fuel - Prims.int_one) st tl source
                          doc_kids)
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.Some nm) ->
                     let frag =
                       instantiate_seq (fuel - Prims.int_one) st
                         (D_Doc (source, doc_kids)) Prims.int_one
                         Prims.int_one [] [] "" Prims.int_zero body in
                     let sval = text_value_nodes (only_nodes frag) in
                     (nm, (XPath_Eval.XV_Str sval)) ::
                       (collect_globals (fuel - Prims.int_one) st tl source
                          doc_kids)
                 | (uu___1, uu___2) ->
                     collect_globals (fuel - Prims.int_one) st tl source
                       doc_kids)
              else
                collect_globals (fuel - Prims.int_one) st tl source doc_kids
          | uu___1 ->
              collect_globals (fuel - Prims.int_one) st tl source doc_kids))
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
let rec collect_href_directives (pfx : Prims.string)
  (children : Parser_XML.xml_node Prims.list) :
  (Prims.bool * Prims.string) Prims.list=
  match children with
  | [] -> []
  | hd::tl ->
      (match hd with
       | Parser_XML.XElement (tag, attrs, uu___) ->
           if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "import")
           then
             (match attr_opt "href" attrs with
              | FStar_Pervasives_Native.Some h -> (true, h) ::
                  (collect_href_directives pfx tl)
              | FStar_Pervasives_Native.None ->
                  collect_href_directives pfx tl)
           else
             if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "include")
             then
               (match attr_opt "href" attrs with
                | FStar_Pervasives_Native.Some h -> (false, h) ::
                    (collect_href_directives pfx tl)
                | FStar_Pervasives_Native.None ->
                    collect_href_directives pfx tl)
             else collect_href_directives pfx tl
       | uu___ -> collect_href_directives pfx tl)
let stylesheet_href_directives (root : Parser_XML.xml_node) :
  (Prims.bool * Prims.string) Prims.list=
  match root with
  | Parser_XML.XElement (tag, attrs, children) ->
      let pfx = xsl_prefix_of root in
      if
        (is_xsl pfx tag) &&
          (let ln = xsl_instr pfx tag in
           (ln = "stylesheet") || (ln = "transform"))
      then collect_href_directives pfx children
      else []
  | uu___ -> []
type sheet_tree =
  | Sheet_Node of Parser_XML.xml_node * sheet_tree Prims.list * sheet_tree
  Prims.list 
let uu___is_Sheet_Node (projectee : sheet_tree) : Prims.bool= true
let __proj__Sheet_Node__item__root (projectee : sheet_tree) :
  Parser_XML.xml_node=
  match projectee with | Sheet_Node (root, includes, imports) -> root
let __proj__Sheet_Node__item__includes (projectee : sheet_tree) :
  sheet_tree Prims.list=
  match projectee with | Sheet_Node (root, includes, imports) -> includes
let __proj__Sheet_Node__item__imports (projectee : sheet_tree) :
  sheet_tree Prims.list=
  match projectee with | Sheet_Node (root, includes, imports) -> imports
let rec sheet_tree_xml_count (t : sheet_tree) : Prims.nat=
  match t with
  | Sheet_Node (root, incs, imps) ->
      ((XPath_Eval.xml_node_count root) + (sheet_tree_list_xml_count incs)) +
        (sheet_tree_list_xml_count imps)
and sheet_tree_list_xml_count (ts : sheet_tree Prims.list) : Prims.nat=
  match ts with
  | [] -> Prims.int_zero
  | hd::tl -> (sheet_tree_xml_count hd) + (sheet_tree_list_xml_count tl)
let rec process_node (fuel : Prims.nat) (counter : Prims.int)
  (t : sheet_tree) :
  (Prims.int * (Prims.int * Parser_XML.xml_node Prims.list) Prims.list)=
  if fuel = Prims.int_zero
  then (counter, [])
  else
    (match t with
     | Sheet_Node (root, includes, imports) ->
         let pfx = xsl_prefix_of root in
         (match root with
          | Parser_XML.XElement (tag, attrs, children) ->
              if
                (is_xsl pfx tag) &&
                  (let ln = xsl_instr pfx tag in
                   (ln = "stylesheet") || (ln = "transform"))
              then
                let uu___1 =
                  process_children (fuel - Prims.int_one) counter pfx
                    children includes imports in
                (match uu___1 with
                 | (counter1, ordinary, import_units) ->
                     let my_prec = counter1 + Prims.int_one in
                     (my_prec,
                       (FStar_List_Tot_Base.append import_units
                          [(my_prec, ordinary)])))
              else (counter, [])
          | uu___1 -> (counter, [])))
and process_children (fuel : Prims.nat) (counter : Prims.int)
  (pfx : Prims.string) (children : Parser_XML.xml_node Prims.list)
  (includes : sheet_tree Prims.list) (imports : sheet_tree Prims.list) :
  (Prims.int * Parser_XML.xml_node Prims.list * (Prims.int *
    Parser_XML.xml_node Prims.list) Prims.list)=
  if fuel = Prims.int_zero
  then (counter, [], [])
  else
    (match children with
     | [] -> (counter, [], [])
     | hd::tl ->
         (match hd with
          | Parser_XML.XElement (tag, attrs, uu___1) ->
              if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "include")
              then
                (match includes with
                 | [] ->
                     process_children (fuel - Prims.int_one) counter pfx tl
                       [] imports
                 | inc::more_incs ->
                     let uu___2 =
                       expand_include (fuel - Prims.int_one) counter inc in
                     (match uu___2 with
                      | (counter1, sub_ordinary, sub_units) ->
                          let uu___3 =
                            process_children (fuel - Prims.int_one) counter1
                              pfx tl more_incs imports in
                          (match uu___3 with
                           | (counter2, rest_ordinary, rest_units) ->
                               (counter2,
                                 (FStar_List_Tot_Base.append sub_ordinary
                                    rest_ordinary),
                                 (FStar_List_Tot_Base.append sub_units
                                    rest_units)))))
              else
                if (is_xsl pfx tag) && ((xsl_instr pfx tag) = "import")
                then
                  (match imports with
                   | [] ->
                       process_children (fuel - Prims.int_one) counter pfx tl
                         includes []
                   | imp::more_imps ->
                       let uu___3 =
                         process_node (fuel - Prims.int_one) counter imp in
                       (match uu___3 with
                        | (counter1, imp_units) ->
                            let uu___4 =
                              process_children (fuel - Prims.int_one)
                                counter1 pfx tl includes more_imps in
                            (match uu___4 with
                             | (counter2, rest_ordinary, rest_units) ->
                                 (counter2, rest_ordinary,
                                   (FStar_List_Tot_Base.append imp_units
                                      rest_units)))))
                else
                  (let uu___4 =
                     process_children (fuel - Prims.int_one) counter pfx tl
                       includes imports in
                   match uu___4 with
                   | (counter1, rest_ordinary, rest_units) ->
                       (counter1, (hd :: rest_ordinary), rest_units))
          | uu___1 ->
              let uu___2 =
                process_children (fuel - Prims.int_one) counter pfx tl
                  includes imports in
              (match uu___2 with
               | (counter1, rest_ordinary, rest_units) ->
                   (counter1, (hd :: rest_ordinary), rest_units))))
and expand_include (fuel : Prims.nat) (counter : Prims.int) (t : sheet_tree)
  :
  (Prims.int * Parser_XML.xml_node Prims.list * (Prims.int *
    Parser_XML.xml_node Prims.list) Prims.list)=
  if fuel = Prims.int_zero
  then (counter, [], [])
  else
    (match t with
     | Sheet_Node (root, includes, imports) ->
         let pfx = xsl_prefix_of root in
         (match root with
          | Parser_XML.XElement (tag, attrs, children) ->
              if
                (is_xsl pfx tag) &&
                  (let ln = xsl_instr pfx tag in
                   (ln = "stylesheet") || (ln = "transform"))
              then
                process_children (fuel - Prims.int_one) counter pfx children
                  includes imports
              else (counter, [], [])
          | uu___1 -> (counter, [], [])))
let sheet_units (t : sheet_tree) :
  (Prims.int * Parser_XML.xml_node Prims.list) Prims.list=
  let fuel =
    ((Prims.of_int (4)) * ((sheet_tree_xml_count t) + Prims.int_one)) +
      (Prims.of_int (1000)) in
  let uu___ = process_node fuel Prims.int_zero t in
  match uu___ with | (uu___1, units) -> units
let build_style_from_units
  (units : (Prims.int * Parser_XML.xml_node Prims.list) Prims.list)
  (root_pfx : Prims.string)
  (root_attrs : Parser_XML.xml_attribute Prims.list)
  (root_node : Parser_XML.xml_node) (source : Parser_XML.xml_node)
  (doc_kids : Parser_XML.xml_node Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list) : xstyle=
  let nsctx = build_nsctx root_attrs in
  let units_desc = FStar_List_Tot_Base.rev units in
  let all_children_desc =
    FStar_List_Tot_Base.flatten
      (FStar_List_Tot_Base.map FStar_Pervasives_Native.snd units_desc) in
  let decfmts = collect_decimal_formats root_pfx all_children_desc in
  let out_settings =
    collect_output_settings root_pfx nsctx all_children_desc
      default_output_settings in
  let key_decls = collect_keys root_pfx all_children_desc in
  let key_table =
    match key_decls with
    | [] -> []
    | uu___ ->
        build_key_table nsctx id_attrs root_node decfmts key_decls
          (XPath_Eval.all_document_items
             (XPath_Eval.CI_Elem ([], [], source))) in
  let st0 =
    {
      xs_pfx = root_pfx;
      xs_templates =
        (FStar_List_Tot_Base.concatMap
           (fun pc ->
              collect_templates_prec root_pfx
                (FStar_Pervasives_Native.fst pc)
                (FStar_Pervasives_Native.snd pc)) units);
      xs_attrsets = (collect_attribute_sets root_pfx all_children_desc);
      xs_method =
        (if out_settings.os_method_raw = "text" then "text" else "xml");
      xs_output_present = (any_output_decl root_pfx all_children_desc);
      xs_output = out_settings;
      xs_globals = [];
      xs_nsscope = (build_nsscope root_attrs);
      xs_nsctx = nsctx;
      xs_id_attrs = id_attrs;
      xs_style_root = root_node;
      xs_decfmts = decfmts;
      xs_key_table = key_table
    } in
  let gfuel =
    ((Prims.of_int (4)) *
       ((XPath_Eval.xml_nodes_count all_children_desc) + Prims.int_one))
      + (Prims.of_int (1000)) in
  {
    xs_pfx = (st0.xs_pfx);
    xs_templates = (st0.xs_templates);
    xs_attrsets = (st0.xs_attrsets);
    xs_method = (st0.xs_method);
    xs_output_present = (st0.xs_output_present);
    xs_output = (st0.xs_output);
    xs_globals =
      (collect_globals gfuel st0 all_children_desc source doc_kids);
    xs_nsscope = (st0.xs_nsscope);
    xs_nsctx = (st0.xs_nsctx);
    xs_id_attrs = (st0.xs_id_attrs);
    xs_style_root = (st0.xs_style_root);
    xs_decfmts = (st0.xs_decfmts);
    xs_key_table = (st0.xs_key_table)
  }
let build_style (stylesheet : Parser_XML.xml_node)
  (source : Parser_XML.xml_node) (doc_kids : Parser_XML.xml_node Prims.list)
  (id_attrs : (Prims.string * Prims.string) Prims.list) : xstyle=
  match stylesheet with
  | Parser_XML.XElement (tag, attrs, children) ->
      let pfx = xsl_prefix_of stylesheet in
      if
        (is_xsl pfx tag) &&
          (let ln = xsl_instr pfx tag in
           (ln = "stylesheet") || (ln = "transform"))
      then
        let nsctx = build_nsctx attrs in
        let decfmts = collect_decimal_formats pfx children in
        let out_settings =
          collect_output_settings pfx nsctx children default_output_settings in
        let key_decls = collect_keys pfx children in
        let key_table =
          match key_decls with
          | [] -> []
          | uu___ ->
              build_key_table nsctx id_attrs stylesheet decfmts key_decls
                (XPath_Eval.all_document_items
                   (XPath_Eval.CI_Elem ([], [], source))) in
        let st0 =
          {
            xs_pfx = pfx;
            xs_templates = (collect_templates pfx children);
            xs_attrsets = (collect_attribute_sets pfx children);
            xs_method =
              (if out_settings.os_method_raw = "text" then "text" else "xml");
            xs_output_present = (any_output_decl pfx children);
            xs_output = out_settings;
            xs_globals = [];
            xs_nsscope = (build_nsscope attrs);
            xs_nsctx = nsctx;
            xs_id_attrs = id_attrs;
            xs_style_root = stylesheet;
            xs_decfmts = decfmts;
            xs_key_table = key_table
          } in
        let gfuel =
          ((Prims.of_int (4)) *
             ((XPath_Eval.xml_nodes_count children) + Prims.int_one))
            + (Prims.of_int (1000)) in
        {
          xs_pfx = (st0.xs_pfx);
          xs_templates = (st0.xs_templates);
          xs_attrsets = (st0.xs_attrsets);
          xs_method = (st0.xs_method);
          xs_output_present = (st0.xs_output_present);
          xs_output = (st0.xs_output);
          xs_globals = (collect_globals gfuel st0 children source doc_kids);
          xs_nsscope = (st0.xs_nsscope);
          xs_nsctx = (st0.xs_nsctx);
          xs_id_attrs = (st0.xs_id_attrs);
          xs_style_root = (st0.xs_style_root);
          xs_decfmts = (st0.xs_decfmts);
          xs_key_table = (st0.xs_key_table)
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
               tpl_body = [stylesheet];
               tpl_import_prec = Prims.int_zero
             }];
          xs_attrsets = [];
          xs_method = "xml";
          xs_output_present = false;
          xs_output = default_output_settings;
          xs_globals = [];
          xs_nsscope = [];
          xs_nsctx = (build_nsctx attrs);
          xs_id_attrs = id_attrs;
          xs_style_root = stylesheet;
          xs_decfmts = [];
          xs_key_table = []
        }
  | uu___ ->
      {
        xs_pfx = "xsl";
        xs_templates = [];
        xs_attrsets = [];
        xs_method = "xml";
        xs_output_present = false;
        xs_output = default_output_settings;
        xs_globals = [];
        xs_nsscope = [];
        xs_nsctx = [];
        xs_id_attrs = id_attrs;
        xs_style_root = stylesheet;
        xs_decfmts = [];
        xs_key_table = []
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
let make_decl (cfg : output_settings) : Prims.string=
  let ver = if cfg.os_version = "" then "1.0" else cfg.os_version in
  let enc = if cfg.os_encoding = "" then "UTF-8" else cfg.os_encoding in
  let standalone_part =
    if cfg.os_standalone = ""
    then ""
    else FStar_String.concat "" [" standalone=\""; cfg.os_standalone; "\""] in
  FStar_String.concat ""
    ["<?xml version=\"";
    ver;
    "\" encoding=\"";
    enc;
    "\"";
    standalone_part;
    "?>\n"]
let rec root_tag_of (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match nodes with
  | [] -> FStar_Pervasives_Native.None
  | (Parser_XML.XElement (t, uu___, uu___1))::uu___2 ->
      FStar_Pervasives_Native.Some t
  | uu___::rest -> root_tag_of rest
let implicit_html_root (nodes : Parser_XML.xml_node Prims.list) : Prims.bool=
  match root_tag_of nodes with
  | FStar_Pervasives_Native.Some tag ->
      ((XPath_Eval.prefix_of tag) = "") &&
        ((ascii_lower_str (XPath_Eval.local_name_of tag)) = "html")
  | FStar_Pervasives_Native.None -> false
let make_doctype (is_html : Prims.bool) (cfg : output_settings)
  (nodes : Parser_XML.xml_node Prims.list) : Prims.string=
  if is_html
  then
    (if (cfg.os_doctype_system = "") && (cfg.os_doctype_public = "")
     then ""
     else
       (let tag = "HTML" in
        if (cfg.os_doctype_public <> "") && (cfg.os_doctype_system <> "")
        then
          FStar_String.concat ""
            ["<!DOCTYPE ";
            tag;
            " PUBLIC \"";
            cfg.os_doctype_public;
            "\" \"";
            cfg.os_doctype_system;
            "\">\n"]
        else
          if cfg.os_doctype_public <> ""
          then
            FStar_String.concat ""
              ["<!DOCTYPE ";
              tag;
              " PUBLIC \"";
              cfg.os_doctype_public;
              "\">\n"]
          else
            FStar_String.concat ""
              ["<!DOCTYPE ";
              tag;
              " SYSTEM \"";
              cfg.os_doctype_system;
              "\">\n"]))
  else
    if cfg.os_doctype_system = ""
    then ""
    else
      (match root_tag_of nodes with
       | FStar_Pervasives_Native.None -> ""
       | FStar_Pervasives_Native.Some tag ->
           if cfg.os_doctype_public <> ""
           then
             FStar_String.concat ""
               ["<!DOCTYPE ";
               tag;
               " PUBLIC \"";
               cfg.os_doctype_public;
               "\" \"";
               cfg.os_doctype_system;
               "\">\n"]
           else
             FStar_String.concat ""
               ["<!DOCTYPE ";
               tag;
               " SYSTEM \"";
               cfg.os_doctype_system;
               "\">\n"])
let is_meta_content_type (n : Parser_XML.xml_node) : Prims.bool=
  match n with
  | Parser_XML.XElement (tag, attrs, uu___) ->
      ((ascii_lower_str (XPath_Eval.local_name_of tag)) = "meta") &&
        ((match attr_opt "http-equiv" attrs with
          | FStar_Pervasives_Native.Some v ->
              (ascii_lower_str v) = "content-type"
          | FStar_Pervasives_Native.None -> false))
  | uu___ -> false
let rec has_meta_content_type (kids : Parser_XML.xml_node Prims.list) :
  Prims.bool=
  match kids with
  | [] -> false
  | hd::tl ->
      if is_meta_content_type hd then true else has_meta_content_type tl
let make_meta_elem (encoding : Prims.string) : Parser_XML.xml_node=
  Parser_XML.XElement
    ("meta",
      [{
         Parser_XML.attr_name = "http-equiv";
         Parser_XML.attr_value = "Content-Type"
       };
      {
        Parser_XML.attr_name = "content";
        Parser_XML.attr_value =
          (FStar_String.concat "" ["text/html; charset="; encoding])
      }], [])
let rec inject_meta_in_elem (encoding : Prims.string)
  (n : Parser_XML.xml_node) : (Parser_XML.xml_node * Prims.bool)=
  match n with
  | Parser_XML.XElement (tag, attrs, children) ->
      if (ascii_lower_str (XPath_Eval.local_name_of tag)) = "head"
      then
        let children' =
          if has_meta_content_type children
          then children
          else (make_meta_elem encoding) :: children in
        ((Parser_XML.XElement (tag, attrs, children')), true)
      else
        (let uu___1 = inject_meta_in_list encoding children in
         match uu___1 with
         | (children', found) ->
             ((Parser_XML.XElement (tag, attrs, children')), found))
  | uu___ -> (n, false)
and inject_meta_in_list (encoding : Prims.string)
  (kids : Parser_XML.xml_node Prims.list) :
  (Parser_XML.xml_node Prims.list * Prims.bool)=
  match kids with
  | [] -> ([], false)
  | hd::tl ->
      let uu___ = inject_meta_in_elem encoding hd in
      (match uu___ with
       | (hd', found) ->
           if found
           then ((hd' :: tl), true)
           else
             (let uu___2 = inject_meta_in_list encoding tl in
              match uu___2 with | (tl', found2) -> ((hd' :: tl'), found2)))
let html_inject_meta (encoding : Prims.string)
  (nodes : Parser_XML.xml_node Prims.list) : Parser_XML.xml_node Prims.list=
  FStar_Pervasives_Native.fst (inject_meta_in_list encoding nodes)
let finalize_output (present : Prims.bool) (cfg : output_settings)
  (method1 : Prims.string) (nodes : Parser_XML.xml_node Prims.list) :
  Prims.string=
  if method1 = "text"
  then text_value_nodes nodes
  else
    if Prims.op_Negation present
    then serialize_nodes default_ser_settings [] nodes
    else
      (let is_html =
         (cfg.os_method_raw = "html") ||
           ((cfg.os_method_raw = "") && (implicit_html_root nodes)) in
       let indent_on =
         if cfg.os_indent_raw = "yes"
         then true
         else if cfg.os_indent_raw = "no" then false else is_html in
       let ser =
         {
           ser_cdata = (cfg.os_cdata);
           ser_indent = indent_on;
           ser_encoding = (cfg.os_encoding);
           ser_html = is_html
         } in
       let charset =
         if cfg.os_encoding = "" then "UTF-8" else cfg.os_encoding in
       let nodes' = if is_html then html_inject_meta charset nodes else nodes in
       let body = serialize_nodes ser [] nodes' in
       let decl = if cfg.os_omit_decl then "" else make_decl cfg in
       let doctype = make_doctype is_html cfg nodes in
       FStar_String.concat "" [decl; doctype; body])
let transform (stylesheet : Parser_XML.xml_node)
  (source : Parser_XML.xml_node) : Prims.string=
  let source' = strip_source_whitespace_simple stylesheet source in
  let st = build_style stylesheet source' [source'] [] in
  let sz =
    (XPath_Eval.xml_node_count stylesheet) +
      (XPath_Eval.xml_node_count source') in
  let fuel =
    ((sz + Prims.int_one) * (Prims.of_int (256))) +
      (Prims.parse_int "100000") in
  let result =
    dispatch fuel st (D_Doc (source', [source'])) Prims.int_one Prims.int_one
      "" st.xs_globals [] in
  let nodes = only_nodes result in
  finalize_output st.xs_output_present st.xs_output st.xs_method nodes
let transform_doc (stylesheet : Parser_XML.xml_node)
  (source_kids : Parser_XML.xml_node Prims.list) : Prims.string=
  match doc_root_elem source_kids with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some root ->
      let root' = strip_source_whitespace_simple stylesheet root in
      let source_kids' = replace_doc_root source_kids root' in
      let st = build_style stylesheet root' source_kids' [] in
      let sz =
        (XPath_Eval.xml_node_count stylesheet) +
          (xml_nodes_count_sum source_kids') in
      let fuel =
        ((sz + Prims.int_one) * (Prims.of_int (256))) +
          (Prims.parse_int "100000") in
      let result =
        dispatch fuel st (D_Doc (root', source_kids')) Prims.int_one
          Prims.int_one "" st.xs_globals [] in
      let nodes = only_nodes result in
      finalize_output st.xs_output_present st.xs_output st.xs_method nodes
let transform_doc_ids (stylesheet : Parser_XML.xml_node)
  (source_kids : Parser_XML.xml_node Prims.list)
  (source_id_attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string=
  match doc_root_elem source_kids with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some root ->
      let root' = strip_source_whitespace_simple stylesheet root in
      let source_kids' = replace_doc_root source_kids root' in
      let st = build_style stylesheet root' source_kids' source_id_attrs in
      let sz =
        (XPath_Eval.xml_node_count stylesheet) +
          (xml_nodes_count_sum source_kids') in
      let fuel =
        ((sz + Prims.int_one) * (Prims.of_int (256))) +
          (Prims.parse_int "100000") in
      let result =
        dispatch fuel st (D_Doc (root', source_kids')) Prims.int_one
          Prims.int_one "" st.xs_globals [] in
      let nodes = only_nodes result in
      finalize_output st.xs_output_present st.xs_output st.xs_method nodes
let transform_doc_ids_merged (t : sheet_tree)
  (source_kids : Parser_XML.xml_node Prims.list)
  (source_id_attrs : (Prims.string * Prims.string) Prims.list) :
  Prims.string=
  match doc_root_elem source_kids with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some root ->
      (match t with
       | Sheet_Node (root_style_node, uu___, uu___1) ->
           let root_pfx = xsl_prefix_of root_style_node in
           let root_attrs = Parser_XML.element_attrs root_style_node in
           let units = sheet_units t in
           let root' =
             strip_source_whitespace_units units root_pfx root_attrs root in
           let source_kids' = replace_doc_root source_kids root' in
           let st =
             build_style_from_units units root_pfx root_attrs root_style_node
               root' source_kids' source_id_attrs in
           let sz =
             (sheet_tree_xml_count t) + (xml_nodes_count_sum source_kids') in
           let fuel =
             ((sz + Prims.int_one) * (Prims.of_int (256))) +
               (Prims.parse_int "100000") in
           let result =
             dispatch fuel st (D_Doc (root', source_kids')) Prims.int_one
               Prims.int_one "" st.xs_globals [] in
           let nodes = only_nodes result in
           finalize_output st.xs_output_present st.xs_output st.xs_method
             nodes)
