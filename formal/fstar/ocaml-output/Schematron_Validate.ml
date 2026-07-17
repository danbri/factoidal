open Prims
type sch_assertion =
  {
  sa_is_assert: Prims.bool ;
  sa_test: Prims.string ;
  sa_message: Prims.string }
let __proj__Mksch_assertion__item__sa_is_assert (projectee : sch_assertion) :
  Prims.bool=
  match projectee with
  | { sa_is_assert; sa_test; sa_message;_} -> sa_is_assert
let __proj__Mksch_assertion__item__sa_test (projectee : sch_assertion) :
  Prims.string=
  match projectee with | { sa_is_assert; sa_test; sa_message;_} -> sa_test
let __proj__Mksch_assertion__item__sa_message (projectee : sch_assertion) :
  Prims.string=
  match projectee with | { sa_is_assert; sa_test; sa_message;_} -> sa_message
type sch_let = {
  sl_name: Prims.string ;
  sl_value: Prims.string }
let __proj__Mksch_let__item__sl_name (projectee : sch_let) : Prims.string=
  match projectee with | { sl_name; sl_value;_} -> sl_name
let __proj__Mksch_let__item__sl_value (projectee : sch_let) : Prims.string=
  match projectee with | { sl_name; sl_value;_} -> sl_value
type sch_rule =
  {
  sr_context: Prims.string ;
  sr_lets: sch_let Prims.list ;
  sr_asserts: sch_assertion Prims.list }
let __proj__Mksch_rule__item__sr_context (projectee : sch_rule) :
  Prims.string=
  match projectee with | { sr_context; sr_lets; sr_asserts;_} -> sr_context
let __proj__Mksch_rule__item__sr_lets (projectee : sch_rule) :
  sch_let Prims.list=
  match projectee with | { sr_context; sr_lets; sr_asserts;_} -> sr_lets
let __proj__Mksch_rule__item__sr_asserts (projectee : sch_rule) :
  sch_assertion Prims.list=
  match projectee with | { sr_context; sr_lets; sr_asserts;_} -> sr_asserts
type sch_pattern = {
  sp_id: Prims.string ;
  sp_rules: sch_rule Prims.list }
let __proj__Mksch_pattern__item__sp_id (projectee : sch_pattern) :
  Prims.string= match projectee with | { sp_id; sp_rules;_} -> sp_id
let __proj__Mksch_pattern__item__sp_rules (projectee : sch_pattern) :
  sch_rule Prims.list=
  match projectee with | { sp_id; sp_rules;_} -> sp_rules
type sch_schema =
  {
  ss_ns: (Prims.string * Prims.string) Prims.list ;
  ss_lets: sch_let Prims.list ;
  ss_patterns: sch_pattern Prims.list }
let __proj__Mksch_schema__item__ss_ns (projectee : sch_schema) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { ss_ns; ss_lets; ss_patterns;_} -> ss_ns
let __proj__Mksch_schema__item__ss_lets (projectee : sch_schema) :
  sch_let Prims.list=
  match projectee with | { ss_ns; ss_lets; ss_patterns;_} -> ss_lets
let __proj__Mksch_schema__item__ss_patterns (projectee : sch_schema) :
  sch_pattern Prims.list=
  match projectee with | { ss_ns; ss_lets; ss_patterns;_} -> ss_patterns
type finding =
  | Assert_fail of Prims.string * Prims.string * Prims.string * Prims.string
  
  | Report_hit of Prims.string * Prims.string * Prims.string * Prims.string 
  | Indeterminate of Prims.string * Prims.string * Prims.string *
  Prims.string * Prims.string 
let uu___is_Assert_fail (projectee : finding) : Prims.bool=
  match projectee with
  | Assert_fail (ctx, test, msg, path) -> true
  | uu___ -> false
let __proj__Assert_fail__item__ctx (projectee : finding) : Prims.string=
  match projectee with | Assert_fail (ctx, test, msg, path) -> ctx
let __proj__Assert_fail__item__test (projectee : finding) : Prims.string=
  match projectee with | Assert_fail (ctx, test, msg, path) -> test
let __proj__Assert_fail__item__msg (projectee : finding) : Prims.string=
  match projectee with | Assert_fail (ctx, test, msg, path) -> msg
let __proj__Assert_fail__item__path (projectee : finding) : Prims.string=
  match projectee with | Assert_fail (ctx, test, msg, path) -> path
let uu___is_Report_hit (projectee : finding) : Prims.bool=
  match projectee with
  | Report_hit (ctx, test, msg, path) -> true
  | uu___ -> false
let __proj__Report_hit__item__ctx (projectee : finding) : Prims.string=
  match projectee with | Report_hit (ctx, test, msg, path) -> ctx
let __proj__Report_hit__item__test (projectee : finding) : Prims.string=
  match projectee with | Report_hit (ctx, test, msg, path) -> test
let __proj__Report_hit__item__msg (projectee : finding) : Prims.string=
  match projectee with | Report_hit (ctx, test, msg, path) -> msg
let __proj__Report_hit__item__path (projectee : finding) : Prims.string=
  match projectee with | Report_hit (ctx, test, msg, path) -> path
let uu___is_Indeterminate (projectee : finding) : Prims.bool=
  match projectee with
  | Indeterminate (ctx, test, msg, path, reason) -> true
  | uu___ -> false
let __proj__Indeterminate__item__ctx (projectee : finding) : Prims.string=
  match projectee with | Indeterminate (ctx, test, msg, path, reason) -> ctx
let __proj__Indeterminate__item__test (projectee : finding) : Prims.string=
  match projectee with | Indeterminate (ctx, test, msg, path, reason) -> test
let __proj__Indeterminate__item__msg (projectee : finding) : Prims.string=
  match projectee with | Indeterminate (ctx, test, msg, path, reason) -> msg
let __proj__Indeterminate__item__path (projectee : finding) : Prims.string=
  match projectee with | Indeterminate (ctx, test, msg, path, reason) -> path
let __proj__Indeterminate__item__reason (projectee : finding) : Prims.string=
  match projectee with
  | Indeterminate (ctx, test, msg, path, reason) -> reason
let finding_kind (f : finding) : Prims.string=
  match f with
  | Assert_fail (uu___, uu___1, uu___2, uu___3) -> "assert-fail"
  | Report_hit (uu___, uu___1, uu___2, uu___3) -> "report-hit"
  | Indeterminate (uu___, uu___1, uu___2, uu___3, uu___4) -> "indeterminate"
let finding_context (f : finding) : Prims.string=
  match f with
  | Assert_fail (c, uu___, uu___1, uu___2) -> c
  | Report_hit (c, uu___, uu___1, uu___2) -> c
  | Indeterminate (c, uu___, uu___1, uu___2, uu___3) -> c
let finding_test (f : finding) : Prims.string=
  match f with
  | Assert_fail (uu___, t, uu___1, uu___2) -> t
  | Report_hit (uu___, t, uu___1, uu___2) -> t
  | Indeterminate (uu___, t, uu___1, uu___2, uu___3) -> t
let finding_message (f : finding) : Prims.string=
  match f with
  | Assert_fail (uu___, uu___1, m, uu___2) -> m
  | Report_hit (uu___, uu___1, m, uu___2) -> m
  | Indeterminate (uu___, uu___1, m, uu___2, uu___3) -> m
let finding_path (f : finding) : Prims.string=
  match f with
  | Assert_fail (uu___, uu___1, uu___2, p) -> p
  | Report_hit (uu___, uu___1, uu___2, p) -> p
  | Indeterminate (uu___, uu___1, uu___2, p, uu___3) -> p
let rec flatmap :
  'a 'b . ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list =
  fun f xs ->
    match xs with
    | [] -> []
    | x::r -> FStar_List_Tot_Base.op_At (f x) (flatmap f r)
let attr_or_empty (name : Prims.string) (n : Parser_XML.xml_node) :
  Prims.string=
  match Parser_XML.find_attr name (Parser_XML.element_attrs n) with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None -> ""
let el_local (n : Parser_XML.xml_node) : Prims.string=
  match Parser_XML.element_tag n with
  | FStar_Pervasives_Native.Some t -> XSLT_Transform.local_name t
  | FStar_Pervasives_Native.None -> ""
let el_is (lname : Prims.string) (n : Parser_XML.xml_node) : Prims.bool=
  (el_local n) = lname
let assertion_of (n : Parser_XML.xml_node) :
  sch_assertion FStar_Pervasives_Native.option=
  if el_is "assert" n
  then
    FStar_Pervasives_Native.Some
      {
        sa_is_assert = true;
        sa_test = (attr_or_empty "test" n);
        sa_message = (Parser_XML.text_content n)
      }
  else
    if el_is "report" n
    then
      FStar_Pervasives_Native.Some
        {
          sa_is_assert = false;
          sa_test = (attr_or_empty "test" n);
          sa_message = (Parser_XML.text_content n)
        }
    else FStar_Pervasives_Native.None
let rec collect_assertions (nodes : Parser_XML.xml_node Prims.list) :
  sch_assertion Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      (match assertion_of hd with
       | FStar_Pervasives_Native.Some a -> a :: (collect_assertions tl)
       | FStar_Pervasives_Native.None -> collect_assertions tl)
let let_of (n : Parser_XML.xml_node) :
  sch_let FStar_Pervasives_Native.option=
  if el_is "let" n
  then
    FStar_Pervasives_Native.Some
      {
        sl_name = (attr_or_empty "name" n);
        sl_value = (attr_or_empty "value" n)
      }
  else FStar_Pervasives_Native.None
let rec collect_lets (nodes : Parser_XML.xml_node Prims.list) :
  sch_let Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      (match let_of hd with
       | FStar_Pervasives_Native.Some l -> l :: (collect_lets tl)
       | FStar_Pervasives_Native.None -> collect_lets tl)
let rule_of (n : Parser_XML.xml_node) : sch_rule=
  let kids = Parser_XML.element_children n in
  {
    sr_context = (attr_or_empty "context" n);
    sr_lets = (collect_lets kids);
    sr_asserts = (collect_assertions kids)
  }
let rec collect_rules (nodes : Parser_XML.xml_node Prims.list) :
  sch_rule Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      if el_is "rule" hd
      then (rule_of hd) :: (collect_rules tl)
      else collect_rules tl
let pattern_of (n : Parser_XML.xml_node) : sch_pattern=
  {
    sp_id = (attr_or_empty "id" n);
    sp_rules = (collect_rules (Parser_XML.element_children n))
  }
let rec collect_patterns (nodes : Parser_XML.xml_node Prims.list) :
  sch_pattern Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      if el_is "pattern" hd
      then (pattern_of hd) :: (collect_patterns tl)
      else collect_patterns tl
let rec collect_ns (nodes : Parser_XML.xml_node Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      if el_is "ns" hd
      then ((attr_or_empty "prefix" hd), (attr_or_empty "uri" hd)) ::
        (collect_ns tl)
      else collect_ns tl
let extract_schema (schema_root : Parser_XML.xml_node) : sch_schema=
  let kids = Parser_XML.element_children schema_root in
  {
    ss_ns = (collect_ns kids);
    ss_lets = (collect_lets kids);
    ss_patterns = (collect_patterns kids)
  }
let node_with_attrs (it : XPath_Eval.xctx_item) :
  XPath_Eval.xctx_item Prims.list=
  match it with
  | XPath_Eval.CI_Elem (p, anc, n) -> it ::
      (XPath_Eval.attribute_items p anc n)
  | uu___ -> [it]
let all_doc_items (root : Parser_XML.xml_node) :
  XPath_Eval.xctx_item Prims.list=
  flatmap node_with_attrs ((XPath_Eval.CI_Elem ([], [], root)) ::
    (XPath_Eval.descendant_items [] [] root))
let sch_eval (it : XPath_Eval.xctx_item)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (expr : Prims.string) : XPath_Eval.xp_value FStar_Pervasives_Native.option=
  match Parser_XPath.parse_xpath expr with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      let fuel =
        XPath_Eval.initial_eval_fuel e
          (XPath_Eval.xml_node_count (XPath_Eval.root_of_item it)) in
      let env =
        {
          XPath_Eval.env_item = it;
          XPath_Eval.env_pos = Prims.int_one;
          XPath_Eval.env_size = Prims.int_one;
          XPath_Eval.env_vars = vars;
          XPath_Eval.env_nsctx = [];
          XPath_Eval.env_doc_kids = [];
          XPath_Eval.env_id_attrs = [];
          XPath_Eval.env_style_root = XPath_Eval.xnode_none
        } in
      FStar_Pervasives_Native.Some (XPath_Eval.eval_expr fuel env e)
let context_matches (ctx : Prims.string)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (it : XPath_Eval.xctx_item) : Prims.bool=
  if (XSLT_Transform.trim_str ctx) = ""
  then false
  else
    XSLT_Transform.any_alt_matches vars [] []
      (XSLT_Transform.split_on_char 124 ctx) (XSLT_Transform.D_Item it)
let item_self_label (it : XPath_Eval.xctx_item) : Prims.string=
  match it with
  | XPath_Eval.CI_Elem (uu___, uu___1, n) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> "")
  | XPath_Eval.CI_Attr (uu___, uu___1, uu___2, a) ->
      Prims.strcat "@" a.Parser_XML.attr_name
  | XPath_Eval.CI_Text (uu___, uu___1, uu___2, uu___3) -> "text()"
  | XPath_Eval.CI_Comment (uu___, uu___1, uu___2, uu___3) -> "comment()"
  | XPath_Eval.CI_PI (uu___, uu___1, uu___2, tg, uu___3) ->
      Prims.strcat "processing-instruction()::" tg
  | XPath_Eval.CI_Namespace (uu___, uu___1, uu___2, pfx, uu___3) ->
      Prims.strcat "namespace::" pfx
let item_path (it : XPath_Eval.xctx_item) : Prims.string=
  let anc = FStar_List_Tot_Base.rev (XSLT_Transform.ancestor_tags_of it) in
  Prims.strcat "/"
    (FStar_String.concat "/"
       (FStar_List_Tot_Base.op_At anc [item_self_label it]))
let rec eval_lets (it : XPath_Eval.xctx_item)
  (base : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (lets : sch_let Prims.list) :
  (Prims.string * XPath_Eval.xp_value) Prims.list=
  match lets with
  | [] -> base
  | l::rest ->
      let v =
        match sch_eval it base l.sl_value with
        | FStar_Pervasives_Native.Some x -> x
        | FStar_Pervasives_Native.None -> XPath_Eval.XV_Str "" in
      eval_lets it (((l.sl_name), v) :: base) rest
let eval_assertion (ctx : Prims.string) (it : XPath_Eval.xctx_item)
  (vars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (a : sch_assertion) : finding Prims.list=
  match sch_eval it vars a.sa_test with
  | FStar_Pervasives_Native.None ->
      [Indeterminate
         (ctx, (a.sa_test), (a.sa_message), (item_path it),
           "test did not parse in XPath.Eval (unsupported XPath construct such as a deferred axis)")]
  | FStar_Pervasives_Native.Some v ->
      let b = XPath_Eval.to_bool_val v in
      if a.sa_is_assert
      then
        (if b
         then []
         else
           [Assert_fail (ctx, (a.sa_test), (a.sa_message), (item_path it))])
      else
        if b
        then [Report_hit (ctx, (a.sa_test), (a.sa_message), (item_path it))]
        else []
let rec first_matching_rule (rules : sch_rule Prims.list)
  (gvars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (it : XPath_Eval.xctx_item) : sch_rule FStar_Pervasives_Native.option=
  match rules with
  | [] -> FStar_Pervasives_Native.None
  | r::rest ->
      if context_matches r.sr_context gvars it
      then FStar_Pervasives_Native.Some r
      else first_matching_rule rest gvars it
let validate_item_in_pattern (rules : sch_rule Prims.list)
  (gvars : (Prims.string * XPath_Eval.xp_value) Prims.list)
  (it : XPath_Eval.xctx_item) : finding Prims.list=
  match first_matching_rule rules gvars it with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some r ->
      let rvars = eval_lets it gvars r.sr_lets in
      flatmap (fun a -> eval_assertion r.sr_context it rvars a) r.sr_asserts
let validate_pattern (pat : sch_pattern)
  (items : XPath_Eval.xctx_item Prims.list)
  (gvars : (Prims.string * XPath_Eval.xp_value) Prims.list) :
  finding Prims.list=
  flatmap (fun it -> validate_item_in_pattern pat.sp_rules gvars it) items
let validate (schema_root : Parser_XML.xml_node)
  (instance_root : Parser_XML.xml_node) : finding Prims.list=
  let sch = extract_schema schema_root in
  let items = all_doc_items instance_root in
  let gvars =
    eval_lets (XPath_Eval.CI_Elem ([], [], instance_root)) [] sch.ss_lets in
  flatmap (fun pat -> validate_pattern pat items gvars) sch.ss_patterns
let has_hard_finding (f : finding) : Prims.bool=
  match f with
  | Assert_fail (uu___, uu___1, uu___2, uu___3) -> true
  | Report_hit (uu___, uu___1, uu___2, uu___3) -> true
  | Indeterminate (uu___, uu___1, uu___2, uu___3, uu___4) -> false
let rec any_hard (fs : finding Prims.list) : Prims.bool=
  match fs with
  | [] -> false
  | f::rest -> if has_hard_finding f then true else any_hard rest
let is_valid (schema_root : Parser_XML.xml_node)
  (instance_root : Parser_XML.xml_node) : Prims.bool=
  Prims.op_Negation (any_hard (validate schema_root instance_root))
