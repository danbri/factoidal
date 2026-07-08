module XSLT.Transform

open FStar.String
open FStar.List.Tot
open Parser.XML
open Parser.XPath
open XPath.Eval

// XSLT 1.0 transformation engine (slice 1), built entirely on top of
// the already-verified Parser.XML (xml_node tree, used here as BOTH
// the stylesheet AST, the source tree, and the result tree) and
// XPath.Eval (the XPath 1.0 evaluator). No new parser: a stylesheet
// is just XML, so Parser.XML.parse_xml_document already parses it.
//
// First wave of the XSLT -> MathML -> XForms -> JSON-Schema/Schematron
// program. See docs/designissues/2026-07-05-xforms-model-program-plan.md.
//
// SCOPE, instructions supported:
//   xsl:template (match-based dispatch, name= for call-template,
//   mode=, priority= override), xsl:apply-templates (default + select +
//   mode= + xsl:sort children), xsl:call-template + xsl:with-param,
//   xsl:param/xsl:variable (select= constant AND element/text body =
//   result-tree-fragment), xsl:value-of (select), xsl:for-each (select
//   + xsl:sort children), xsl:sort (select, data-type number|text,
//   order ascending|descending, stable, NaN-first ascending),
//   xsl:if (test), xsl:choose/when/otherwise, xsl:element,
//   xsl:attribute, xsl:text, xsl:comment, xsl:copy, xsl:copy-of
//   (node-set select AND $rtf-variable), literal result elements with
//   attribute value templates ({expr}), and the built-in template
//   rules (root/element -> apply-templates in the current mode,
//   text/attribute -> copy string value, comment/PI -> no output).
// Output methods: "xml" (default) and "text".
//
// Match patterns: a general right-to-left location-path matcher over
// name/"*" steps with "/" (child) and "//" (descendant) separators,
// optional leading "/" (root-anchored) or "//" (any-descendant), and
// "child::" axis prefixes; plus "@name"/"@*"/node-test alternatives.
//
// Deliberately OUT of scope (a mismatch here is expected, not a bug):
//   xsl:number, xsl:key/key(), document(), xsl:import/include,
//   xsl:apply-imports/next-match, format-number, xsl:sort case-order /
//   lang collations, namespace-node synthesis / exclude-result-prefixes,
//   disable-output-escaping, positional pattern predicates (predicates
//   are evaluated as a plain boolean against the candidate node, so
//   [1]-style position tests can be wrong), and the
//   processing-instruction() node test (a gap inherited from
//   XPath.Eval; PI alternatives are dropped from a union select before
//   evaluation). call-template recursion is bounded by the shared fuel
//   parameter: a self-calling template exhausts fuel and yields [], it
//   cannot diverge.
//
// TOTALITY: the template-dispatch / instantiation cycle can loop
// (a template applies templates that re-match the same node), so the
// whole mutual-recursion family threads an explicit fuel:nat,
// decremented by exactly 1 on every call, sized from the source +
// stylesheet node counts. Same idiom as XPath.Eval's eval_expr and
// SHACL.Validation's closure loop. No --lax, no admit.

(* ================================================================ *)
(* Small string helpers -- everything runs over `list char` so the    *)
(* totality proofs are plain structural recursion (no nat-index       *)
(* preconditions from String.sub).                                    *)
(* ================================================================ *)

let soc (c:char) : string = String.string_of_char c

let chars_of (s:string) : list char = String.list_of_string s
let str_of_chars (cs:list char) : string = String.string_of_list cs

let is_space_char (c:char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let rec drop_leading_ws (cs:list char) : Tot (list char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest -> if is_space_char c then drop_leading_ws rest else cs

let trim_chars (cs:list char) : list char =
  List.Tot.rev (drop_leading_ws (List.Tot.rev (drop_leading_ws cs)))

let trim_str (s:string) : string = str_of_chars (trim_chars (chars_of s))

let rec all_ws_chars (cs:list char) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> if is_space_char c then all_ws_chars rest else false

let is_all_ws (s:string) : bool = all_ws_chars (chars_of s)

let rec starts_with_chars (pre:list char) (cs:list char) : Tot bool (decreases pre) =
  match pre, cs with
  | [], _ -> true
  | _, [] -> false
  | p :: pr, c :: cr -> if p = c then starts_with_chars pr cr else false

let starts_with (pre:string) (s:string) : bool =
  starts_with_chars (chars_of pre) (chars_of s)

// Split a string on a single delimiter character (used to split a
// union pattern / union select on '|', and a path pattern on '/').
let rec split_on_char_acc (d:char) (cs:list char) (cur:list char) (acc:list (list char))
  : Tot (list (list char)) (decreases cs) =
  match cs with
  | [] -> List.Tot.rev (List.Tot.rev cur :: acc)
  | c :: rest ->
    if c = d then split_on_char_acc d rest [] (List.Tot.rev cur :: acc)
    else split_on_char_acc d rest (c :: cur) acc

let split_on_char (d:char) (s:string) : list string =
  List.Tot.map str_of_chars (split_on_char_acc d (chars_of s) [] [])

// Does `cs` contain the two-char sub-sequence "//" ?
let rec has_double_slash (cs:list char) : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | c0 :: rest ->
    (match rest with
     | c1 :: _ -> if c0 = '/' && c1 = '/' then true else has_double_slash rest
     | [] -> false)

let contains_double_slash (s:string) : bool = has_double_slash (chars_of s)

let rec has_char (d:char) (cs:list char) : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | c :: rest -> if c = d then true else has_char d rest

let contains_char (d:char) (s:string) : bool = has_char d (chars_of s)

// Local-name of a QName tag: the part after the (single) ':' colon,
// or the whole tag if unprefixed.
let local_name (tag:string) : string =
  match split_on_char ':' tag with
  | _ :: local :: _ -> local
  | _ -> tag

(* ================================================================ *)
(* Result nodes: an instantiated instruction produces a sequence of   *)
(* result-tree nodes, some of which are ATTRIBUTES (from xsl:attribute *)
(* or an attribute copied by xsl:copy/copy-of). Attributes are folded  *)
(* onto the enclosing constructed element; any left at the top level   *)
(* is dropped (as XSLT requires).                                      *)
(* ================================================================ *)

noeq type rnode =
  | R_Node : xml_node -> rnode
  | R_Attr : xml_attribute -> rnode

let rec split_rnodes (rs:list rnode) (as_acc:list xml_attribute) (ns_acc:list xml_node)
  : Tot (list xml_attribute & list xml_node) (decreases rs) =
  match rs with
  | [] -> (List.Tot.rev as_acc, List.Tot.rev ns_acc)
  | R_Attr a :: rest -> split_rnodes rest (a :: as_acc) ns_acc
  | R_Node n :: rest -> split_rnodes rest as_acc (n :: ns_acc)

let build_element (tag:string) (extra_attrs:list xml_attribute) (body:list rnode) : xml_node =
  let (attrs, nodes) = split_rnodes body [] [] in
  XElement tag (extra_attrs @ attrs) nodes

let rec rnodes_text (rs:list rnode) : Tot string (decreases rs) =
  match rs with
  | [] -> ""
  | R_Node (XText t) :: rest -> strcat t (rnodes_text rest)
  | R_Node (XCDATA t) :: rest -> strcat t (rnodes_text rest)
  | _ :: rest -> rnodes_text rest

let only_nodes (rs:list rnode) : list xml_node =
  let (_, nodes) = split_rnodes rs [] [] in nodes

// The raw text content of an xsl:text element's children (no
// whitespace stripping -- xsl:text is verbatim).
let rec raw_text (children:list xml_node) : Tot string (decreases children) =
  match children with
  | [] -> ""
  | XText t :: rest -> strcat t (raw_text rest)
  | XCDATA t :: rest -> strcat t (raw_text rest)
  | _ :: rest -> raw_text rest

let item_to_rnode (it:xctx_item) : rnode =
  match it with
  | CI_Elem _ _ n -> R_Node n
  | CI_Text _ _ _ t -> R_Node (XText t)
  | CI_Comment _ _ _ t -> R_Node (XComment t)
  | CI_PI _ _ _ tg d -> R_Node (XPI tg d)
  | CI_Attr _ _ _ a -> R_Attr a

(* ================================================================ *)
(* Driver node: any real tree node (an xctx_item, which carries its    *)
(* ancestry) plus the special document node whose single child is the  *)
(* root element.                                                       *)
(* ================================================================ *)

noeq type dnode =
  | D_Doc  : xml_node -> dnode
  | D_Item : xctx_item -> dnode

// XPath context item for a driver node. The document node presents to
// the XPath engine as its root element (ancestors empty), so absolute
// paths and "." behave correctly (copy-of/apply-templates/for-each of a
// relative child select from a "/" template go through the child-union
// fast path in select_nodes, which resolves against the document node's
// children directly and does not need a synthetic wrapper element -- a
// wrapper would otherwise leak an empty-tag element into copy-of ".").
let dnode_ci (nd:dnode) : xctx_item =
  match nd with
  | D_Doc root -> CI_Elem [] [] root
  | D_Item it -> it

// The children of a driver node, in document order, as driver nodes --
// the default node-set for xsl:apply-templates with no select.
let dnode_children (nd:dnode) : list dnode =
  match nd with
  | D_Doc root -> [D_Item (CI_Elem [] [] root)]
  | D_Item (CI_Elem p anc n) -> List.Tot.map (fun it -> D_Item it) (child_items p anc n)
  | D_Item _ -> []

// (attributes, child-nodes) of a driver node in document order -- the
// basis of the child-union select fast path (see select_child_union).
let dnode_attrs_and_kids (nd:dnode) : (list xctx_item & list xctx_item) =
  match nd with
  | D_Doc root -> ([], [CI_Elem [] [] root])
  | D_Item (CI_Elem p anc n) -> (attribute_items p anc n, child_items p anc n)
  | D_Item _ -> ([], [])

(* ================================================================ *)
(* Templates + compiled stylesheet.                                   *)
(* ================================================================ *)

type template = {
  tpl_match : string;   // "" when this is a name-only (call-template) template
  tpl_name : string;    // name= for xsl:call-template; "" if none
  tpl_mode : string;    // mode= ; "" is the default (unnamed) mode
  tpl_prio : option int;  // priority= override, x10-scaled to match the defaults below
  tpl_body : list xml_node;
}

noeq type xstyle = {
  xs_pfx : string;
  xs_templates : list template;
  xs_method : string;
  xs_globals : list (string & xp_value);
}

let xslt_ns : string = "http://www.w3.org/1999/XSL/Transform"

// Detect the prefix bound to the XSLT namespace on the stylesheet
// element's own xmlns:* declarations; default "xsl".
let rec drop_prefix_chars (cs:list char) (n:nat) : Tot (list char) (decreases n) =
  if n = 0 then cs
  else match cs with
       | [] -> []
       | _ :: rest -> drop_prefix_chars rest (n - 1)

let rec find_xsl_prefix (attrs:list xml_attribute) : Tot (option string) (decreases attrs) =
  match attrs with
  | [] -> None
  | a :: rest ->
    if a.attr_value = xslt_ns && starts_with "xmlns:" a.attr_name then
      Some (str_of_chars (drop_prefix_chars (chars_of a.attr_name) 6))
    else find_xsl_prefix rest

let xsl_prefix_of (root:xml_node) : string =
  match find_xsl_prefix (element_attrs root) with
  | Some p -> p
  | None -> "xsl"

let is_xsl (pfx:string) (tag:string) : bool =
  starts_with (strcat pfx ":") tag

// The xsl: instruction local-name (the part after "pfx:").
let xsl_instr (pfx:string) (tag:string) : string = local_name tag

let attr_opt (name:string) (attrs:list xml_attribute) : option string = find_attr name attrs
let attr_or (name:string) (dflt:string) (attrs:list xml_attribute) : string =
  match find_attr name attrs with Some v -> v | None -> dflt

(* ================================================================ *)
(* XPath call-outs. We construct the xp_env directly (rather than via  *)
(* eval_xpath_from_item, which hardwires position 1 / size 1) so that  *)
(* position()/last() are correct inside for-each / apply-templates.    *)
(* Each call is self-fuelled by initial_eval_fuel; these helpers are    *)
(* NOT part of the transform's own fuel-threaded recursion.            *)
(* ================================================================ *)

let eval_val (ctx:xctx_item) (pos:nat) (size:nat) (vars:list (string & xp_value)) (expr_text:string)
  : xp_value =
  match parse_xpath expr_text with
  | None -> XV_Str ""
  | Some e ->
    let doc_nodes = xml_node_count (root_of_item ctx) in
    let fuel = initial_eval_fuel e doc_nodes in
    let env = { env_item = ctx; env_pos = pos; env_size = size; env_vars = vars } in
    eval_expr fuel env e

let eval_string (ctx:xctx_item) (pos size:nat) (vars) (expr_text:string) : string =
  to_string_val (eval_val ctx pos size vars expr_text)

let eval_bool (ctx:xctx_item) (pos size:nat) (vars) (expr_text:string) : bool =
  to_bool_val (eval_val ctx pos size vars expr_text)

// Drop `processing-instruction()` alternatives from a union select
// before handing it to XPath.Eval (which has no PI node test).
let is_pi_alt (s:string) : bool = trim_str s = "processing-instruction()"

let drop_pi_alts (sel:string) : string =
  let alts = split_on_char '|' sel in
  let kept = List.Tot.filter (fun a -> not (is_pi_alt a)) alts in
  match kept with
  | [] -> "self::processing-instruction()"   // whole thing was PI -> empty node set
  | _ -> String.concat "|" kept

let eval_nodeset (ctx:xctx_item) (pos size:nat) (vars) (sel:string) : list xctx_item =
  match eval_val ctx pos size vars (drop_pi_alts sel) with
  | XV_Nodes items -> items
  | _ -> []

// select_nodes is defined after the pattern helpers (it needs
// is_simple_child_union / select_child_union); see below.

(* ================================================================ *)
(* Attribute value templates: replace {expr} with the string-value of  *)
(* the expression; {{ and }} are literal braces.                       *)
(* ================================================================ *)

let rec read_until_brace (cs:list char) (acc:list char)
  : Tot (list char & list char) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, [])
  | '}' :: rest -> (List.Tot.rev acc, rest)
  | c :: rest -> read_until_brace rest (c :: acc)

let rec expand_avt_chars (ctx:xctx_item) (pos size:nat) (vars:list (string & xp_value))
                         (cs:list char) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match cs with
    | [] -> ""
    | '{' :: '{' :: rest -> strcat "{" (expand_avt_chars ctx pos size vars rest (fuel - 1))
    | '}' :: '}' :: rest -> strcat "}" (expand_avt_chars ctx pos size vars rest (fuel - 1))
    | '{' :: rest ->
      let (expr_cs, after) = read_until_brace rest [] in
      let v = eval_string ctx pos size vars (str_of_chars expr_cs) in
      strcat v (expand_avt_chars ctx pos size vars after (fuel - 1))
    | c :: rest ->
      strcat (soc c) (expand_avt_chars ctx pos size vars rest (fuel - 1))

let expand_avt (ctx:xctx_item) (pos size:nat) (vars) (s:string) : string =
  let cs = chars_of s in
  if contains_char '{' s then expand_avt_chars ctx pos size vars cs (List.Tot.length cs + 1)
  else s

(* ================================================================ *)
(* Pattern matching (slice 1, hard-coded forms).                       *)
(*                                                                     *)
(* Supported: "/", "*", "@*", "text()", "comment()", "node()",         *)
(* "name", "prefix:name", "@name", a child chain "a/b/c" (steps are    *)
(* names or "*"), "//name" and "a//b" (descendant), and "name[pred]"   *)
(* (best-effort: name matches, predicate evaluated as a boolean).      *)
(* processing-instruction() and positional predicates are NOT          *)
(* faithfully supported (documented in the module banner).             *)
(* ================================================================ *)

let step_ok (stp:string) (tag:string) : bool =
  let s = trim_str stp in s = "*" || s = tag

let rec match_chain (rsteps:list string) (tags:list string)
  : Tot bool (decreases rsteps) =
  match rsteps with
  | [] -> true
  | s :: rest ->
    (match tags with
     | [] -> false
     | tg :: trest -> if step_ok s tg then match_chain rest trest else false)

let rec any_tag_matches (stp:string) (tags:list string) : Tot bool (decreases tags) =
  match tags with
  | [] -> false
  | tg :: rest -> if step_ok stp tg then true else any_tag_matches stp rest

// Predicate stripping: for "name[pred]", return (name-part, Some pred).
let split_predicate (alt:string) : (string & option string) =
  match split_on_char '[' alt with
  | namep :: predp :: _ ->
    // drop trailing ']' from predp
    let pc = chars_of predp in
    let pc' = List.Tot.rev pc in
    let pc'' = (match pc' with ']' :: r -> List.Tot.rev r | _ -> pc) in
    (trim_str namep, Some (str_of_chars pc''))
  | _ -> (alt, None)

let ancestor_tags_of (it:xctx_item) : list string =
  List.Tot.choose (fun (m:xml_node) -> element_tag m) (item_ancestors it)

// General location-path pattern matcher for element nodes: a chain of
// name/"*" steps separated by "/" (child) or "//" (descendant), with an
// optional leading "/" (root-anchored) or "//" (any-descendant), and
// "child::" axis prefixes normalized away. Matching is right-to-left
// (the last step matches the node; earlier steps match its ancestor
// tags), with backtracking over "//" so "a/b//c" means "a c that is a
// descendant of a b that is a child of an a". This replaces the earlier
// single-"//"-step approximation and makes the multi-level match tests
// (doc/l1//v3, doc//l2/w3, doc/child::l1/x2, ...) resolve correctly.
type pconn = | PC_Child | PC_Desc

let norm_pstep (s:string) : string =
  let s0 = trim_str s in
  if starts_with "child::" s0 then str_of_chars (drop_prefix_chars (chars_of s0) 7)
  else s0

let pname_ok (nm:string) (tag:string) : bool = nm = "*" || nm = tag

let rec build_psteps (toks:list string) (pending:pconn) : Tot (list (pconn & string)) (decreases toks) =
  match toks with
  | [] -> []
  | t :: rest ->
    if trim_str t = "" then build_psteps rest PC_Desc
    else (pending, norm_pstep t) :: build_psteps rest PC_Child

// (root-anchored?, steps in document order, top-first).
let parse_psteps (a:string) : (bool & list (pconn & string)) =
  let toks = split_on_char '/' a in
  match toks with
  | first :: t2 :: rest ->
    if trim_str first = "" then
      (if trim_str t2 = "" then (false, build_psteps rest PC_Desc)   // "//x": relative descendant
       else (true, build_psteps (t2 :: rest) PC_Child))              // "/x":  root-anchored
    else (false, build_psteps toks PC_Child)
  | _ -> (false, build_psteps toks PC_Child)

// rsteps: remaining steps most-specific-first (excluding the node step).
// childconn: how the more-specific step below connects to rsteps' head.
let rec match_up (anchored:bool) (rsteps:list (pconn & string)) (childconn:pconn) (anc:list string)
  : Tot bool (decreases (List.Tot.length rsteps + List.Tot.length anc)) =
  match rsteps with
  | [] -> if anchored then Nil? anc else true
  | (c, nm) :: rest ->
    (match childconn with
     | PC_Child ->
       (match anc with
        | [] -> false
        | a :: az -> pname_ok nm a && match_up anchored rest c az)
     | PC_Desc -> match_desc anchored nm rest c anc)

and match_desc (anchored:bool) (nm:string) (rest:list (pconn & string)) (c:pconn) (anc:list string)
  : Tot bool (decreases (List.Tot.length rest + List.Tot.length anc)) =
  match anc with
  | [] -> false
  | a :: az ->
    (pname_ok nm a && match_up anchored rest c az) || match_desc anchored nm rest c az

let alt_matches_elem (a:string) (it:xctx_item) (tag:string) : bool =
  let (anchored, steps) = parse_psteps a in
  match List.Tot.rev steps with
  | [] -> false
  | (ck, nk) :: rrest ->
    if not (pname_ok nk tag) then false
    else match_up anchored rrest ck (ancestor_tags_of it)

let alt_matches_core (alt:string) (nd:dnode) : bool =
  let a = trim_str alt in
  if a = "/" then (match nd with D_Doc _ -> true | _ -> false)
  else if a = "*" then (match nd with D_Item (CI_Elem _ _ _) -> true | _ -> false)
  else if a = "@*" then (match nd with D_Item (CI_Attr _ _ _ _) -> true | _ -> false)
  else if a = "text()" then (match nd with D_Item (CI_Text _ _ _ _) -> true | _ -> false)
  else if a = "comment()" then (match nd with D_Item (CI_Comment _ _ _ _) -> true | _ -> false)
  else if a = "node()" then
    (match nd with
     | D_Item (CI_Elem _ _ _) -> true
     | D_Item (CI_Text _ _ _ _) -> true
     | D_Item (CI_Comment _ _ _ _) -> true
     | D_Item (CI_PI _ _ _ _ _) -> true
     | _ -> false)
  else if a = "processing-instruction()" then
    (match nd with D_Item (CI_PI _ _ _ _ _) -> true | _ -> false)
  else if starts_with "@" a then
    (match nd with
     | D_Item (CI_Attr _ _ _ att) -> att.attr_name = str_of_chars (drop_prefix_chars (chars_of a) 1)
     | _ -> false)
  else
    (match nd with
     | D_Item (CI_Elem _ _ n) ->
       (match element_tag n with
        | Some tag -> alt_matches_elem a (dnode_ci nd) tag
        | None -> false)
     | _ -> false)

// A union select alternative that names only a forward child-axis node
// test (no path step, predicate, axis, or function). For such a union
// the correct document-ordered result can be produced directly from
// the child list -- sidestepping XPath.Eval's disclosed
// concatenation-not-document-order union gap (which otherwise clusters
// all text nodes after all elements, breaking identity/copy and the
// node-order tests).
let rec has_double_colon_chars (cs:list char) : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | c0 :: rest ->
    (match rest with
     | c1 :: _ -> if c0 = ':' && c1 = ':' then true else has_double_colon_chars rest
     | [] -> false)

let contains_double_colon (s:string) : bool = has_double_colon_chars (chars_of s)

let is_child_union_alt (alt:string) : bool =
  let a = trim_str alt in
  if a = "*" || a = "@*" || a = "text()" || a = "comment()"
     || a = "node()" || a = "processing-instruction()"
  then true
  else if starts_with "@" a then
    not (contains_char '/' a || contains_char '[' a || contains_char '(' a)
  else
    a <> "" && not (starts_with "." a)
    && not (contains_char '/' a) && not (contains_char '[' a)
    && not (contains_char '(' a) && not (contains_double_colon a)

let rec all_child_union_alts (alts:list string) : Tot bool (decreases alts) =
  match alts with
  | [] -> true
  | a :: rest -> if is_child_union_alt a then all_child_union_alts rest else false

let is_simple_child_union (sel:string) : bool =
  let alts = split_on_char '|' sel in
  match alts with [] -> false | _ -> all_child_union_alts alts

let rec any_core_matches (alts:list string) (it:xctx_item) : Tot bool (decreases alts) =
  match alts with
  | [] -> false
  | a :: rest -> if alt_matches_core a (D_Item it) then true else any_core_matches rest it

// Document-ordered node-set for a simple child union: attributes (if
// the union selects them) first, then child nodes in document order.
let select_child_union (nd:dnode) (alts:list string) : list xctx_item =
  let (attrs, kids) = dnode_attrs_and_kids nd in
  let sel_attrs = List.Tot.filter (fun it -> any_core_matches alts it) attrs in
  let sel_kids = List.Tot.filter (fun it -> any_core_matches alts it) kids in
  sel_attrs @ sel_kids

// Node-set for a select expression on the current context node. A
// "simple child union" (only forward child-axis node tests, e.g. the
// identity pattern *|@*|comment()|processing-instruction()|text(), or
// a bare child name) is resolved directly in document order; anything
// else (paths, predicates, axes, functions, ".") goes through the full
// XPath.Eval engine.
let select_nodes (ctx:dnode) (pos size:nat) (vars:list (string & xp_value)) (sel:string)
  : list xctx_item =
  if is_simple_child_union sel then select_child_union ctx (split_on_char '|' sel)
  else eval_nodeset (dnode_ci ctx) pos size vars sel

// Evaluate a "name[pred]" predicate best-effort as a boolean against
// the candidate node. Self-fuelled via eval_bool.
let alt_matches (vars:list (string & xp_value)) (alt:string) (nd:dnode) : bool =
  let (namepart, predopt) = split_predicate alt in
  match predopt with
  | None -> alt_matches_core alt nd
  | Some pred ->
    if not (alt_matches_core namepart nd) then false
    else eval_bool (dnode_ci nd) 1 1 vars pred

let rec any_alt_matches (vars:list (string & xp_value)) (alts:list string) (nd:dnode)
  : Tot bool (decreases alts) =
  match alts with
  | [] -> false
  | a :: rest -> if alt_matches vars a nd then true else any_alt_matches vars rest nd

let template_matches (vars:list (string & xp_value)) (tpl:template) (nd:dnode) : bool =
  if tpl.tpl_match = "" then false
  else any_alt_matches vars (split_on_char '|' tpl.tpl_match) nd

// Default priority of a single alternative (x10 to keep integers).
let alt_priority (alt:string) : int =
  let a = trim_str alt in
  if a = "*" || a = "@*" || a = "node()" || a = "text()" || a = "comment()"
     || a = "processing-instruction()"
  then -5
  else if contains_char '/' a || contains_char '[' a then 5
  else 0

let rec max_alt_priority (alts:list string) (cur:int) : Tot int (decreases alts) =
  match alts with
  | [] -> cur
  | a :: rest ->
    let p = alt_priority a in
    max_alt_priority rest (if p > cur then p else cur)

let template_priority (tpl:template) : int =
  match tpl.tpl_prio with
  | Some p -> p
  | None -> max_alt_priority (split_on_char '|' tpl.tpl_match) (-100)

// Highest-priority template that both matches `nd` AND is declared in
// the active `mode` (default mode = ""); ties resolved to the LAST in
// document order (XSLT 1.0 conflict resolution, minus the error).
let rec pick_template (vars) (mode:string) (tpls:list template) (nd:dnode) (best:option template)
  : Tot (option template) (decreases tpls) =
  match tpls with
  | [] -> best
  | t :: rest ->
    let best' =
      if t.tpl_mode = mode && template_matches vars t nd then
        (match best with
         | None -> Some t
         | Some b -> if template_priority t >= template_priority b then Some t else best)
      else best
    in
    pick_template vars mode rest nd best'

// Look up a named template (xsl:call-template target); first match wins.
let rec find_named_template (tpls:list template) (nm:string) : Tot (option template) (decreases tpls) =
  match tpls with
  | [] -> None
  | t :: rest -> if t.tpl_name = nm && nm <> "" then Some t else find_named_template rest nm

(* ================================================================ *)
(* Serialization: result tree -> XML text (method="xml") or text       *)
(* concatenation (method="text").                                      *)
(* ================================================================ *)

let escape_text_char (c:char) : string =
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else if c = '>' then "&gt;"
  else soc c

let escape_attr_char (c:char) : string =
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else if c = '"' then "&quot;"
  else if c = '>' then "&gt;"
  else soc c

let rec escape_with (f:char -> string) (cs:list char) : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: rest -> strcat (f c) (escape_with f rest)

let escape_text (s:string) : string = escape_with escape_text_char (chars_of s)
let escape_attr (s:string) : string = escape_with escape_attr_char (chars_of s)

let serialize_attr (a:xml_attribute) : string =
  String.concat "" [" "; a.attr_name; "=\""; escape_attr a.attr_value; "\""]

let rec serialize_attrs (attrs:list xml_attribute) : Tot string (decreases attrs) =
  match attrs with
  | [] -> ""
  | a :: rest -> strcat (serialize_attr a) (serialize_attrs rest)

let rec serialize_node (n:xml_node) : Tot string (decreases n) =
  match n with
  | XText t -> escape_text t
  | XCDATA t -> escape_text t
  | XComment t -> String.concat "" ["<!--"; t; "-->"]
  | XPI tg d -> String.concat "" ["<?"; tg; " "; d; "?>"]
  | XElement tag attrs children ->
    let a = serialize_attrs attrs in
    if Nil? children then String.concat "" ["<"; tag; a; "/>"]
    else String.concat "" ["<"; tag; a; ">"; serialize_nodes children; "</"; tag; ">"]

and serialize_nodes (ns:list xml_node) : Tot string (decreases ns) =
  match ns with
  | [] -> ""
  | hd :: tl -> strcat (serialize_node hd) (serialize_nodes tl)

let serialize_result (n:xml_node) : string = serialize_node n

// method="text": concatenate the string-value of every result text
// node (elements contribute their descendant text).
let rec text_value_node (n:xml_node) : Tot string (decreases n) =
  match n with
  | XText t -> t
  | XCDATA t -> t
  | XComment _ -> ""
  | XPI _ _ -> ""
  | XElement _ _ children -> text_value_nodes children

and text_value_nodes (ns:list xml_node) : Tot string (decreases ns) =
  match ns with
  | [] -> ""
  | hd :: tl -> strcat (text_value_node hd) (text_value_nodes tl)

(* ================================================================ *)
(* xsl:sort -- key specs collected from the leading xsl:sort children  *)
(* of an xsl:for-each / xsl:apply-templates, and a stable sort of the  *)
(* selected node-set by those keys. Sort keys are evaluated with each  *)
(* candidate as the context node (self-fuelled via eval_string).       *)
(* ================================================================ *)

type sortspec = {
  so_select : string;
  so_numeric : bool;
  so_descending : bool;
}

let parse_sort (pfx:string) (n:xml_node) : option sortspec =
  match n with
  | XElement tag attrs _ ->
    if is_xsl pfx tag && xsl_instr pfx tag = "sort" then
      Some { so_select = attr_or "select" "." attrs;
             so_numeric = (attr_or "data-type" "text" attrs = "number");
             so_descending = (attr_or "order" "ascending" attrs = "descending") }
    else None
  | _ -> None

// Leading xsl:sort children (whitespace-only text between them is
// skipped; the first non-sort content stops the collection).
let rec collect_sorts (pfx:string) (body:list xml_node) : Tot (list sortspec) (decreases body) =
  match body with
  | [] -> []
  | hd :: tl ->
    (match parse_sort pfx hd with
     | Some s -> s :: collect_sorts pfx tl
     | None ->
       (match hd with
        | XText t -> if is_all_ws t then collect_sorts pfx tl else []
        | _ -> []))

let rec sort_key_cmp (vars:list (string & xp_value)) (specs:list sortspec) (a b:xctx_item)
  : Tot int (decreases specs) =
  match specs with
  | [] -> 0
  | s :: rest ->
    let sa = eval_string a 1 1 vars s.so_select in
    let sb = eval_string b 1 1 vars s.so_select in
    let raw =
      if s.so_numeric then
        (let na = string_to_xn sa in
         let nb = string_to_xn sb in
         match xn_compare na nb with
         | Some c -> c
         | None ->
           // A NaN key (non-numeric text under data-type="number") sorts
           // before every real number in ascending order (so it sorts
           // last once the descending sign-flip below is applied), which
           // is what the W3C numeric-sort reference outputs expect.
           let a_nan = (match na with XN_NaN -> true | _ -> false) in
           let b_nan = (match nb with XN_NaN -> true | _ -> false) in
           if a_nan && b_nan then 0 else if a_nan then -1 else 1)
      else String.compare sa sb in
    let signed = if s.so_descending then 0 - raw else raw in
    if signed <> 0 then signed else sort_key_cmp vars rest a b

// Stable insertion sort: an element with a key equal to an already-
// placed one is inserted AFTER it, preserving original document order
// among equal keys (XSLT 1.0 sorts are stable).
let rec sort_insert (vars:list (string & xp_value)) (specs:list sortspec) (x:xctx_item) (l:list xctx_item)
  : Tot (list xctx_item) (decreases l) =
  match l with
  | [] -> [x]
  | y :: ys -> if sort_key_cmp vars specs x y <= 0 then x :: l else y :: sort_insert vars specs x ys

let rec sort_items (vars:list (string & xp_value)) (specs:list sortspec) (l:list xctx_item)
  : Tot (list xctx_item) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> sort_insert vars specs x (sort_items vars specs xs)

let sort_maybe (pfx:string) (vars:list (string & xp_value)) (body:list xml_node) (items:list xctx_item)
  : list xctx_item =
  match collect_sorts pfx body with
  | [] -> items
  | specs -> sort_items vars specs items

(* ================================================================ *)
(* Result-tree-fragment variables. A variable/param with element/text  *)
(* content (no select=) binds to the sequence of result nodes its body  *)
(* instantiates. The string-value is bound in the XPath variable list   *)
(* (so value-of/string contexts work); the node sequence is kept in a   *)
(* separate rtf table so xsl:copy-of select="$var" can re-emit it.      *)
(* ================================================================ *)

let rtf_var_name (sel:string) : option string =
  let s = trim_str sel in
  if starts_with "$" s then Some (str_of_chars (drop_prefix_chars (chars_of s) 1)) else None

let rec rtf_find (rtf:list (string & list rnode)) (nm:string) : option (list rnode) =
  match rtf with
  | [] -> None
  | (k, v) :: rest -> if k = nm then Some v else rtf_find rest nm

(* ================================================================ *)
(* The transform engine -- one fuel-threaded mutual-recursion family.  *)
(* ================================================================ *)

// The context node is carried as a `dnode` (not a bare xctx_item) so
// that a template matching the document node ("/") whose body calls
// <xsl:apply-templates/> processes the DOCUMENT node's children (the
// root element), not the root element's children -- the distinction
// that makes the identity/copy transforms produce the wrapper element.
// XPath call-outs use `dnode_ci ctx` (the document node presents as
// its root element for expression evaluation).

let rec dispatch (fuel:nat) (st:xstyle) (nd:dnode) (pos size:nat) (mode:string)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match pick_template st.xs_globals mode st.xs_templates nd None with
    | Some tpl -> instantiate_seq (fuel - 1) st nd pos size st.xs_globals [] tpl.tpl_body
    | None -> builtin_rule (fuel - 1) st nd mode

and builtin_rule (fuel:nat) (st:xstyle) (nd:dnode) (mode:string) : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match nd with
    | D_Doc _ ->
      let kids = dnode_children nd in
      apply_list (fuel - 1) st kids 1 (List.Tot.length kids) mode
    | D_Item (CI_Elem _ _ _) ->
      let kids = dnode_children nd in
      apply_list (fuel - 1) st kids 1 (List.Tot.length kids) mode
    | D_Item (CI_Text _ _ _ t) -> [R_Node (XText t)]
    | D_Item (CI_Attr _ _ _ a) -> [R_Node (XText a.attr_value)]
    | D_Item (CI_Comment _ _ _ _) -> []
    | D_Item (CI_PI _ _ _ _ _) -> []

// Apply templates (in the active mode) to a list of driver nodes,
// threading 1-based position and the common size.
and apply_list (fuel:nat) (st:xstyle) (nodes:list dnode) (pos size:nat) (mode:string)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match nodes with
    | [] -> []
    | hd :: tl ->
      let here = dispatch (fuel - 1) st hd pos size mode in
      here @ apply_list (fuel - 1) st tl (pos + 1) size mode

// Instantiate a template body (sequence of instruction nodes),
// threading local variable bindings (xp-value + result-tree-fragment)
// across siblings.
and instantiate_seq (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                    (vars:list (string & xp_value)) (rtf:list (string & list rnode)) (nodes:list xml_node)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match nodes with
    | [] -> []
    | hd :: tl ->
      (match hd with
       | XElement tag attrs children ->
         if is_xsl st.xs_pfx tag &&
            (let ln = xsl_instr st.xs_pfx tag in ln = "variable" || ln = "param") then
           let nm = attr_or "name" "" attrs in
           // xsl:param uses an already-bound value (e.g. from
           // xsl:with-param on the calling xsl:call-template) if present,
           // and only falls back to its own default otherwise.
           let already = (xsl_instr st.xs_pfx tag = "param") && Some? (lookup_var vars nm) in
           if already then instantiate_seq (fuel - 1) st ctx pos size vars rtf tl
           else
             (match attr_opt "select" attrs with
              | Some sel ->
                let v = eval_val (dnode_ci ctx) pos size vars sel in
                instantiate_seq (fuel - 1) st ctx pos size ((nm, v) :: vars) rtf tl
              | None ->
                // Result-tree-fragment: instantiate the body, bind its
                // string-value for XPath and its nodes for copy-of.
                let frag = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
                let sval = text_value_nodes (only_nodes frag) in
                instantiate_seq (fuel - 1) st ctx pos size ((nm, XV_Str sval) :: vars) ((nm, frag) :: rtf) tl)
         else
           let here = instantiate_one (fuel - 1) st ctx pos size vars rtf hd in
           here @ instantiate_seq (fuel - 1) st ctx pos size vars rtf tl
       | _ ->
         let here = instantiate_one (fuel - 1) st ctx pos size vars rtf hd in
         here @ instantiate_seq (fuel - 1) st ctx pos size vars rtf tl)

// Bind xsl:with-param children (select= or body RTF) onto the variable
// lists that will seed a called template. First non-param handling is
// skipped; params accumulate onto (vars, rtf).
and bind_with_params (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                     (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                     (children:list xml_node)
  : Tot (list (string & xp_value) & list (string & list rnode)) (decreases fuel) =
  if fuel = 0 then (vars, rtf)
  else
    match children with
    | [] -> (vars, rtf)
    | hd :: tl ->
      (match hd with
       | XElement tag attrs pchildren ->
         if is_xsl st.xs_pfx tag && xsl_instr st.xs_pfx tag = "with-param" then
           let nm = attr_or "name" "" attrs in
           (match attr_opt "select" attrs with
            | Some sel ->
              let v = eval_val (dnode_ci ctx) pos size vars sel in
              bind_with_params (fuel - 1) st ctx pos size ((nm, v) :: vars) rtf tl
            | None ->
              let frag = instantiate_seq (fuel - 1) st ctx pos size vars rtf pchildren in
              let sval = text_value_nodes (only_nodes frag) in
              bind_with_params (fuel - 1) st ctx pos size ((nm, XV_Str sval) :: vars) ((nm, frag) :: rtf) tl)
         else bind_with_params (fuel - 1) st ctx pos size vars rtf tl
       | _ -> bind_with_params (fuel - 1) st ctx pos size vars rtf tl)

and instantiate_one (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                    (vars:list (string & xp_value)) (rtf:list (string & list rnode)) (node:xml_node)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match node with
    | XText t -> if is_all_ws t then [] else [R_Node (XText t)]
    | XComment _ -> []
    | XPI tg d -> [R_Node (XPI tg d)]
    | XCDATA t -> [R_Node (XText t)]
    | XElement tag attrs children ->
      if is_xsl st.xs_pfx tag then
        let ln = xsl_instr st.xs_pfx tag in
        if ln = "value-of" then
          [R_Node (XText (eval_string (dnode_ci ctx) pos size vars (attr_or "select" "." attrs)))]
        else if ln = "text" then
          [R_Node (XText (raw_text children))]
        else if ln = "if" then
          (if eval_bool (dnode_ci ctx) pos size vars (attr_or "test" "false()" attrs)
           then instantiate_seq (fuel - 1) st ctx pos size vars rtf children
           else [])
        else if ln = "choose" then
          instantiate_choose (fuel - 1) st ctx pos size vars rtf children
        else if ln = "for-each" then
          let sel = attr_or "select" "." attrs in
          let items0 = select_nodes ctx pos size vars sel in
          let items = sort_maybe st.xs_pfx vars children items0 in
          for_each_items (fuel - 1) st children vars rtf items 1 (List.Tot.length items)
        else if ln = "apply-templates" then
          let amode = attr_or "mode" "" attrs in
          (match attr_opt "select" attrs with
           | Some sel ->
             let items0 = select_nodes ctx pos size vars sel in
             let items = sort_maybe st.xs_pfx vars children items0 in
             let dns = List.Tot.map (fun it -> D_Item it) items in
             apply_list (fuel - 1) st dns 1 (List.Tot.length items) amode
           | None ->
             let kids = dnode_children ctx in
             apply_list (fuel - 1) st kids 1 (List.Tot.length kids) amode)
        else if ln = "call-template" then
          let nm = attr_or "name" "" attrs in
          (match find_named_template st.xs_templates nm with
           | Some tpl ->
             // Named-template invocation keeps the current context node.
             // with-param bindings seed the called template's params;
             // recursion is bounded by the same fuel as every other call
             // (a self-calling template exhausts fuel and yields [], not
             // a nonterminating loop).
             let (cvars, crtf) = bind_with_params (fuel - 1) st ctx pos size st.xs_globals [] children in
             instantiate_seq (fuel - 1) st ctx pos size cvars crtf tpl.tpl_body
           | None -> [])
        else if ln = "copy-of" then
          let sel = attr_or "select" "." attrs in
          (match rtf_var_name sel with
           | Some nm ->
             (match rtf_find rtf nm with
              | Some frag -> frag
              | None -> List.Tot.map item_to_rnode (select_nodes ctx pos size vars sel))
           | None -> List.Tot.map item_to_rnode (select_nodes ctx pos size vars sel))
        else if ln = "copy" then
          instantiate_copy (fuel - 1) st ctx pos size vars rtf children
        else if ln = "element" then
          let nm = expand_avt (dnode_ci ctx) pos size vars (attr_or "name" "" attrs) in
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
          [R_Node (build_element nm [] body)]
        else if ln = "attribute" then
          let nm = expand_avt (dnode_ci ctx) pos size vars (attr_or "name" "" attrs) in
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
          [R_Attr ({ attr_name = nm; attr_value = rnodes_text body })]
        else if ln = "comment" then
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
          [R_Node (XComment (rnodes_text body))]
        else
          []  // unsupported xsl instruction: emit nothing
      else
        // literal result element: copy tag, AVT-expand its attributes,
        // instantiate its content; xsl:attribute children fold in.
        let out_attrs =
          List.Tot.map
            (fun (a:xml_attribute) ->
               { attr_name = a.attr_name; attr_value = expand_avt (dnode_ci ctx) pos size vars a.attr_value })
            attrs in
        let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
        [R_Node (build_element tag out_attrs body)]

and instantiate_choose (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                       (vars:list (string & xp_value)) (rtf:list (string & list rnode)) (branches:list xml_node)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match branches with
    | [] -> []
    | hd :: tl ->
      (match hd with
       | XElement tag attrs children ->
         if is_xsl st.xs_pfx tag then
           let ln = xsl_instr st.xs_pfx tag in
           if ln = "when" then
             (if eval_bool (dnode_ci ctx) pos size vars (attr_or "test" "false()" attrs)
              then instantiate_seq (fuel - 1) st ctx pos size vars rtf children
              else instantiate_choose (fuel - 1) st ctx pos size vars rtf tl)
           else if ln = "otherwise" then
             instantiate_seq (fuel - 1) st ctx pos size vars rtf children
           else instantiate_choose (fuel - 1) st ctx pos size vars rtf tl
         else instantiate_choose (fuel - 1) st ctx pos size vars rtf tl
       | _ -> instantiate_choose (fuel - 1) st ctx pos size vars rtf tl)

and instantiate_copy (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                     (vars:list (string & xp_value)) (rtf:list (string & list rnode)) (children:list xml_node)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match ctx with
    | D_Doc _ -> instantiate_seq (fuel - 1) st ctx pos size vars rtf children
    | D_Item (CI_Elem _ _ n) ->
      (match n with
       | XElement t _ _ ->
         let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
         [R_Node (build_element t [] body)]
       | _ -> instantiate_seq (fuel - 1) st ctx pos size vars rtf children)
    | D_Item (CI_Text _ _ _ t) -> [R_Node (XText t)]
    | D_Item (CI_Comment _ _ _ t) -> [R_Node (XComment t)]
    | D_Item (CI_PI _ _ _ tg d) -> [R_Node (XPI tg d)]
    | D_Item (CI_Attr _ _ _ a) -> [R_Attr a]

and for_each_items (fuel:nat) (st:xstyle) (body:list xml_node)
                   (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                   (items:list xctx_item) (pos size:nat)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | it :: rest ->
      let here = instantiate_seq (fuel - 1) st (D_Item it) pos size vars rtf body in
      here @ for_each_items (fuel - 1) st body vars rtf rest (pos + 1) size

(* ================================================================ *)
(* Stylesheet compilation.                                            *)
(* ================================================================ *)

// Parse an integer priority= attribute, x10-scaled to match the
// default-priority scale (name=0, node-test=-5, path/predicate=5). A
// fractional or unparseable value falls back to the computed default.
let rec digits_to_int (cs:list char) (acc:int) : Tot (option int) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: rest ->
    let d = FStar.Char.int_of_char c - 0x30 in
    if d >= 0 && d <= 9 then digits_to_int rest (op_Multiply acc 10 + d) else None

let parse_priority (s:string) : option int =
  match chars_of (trim_str s) with
  | [] -> None
  | '-' :: rest -> (match digits_to_int rest 0 with Some n -> Some (op_Multiply (0 - n) 10) | None -> None)
  | cs -> (match digits_to_int cs 0 with Some n -> Some (op_Multiply n 10) | None -> None)

let rec collect_templates (pfx:string) (children:list xml_node) : Tot (list template) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs body ->
       if is_xsl pfx tag && xsl_instr pfx tag = "template" then
         let m = attr_or "match" "" attrs in
         let nm = attr_or "name" "" attrs in
         if m = "" && nm = "" then collect_templates pfx tl
         else
           let t = { tpl_match = m; tpl_name = nm;
                     tpl_mode = attr_or "mode" "" attrs;
                     tpl_prio = (match attr_opt "priority" attrs with
                                 | Some p -> parse_priority p | None -> None);
                     tpl_body = body } in
           t :: collect_templates pfx tl
       else collect_templates pfx tl
     | _ -> collect_templates pfx tl)

let rec find_output_method (pfx:string) (children:list xml_node) : Tot string (decreases children) =
  match children with
  | [] -> "xml"
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag && xsl_instr pfx tag = "output" then attr_or "method" "xml" attrs
       else find_output_method pfx tl
     | _ -> find_output_method pfx tl)

// Top-level xsl:variable / xsl:param with a select= expression,
// evaluated once against the source document root.
let rec collect_globals (pfx:string) (children:list xml_node) (source:xml_node)
  : Tot (list (string & xp_value)) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag &&
          (let ln = xsl_instr pfx tag in ln = "variable" || ln = "param") then
         (match attr_opt "select" attrs, attr_opt "name" attrs with
          | Some sel, Some nm ->
            let v = eval_val (CI_Elem [] [] source) 1 1 [] sel in
            (nm, v) :: collect_globals pfx tl source
          | _, _ -> collect_globals pfx tl source)
       else collect_globals pfx tl source
     | _ -> collect_globals pfx tl source)

let build_style (stylesheet:xml_node) (source:xml_node) : xstyle =
  match stylesheet with
  | XElement tag _ children ->
    let pfx = xsl_prefix_of stylesheet in
    if is_xsl pfx tag &&
       (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform") then
      { xs_pfx = pfx;
        xs_templates = collect_templates pfx children;
        xs_method = find_output_method pfx children;
        xs_globals = collect_globals pfx children source }
    else
      // Simplified stylesheet: the literal result element IS the body
      // of a single template matching the document root.
      { xs_pfx = pfx;
        xs_templates = [ { tpl_match = "/"; tpl_name = ""; tpl_mode = ""; tpl_prio = None; tpl_body = [stylesheet] } ];
        xs_method = "xml";
        xs_globals = [] }
  | _ ->
    { xs_pfx = "xsl"; xs_templates = []; xs_method = "xml"; xs_globals = [] }

(* ================================================================ *)
(* Entry point.                                                       *)
(* ================================================================ *)

let transform (stylesheet:xml_node) (source:xml_node) : string =
  let st = build_style stylesheet source in
  // Fuel: generous multiple of the combined tree sizes -- every
  // apply-templates / instantiate step consumes one unit.
  let sz = xml_node_count stylesheet + xml_node_count source in
  let fuel = op_Multiply (sz + 1) 256 + 100000 in
  let result = dispatch fuel st (D_Doc source) 1 1 "" in
  let nodes = only_nodes result in
  if st.xs_method = "text" then text_value_nodes nodes
  else serialize_nodes nodes
