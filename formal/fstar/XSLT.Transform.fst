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
//   xsl:param/xsl:variable (select= node-set/string/number/boolean AND
//   element/text body = result-tree-fragment; a node-set variable is
//   iterable via for-each select="$v"), xsl:value-of (select),
//   xsl:for-each (select + xsl:sort children), xsl:sort (select,
//   data-type number|text and order ascending|descending -- both
//   attribute-value-template-expanded, sort key evaluated with each
//   node's own position()/last(), stable, NaN-first ascending;
//   xsl:sort also honored on xsl:apply-templates with no select),
//   xsl:if (test), xsl:choose/when/otherwise, xsl:element,
//   xsl:attribute, xsl:text, xsl:comment, xsl:copy, xsl:copy-of
//   (node-set select AND $rtf-variable), literal result elements with
//   attribute value templates ({expr}), and the built-in template
//   rules (root/element -> apply-templates in the current mode,
//   text/attribute -> copy string value, comment/PI -> no output).
// Output methods: "xml" (default) and "text".
//
// Namespace nodes (XSLT 1.0 §7.5): literal result elements copy the
// in-scope namespace declarations of the stylesheet element onto the
// result tree (stripped of the XSLT namespace and of the stylesheet's
// exclude-result-prefixes); xsl:copy and xsl:copy-of copy an element's
// in-scope namespace nodes (own + ancestor-inherited) onto the copied
// element. xsl:copy-of copy-namespaces="no" (XSLT 2.0) strips those
// namespace nodes from the copied subtree. xsl:element honours a
// namespace= AVT (and an unprefixed name with no namespace= takes the
// stylesheet's default namespace, null if none), attaching the right
// xmlns / xmlns:pfx declaration. The serializer threads output scope,
// suppresses redundant declarations, emits xmlns="" resets when a
// null-namespace element sits inside a default-namespaced context, and
// does NOT write xsl:-namespaced attributes on LREs. namespace-uri()
// resolves a source node's expanded-name namespace.
//
// Match patterns: a general right-to-left location-path matcher over
// name/"*"/"pfx:*" steps with "/" (child) and "//" (descendant)
// separators, optional leading "/" (root-anchored) or "//" (any-
// descendant), and "child::" axis prefixes; plus "@name"/"@*"/"@pfx:*"/
// node-test alternatives. Prefixed name and pfx:* tests are namespace-
// URI aware (resolved via the stylesheet's namespace context).
//
// Node-set order: xsl:for-each and xsl:apply-templates process the
// selected node-set in DOCUMENT ORDER with duplicates removed (XSLT 1.0
// §5.4), so reverse-axis selects (preceding::, ancestor::) and
// descendant (//) selects that would otherwise arrive in proximity
// order / with repeats are normalised before iteration.
//
// Document node: a `match="/"` template's context is the document node;
// a relative multi-step location path from it (e.g. `doc/num`) resolves
// against the document element as the document node's only child.
// Serialization: an element whose content is empty (e.g. an empty
// xsl:value-of) is written as an empty-element tag `<t/>`.
//
// Deliberately OUT of scope (a mismatch here is expected, not a bug):
//   xsl:number, xsl:key/key(), id() (needs DTD ATTLIST ID typing),
//   document(), xsl:import/include, xsl:apply-imports/next-match,
//   format-number, xsl:sort case-order / lang collations, the
//   `namespace::` axis and namespace-node counting (XPath.Eval models no
//   namespace-node kind, so `namespace::node()` selects nothing -- the
//   only namespace machinery still missing after the namespace-node
//   work: namespace-uri(), pfx:* / @pfx:* patterns, xsl:element/@namespace
//   with default-namespace reset, and copy-namespaces="no" now land),
//   xsl:namespace-alias, disable-output-escaping,
//   document-level comments/PIs around the root element (Parser.XML
//   models the source as the root element, so a sibling comment/PI of
//   the root is not in the tree),
//   XPath 2.0 comparison operators (eq/ne/lt/le/gt/ge), and the
//   processing-instruction() node test (a gap inherited from XPath.Eval;
//   PI alternatives are dropped from a union select before evaluation).
//   call-template recursion is bounded by the shared fuel parameter: a
//   self-calling template exhausts fuel and yields [], it cannot diverge.
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

let rec drop_prefix_chars (cs:list char) (n:nat) : Tot (list char) (decreases n) =
  if n = 0 then cs
  else match cs with
       | [] -> []
       | _ :: rest -> drop_prefix_chars rest (n - 1)

// Prefix of a QName tag ("" when unprefixed).
let name_prefix (tag:string) : string =
  match split_on_char ':' tag with
  | pfx :: _ :: _ -> pfx
  | _ -> ""

(* ================================================================ *)
(* Namespace declarations (XSLT 1.0 §7.5).                             *)
(*                                                                     *)
(* The XML parser keeps `xmlns`/`xmlns:prefix` declarations as ordinary *)
(* attributes on the element. A namespace node is therefore recovered  *)
(* from such an attribute: `xmlns` declares the default namespace       *)
(* (prefix ""), `xmlns:p` declares prefix "p".                          *)
(* ================================================================ *)

let ns_decl_prefix (name:string) : option string =
  if name = "xmlns" then Some ""
  else if starts_with "xmlns:" name then Some (str_of_chars (drop_prefix_chars (chars_of name) 6))
  else None

let is_ns_decl (a:xml_attribute) : bool = Some? (ns_decl_prefix a.attr_name)

let rec mem_str (x:string) (xs:list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: t -> if h = x then true else mem_str x t

// Accumulate the namespace declarations of one element's attribute
// list, keeping only prefixes not already bound nearer (`seen`).
let rec ns_add (acc:list xml_attribute) (seen:list string) (attrs:list xml_attribute)
  : Tot (list xml_attribute & list string) (decreases attrs) =
  match attrs with
  | [] -> (acc, seen)
  | a :: rest ->
    (match ns_decl_prefix a.attr_name with
     | Some pfx -> if mem_str pfx seen then ns_add acc seen rest
                   else ns_add (acc @ [a]) (pfx :: seen) rest
     | None -> ns_add acc seen rest)

// In-scope namespace nodes of a node: its own declarations plus those
// inherited from its ancestors (nearest-first), each prefix bound by
// the nearest declaration. Used by xsl:copy to copy an element's
// namespace nodes onto the result element (XSLT §7.5).
let rec inscope_ns (acc:list xml_attribute) (seen:list string) (nodes:list xml_node)
  : Tot (list xml_attribute) (decreases nodes) =
  match nodes with
  | [] -> acc
  | n :: rest ->
    let (acc', seen') = ns_add acc seen (element_attrs n) in
    inscope_ns acc' seen' rest

// Lexicographic (codepoint) order on strings, used to sort namespace
// declarations by prefix so the emission order is stable and matches
// the sorted-by-prefix order compliant serializers produce.
let rec char_list_cmp (a b:list char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let cx = FStar.Char.int_of_char x in
    let cy = FStar.Char.int_of_char y in
    if cx < cy then -1 else if cx > cy then 1 else char_list_cmp xs ys

// Compares two namespace-declaration attributes for build_nsscope's
// stable sort, by PREFIX rather than the raw attr_name string -- and
// the unprefixed default-namespace declaration (xmlns="...", prefix
// "") sorts LAST, not first. A plain string compare treats "xmlns" as
// a prefix of "xmlns:x" (hence "less than"), which is what this
// function used to do; but that puts the default namespace first,
// which is wrong for apply-templates/conflict-resolution-1301's
// `<fo:root>` (wants xmlns:fo before the default xmlns). Prefixed
// declarations among themselves still sort alphabetically, which is
// what copy/copy-3102's `<out>` needs (xmlns:foo, xmlns:huh,
// xmlns:joes, no default present at all) -- so this single comparator
// change satisfies both without a stylesheet-order/sorted-order split:
// see the long comment on build_nsscope below for why an earlier
// attempt at a stylesheet-order-vs-sorted-order PROVENANCE split
// turned out not to be the right axis at all.
let attr_name_cmp (a b:xml_attribute) : int =
  match ns_decl_prefix a.attr_name, ns_decl_prefix b.attr_name with
  | Some pa, Some pb ->
    if pa = "" && pb <> "" then 1
    else if pa <> "" && pb = "" then -1
    else char_list_cmp (chars_of pa) (chars_of pb)
  | _, _ -> char_list_cmp (chars_of a.attr_name) (chars_of b.attr_name)

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

// A D_Doc carries the document node's root element (its string value and
// legacy absolute-path base) AND the document node's full ordered child
// list `doc_kids` (prolog Comment/PI Misc, root element, epilog Misc), as
// retained by Parser.XML.parse_xml_document_children. When `doc_kids` is
// just the root (no prolog/epilog Misc -- every document GRDDL and the
// legacy `transform` entry produce), the node behaves exactly as before.
noeq type dnode =
  | D_Doc  : xml_node -> list xml_node -> dnode
  | D_Item : xctx_item -> dnode

// True when the document node has children beyond the root element, i.e.
// prolog/epilog Comment/PI Misc that the document-node model must expose.
let doc_has_misc (doc_kids:list xml_node) : bool =
  match doc_kids with [] -> false | [_] -> false | _ -> true

// XPath context item for a driver node. The document node presents to
// the XPath engine as its root element (ancestors empty), so absolute
// paths and "." behave correctly (copy-of/apply-templates/for-each of a
// relative child select from a "/" template go through the child-union
// fast path in select_nodes, which resolves against the document node's
// children directly and does not need a synthetic wrapper element -- a
// wrapper would otherwise leak an empty-tag element into copy-of ".").
let dnode_ci (nd:dnode) : xctx_item =
  match nd with
  | D_Doc root _ -> CI_Elem [] [] root
  | D_Item it -> it

// The children of a driver node, in document order, as driver nodes --
// the default node-set for xsl:apply-templates with no select. For a
// document node WITH prolog/epilog Misc, that child list is the prolog
// Misc, the root element, then the epilog Misc (the identity transform's
// built-in rule then copies a leading comment -- copy-2601); WITHOUT it,
// the single root element, exactly as before.
let dnode_children (nd:dnode) : list dnode =
  match nd with
  | D_Doc root doc_kids ->
    if doc_has_misc doc_kids
    then List.Tot.map (fun it -> D_Item it) (doc_child_items doc_kids)
    else [D_Item (CI_Elem [] [] root)]
  | D_Item (CI_Elem p anc n) -> List.Tot.map (fun it -> D_Item it) (child_items p anc n)
  | D_Item _ -> []

// (attributes, child-nodes) of a driver node in document order -- the
// basis of the child-union select fast path (see select_child_union).
let dnode_attrs_and_kids (nd:dnode) : (list xctx_item & list xctx_item) =
  match nd with
  | D_Doc root doc_kids ->
    if doc_has_misc doc_kids
    then ([], doc_child_items doc_kids)
    else ([], [CI_Elem [] [] root])
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
  // In-scope namespace declarations from the stylesheet element that
  // literal result elements copy onto the result tree (XSLT §7.5),
  // already stripped of the XSLT namespace and of any prefix named in
  // the stylesheet's exclude-result-prefixes. The serializer dedups
  // these against output ancestors so each appears once.
  xs_nsscope : list xml_attribute;
  // The stylesheet element's FULL namespace context (prefix -> URI),
  // UNfiltered by exclude-result-prefixes -- used to resolve prefixed
  // name tests in select/test/match XPath (XPath.Eval.matches_node_test,
  // pstep_ok). A prefix like `html` that is excluded from the RESULT
  // tree still names a namespace for pattern matching, so this must NOT
  // apply the exclude-result-prefixes filter that xs_nsscope does.
  xs_nsctx : list (string & string);
  // (element-name, attribute-name) pairs declared type ID in the SOURCE
  // document's DTD internal subset (from Parser.XML). Consulted by id()
  // and id()-anchored match patterns. [] when the source has no such DTD.
  xs_id_attrs : list (string & string);
  // The stylesheet document's root element, so document("") resolves to
  // the stylesheet itself as a source document.
  xs_style_root : xml_node;
}

let xslt_ns : string = "http://www.w3.org/1999/XSL/Transform"

// xsl:copy-of / identity copy of an element copies its namespace nodes
// (XSLT §11.3 / §7.5): the element's in-scope namespaces, including
// those inherited from source ancestors, are attached to the copied
// element (the serializer dedups against output ancestors). Non-element
// items copy verbatim.
let copy_of_item (it:xctx_item) : rnode =
  match it with
  | CI_Elem _ anc (XElement t attrs kids) ->
    let (_, own_seen) = ns_add [] [] attrs in
    let inherited =
      List.Tot.filter (fun (a:xml_attribute) -> a.attr_value <> xslt_ns)
        (inscope_ns [] own_seen anc) in
    R_Node (XElement t (List.Tot.append inherited attrs) kids)
  | _ -> item_to_rnode it

// Recursively remove every namespace declaration (xmlns / xmlns:pfx)
// from an element subtree. Realises xsl:copy-of's copy-namespaces="no"
// (XSLT 2.0 §11.9.2, copy-0601): the copied elements keep their names
// and content but shed all namespace nodes.
let rec strip_ns_node (n:xml_node) : Tot xml_node (decreases n) =
  match n with
  | XElement tag attrs kids ->
    let attrs' = List.Tot.filter (fun (a:xml_attribute) -> not (is_ns_decl a)) attrs in
    XElement tag attrs' (strip_ns_nodes kids)
  | other -> other
and strip_ns_nodes (ns:list xml_node) : Tot (list xml_node) (decreases ns) =
  match ns with
  | [] -> []
  | hd :: tl -> strip_ns_node hd :: strip_ns_nodes tl

let rnode_strip_ns (r:rnode) : rnode =
  match r with
  | R_Node n -> R_Node (strip_ns_node n)
  | _ -> r

let copy_of_item_no_ns (it:xctx_item) : rnode = rnode_strip_ns (copy_of_item it)

// Detect the prefix bound to the XSLT namespace on the stylesheet
// element's own xmlns:* declarations; default "xsl".
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

// `nsctx` is the stylesheet's in-scope namespace context (prefix -> URI)
// threaded to XPath.Eval so PREFIXED name tests in select/test/match
// XPath resolve to (namespace-URI, local-name) pairs -- see
// XPath.Eval.matches_node_test. It is constant for a whole transform
// (built from the stylesheet element's xmlns:* declarations).
// `id_attrs` (context document's DTD ID-typed attribute declarations) and
// `style_root` (the stylesheet document root, for document("")) are
// transform constants threaded to XPath.Eval so id() and document("")
// resolve. Both default to []/xnode_none on paths that never use them.
let eval_val (ctx:xctx_item) (pos:nat) (size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
             (id_attrs:list (string & string)) (style_root:xml_node) (expr_text:string)
  : xp_value =
  match parse_xpath expr_text with
  | None -> XV_Str ""
  | Some e ->
    let doc_nodes = xml_node_count (root_of_item ctx) in
    let fuel = initial_eval_fuel e doc_nodes in
    let env = { env_item = ctx; env_pos = pos; env_size = size; env_vars = vars; env_nsctx = nsctx; env_doc_kids = []; env_id_attrs = id_attrs; env_style_root = style_root } in
    eval_expr fuel env e

// AVT / sort-key / predicate call-outs never carry id()/document("")
// context in the vendored suite, so these keep their arity and pass the
// neutral defaults.
let eval_string (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string)) (expr_text:string) : string =
  to_string_val (eval_val ctx pos size vars nsctx [] xnode_none expr_text)

let eval_bool (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string)) (expr_text:string) : bool =
  to_bool_val (eval_val ctx pos size vars nsctx [] xnode_none expr_text)

// Drop `processing-instruction()` alternatives from a union select
// before handing it to XPath.Eval (which has no PI node test).
let is_pi_alt (s:string) : bool = trim_str s = "processing-instruction()"

let drop_pi_alts (sel:string) : string =
  let alts = split_on_char '|' sel in
  let kept = List.Tot.filter (fun a -> not (is_pi_alt a)) alts in
  match kept with
  | [] -> "self::processing-instruction()"   // whole thing was PI -> empty node set
  | _ -> String.concat "|" kept

let eval_nodeset (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string)) (sel:string) : list xctx_item =
  match eval_val ctx pos size vars nsctx [] xnode_none (drop_pi_alts sel) with
  | XV_Nodes items -> items
  | _ -> []

// ---- Document-node aware evaluation -------------------------------
// This engine models the document node (D_Doc) as the root element for
// XPath call-outs (dnode_ci). That is exact for absolute paths and ".",
// but a RELATIVE multi-step location path like `doc/num` evaluated from
// a `match="/"` template used to resolve child::doc against the root
// element itself and return the empty set. From the document node,
// `doc/num` is equivalent to the absolute `/doc/num` (the document
// node's only child IS the root element, which this engine matches as
// the first step of an absolute path). `force_abs` flips the top-level
// (and each union arm's) relative location path to absolute so those
// selects resolve; predicates and inner filter-paths keep their own
// (relative) context and are left untouched.
let rec force_abs (e:xp_expr) : Tot xp_expr (decreases e) =
  match e with
  | XE_Path false steps -> XE_Path true steps
  | XE_Union a b -> XE_Union (force_abs a) (force_abs b)
  | _ -> e

let eval_val_dn (ctx:dnode) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
                (id_attrs:list (string & string)) (style_root:xml_node) (expr_text:string)
  : xp_value =
  match ctx with
  | D_Item it -> eval_val it pos size vars nsctx id_attrs style_root expr_text
  | D_Doc root doc_kids ->
    (match parse_xpath expr_text with
     | None -> XV_Str ""
     | Some e ->
       let e2 = force_abs e in
       let doc_nodes = xml_node_count root in
       let fuel = initial_eval_fuel e2 doc_nodes in
       // env_doc_kids carries the document node's children so an absolute
       // path (force_abs made every top-level path absolute) resolves
       // against the true document node when prolog/epilog Misc are
       // present -- `//comment()` reaches a prolog comment (select-1001).
       let env = { env_item = CI_Elem [] [] root; env_pos = pos; env_size = size; env_vars = vars; env_nsctx = nsctx; env_doc_kids = doc_kids; env_id_attrs = id_attrs; env_style_root = style_root } in
       eval_expr fuel env e2)

let eval_string_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                   (id_attrs:list (string & string)) (style_root:xml_node) (expr_text:string) : string =
  to_string_val (eval_val_dn ctx pos size vars nsctx id_attrs style_root expr_text)

let eval_bool_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                 (id_attrs:list (string & string)) (style_root:xml_node) (expr_text:string) : bool =
  to_bool_val (eval_val_dn ctx pos size vars nsctx id_attrs style_root expr_text)

let eval_nodeset_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                    (id_attrs:list (string & string)) (style_root:xml_node) (sel:string) : list xctx_item =
  match eval_val_dn ctx pos size vars nsctx id_attrs style_root (drop_pi_alts sel) with
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

let rec expand_avt_chars (ctx:xctx_item) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
                         (cs:list char) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match cs with
    | [] -> ""
    | '{' :: '{' :: rest -> strcat "{" (expand_avt_chars ctx pos size vars nsctx rest (fuel - 1))
    | '}' :: '}' :: rest -> strcat "}" (expand_avt_chars ctx pos size vars nsctx rest (fuel - 1))
    | '{' :: rest ->
      let (expr_cs, after) = read_until_brace rest [] in
      let v = eval_string ctx pos size vars nsctx (str_of_chars expr_cs) in
      strcat v (expand_avt_chars ctx pos size vars nsctx after (fuel - 1))
    | c :: rest ->
      strcat (soc c) (expand_avt_chars ctx pos size vars nsctx rest (fuel - 1))

let expand_avt (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string)) (s:string) : string =
  let cs = chars_of s in
  if contains_char '{' s then expand_avt_chars ctx pos size vars nsctx cs (List.Tot.length cs + 1)
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

// Namespace-aware element name test for a MATCH-PATTERN step: the step
// name `nm` ("*" = any element) against element node `n` whose in-scope
// namespaces are its own attributes plus `anc` (its ancestors,
// nearest-first). Prefixes in `nm` resolve via the stylesheet's `nsctx`
// exactly as in XPath.Eval, so `h:title` matches a default-namespaced
// <title> in the XHTML namespace (the GRDDL case).
let pstep_ok (nsctx:list (string & string)) (nm:string) (n:xml_node) (anc:list xml_node) : bool =
  let nm' = trim_str nm in
  if nm' = "*" then true
  else match element_tag n with
       | Some tag ->
         // `pfx:*` (namespace wildcard, XPath 1.0 §2.3 / XSLT match
         // pattern) matches any element whose expanded-name namespace is
         // the URI bound to `pfx` in the stylesheet context, regardless of
         // the source prefix. Distinguished from a plain `pfx:local`
         // QName test by a "*" local part (match-045: `xhtml:*`).
         let tpfx = prefix_of nm' in
         if local_name_of nm' = "*" && tpfx <> "" then
           prefix_test_matches_elem nsctx tpfx (element_attrs n) anc tag
         else name_test_matches_elem nsctx nm' (element_attrs n) anc tag
       | None -> false

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
// `anc` is the ancestor CHAIN as element nodes (nearest-first): each
// step name resolves against the node's own attributes plus the tail of
// the chain above it, so prefixed steps are namespace-URI aware.
let rec match_up (nsctx:list (string & string)) (anchored:bool) (rsteps:list (pconn & string)) (childconn:pconn) (anc:list xml_node)
  : Tot bool (decreases (List.Tot.length rsteps + List.Tot.length anc)) =
  match rsteps with
  | [] -> if anchored then Nil? anc else true
  | (c, nm) :: rest ->
    (match childconn with
     | PC_Child ->
       (match anc with
        | [] -> false
        | a :: az -> pstep_ok nsctx nm a az && match_up nsctx anchored rest c az)
     | PC_Desc -> match_desc nsctx anchored nm rest c anc)

and match_desc (nsctx:list (string & string)) (anchored:bool) (nm:string) (rest:list (pconn & string)) (c:pconn) (anc:list xml_node)
  : Tot bool (decreases (List.Tot.length rest + List.Tot.length anc)) =
  match anc with
  | [] -> false
  | a :: az ->
    (pstep_ok nsctx nm a az && match_up nsctx anchored rest c az) || match_desc nsctx anchored nm rest c az

let alt_matches_elem (nsctx:list (string & string)) (a:string) (n:xml_node) (anc:list xml_node) : bool =
  let (anchored, steps) = parse_psteps a in
  match List.Tot.rev steps with
  | [] -> false
  | (ck, nk) :: rrest ->
    if not (pstep_ok nsctx nk n anc) then false
    else match_up nsctx anchored rrest ck anc

// Strip one layer of matching surrounding single/double quotes.
let strip_quotes (s:string) : string =
  let t = trim_str s in
  match chars_of t with
  | q :: rest ->
    if q = '\'' || q = '"' then
      (match List.Tot.rev rest with
       | q2 :: mid -> if q2 = q then str_of_chars (List.Tot.rev mid) else t
       | [] -> t)
    else t
  | [] -> t

// Literal target of a `processing-instruction('target')` node test, or
// None for the no-argument form `processing-instruction()` (which then
// matches any PI). `a` is assumed to start with "processing-instruction(".
let pi_test_target (a:string) : option string =
  match split_on_char '(' a with
  | _ :: rest :: _ ->
    let before_close = (match split_on_char ')' rest with x :: _ -> x | [] -> rest) in
    let t = trim_str before_close in
    if t = "" then None else Some (strip_quotes t)
  | _ -> None

let alt_matches_core (nsctx:list (string & string)) (alt:string) (nd:dnode) : bool =
  let a = trim_str alt in
  if a = "/" then (match nd with D_Doc _ _ -> true | _ -> false)
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
  else if starts_with "processing-instruction(" a then
    // processing-instruction('target') — matches a PI whose target is
    // the given literal (construct-node-026). XPath.Eval already carries
    // the NT_PI (Some target) node test for the axis path; this brings
    // the same test to XSLT match patterns.
    (match nd with
     | D_Item (CI_PI _ _ _ tgt _) ->
       (match pi_test_target a with None -> true | Some want -> tgt = want)
     | _ -> false)
  else if starts_with "@" a then
    (match nd with
     | D_Item (CI_Attr _ anc owner att) ->
       let nm = str_of_chars (drop_prefix_chars (chars_of a) 1) in
       let tpfx = prefix_of nm in
       // `@pfx:*` namespace-wildcard attribute pattern (match-045: the
       // `@xhtml:*` template). Matches any attribute whose namespace URI
       // is the one `pfx` names in the stylesheet context. Plain `@name`
       // keeps the literal-name test (unchanged behaviour).
       if local_name_of nm = "*" && tpfx <> "" then
         (match lookup_nsctx nsctx tpfx with
          | None -> string_starts_with att.attr_name (strcat tpfx ":")
          | Some turi ->
            let apfx = prefix_of att.attr_name in
            apfx <> "" && ns_uri_eq (resolve_ns_uri apfx (element_attrs owner) anc) (Some turi))
       else att.attr_name = nm
     | _ -> false)
  // Explicit `attribute::` axis prefix in a match pattern -- the same
  // node test as the `@` abbreviation, just spelled out. Needed for
  // patterns like `attribute::*` / `attribute::name` (W3C test
  // node-1102): without this the pattern never matches ANY node (the
  // final catch-all below only tries the ELEMENT path matcher), so an
  // `attribute::*` template silently never fires and the attribute
  // falls through to the built-in template instead.
  else if a = "attribute::*" then
    (match nd with D_Item (CI_Attr _ _ _ _) -> true | _ -> false)
  else if starts_with "attribute::" a then
    (match nd with
     | D_Item (CI_Attr _ _ _ att) -> att.attr_name = str_of_chars (drop_prefix_chars (chars_of a) 11)
     | _ -> false)
  else
    (match nd with
     | D_Item (CI_Elem _ anc n) -> alt_matches_elem nsctx a n anc
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
    a <> "" && not (starts_with "." a) && not (starts_with "$" a)
    && not (contains_char '/' a) && not (contains_char '[' a)
    && not (contains_char '(' a) && not (contains_double_colon a)

let rec all_child_union_alts (alts:list string) : Tot bool (decreases alts) =
  match alts with
  | [] -> true
  | a :: rest -> if is_child_union_alt a then all_child_union_alts rest else false

let is_simple_child_union (sel:string) : bool =
  let alts = split_on_char '|' sel in
  match alts with [] -> false | _ -> all_child_union_alts alts

let rec any_core_matches (nsctx:list (string & string)) (alts:list string) (it:xctx_item) : Tot bool (decreases alts) =
  match alts with
  | [] -> false
  | a :: rest -> if alt_matches_core nsctx a (D_Item it) then true else any_core_matches nsctx rest it

// Document-ordered node-set for a simple child union: attributes (if
// the union selects them) first, then child nodes in document order.
let select_child_union (nsctx:list (string & string)) (nd:dnode) (alts:list string) : list xctx_item =
  let (attrs, kids) = dnode_attrs_and_kids nd in
  let sel_attrs = List.Tot.filter (fun it -> any_core_matches nsctx alts it) attrs in
  let sel_kids = List.Tot.filter (fun it -> any_core_matches nsctx alts it) kids in
  sel_attrs @ sel_kids

// Node-set for a select expression on the current context node. A
// "simple child union" (only forward child-axis node tests, e.g. the
// identity pattern *|@*|comment()|processing-instruction()|text(), or
// a bare child name) is resolved directly in document order; anything
// else (paths, predicates, axes, functions, ".") goes through the full
// XPath.Eval engine.
let select_nodes (ctx:dnode) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
                 (id_attrs:list (string & string)) (style_root:xml_node) (sel:string)
  : list xctx_item =
  if is_simple_child_union sel then select_child_union nsctx ctx (split_on_char '|' sel)
  else eval_nodeset_dn ctx pos size vars nsctx id_attrs style_root sel

// XSLT 1.0 5.5 proximity position: position()/last() inside a match-
// pattern predicate ("name[position()=last()]", apply-templates/
// conflict-resolution-1301) are NOT the surrounding apply-templates/
// for-each position -- they count the node among its OWN SIBLINGS that
// satisfy the pattern's node test (namepart), independent of the
// enclosing context. siblings_of/item_path/path_compare (XPath.Eval)
// already rebuild a node's parent-relative sibling list with document-
// order paths for the sibling axes, so this reuses them rather than
// re-deriving parent/child bookkeeping. A node with no ancestors (the
// document's root element) has no siblings and is trivially (1, 1).
let match_proximity (nsctx:list (string & string)) (namepart:string) (it:xctx_item) : (nat & nat) =
  let sibs = siblings_of it in
  if Nil? sibs then (1, 1)
  else
    let matching = List.Tot.filter (fun s -> alt_matches_core nsctx namepart (D_Item s)) sibs in
    let p = item_path it in
    let before = List.Tot.filter (fun s -> path_compare (item_path s) p < 0) matching in
    (List.Tot.length before + 1, List.Tot.length matching)

// Evaluate a "name[pred]" predicate best-effort as a boolean against
// the candidate node. Self-fuelled via eval_bool. The predicate is
// evaluated with the node's PROXIMITY position/size (see
// match_proximity), not the caller's apply-templates/for-each
// position -- those are unrelated per XSLT 5.5.
// An id()-anchored match pattern (`id('x')`, `id('x')/a/b`, `id('x')//b`)
// matches a node N iff N is a member of the node-set the pattern selects
// when evaluated as an expression from the context document (XSLT 1.0
// §5.2). id() is absolute, so the starting context is immaterial -- we
// evaluate from the document root. Membership is by document-order path.
let match_id_pattern (id_attrs:list (string & string)) (nsctx:list (string & string)) (pat:string) (it:xctx_item) : bool =
  match parse_xpath pat with
  | None -> false
  | Some e ->
    let root = root_of_item it in
    let fuel = initial_eval_fuel e (xml_node_count root) in
    let env = { env_item = CI_Elem [] [] root; env_pos = 1; env_size = 1; env_vars = []; env_nsctx = nsctx; env_doc_kids = []; env_id_attrs = id_attrs; env_style_root = xnode_none } in
    // Membership by node identity: same element node AND same ancestor
    // chain. Not by item_path, because the candidate `it` may have been
    // selected under the document-node path framing (root element at [i])
    // while the pattern's own id()-rooted evaluation numbers the root at
    // [] -- the two schemes disagree by that offset, so a path compare
    // misses (id-016's `b/c`-selected id14 vs the `id('id8')//c` pattern).
    // Structural node+ancestor equality is offset-independent; the fixture
    // has no identical-content twins under an identical ancestor chain.
    let same_node (s:xctx_item) : bool =
      match s, it with
      | CI_Elem _ sanc sn, CI_Elem _ ianc inode -> sn = inode && sanc = ianc
      | _, _ -> item_path s = item_path it
    in
    (match eval_expr fuel env e with
     | XV_Nodes items -> List.Tot.existsb same_node items
     | _ -> false)

let alt_matches (vars:list (string & xp_value)) (nsctx:list (string & string)) (id_attrs:list (string & string)) (alt:string) (nd:dnode) : bool =
  if starts_with "id(" (trim_str alt) then
    (match nd with D_Item it -> match_id_pattern id_attrs nsctx (trim_str alt) it | _ -> false)
  else
  let (namepart, predopt) = split_predicate alt in
  match predopt with
  | None -> alt_matches_core nsctx alt nd
  | Some pred ->
    if not (alt_matches_core nsctx namepart nd) then false
    else
      match nd with
      | D_Doc _ _ -> eval_bool (dnode_ci nd) 1 1 vars nsctx pred
      | D_Item it ->
        let (p, s) = match_proximity nsctx namepart it in
        eval_bool it p s vars nsctx pred

let rec any_alt_matches (vars:list (string & xp_value)) (nsctx:list (string & string)) (id_attrs:list (string & string)) (alts:list string) (nd:dnode)
  : Tot bool (decreases alts) =
  match alts with
  | [] -> false
  | a :: rest -> if alt_matches vars nsctx id_attrs a nd then true else any_alt_matches vars nsctx id_attrs rest nd

let template_matches (vars:list (string & xp_value)) (nsctx:list (string & string)) (id_attrs:list (string & string)) (tpl:template) (nd:dnode) : bool =
  if tpl.tpl_match = "" then false
  else any_alt_matches vars nsctx id_attrs (split_on_char '|' tpl.tpl_match) nd

// Default priority of a single alternative (x10 to keep integers).
let alt_priority (alt:string) : int =
  let a = trim_str alt in
  if a = "*" || a = "@*" || a = "node()" || a = "text()" || a = "comment()"
     || a = "processing-instruction()" || a = "attribute::*"
  then -5
  else if contains_char '/' a || contains_char '[' a then 5
  else
    // `pfx:*` / `@pfx:*` namespace-wildcard test: XSLT 1.0 §5.5 default
    // priority -0.25 (x10 = -2 here), between a QName test (0) and a bare
    // node test (-0.5). A prefixed name with a "*" local part.
    let core = if starts_with "@" a then str_of_chars (drop_prefix_chars (chars_of a) 1) else a in
    if local_name_of core = "*" && prefix_of core <> "" then -2
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
let rec pick_template (vars) (nsctx:list (string & string)) (id_attrs:list (string & string)) (mode:string) (tpls:list template) (nd:dnode) (best:option template)
  : Tot (option template) (decreases tpls) =
  match tpls with
  | [] -> best
  | t :: rest ->
    let best' =
      if t.tpl_mode = mode && template_matches vars nsctx id_attrs t nd then
        (match best with
         | None -> Some t
         | Some b -> if template_priority t >= template_priority b then Some t else best)
      else best
    in
    pick_template vars nsctx id_attrs mode rest nd best'

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

// Nearest-first lookup of the URI a prefix is bound to in the output
// scope accumulated from ancestor elements.
let rec lookup_ns (scope:list (string & string)) (pfx:string) : Tot (option string) (decreases scope) =
  match scope with
  | [] -> None
  | (p, u) :: rest -> if p = pfx then Some u else lookup_ns rest pfx

// Emit an element's namespace declarations, suppressing any that are
// already in scope with the same URI (XSLT §7.5 / XML serialization:
// no redundant declarations). Returns the serialized xmlns attributes
// plus the scope extended with every declaration this element makes.
let rec emit_ns_decls (scope:list (string & string)) (decls:list xml_attribute)
  : Tot (string & list (string & string)) (decreases decls) =
  match decls with
  | [] -> ("", scope)
  | a :: rest ->
    (match ns_decl_prefix a.attr_name with
     | None -> emit_ns_decls scope rest
     | Some pfx ->
       let cur = lookup_ns scope pfx in
       // A declaration is redundant if the same prefix is already bound to
       // the same URI in scope. Additionally, an unbind (xmlns="" /
       // xmlns:pfx="") is redundant when the prefix is not bound at all in
       // scope -- there is nothing to reset (namespace-4501: a null-
       // namespace xsl:element at a context with no default namespace must
       // NOT emit a spurious xmlns="").
       let redundant =
         (cur = Some a.attr_value) ||
         (a.attr_value = "" && cur = None) in
       let scope' = if redundant then scope else (pfx, a.attr_value) :: scope in
       let (s_rest, scope'') = emit_ns_decls scope' rest in
       let here = if redundant then "" else serialize_attr a in
       (strcat here s_rest, scope''))

let rec serialize_node (scope:list (string & string)) (n:xml_node) : Tot string (decreases n) =
  match n with
  | XText t -> escape_text t
  | XCDATA t -> escape_text t
  | XComment t -> String.concat "" ["<!--"; t; "-->"]
  | XPI tg d -> String.concat "" ["<?"; tg; " "; d; "?>"]
  | XElement tag attrs children ->
    // Namespace declarations serialize first (deduped against ancestors);
    // then the ordinary attributes.
    let (decls, normal) = List.Tot.partition is_ns_decl attrs in
    let (ns_str, scope') = emit_ns_decls scope decls in
    let a = strcat ns_str (serialize_attrs normal) in
    // XML output method: an element whose content serializes to nothing
    // (no children, or only empty text nodes produced by e.g. an empty
    // xsl:value-of) is written as an empty-element tag `<t/>`, matching
    // the W3C expected outputs (which self-close such elements).
    let inner = serialize_nodes scope' children in
    if inner = "" then String.concat "" ["<"; tag; a; "/>"]
    else String.concat "" ["<"; tag; a; ">"; inner; "</"; tag; ">"]

and serialize_nodes (scope:list (string & string)) (ns:list xml_node) : Tot string (decreases ns) =
  match ns with
  | [] -> ""
  | hd :: tl -> strcat (serialize_node scope hd) (serialize_nodes scope tl)

let serialize_result (n:xml_node) : string = serialize_node [] n

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

// ASCII case folding for the case-order collation below (non-ASCII
// characters are left unchanged, which is conservative — they never
// participate in a case-only tie).
let ascii_lower_char (c:char) : char =
  let n = FStar.Char.int_of_char c in
  if n >= 0x41 && n <= 0x5A then FStar.Char.char_of_int (n + 0x20) else c

let is_ascii_lower (c:char) : bool =
  let n = FStar.Char.int_of_char c in n >= 0x61 && n <= 0x7A

// Primary key of the case-order collation: compare case-folded, by
// codepoint. So "Namespaces" and "must" order case-insensitively.
let rec cmp_chars_ci (a b : list char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let lx = FStar.Char.int_of_char (ascii_lower_char x) in
    let ly = FStar.Char.int_of_char (ascii_lower_char y) in
    if lx = ly then cmp_chars_ci xs ys
    else if lx < ly then -1 else 1

// Tiebreak among strings equal under the case-folded primary key: the
// first position that differs is a same-letter case difference. Under
// lower-first the lowercase variant sorts first; upper-first mirrors it.
let rec cmp_chars_case (lower_first:bool) (a b : list char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    if x = y then cmp_chars_case lower_first xs ys
    else
      let x_is_lower = is_ascii_lower x in
      if lower_first then (if x_is_lower then -1 else 1)
      else (if x_is_lower then 1 else -1)

// XSLT 1.0 §10 case-order collation for xsl:sort. Applied ONLY when
// case-order= is explicitly present (so_case_order <> 0); the default
// text sort keeps the codepoint String.compare path, so the other sort
// tests are untouched. Primary key is the ASCII-case-folded string;
// case-only ties break by case-order (sort-043).
let cmp_text_caseorder (lower_first:bool) (a b : string) : int =
  let ca = chars_of a in
  let cb = chars_of b in
  let prim = cmp_chars_ci ca cb in
  if prim <> 0 then prim else cmp_chars_case lower_first ca cb

type sortspec = {
  so_select : string;
  so_numeric : bool;
  so_descending : bool;
  so_case_order : int;   // 0 = none (codepoint), 1 = lower-first, 2 = upper-first
}

// The data-type / order attributes of xsl:sort are attribute value
// templates (XSLT 1.0 §10), so they are AVT-expanded against the
// context node in scope when the enclosing for-each / apply-templates
// is instantiated (the `ctx`/`pos`/`size`/`vars` supplied here). The
// select attribute is a plain XPath expression, NOT an AVT.
let parse_sort (ctx:xctx_item) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
               (pfx:string) (n:xml_node) : option sortspec =
  match n with
  | XElement tag attrs _ ->
    if is_xsl pfx tag && xsl_instr pfx tag = "sort" then
      let dt = expand_avt ctx pos size vars nsctx (attr_or "data-type" "text" attrs) in
      let od = expand_avt ctx pos size vars nsctx (attr_or "order" "ascending" attrs) in
      let co = expand_avt ctx pos size vars nsctx (attr_or "case-order" "" attrs) in
      Some { so_select = attr_or "select" "." attrs;
             so_numeric = (dt = "number");
             so_descending = (od = "descending");
             so_case_order = (if co = "lower-first" then 1
                              else if co = "upper-first" then 2 else 0) }
    else None
  | _ -> None

// Leading xsl:sort children (whitespace-only text AND comments between
// them are skipped; the first non-sort content stops the collection).
let rec collect_sorts (ctx:xctx_item) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
                      (pfx:string) (body:list xml_node) : Tot (list sortspec) (decreases body) =
  match body with
  | [] -> []
  | hd :: tl ->
    (match parse_sort ctx pos size vars nsctx pfx hd with
     | Some s -> s :: collect_sorts ctx pos size vars nsctx pfx tl
     | None ->
       (match hd with
        | XText t -> if is_all_ws t then collect_sorts ctx pos size vars nsctx pfx tl else []
        | XComment _ -> collect_sorts ctx pos size vars nsctx pfx tl
        | _ -> []))

// The sort key strings for one node, evaluated with the node's OWN
// proximity position/size in the unsorted node list (so a sort by
// position() or last() is correct). One string per sort spec.
let rec eval_sort_keys (specs:list sortspec) (vars:list (string & xp_value)) (nsctx:list (string & string))
                       (it:xctx_item) (pos size:nat)
  : Tot (list string) (decreases specs) =
  match specs with
  | [] -> []
  | s :: rest -> eval_string it pos size vars nsctx s.so_select :: eval_sort_keys rest vars nsctx it pos size

// Annotate each node with its precomputed sort keys, threading the
// 1-based position through the ORIGINAL (document-order) list.
let rec annotate_items (specs:list sortspec) (vars:list (string & xp_value)) (nsctx:list (string & string))
                       (items:list xctx_item) (pos size:nat)
  : Tot (list (xctx_item & list string)) (decreases items) =
  match items with
  | [] -> []
  | it :: tl -> (it, eval_sort_keys specs vars nsctx it pos size) :: annotate_items specs vars nsctx tl (pos + 1) size

// Compare two nodes by their precomputed key lists, honoring each
// spec's data-type and order. A NaN key (non-numeric text under
// data-type="number") sorts before every real number in ascending
// order, which is what the W3C numeric-sort reference outputs expect.
let rec cmp_sort_keys (specs:list sortspec) (ka kb:list string)
  : Tot int (decreases specs) =
  match specs, ka, kb with
  | s :: sr, a :: ar, b :: br ->
    let raw =
      if s.so_numeric then
        (let na = string_to_xn a in
         let nb = string_to_xn b in
         match xn_compare na nb with
         | Some c -> c
         | None ->
           let a_nan = (match na with XN_NaN -> true | _ -> false) in
           let b_nan = (match nb with XN_NaN -> true | _ -> false) in
           if a_nan && b_nan then 0 else if a_nan then -1 else 1)
      else if s.so_case_order = 0 then String.compare a b
      else cmp_text_caseorder (s.so_case_order = 1) a b in
    let signed = if s.so_descending then 0 - raw else raw in
    if signed <> 0 then signed else cmp_sort_keys sr ar br
  | _, _, _ -> 0

// Stable insertion sort: an element with a key equal to an already-
// placed one is inserted AFTER it, preserving original document order
// among equal keys (XSLT 1.0 sorts are stable).
let rec sort_insert (specs:list sortspec) (x:(xctx_item & list string)) (l:list (xctx_item & list string))
  : Tot (list (xctx_item & list string)) (decreases l) =
  match l with
  | [] -> [x]
  | y :: ys -> if cmp_sort_keys specs (snd x) (snd y) <= 0 then x :: l else y :: sort_insert specs x ys

let rec sort_items (specs:list sortspec) (l:list (xctx_item & list string))
  : Tot (list (xctx_item & list string)) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> sort_insert specs x (sort_items specs xs)

let sort_maybe (ctx:xctx_item) (pos size:nat) (pfx:string)
               (vars:list (string & xp_value)) (nsctx:list (string & string)) (body:list xml_node) (items:list xctx_item)
  : list xctx_item =
  match collect_sorts ctx pos size vars nsctx pfx body with
  | [] -> items
  | specs ->
    let n = List.Tot.length items in
    List.Tot.map fst (sort_items specs (annotate_items specs vars nsctx items 1 n))

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

// `svars`/`srtf` seed the matched template's xsl:param slots: they carry
// xsl:with-param bindings from an enclosing xsl:apply-templates (XSLT 1.0
// §11.6). For a plain apply-templates with no with-param they are
// st.xs_globals / [] and the behavior is unchanged. The built-in rule
// does NOT forward params (§5.8), so it re-seeds with globals only.
let rec dispatch (fuel:nat) (st:xstyle) (nd:dnode) (pos size:nat) (mode:string)
                 (svars:list (string & xp_value)) (srtf:list (string & list rnode))
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match pick_template st.xs_globals st.xs_nsctx st.xs_id_attrs mode st.xs_templates nd None with
    | Some tpl -> instantiate_seq (fuel - 1) st nd pos size svars srtf tpl.tpl_body
    | None -> builtin_rule (fuel - 1) st nd mode

and builtin_rule (fuel:nat) (st:xstyle) (nd:dnode) (mode:string) : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match nd with
    | D_Doc _ _ ->
      let kids = dnode_children nd in
      apply_list (fuel - 1) st kids 1 (List.Tot.length kids) mode st.xs_globals []
    | D_Item (CI_Elem _ _ _) ->
      let kids = dnode_children nd in
      apply_list (fuel - 1) st kids 1 (List.Tot.length kids) mode st.xs_globals []
    | D_Item (CI_Text _ _ _ t) -> [R_Node (XText t)]
    | D_Item (CI_Attr _ _ _ a) -> [R_Node (XText a.attr_value)]
    | D_Item (CI_Comment _ _ _ _) -> []
    | D_Item (CI_PI _ _ _ _ _) -> []

// Apply templates (in the active mode) to a list of driver nodes,
// threading 1-based position and the common size.
and apply_list (fuel:nat) (st:xstyle) (nodes:list dnode) (pos size:nat) (mode:string)
               (svars:list (string & xp_value)) (srtf:list (string & list rnode))
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match nodes with
    | [] -> []
    | hd :: tl ->
      let here = dispatch (fuel - 1) st hd pos size mode svars srtf in
      here @ apply_list (fuel - 1) st tl (pos + 1) size mode svars srtf

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
                let v = eval_val_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel in
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

// Bind xsl:with-param children (select= or body RTF) for xsl:call-template
// and xsl:apply-templates. `evars`/`ertf` are the CALLER's in-scope
// variables + result-tree fragments, used to evaluate each with-param's
// select=/body; the bound pairs accumulate onto the seed lists
// `svars`/`srtf`, which start at st.xs_globals / [] and become the callee
// template's parameter seed. Separating the evaluation scope from the seed
// is what lets a with-param whose value references a LOCAL variable of the
// calling template resolve correctly (hcard2rdf.xsl forwards select="$field"
// both to <xsl:call-template name="testclass"> and to a recursive
// <xsl:apply-templates ... mode="extract-field">) without leaking the
// caller's locals into the callee.
and bind_with_params_scoped (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                            (evars:list (string & xp_value)) (ertf:list (string & list rnode))
                            (svars:list (string & xp_value)) (srtf:list (string & list rnode))
                            (children:list xml_node)
  : Tot (list (string & xp_value) & list (string & list rnode)) (decreases fuel) =
  if fuel = 0 then (svars, srtf)
  else
    match children with
    | [] -> (svars, srtf)
    | hd :: tl ->
      (match hd with
       | XElement tag attrs pchildren ->
         if is_xsl st.xs_pfx tag && xsl_instr st.xs_pfx tag = "with-param" then
           let nm = attr_or "name" "" attrs in
           (match attr_opt "select" attrs with
            | Some sel ->
              let v = eval_val_dn ctx pos size evars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel in
              bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf ((nm, v) :: svars) srtf tl
            | None ->
              let frag = instantiate_seq (fuel - 1) st ctx pos size evars ertf pchildren in
              let sval = text_value_nodes (only_nodes frag) in
              bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf ((nm, XV_Str sval) :: svars) ((nm, frag) :: srtf) tl)
         else bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf svars srtf tl
       | _ -> bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf svars srtf tl)

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
          [R_Node (XText (eval_string_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root (attr_or "select" "." attrs)))]
        else if ln = "text" then
          [R_Node (XText (raw_text children))]
        else if ln = "if" then
          (if eval_bool_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root (attr_or "test" "false()" attrs)
           then instantiate_seq (fuel - 1) st ctx pos size vars rtf children
           else [])
        else if ln = "choose" then
          instantiate_choose (fuel - 1) st ctx pos size vars rtf children
        else if ln = "for-each" then
          let sel = attr_or "select" "." attrs in
          // XSLT 1.0 §5.4: the current node list is the selected node-set
          // in DOCUMENT ORDER with duplicates removed (only overridden by
          // an xsl:sort). doc_sort_dedup fixes reverse-axis proximity
          // order (preceding::, ancestor::) and de-duplicates descendant
          // (//) selects before iteration.
          let items0 = doc_sort_dedup (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel) in
          let items = sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars st.xs_nsctx children items0 in
          for_each_items (fuel - 1) st children vars rtf items 1 (List.Tot.length items)
        else if ln = "apply-templates" then
          let amode = attr_or "mode" "" attrs in
          // xsl:with-param children seed the params of whichever templates
          // match the selected nodes (XSLT 1.0 §11.6). Their select= /
          // body is evaluated in THIS instruction's scope (current context
          // node + the caller's in-scope variables `vars`/`rtf`), so a
          // recursive apply-templates that forwards a param with
          // select="$field" resolves the caller's local $field. The bound
          // pairs are prepended onto st.xs_globals to form the callee seed.
          let (pvars, prtf) =
            bind_with_params_scoped (fuel - 1) st ctx pos size vars rtf st.xs_globals [] children in
          (match attr_opt "select" attrs with
           | Some sel ->
             let items0 = doc_sort_dedup (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel) in
             let items = sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars st.xs_nsctx children items0 in
             let dns = List.Tot.map (fun it -> D_Item it) items in
             apply_list (fuel - 1) st dns 1 (List.Tot.length items) amode pvars prtf
           | None ->
             // Default node-set = the context node's children; an
             // xsl:sort child reorders them (apply-templates with no
             // select still honors xsl:sort).
             let kids0 = dnode_children ctx in
             let items0 = List.Tot.map dnode_ci kids0 in
             let items = sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars st.xs_nsctx children items0 in
             let dns = List.Tot.map (fun it -> D_Item it) items in
             apply_list (fuel - 1) st dns 1 (List.Tot.length items) amode pvars prtf)
        else if ln = "call-template" then
          let nm = attr_or "name" "" attrs in
          (match find_named_template st.xs_templates nm with
           | Some tpl ->
             // Named-template invocation keeps the current context node.
             // with-param bindings seed the called template's params;
             // recursion is bounded by the same fuel as every other call
             // (a self-calling template exhausts fuel and yields [], not
             // a nonterminating loop). Each with-param's select=/body is
             // evaluated in the CALLER's scope (its in-scope variables
             // `vars`/`rtf`) so a param forwarded as select="$field"
             // resolves the caller's local $field (hcard2rdf.xsl calls
             // <xsl:call-template name="testclass"> with val="$field");
             // the bound pairs seed onto st.xs_globals for the callee.
             let (cvars, crtf) = bind_with_params_scoped (fuel - 1) st ctx pos size vars rtf st.xs_globals [] children in
             instantiate_seq (fuel - 1) st ctx pos size cvars crtf tpl.tpl_body
           | None -> [])
        else if ln = "copy-of" then
          let sel = attr_or "select" "." attrs in
          // copy-namespaces="no" (XSLT 2.0) strips namespace nodes from the
          // copied elements; the default "yes" keeps them (copy-0601).
          let no_ns = (attr_or "copy-namespaces" "yes" attrs = "no") in
          let mk = if no_ns then copy_of_item_no_ns else copy_of_item in
          (match rtf_var_name sel with
           | Some nm ->
             (match rtf_find rtf nm with
              | Some frag -> if no_ns then List.Tot.map rnode_strip_ns frag else frag
              | None -> List.Tot.map mk (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel))
           | None -> List.Tot.map mk (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root sel))
        else if ln = "copy" then
          instantiate_copy (fuel - 1) st ctx pos size vars rtf children
        else if ln = "element" then
          let nm = expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx (attr_or "name" "" attrs) in
          let epfx = name_prefix nm in
          // xsl:element namespace (XSLT 1.0 §7.1.2, namespace-4501). With
          // an explicit namespace= AVT the element goes into that URI; with
          // none, an unprefixed name takes the stylesheet's default
          // namespace (null if none), a prefixed name its bound URI. The
          // resulting xmlns/xmlns:pfx declaration is attached to the built
          // element; the serializer dedups it (and suppresses a redundant
          // xmlns="" when the output default is already null).
          let nsdecls : list xml_attribute =
            (match attr_opt "namespace" attrs with
             | Some nsraw ->
               let u = expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx nsraw in
               if epfx = "" then [ { attr_name = "xmlns"; attr_value = u } ]
               else if u = "" then []
               else [ { attr_name = strcat "xmlns:" epfx; attr_value = u } ]
             | None ->
               if epfx = "" then
                 (match lookup_nsctx st.xs_nsctx "" with
                  | Some u -> [ { attr_name = "xmlns"; attr_value = u } ]
                  | None -> [ { attr_name = "xmlns"; attr_value = "" } ])
               else
                 (match lookup_nsctx st.xs_nsctx epfx with
                  | Some u -> [ { attr_name = strcat "xmlns:" epfx; attr_value = u } ]
                  | None -> [])) in
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
          [R_Node (build_element nm nsdecls body)]
        else if ln = "attribute" then
          let nm = expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx (attr_or "name" "" attrs) in
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
        // XSLT §7.5: xsl:-namespaced attributes (xsl:exclude-result-
        // prefixes, xsl:use-attribute-sets, …) and any declaration of
        // the XSLT namespace itself are NOT written to the result tree.
        let kept =
          List.Tot.filter
            (fun (a:xml_attribute) ->
               not (starts_with (strcat st.xs_pfx ":") a.attr_name) &&
               not (is_ns_decl a && a.attr_value = xslt_ns))
            attrs in
        let out_attrs =
          List.Tot.map
            (fun (a:xml_attribute) ->
               { attr_name = a.attr_name; attr_value = expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx a.attr_value })
            kept in
        let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
        // An unprefixed literal result element is in the stylesheet's
        // default namespace. If that namespace was named in
        // exclude-result-prefixes (#default) it is absent from xs_nsscope,
        // yet the element still USES it, so it must be declared (XSLT §7.5
        // namespace fixup: exclude-result-prefixes only drops UNused
        // namespace nodes, never the element's own namespace). Add it only
        // when otherwise missing (not on the element, not already in
        // nsscope) so every previously-passing case is byte-identical; the
        // serializer dedups it against an ancestor declaring the same
        // default (namespace-4801).
        let default_ns_fixup : list xml_attribute =
          if contains_char ':' tag then []
          else if List.Tot.existsb (fun (a:xml_attribute) -> a.attr_name = "xmlns") kept
               || List.Tot.existsb (fun (a:xml_attribute) -> a.attr_name = "xmlns") st.xs_nsscope then []
          else (match lookup_nsctx st.xs_nsctx "" with
                | Some u -> if u <> "" then [ { attr_name = "xmlns"; attr_value = u } ] else []
                | None -> []) in
        // Copy the in-scope stylesheet namespace nodes onto the result
        // element (deduped later by the serializer).
        [R_Node (build_element tag (default_ns_fixup @ st.xs_nsscope @ out_attrs) body)]

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
             (if eval_bool_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root (attr_or "test" "false()" attrs)
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
    | D_Doc _ _ -> instantiate_seq (fuel - 1) st ctx pos size vars rtf children
    | D_Item (CI_Elem _ anc n) ->
      (match n with
       | XElement t _ _ ->
         let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf children in
         // xsl:copy copies the element's namespace nodes (its in-scope
         // declarations), but not its attributes or content; the
         // serializer dedups against output ancestors. All in-scope
         // namespaces are copied, including one bound to the XSLT
         // namespace: when the copied node comes from document("") (the
         // stylesheet loaded as a source document) its xmlns:xsl is an
         // ordinary namespace node that xsl:copy must preserve
         // (namespace-4801). A source node in a normal transform never has
         // the XSLT namespace in scope, so this is a no-op for those.
         let nsnodes = inscope_ns [] [] (n :: anc) in
         [R_Node (build_element t nsnodes body)]
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

// The stylesheet element's full namespace context (prefix -> URI),
// UNfiltered by exclude-result-prefixes -- see the xs_nsctx field.
let rec build_nsctx (attrs:list xml_attribute) : Tot (list (string & string)) (decreases attrs) =
  match attrs with
  | [] -> []
  | a :: rest ->
    (match ns_decl_prefix a.attr_name with
     | Some pfx -> (pfx, a.attr_value) :: build_nsctx rest
     | None -> build_nsctx rest)

// Top-level xsl:variable / xsl:param with a select= expression,
// evaluated once against the source DOCUMENT node (XSLT 1.0 §11.4: the
// context node for a global variable is the root node, not the document
// element). Using the document-node evaluator makes a relative location
// path like `data/row` resolve as the absolute `/data/row` — evaluating
// it against the root ELEMENT instead (the earlier behaviour) looked for
// a `data` CHILD of `<data>` and returned the empty node-set, so
// `for-each select="$var"` over such a global silently produced nothing
// (namespace-1701).
let rec collect_globals (pfx:string) (nsctx:list (string & string)) (children:list xml_node) (source:xml_node) (doc_kids:list xml_node)
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
            let v = eval_val_dn (D_Doc source doc_kids) 1 1 [] nsctx [] xnode_none sel in
            (nm, v) :: collect_globals pfx nsctx tl source doc_kids
          | _, _ -> collect_globals pfx nsctx tl source doc_kids)
       else collect_globals pfx nsctx tl source doc_kids
     | _ -> collect_globals pfx nsctx tl source doc_kids)

// Parse a whitespace-separated prefix list (exclude-result-prefixes).
// "#default" designates the default namespace (prefix "").
let parse_prefix_list (s:string) : list string =
  List.Tot.map (fun p -> if p = "#default" then "" else p)
    (List.Tot.filter (fun p -> p <> "")
       (List.Tot.map trim_str (split_on_char ' ' s)))

// In-scope namespace declarations of the stylesheet element that
// literal result elements must copy: every xmlns declaration EXCEPT
// the XSLT namespace and any prefix named in exclude-result-prefixes.
//
// Ordering note (2026-07-13): apply-templates/conflict-resolution-1301
// and copy/copy-3102 both attach THIS SAME list (via xs_nsscope, below)
// to a literal result element -- 1301's `<fo:root>` wants xmlns:fo
// before the stylesheet's default xmlns, and 3102's `<out>` wants its
// three prefixed declarations alphabetical. An earlier attempt assumed
// the two tests needed different ORDERING STRATEGIES by PROVENANCE
// (raw stylesheet-declaration-order for this LRE path vs.
// sorted-by-prefix for the separate xsl:copy/copy-of source-namespace
// path in instantiate_copy/copy_of_item below) and flipping xs_nsscope
// to emit raw stylesheet order broke 3102 (whose stylesheet declares
// xmlns:foo, xmlns:joes, xmlns:huh in THAT order, not the expected
// xmlns:foo, xmlns:huh, xmlns:joes). Tracing both fixtures byte for
// byte shows they are not actually on different provenance paths --
// 3102's <out> reaches this SAME build_nsscope/xs_nsscope list, same as
// 1301's <fo:root>. The real defect was narrower: attr_name_cmp sorted
// by the raw attribute-name STRING, under which "xmlns" (default,
// prefix "") sorts before "xmlns:x" (any prefixed decl) because it is
// a literal string prefix of it -- so the default namespace always
// came first. Real serializers commonly put it last. Fixing
// attr_name_cmp to sort by extracted PREFIX with the empty (default)
// prefix pushed to the end satisfies both fixtures with the existing
// single sorted-order list: no stylesheet-order/sorted-order split
// needed after all. The xsl:copy / copy-of source-namespace path
// (inscope_ns/ns_add/copy_of_item/instantiate_copy) never sorts --
// it preserves source-document declaration order, unaffected by this
// change, which remains correct provenance separation in its own
// right (it just isn't what distinguishes 1301 from 3102).
let build_nsscope (attrs:list xml_attribute) : list xml_attribute =
  let excluded = parse_prefix_list (attr_or "exclude-result-prefixes" "" attrs) in
  List.Tot.sortWith attr_name_cmp
    (List.Tot.filter
      (fun (a:xml_attribute) ->
         match ns_decl_prefix a.attr_name with
         | None -> false
         | Some pfx -> a.attr_value <> xslt_ns && not (mem_str pfx excluded))
      attrs)

let build_style (stylesheet:xml_node) (source:xml_node) (doc_kids:list xml_node) (id_attrs:list (string & string)) : xstyle =
  match stylesheet with
  | XElement tag attrs children ->
    let pfx = xsl_prefix_of stylesheet in
    if is_xsl pfx tag &&
       (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform") then
      let nsctx = build_nsctx attrs in
      { xs_pfx = pfx;
        xs_templates = collect_templates pfx children;
        xs_method = find_output_method pfx children;
        xs_globals = collect_globals pfx nsctx children source doc_kids;
        xs_nsscope = build_nsscope attrs;
        xs_nsctx = nsctx;
        xs_id_attrs = id_attrs;
        xs_style_root = stylesheet }
    else
      // Simplified stylesheet: the literal result element IS the body
      // of a single template matching the document root. Its own
      // namespace declarations are on the element itself, so no
      // inherited scope is threaded.
      { xs_pfx = pfx;
        xs_templates = [ { tpl_match = "/"; tpl_name = ""; tpl_mode = ""; tpl_prio = None; tpl_body = [stylesheet] } ];
        xs_method = "xml";
        xs_globals = [];
        xs_nsscope = [];
        xs_nsctx = build_nsctx attrs;
        xs_id_attrs = id_attrs;
        xs_style_root = stylesheet }
  | _ ->
    { xs_pfx = "xsl"; xs_templates = []; xs_method = "xml"; xs_globals = []; xs_nsscope = []; xs_nsctx = [];
      xs_id_attrs = id_attrs; xs_style_root = stylesheet }

// The root element among a document node's children (the single element
// child; XML well-formedness guarantees exactly one). Used to recover the
// legacy `source` root from the full child list for transform_doc.
let rec doc_root_elem (doc_kids:list xml_node) : Tot (option xml_node) (decreases doc_kids) =
  match doc_kids with
  | [] -> None
  | (XElement t a c) :: _ -> Some (XElement t a c)
  | _ :: tl -> doc_root_elem tl

let rec xml_nodes_count_sum (ns:list xml_node) : Tot nat (decreases ns) =
  match ns with
  | [] -> 0
  | hd :: tl -> xml_node_count hd + xml_nodes_count_sum tl

(* ================================================================ *)
(* Entry point.                                                       *)
(* ================================================================ *)

// Legacy entry: `source` is the root element alone (the document node has
// no prolog/epilog Misc). GRDDL and the js/npm bridge use this; behavior
// is byte-for-byte what it was before the document-node model existed.
let transform (stylesheet:xml_node) (source:xml_node) : string =
  let st = build_style stylesheet source [source] [] in
  // Fuel: generous multiple of the combined tree sizes -- every
  // apply-templates / instantiate step consumes one unit.
  let sz = xml_node_count stylesheet + xml_node_count source in
  let fuel = op_Multiply (sz + 1) 256 + 100000 in
  let result = dispatch fuel st (D_Doc source [source]) 1 1 "" st.xs_globals [] in
  let nodes = only_nodes result in
  if st.xs_method = "text" then text_value_nodes nodes
  else serialize_nodes [] nodes

// Document-node aware entry: `source_kids` is the full ordered child list
// of the source document node (prolog Comment/PI Misc, root element,
// epilog Misc), from Parser.XML.parse_xml_document_children. The XSLT
// document node then exposes those Misc nodes, so `//comment()` reaches a
// prolog comment (select-1001) and the identity transform copies a leading
// comment (copy-2601). With no Misc (source_kids = [root]) it reduces to
// `transform` exactly.
let transform_doc (stylesheet:xml_node) (source_kids:list xml_node) : string =
  match doc_root_elem source_kids with
  | None -> ""
  | Some root ->
    let st = build_style stylesheet root source_kids [] in
    let sz = xml_node_count stylesheet + xml_nodes_count_sum source_kids in
    let fuel = op_Multiply (sz + 1) 256 + 100000 in
    let result = dispatch fuel st (D_Doc root source_kids) 1 1 "" st.xs_globals [] in
    let nodes = only_nodes result in
    if st.xs_method = "text" then text_value_nodes nodes
    else serialize_nodes [] nodes

// Document-node aware entry that ALSO threads the SOURCE document's DTD
// internal-subset ATTLIST ID-type declarations (from
// Parser.XML.parse_xml_document_children_with_ids). id() and id()-anchored
// match patterns need it; document("") uses the stylesheet root (recorded
// in build_style). Reduces to transform_doc when source_id_attrs = [].
let transform_doc_ids (stylesheet:xml_node) (source_kids:list xml_node) (source_id_attrs:list (string & string)) : string =
  match doc_root_elem source_kids with
  | None -> ""
  | Some root ->
    let st = build_style stylesheet root source_kids source_id_attrs in
    let sz = xml_node_count stylesheet + xml_nodes_count_sum source_kids in
    let fuel = op_Multiply (sz + 1) 256 + 100000 in
    let result = dispatch fuel st (D_Doc root source_kids) 1 1 "" st.xs_globals [] in
    let nodes = only_nodes result in
    if st.xs_method = "text" then text_value_nodes nodes
    else serialize_nodes [] nodes
