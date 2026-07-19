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
//   attribute value templates ({expr}), the built-in template
//   rules (root/element -> apply-templates in the current mode,
//   text/attribute -> copy string value, comment/PI -> no output),
//   and xsl:number (level=single/multiple/any + count/from patterns
//   reusing the match-pattern engine, value=, and format tokens
//   1/01/a/A/i/I with prefix/separator/suffix + grouping-separator/
//   grouping-size; letter-value="traditional", xml:lang-specific
//   numbering, and count/from patterns using key() are NOT honoured --
//   see the xsl:number section banner further down).
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
// xsl:import/xsl:include (XSLT 1.0 section 2.6) and xsl:apply-imports
// (section 5.6) ARE supported -- see the "Combining stylesheets" section
// below build_nsscope (sheet_tree, process_node/process_children/
// expand_include, build_style_from_units) and pick_template/
// pick_template_below's import-precedence-aware conflict resolution.
// The runner (bin/xslt-runner/xslt_runner.ml) resolves+reads the
// referenced files from disk and hands back a sheet_tree; this module
// owns 100% of the precedence/splicing semantics. xsl:next-match
// (XSLT 2.0) remains out of scope, as does per-file namespace context
// for a nested include/import target's OWN match/select patterns (no
// impincl fixture exercises a namespaced pattern inside an included/
// imported file; only the ROOT stylesheet's xs_nsctx is consulted).
//
// xsl:key/key()/generate-id() (XSLT 1.0 §12.2/§12.4): top-level
// xsl:key(name, match, use) declarations are collected (collect_keys)
// and materialised into a flat key-value-node table (build_key_table) by
// matching every node in the source document against each key's `match`
// pattern (reusing the same any_alt_matches pattern engine templates
// use) and evaluating its `use` expression at each match. key() and
// generate-id() are XPath.Eval functions threaded the table (and, for
// generate-id, the item's own document-order path) exactly like
// format-number's decimal-format table. Known narrowness: a key's
// `match` pattern is only tested against all_document_items (elements +
// text/comment/PI descendants), never attribute nodes -- no idkey
// fixture declares `match="@..."`, the same scope id() already accepts;
// key() used as a TEMPLATE MATCH PATTERN itself (idkey03/35/44-48) is
// not specially supported (falls through to ordinary pattern text
// comparison, so those few fixtures do not match); and key-table
// construction only walks the transform's OWN source document -- a key
// looked up against a document() secondary document (idkey50) sees no
// entries for it (document() itself only supports the empty-string
// "stylesheet itself" case here, so this rarely matters in practice).
//
// Deliberately OUT of scope (a mismatch here is expected, not a bug):
//   document() for non-empty URIs, xsl:next-match,
//   xsl:sort lang collations, the
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

// `String.string_of_char` extracts to OCaml's byte-oriented `Char.chr`
// (FStar_String.ml: `string_of_char c = BatString.of_char (Char.chr c)`),
// defined only for 0..255 and raising `Invalid_argument("Char.chr")`
// above that -- crashing on any codepoint > 255 reaching text/attribute
// serialization (issue #307: Apache-Xalan output-output28/73,
// sort-sort-alphabet-polish/russian hit this via escape_text_char /
// escape_attr_char / expand_avt_chars). `chars_of` decodes real Unicode
// codepoints via BatUTF8, so re-encoding a single decoded codepoint must
// use `String.string_of_list [c]`, which extracts to
// `BatUTF8.init 1 (fun _ -> BatUChar.chr c)` -- full 0..0x10FFFF range,
// proper multi-byte UTF-8. For codepoints < 128 this is the identical
// single ASCII byte (UTF-8 == ASCII there), so passing output is
// unaffected. Same trap-class fix as RDF.Canonical / RDF.NQuads (#272).
let soc (c:char) : string = String.string_of_list [c]

let chars_of (s:string) : list char = String.list_of_string s
let str_of_chars (cs:list char) : string = String.string_of_list cs

// ASCII case folding (used by both the xsl:sort case-order collation
// and xsl:number's lower-case roman-numeral rendering below). Non-ASCII
// characters are left unchanged, which is conservative for the sort
// collation — they never participate in a case-only tie.
let ascii_lower_char (c:char) : char =
  let n = FStar.Char.int_of_char c in
  if n >= 0x41 && n <= 0x5A then FStar.Char.char_of_int (n + 0x20) else c

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

// Insert/update `a` into `acc` by attr_name: if a name match exists its
// VALUE is replaced but its POSITION is kept (the same "add first, then
// let later/more-specific instructions override in place" merge that
// XSLT uses everywhere two attribute sources can collide -- a literal
// attribute value template vs. an xsl:attribute child, an attribute-set
// vs. the element's own attributes, xsl:attribute vs. xsl:attribute).
let rec attrs_upsert (acc:list xml_attribute) (a:xml_attribute) : Tot (list xml_attribute) (decreases acc) =
  match acc with
  | [] -> [a]
  | hd :: tl -> if hd.attr_name = a.attr_name then a :: tl else hd :: attrs_upsert tl a

// Fold `overrides` onto `base`, upserting each in turn: same-name
// attributes in `overrides` win the VALUE but not the position (the
// base list's first-occurrence ordering survives); brand-new names are
// appended in the order `overrides` introduces them.
let rec merge_attrs_override (base:list xml_attribute) (overrides:list xml_attribute)
  : Tot (list xml_attribute) (decreases overrides) =
  match overrides with
  | [] -> base
  | hd :: tl -> merge_attrs_override (attrs_upsert base hd) tl

let only_attrs (rs:list rnode) : list xml_attribute =
  let (attrs, _) = split_rnodes rs [] [] in attrs

// build_element folds the body's R_Attr entries (from xsl:attribute
// instructions in the element's content) onto extra_attrs (namespace
// declarations, literal/AVT attributes, and -- once attribute-sets are
// threaded in -- use-attribute-sets-derived attributes) via
// merge_attrs_override rather than a plain list append: XSLT 1.0
// §7.1.3/7.1.4 lets a later xsl:attribute REPLACE an attribute already
// established by a literal attribute or an attribute-set, in place
// (attribset06/10/11/12/18).
let build_element (tag:string) (extra_attrs:list xml_attribute) (body:list rnode) : xml_node =
  let (attrs, nodes) = split_rnodes body [] [] in
  XElement tag (merge_attrs_override extra_attrs attrs) nodes

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
  // A namespace node copied directly (e.g. copy-of of a namespace::
  // selection) serialises as its namespace declaration.
  | CI_Namespace _ _ _ pfx uri ->
    R_Attr ({ attr_name = (if pfx = "" then "xmlns" else strcat "xmlns:" pfx); attr_value = uri })

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
  // Import precedence (XSLT 1.0 section 2.6.2): HIGHER wins outright in
  // template conflict resolution, regardless of tpl_prio. Every template
  // from a stylesheet with no xsl:import/xsl:include gets the SAME
  // constant (0) here, which makes the precedence comparison in
  // pick_template a no-op and falls through to the original priority-only
  // comparison -- byte-identical behavior for every stylesheet that
  // doesn't use combining (protects the pre-existing Xalan/xslt/xml-conformance
  // scores). Assigned by collect_templates_prec / the sheet_tree merge
  // (build_style_from_units) via a postorder numbering of the import
  // tree: see the "Combining stylesheets" section below build_nsscope.
  tpl_import_prec : int;
}

// A named top-level xsl:attribute-set declaration (XSLT 1.0 §7.1.4),
// COMBINED across every xsl:attribute-set element sharing the same
// name (a stylesheet may declare a name more than once). ase_deps is
// this combined declaration's own use-attribute-sets dependency names
// (space-separated, in the order they're listed); ase_own is its own
// xsl:attribute children, to be instantiated (AVT-expanded, etc.)
// against the CURRENT context each time the set is used -- attribute
// values are not fixed at parse time.
//
// Merge order for same-named decls (collect_attribute_sets below):
// combined = LAST-declared decl's (deps, own) FIRST, then the next-to-
// last, ... down to the FIRST-declared decl's (deps, own) LAST. This
// reverse-declaration-order concatenation is what Xalan's own merge
// produces for duplicate-name attribute-sets with non-conflicting
// attribute names (attribset10/27/29/31/32/41 in the Apache-Xalan
// xslt1 suite); it is implementation-defined for a stylesheet whose
// duplicate-name attribute-sets have COLLIDING attribute names AND
// their own nested use-attribute-sets (attribset42/43) -- the merged
// VALUES still come out correct there (last-declared decl's value
// wins per XSLT 1.0 §7.1.4's "recover ... using the attribute nearest
// the end of the stylesheet"), but the exact attribute ORDER in that
// double-nested-collision corner does not match Xalan's specific
// internal algorithm. Left as a known gap; not chased further.
noeq type attrset_entry = {
  ase_name : string;
  ase_deps : list string;
  ase_own  : list xml_node;
}

let rec find_attrset_entry (entries:list attrset_entry) (nm:string) : Tot (option attrset_entry) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest -> if e.ase_name = nm then Some e else find_attrset_entry rest nm

// Whitespace-separated QName list (cdata-section-elements' grammar,
// and use-attribute-sets'/xsl:attribute-set's own use-attribute-sets
// grammar -- both are simple whitespace-separated name lists; unlike
// exclude-result-prefixes there is no "#default" token in either).
let parse_qname_list (s:string) : list string =
  List.Tot.filter (fun p -> p <> "") (List.Tot.map trim_str (split_on_char ' ' s))

// xsl:output (XSLT 1.0 section 16), merged across every top-level
// xsl:output element (there may be several -- 16: "attribute values...
// are determined by ... the elements... merged"). Scalar attributes take
// the value of the LAST xsl:output element that specifies them (falling
// through to an earlier one, then the built-in default, when later
// elements omit it); cdata-section-elements is the UNION of every
// element's list, not last-wins (Xalan output-output46/87 both pin this).
// `os_cdata` names are stored pre-resolved to (namespace-URI, local-name)
// pairs (see resolve_qname_ns) because resolution needs the stylesheet's
// nsctx, which is only in scope where collect_output_settings runs.
noeq type output_settings = {
  os_method_raw : string;        // "" = no xsl:output specified method
  os_omit_decl : bool;           // omit-xml-declaration="yes"; default false
  os_standalone : string;        // "" = unspecified; else "yes"/"no"
  os_indent_raw : string;        // "" = unspecified; else "yes"/"no"
  os_encoding : string;          // default "UTF-8"
  os_version : string;           // default "1.0"
  os_doctype_public : string;    // "" = none
  os_doctype_system : string;    // "" = none
  os_cdata : list (option string & string);
}

let default_output_settings : output_settings = {
  os_method_raw = ""; os_omit_decl = false; os_standalone = ""; os_indent_raw = "";
  os_encoding = "UTF-8"; os_version = "1.0"; os_doctype_public = ""; os_doctype_system = "";
  os_cdata = [];
}

noeq type xstyle = {
  xs_pfx : string;
  xs_templates : list template;
  // Top-level xsl:attribute-set declarations, keyed by name, already
  // merged across duplicate-name decls (see attrset_entry / merge order
  // above collect_attribute_sets). Threaded to instantiate_one/
  // instantiate_copy so use-attribute-sets (on a literal result
  // element, xsl:element, or xsl:copy) can expand.
  xs_attrsets : list attrset_entry;
  xs_method : string;
  // Whether at least one top-level xsl:output element was present in the
  // stylesheet. FALSE means the transform's final serialization step MUST
  // reproduce the exact pre-xsl:output-support behaviour byte for byte
  // (no XML declaration, no DOCTYPE, no indent, no CDATA wrapping) -- the
  // hard compatibility requirement that protects the ~1109 Xalan-corpus
  // passes and the xslt slice-1 suite that predate this feature.
  xs_output_present : bool;
  xs_output : output_settings;
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
  // Top-level xsl:decimal-format declarations (named + at most one
  // default/unnamed), for format-number()'s 3rd argument. Duplicate
  // names (including the unnamed default declared twice) resolve to
  // the LAST one parsed -- XSLT 1.0 requires them to agree on every
  // attribute anyway (a static-error case this engine does not detect),
  // so which one wins is only observable when a fixture violates that
  // rule, and last-wins matches every duplicate-declaration Xalan
  // fixture in the numberformat suite (41/42, both consistent by
  // construction).
  xs_decfmts : list decimal_format_symbols;
  // xsl:key table (name, one entry per (matched source node, use-expr
  // node-set member)), for key(). [] means "no xsl:key declarations" --
  // key() then always selects the empty node-set. See build_key_table.
  xs_key_table : list key_entry;
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
// `decfmts` (the stylesheet's xsl:decimal-format table) likewise threads
// to XPath.Eval so format-number() sees named decimal-formats; [] means
// format-number falls back to the built-in defaults for every name.
// `key_table` (the stylesheet's xsl:key table, build_key_table) likewise
// threads so key() resolves; [] means key() always selects nothing.
let eval_val (ctx:xctx_item) (pos:nat) (size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
             (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
             (key_table:list key_entry) (expr_text:string)
  : xp_value =
  match parse_xpath expr_text with
  | None -> XV_Str ""
  | Some e ->
    let doc_nodes = xml_node_count (root_of_item ctx) in
    let fuel = initial_eval_fuel e doc_nodes in
    let env = { env_item = ctx; env_pos = pos; env_size = size; env_vars = vars; env_nsctx = nsctx; env_doc_kids = []; env_id_attrs = id_attrs; env_style_root = style_root; env_decimal_formats = decfmts; env_key_table = key_table } in
    eval_expr fuel env e

// AVT / sort-key / predicate call-outs never carry id()/document()/
// decimal-format/key context in the vendored suite, so these keep their
// arity and pass the neutral defaults.
let eval_string (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string)) (expr_text:string) : string =
  to_string_val (eval_val ctx pos size vars nsctx [] xnode_none [] [] expr_text)

// A bare numeric predicate result is XPath 1.0 §2.4's positional
// shorthand (`[2]` means "proximity position 2", not "boolean(2)" =
// true) -- mirrors XPath.Eval's own filter_one_pred, which every
// ordinary location-step predicate (e.g. `select="item[2]"`) already
// goes through. eval_bool is the match-pattern-predicate path
// (alt_matches, called with the candidate's PROXIMITY pos/size from
// match_proximity), which had been missing this special case: a
// pattern predicate like `e[2]` in an xsl:number count pattern was
// falling through to to_bool_val's boolean(number) = "n <> 0", so
// EVERY e (not just the 2nd) satisfied it. Traced against Apache-Xalan
// numbering78 (`count="b|c|d|e[2]"`).
//
// id_attrs/style_root/decfmts/key_table are threaded (not the neutral
// defaults eval_string above still uses) so key()/id()/document("")/
// format-number() called from a match-pattern PREDICATE (e.g.
// `key('Info','id15')//Level3[Name[starts-with(@First,'J')]]`'s
// trailing `[...]`) see the same key table / DTD ID map / stylesheet
// root / decimal-format table the enclosing template's match resolved
// against, instead of always-empty (idkey44-48's key()-in-match-pattern
// cluster).
let eval_bool (ctx:xctx_item) (pos size:nat) (vars) (nsctx:list (string & string))
              (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
              (key_table:list key_entry) (expr_text:string) : bool =
  match eval_val ctx pos size vars nsctx id_attrs style_root decfmts key_table expr_text with
  | XV_Num n -> (match xn_finite_int (xn_round n) with Some k -> k = pos | None -> false)
  | v -> to_bool_val v

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
  match eval_val ctx pos size vars nsctx [] xnode_none [] [] (drop_pi_alts sel) with
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
// the first step of an absolute path). `force_abs` flips every relative
// location path REACHABLE WITHOUT crossing a context boundary to
// absolute -- so this recurses into union arms, boolean/comparison/
// arithmetic operands, a unary negation's operand, and EVERY function-
// call argument (a FunCall's arguments are evaluated in the SAME
// context as the call itself, e.g. `id(main/b)`, `count(main/b)`,
// `key('k', main/@x)` -- the `main/b` argument needs the identical
// doc-node-relative treatment the top-level select would get, or it
// silently resolves to the empty node-set: `main` never matches as a
// child of the root element itself, only as a child of the document
// node). A FilterPath's `primary` is likewise forced (it is the
// top-level context too), but its predicates and trailing continuation
// steps are context boundaries -- once `primary` has selected nodes,
// later predicates/steps are relative to THOSE nodes, not to the
// document root -- so they stay untouched, as do the predicates nested
// inside an xp_step (step_preds): those are evaluated per-candidate at
// that step, never at the top-level document-node context.
let rec force_abs (e:xp_expr) : Tot xp_expr (decreases e) =
  match e with
  | XE_Path false steps -> XE_Path true steps
  | XE_Path true steps -> XE_Path true steps
  | XE_FilterPath primary preds steps -> XE_FilterPath (force_abs primary) preds steps
  | XE_Union a b -> XE_Union (force_abs a) (force_abs b)
  | XE_Or a b -> XE_Or (force_abs a) (force_abs b)
  | XE_And a b -> XE_And (force_abs a) (force_abs b)
  | XE_Compare op a b -> XE_Compare op (force_abs a) (force_abs b)
  | XE_Arith op a b -> XE_Arith op (force_abs a) (force_abs b)
  | XE_Neg a -> XE_Neg (force_abs a)
  | XE_FunCall name args -> XE_FunCall name (force_abs_list args)
  | _ -> e

and force_abs_list (es:list xp_expr) : Tot (list xp_expr) (decreases es) =
  match es with
  | [] -> []
  | h :: t -> force_abs h :: force_abs_list t

let eval_val_dn (ctx:dnode) (pos size:nat) (vars:list (string & xp_value)) (nsctx:list (string & string))
                (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                (key_table:list key_entry) (expr_text:string)
  : xp_value =
  match ctx with
  | D_Item it -> eval_val it pos size vars nsctx id_attrs style_root decfmts key_table expr_text
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
       let env = { env_item = CI_Elem [] [] root; env_pos = pos; env_size = size; env_vars = vars; env_nsctx = nsctx; env_doc_kids = doc_kids; env_id_attrs = id_attrs; env_style_root = style_root; env_decimal_formats = decfmts; env_key_table = key_table } in
       eval_expr fuel env e2)

let eval_string_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                   (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                   (key_table:list key_entry) (expr_text:string) : string =
  to_string_val (eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts key_table expr_text)

let eval_bool_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                 (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                 (key_table:list key_entry) (expr_text:string) : bool =
  to_bool_val (eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts key_table expr_text)

let eval_nodeset_dn (ctx:dnode) (pos size:nat) (vars) (nsctx:list (string & string))
                    (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                    (key_table:list key_entry) (sel:string) : list xctx_item =
  match eval_val_dn ctx pos size vars nsctx id_attrs style_root decfmts key_table (drop_pi_alts sel) with
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
                 (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                 (key_table:list key_entry) (sel:string)
  : list xctx_item =
  if is_simple_child_union sel then select_child_union nsctx ctx (split_on_char '|' sel)
  else eval_nodeset_dn ctx pos size vars nsctx id_attrs style_root decfmts key_table sel

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
// An id()/key()-anchored match pattern (`id('x')`, `id('x')/a/b`,
// `id('x')//b`, `key('k','v')`, `key('k','v')//b[pred]` -- XSLT 1.0
// §5.2's IdKeyPattern production) matches a node N iff N is a member of
// the node-set the pattern selects when evaluated as an expression from
// the context document. id()/key() are absolute, so the starting
// context is immaterial -- we evaluate from the document root, with the
// SAME vars/id_attrs/style_root/decfmts/key_table the enclosing
// transform has (previously hardcoded to []/xnode_none/[]/[], which
// silently zeroed out any `key()` call here, any `$var` in a trailing
// predicate, and any `document("")`/`format-number()` -- idkey43's
// `id('id2')/*[name()=$major]/text()` and idkey44-48's
// `key('Info','id15')//Level3[...]` clusters). Membership is by
// document-order path.
let match_expr_pattern (vars:list (string & xp_value)) (nsctx:list (string & string))
                       (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                       (key_table:list key_entry) (pat:string) (it:xctx_item) : bool =
  match parse_xpath pat with
  | None -> false
  | Some e ->
    let root = root_of_item it in
    let fuel = initial_eval_fuel e (xml_node_count root) in
    let env = { env_item = CI_Elem [] [] root; env_pos = 1; env_size = 1; env_vars = vars; env_nsctx = nsctx; env_doc_kids = []; env_id_attrs = id_attrs; env_style_root = style_root; env_decimal_formats = decfmts; env_key_table = key_table } in
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

// An IdKeyPattern anchor is `id(Literal)` or `key(Literal,Literal)`
// (XSLT 1.0 §5.2 grammar production 3); trailing steps/predicates ride
// along inside `pat` and are handled by match_expr_pattern's own
// eval_expr call, so this dispatch only has to recognise the anchor.
let is_idkey_pattern (alt:string) : bool =
  let a = trim_str alt in
  starts_with "id(" a || starts_with "key(" a

let alt_matches (vars:list (string & xp_value)) (nsctx:list (string & string))
                (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                (key_table:list key_entry) (alt:string) (nd:dnode) : bool =
  if is_idkey_pattern alt then
    (match nd with D_Item it -> match_expr_pattern vars nsctx id_attrs style_root decfmts key_table (trim_str alt) it | _ -> false)
  else
  let (namepart, predopt) = split_predicate alt in
  match predopt with
  | None -> alt_matches_core nsctx alt nd
  | Some pred ->
    if not (alt_matches_core nsctx namepart nd) then false
    else
      match nd with
      | D_Doc _ _ -> eval_bool (dnode_ci nd) 1 1 vars nsctx id_attrs style_root decfmts key_table pred
      | D_Item it ->
        let (p, s) = match_proximity nsctx namepart it in
        eval_bool it p s vars nsctx id_attrs style_root decfmts key_table pred

let rec any_alt_matches (vars:list (string & xp_value)) (nsctx:list (string & string))
                        (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                        (key_table:list key_entry) (alts:list string) (nd:dnode)
  : Tot bool (decreases alts) =
  match alts with
  | [] -> false
  | a :: rest ->
    if alt_matches vars nsctx id_attrs style_root decfmts key_table a nd then true
    else any_alt_matches vars nsctx id_attrs style_root decfmts key_table rest nd

let template_matches (vars:list (string & xp_value)) (nsctx:list (string & string))
                     (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                     (key_table:list key_entry) (tpl:template) (nd:dnode) : bool =
  if tpl.tpl_match = "" then false
  else any_alt_matches vars nsctx id_attrs style_root decfmts key_table (split_on_char '|' tpl.tpl_match) nd

(* ================================================================ *)
(* xsl:number (XSLT 1.0 §7.7 / §7.7.1).                                *)
(*                                                                     *)
(* Counting (level=single/multiple/any + count/from patterns) is built  *)
(* directly on the ancestor / preceding-sibling / preceding axis        *)
(* helpers XPath.Eval already exports (ancestor_axis, preceding_sibling_*)
(* axis, preceding_axis, item_path, path_is_prefix) and on THIS file's   *)
(* own match-pattern engine (any_alt_matches / alt_matches_core), so a   *)
(* count/from pattern gets id()-anchoring, predicates with proximity     *)
(* position(), and namespace-aware name tests for free -- the same       *)
(* pattern language as xsl:template match=.                              *)
(*                                                                       *)
(* `from`'s boundary differs by level. level=single/multiple stop their  *)
(* upward ancestor-or-self walk the instant they reach a node matching   *)
(* `from` (that node, and anything above it root-ward, is excluded).     *)
(*                                                                       *)
(* level=any is NOT ancestor-subtree-scoped -- it is a single flat        *)
(* counter over the WHOLE document in document order, and any `from`      *)
(* match RESETS that counter to zero the instant it is encountered,       *)
(* wherever it sits (cousin subtree or ancestor, doesn't matter). Traced  *)
(* by hand against Apache-Xalan numbering18 (level=any from="chapter",     *)
(* default count "note": three untouched notes, three notes inside a      *)
(* chapter -- reset to 1..3 -- three more untouched notes RESUMING at 4    *)
(* (not 7: the chapter's own notes never contributed to the untouched     *)
(* run's count), three more chapter notes reset to 1..3 again, three      *)
(* more untouched notes resuming at 4 again) and numbering67 (level=any    *)
(* from="b|d", count defaults to "title", 15+ levels of a/b/c/d/e          *)
(* nesting with resets firing at every b/d regardless of depth). Both      *)
(* match exactly once the counter is computed by walking self's reverse-   *)
(* document-order neighbourhood (self, then every ancestor/preceding       *)
(* node in decreasing document position) and stopping dead the moment a    *)
(* `from` match is hit.                                                    *)
(* ================================================================ *)

// Small unsigned-integer parser for the grouping-size AVT (a plain
// digit string; anything else -- absent, non-numeric -- means "no
// grouping", 0).
let rec parse_nat_chars (cs:list char) (acc:nat) : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: rest ->
    let d = FStar.Char.int_of_char c - 0x30 in
    if d >= 0 && d <= 9 then parse_nat_chars rest (op_Multiply acc 10 + d) else None

// The default `count` pattern (XSLT 1.0 §7.7: "any node with the same
// node type as the current node and, if the current node has an
// expanded-name, with the same expanded-name") expressed as a pattern
// string this file's own match-pattern engine already understands.
let default_count_pattern (it:xctx_item) : string =
  match it with
  | CI_Elem _ _ n -> (match element_tag n with Some t -> t | None -> "*")
  | CI_Text _ _ _ _ -> "text()"
  | CI_Comment _ _ _ _ -> "comment()"
  | CI_PI _ _ _ _ _ -> "processing-instruction()"
  | CI_Attr _ _ _ a -> strcat "@" a.attr_name
  | CI_Namespace _ _ _ _ _ -> "*"

// Does `node` match the (possibly "|"-unioned) count/from pattern?
// Reuses the template match-pattern engine directly (any_alt_matches),
// wrapping the candidate as a D_Item so id()-anchored patterns and
// predicates (evaluated at the candidate's own proximity position, via
// match_proximity inside alt_matches) behave exactly as they do for
// xsl:template match=.
let count_matches (vars:list (string & xp_value)) (nsctx:list (string & string))
                  (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                  (key_table:list key_entry) (pat:string) (node:xctx_item) : bool =
  any_alt_matches vars nsctx id_attrs style_root decfmts key_table (split_on_char '|' pat) (D_Item node)

// 1 + the number of NODE's preceding-siblings matching the count
// pattern (XSLT 1.0 §7.7, the common inner step of level=single AND
// level=multiple).
let count_with_preceding (vars:list (string & xp_value)) (nsctx:list (string & string))
                         (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                         (key_table:list key_entry) (count_pat:string) (node:xctx_item) : nat =
  1 + List.Tot.length (List.Tot.filter (count_matches vars nsctx id_attrs style_root decfmts key_table count_pat) (preceding_sibling_axis node))

// level=single: walk the ancestor-or-self chain (self first) for the
// FIRST node matching `count`; a `from`-match reached before any count
// match is a hard stop (no eligible ancestor -> empty result).
let rec find_level_single (vars:list (string & xp_value)) (nsctx:list (string & string))
                          (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                          (key_table:list key_entry) (count_pat:string) (from_pat:string) (chain:list xctx_item)
  : Tot (option xctx_item) (decreases chain) =
  match chain with
  | [] -> None
  | node :: rest ->
    if count_matches vars nsctx id_attrs style_root decfmts key_table count_pat node then Some node
    else if from_pat <> "" && count_matches vars nsctx id_attrs style_root decfmts key_table from_pat node then None
    else find_level_single vars nsctx id_attrs style_root decfmts key_table count_pat from_pat rest

let level_single_numbers (vars:list (string & xp_value)) (nsctx:list (string & string))
                         (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                         (key_table:list key_entry) (count_pat:string) (from_pat:string) (self:xctx_item) : list nat =
  let chain = self :: ancestor_axis self in
  match find_level_single vars nsctx id_attrs style_root decfmts key_table count_pat from_pat chain with
  | None -> []
  | Some c -> [count_with_preceding vars nsctx id_attrs style_root decfmts key_table count_pat c]

// level=multiple: walk the WHOLE ancestor-or-self chain to the root,
// collecting a (1+preceding) count at every node that matches `count`,
// outermost-first (so "chapter.section.subsection" reads left to
// right); a `from`-match is a hard stop for the walk (that node and
// everything above it, root-ward, is excluded).
let rec multiple_numbers (vars:list (string & xp_value)) (nsctx:list (string & string))
                         (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                         (key_table:list key_entry) (count_pat:string) (from_pat:string) (chain:list xctx_item)
  : Tot (list nat) (decreases chain) =
  match chain with
  | [] -> []
  | node :: rest ->
    if from_pat <> "" && count_matches vars nsctx id_attrs style_root decfmts key_table from_pat node then []
    else
      let tail = multiple_numbers vars nsctx id_attrs style_root decfmts key_table count_pat from_pat rest in
      if count_matches vars nsctx id_attrs style_root decfmts key_table count_pat node
      then tail @ [count_with_preceding vars nsctx id_attrs style_root decfmts key_table count_pat node]
      else tail

let level_multiple_numbers (vars:list (string & xp_value)) (nsctx:list (string & string))
                           (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                           (key_table:list key_entry) (count_pat:string) (from_pat:string) (self:xctx_item) : list nat =
  multiple_numbers vars nsctx id_attrs style_root decfmts key_table count_pat from_pat (self :: ancestor_axis self)

// ancestor_axis and preceding_axis (XPath.Eval) are each already
// individually nearest-first (reverse document order), but they don't
// interleave with each other in that order automatically -- an
// ancestor's own preceding siblings (reached via preceding_axis, since
// preceding:: excludes only the context node's OWN ancestors, not a
// cousin ancestor's siblings) can sit, in true document order, between
// two nodes that came from different one of the two lists. A standard
// descending merge on path_compare recombines them into one genuine
// reverse-document-order sequence.
let rec merge_desc_items (xs ys:list xctx_item)
  : Tot (list xctx_item) (decreases (List.Tot.length xs + List.Tot.length ys)) =
  match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xs', y :: ys' ->
    if path_compare (item_path x) (item_path y) >= 0
    then x :: merge_desc_items xs' ys
    else y :: merge_desc_items xs ys'

// `nodes` is in reverse document order (nearest to the numbered node
// first, self included as the head when called from level_any_numbers
// below). A `from` match at `n` is the reset point: `n` and everything
// further back (`rest`) contribute nothing, so the scan stops dead
// instead of recursing. Absent a `from` match at `n`, `n`'s own
// `count`-match (if any) adds 1 and the scan continues backward.
let rec scan_any_from_reset (vars:list (string & xp_value)) (nsctx:list (string & string))
                            (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                            (key_table:list key_entry) (count_pat:string) (from_pat:string) (nodes:list xctx_item)
  : Tot nat (decreases nodes) =
  match nodes with
  | [] -> 0
  | n :: rest ->
    if from_pat <> "" && count_matches vars nsctx id_attrs style_root decfmts key_table from_pat n then 0
    else
      let here = if count_matches vars nsctx id_attrs style_root decfmts key_table count_pat n then 1 else 0 in
      here + scan_any_from_reset vars nsctx id_attrs style_root decfmts key_table count_pat from_pat rest

let level_any_numbers (vars:list (string & xp_value)) (nsctx:list (string & string))
                      (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                      (key_table:list key_entry) (count_pat:string) (from_pat:string) (self:xctx_item) : list nat =
  let neighborhood = merge_desc_items (ancestor_axis self) (preceding_axis self) in
  [scan_any_from_reset vars nsctx id_attrs style_root decfmts key_table count_pat from_pat (self :: neighborhood)]

// Dispatch on level= (default "single"); a non-element/text/comment/pi
// context (e.g. the document node itself, or an attribute) has no
// ancestor-or-self chain worth walking, so xsl:number is a no-op there.
let level_numbers (vars:list (string & xp_value)) (nsctx:list (string & string))
                  (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                  (key_table:list key_entry) (level:string) (count_raw:string) (from_pat:string) (self:xctx_item) : list nat =
  let count_pat = if count_raw = "" then default_count_pattern self else count_raw in
  if level = "multiple" then level_multiple_numbers vars nsctx id_attrs style_root decfmts key_table count_pat from_pat self
  else if level = "any" then level_any_numbers vars nsctx id_attrs style_root decfmts key_table count_pat from_pat self
  else level_single_numbers vars nsctx id_attrs style_root decfmts key_table count_pat from_pat self

(* ---- Number-to-string formatting (XSLT 1.0 §7.7.1) ---------------- *)

// Bijective base-26 letter numbering: 1 -> "a", 26 -> "z", 27 -> "aa",
// 28 -> "ab" (NOT the "aa","bb","cc" repeated-letter scheme -- this is
// the same convention as spreadsheet column names). `fuel` bounds the
// division loop (n+1 steps always suffice: each step divides by 26).
let alpha_digit_char (upper:bool) (d:nat) : char =
  let base = if upper then 0x41 else 0x61 in
  FStar.Char.char_of_int (base + (if d < 26 then d else 25))

let rec alpha_digits (upper:bool) (n:nat) (fuel:nat) : Tot (list char) (decreases fuel) =
  if fuel = 0 then []
  else if n = 0 then []
  else
    let n0 = n - 1 in
    let d = n0 % 26 in
    let rest = n0 / 26 in
    alpha_digits upper rest (fuel - 1) @ [alpha_digit_char upper d]

let render_alpha (upper:bool) (n:nat) : string =
  if n = 0 then "0" else str_of_chars (alpha_digits upper n (n + 1))

// Roman numerals (standard subtractive notation); `fuel` bounds the
// table-driven subtraction loop (n+1 steps always suffice: the
// smallest table entry is 1, so no step can fail to reduce n).
let roman_table : list (nat & string) =
  [ (1000, "M"); (900, "CM"); (500, "D"); (400, "CD");
    (100, "C"); (90, "XC"); (50, "L"); (40, "XL");
    (10, "X"); (9, "IX"); (5, "V"); (4, "IV"); (1, "I") ]

let rec roman_pick (n:nat) (table:list (nat & string)) : Tot (option (nat & string)) (decreases table) =
  match table with
  | [] -> None
  | (v, s) :: rest -> if v > 0 && v <= n then Some (v, s) else roman_pick n rest

let rec roman_digits_fuel (n:nat) (fuel:nat) : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else if n = 0 then ""
  else
    match roman_pick n roman_table with
    | None -> ""
    | Some (v, s) -> strcat s (roman_digits_fuel (if n >= v then n - v else 0) (fuel - 1))

let roman_digits (n:nat) : string = roman_digits_fuel n (n + 1)

// Plain decimal digits of a nat, most-significant first ("0" for zero).
let rec nat_to_digits (n:nat) (fuel:nat) : Tot (list char) (decreases fuel) =
  if fuel = 0 then []
  else if n = 0 then []
  else
    let d = n % 10 in
    let rest = n / 10 in
    nat_to_digits rest (fuel - 1) @ [FStar.Char.char_of_int (0x30 + d)]

let digits_of_nat (n:nat) : list char =
  if n = 0 then ['0'] else nat_to_digits n (n + 1)

let rec replicate_char (c:char) (k:nat) : Tot (list char) (decreases k) =
  if k = 0 then [] else c :: replicate_char c (k - 1)

// Zero-pad a digit list on the left to at least `want` digits (the
// format token "01" / "001" minimum-width behaviour).
let pad_left_zeros (cs:list char) (want:nat) : list char =
  let len = List.Tot.length cs in
  if want <= len then cs else replicate_char '0' (want - len) @ cs

// Insert `sep_rev` (grouping-separator, already reversed) into a
// REVERSED digit list every `gsize` digits from the right, never
// trailing past the most-significant digit. `i` is the 0-based index
// from the right of the digit about to be emitted.
let rec group_rev (rev_ds:list char) (sep_rev:list char) (gsize:nat) (i:nat)
  : Tot (list char) (decreases rev_ds) =
  match rev_ds with
  | [] -> []
  | c :: rest ->
    let tail = group_rev rest sep_rev gsize (i + 1) in
    if gsize > 0 && (i + 1) % gsize = 0 && Cons? rest
    then c :: (sep_rev @ tail)
    else c :: tail

let apply_grouping (digits:list char) (gsep:string) (gsize:nat) : list char =
  if gsep = "" || gsize = 0 then digits
  else List.Tot.rev (group_rev (List.Tot.rev digits) (List.Tot.rev (chars_of gsep)) gsize 0)

noeq type numfmt_style =
  | NF_Decimal : nat -> numfmt_style   // minimum digit width (format "1" -> 1, "001" -> 3)
  | NF_UpperAlpha | NF_LowerAlpha | NF_UpperRoman | NF_LowerRoman

let render_num_styled (n:nat) (style:numfmt_style) (gsep:string) (gsize:nat) : string =
  match style with
  | NF_Decimal minw -> str_of_chars (apply_grouping (pad_left_zeros (digits_of_nat n) minw) gsep gsize)
  | NF_UpperAlpha -> render_alpha true n
  | NF_LowerAlpha -> render_alpha false n
  | NF_UpperRoman -> roman_digits n
  | NF_LowerRoman -> str_of_chars (List.Tot.map ascii_lower_char (chars_of (roman_digits n)))

// ---- format-string tokenizing (XSLT 1.0 §7.7.1) --------------------
//
// A format string is a run of alternating alphanumeric "format token"
// spans and non-alphanumeric "separator" spans: a leading separator
// span (if any) is the PREFIX, a trailing one is the SUFFIX, and the
// separators BETWEEN two tokens are what gets inserted between the
// numbers they format. If the numbers list is longer than the token
// list, the LAST token (and the LAST inter-token separator, or "." if
// there was only ever one token) is reused for every extra number; the
// suffix is always appended exactly once, after the last number
// (verified against Apache-Xalan numbering08: format="01-001. " on a
// single-level (chapter-only) title renders "01. ", not "01-001. " --
// the unused second token/separator are simply never reached, but the
// suffix ". " still lands after whichever number was last rendered).

let is_alnum_fmt_char (c:char) : bool =
  let code = FStar.Char.int_of_char c in
  (code >= 0x30 && code <= 0x39) || (code >= 0x41 && code <= 0x5A)
    || (code >= 0x61 && code <= 0x7A) || code >= 0x80

let rec run_alnum (cs:list char) (acc:list char) : Tot (list char & list char) (decreases cs) =
  match cs with
  | c :: rest -> if is_alnum_fmt_char c then run_alnum rest (c :: acc) else (List.Tot.rev acc, cs)
  | [] -> (List.Tot.rev acc, [])

let rec run_sep (cs:list char) (acc:list char) : Tot (list char & list char) (decreases cs) =
  match cs with
  | c :: rest -> if not (is_alnum_fmt_char c) then run_sep rest (c :: acc) else (List.Tot.rev acc, cs)
  | [] -> (List.Tot.rev acc, [])

noeq type frun = | FR_Alnum : list char -> frun | FR_Sep : list char -> frun

// `fuel` (not structural recursion on `cs`) sidesteps proving that
// run_alnum/run_sep's returned remainder is a strict sub-list of `cs`
// -- the same idiom expand_avt_chars uses just above for exactly this
// class of function (a helper call, not a direct list-cons pattern,
// stands between this function and its own decreasing argument).
let rec tokenize_runs (cs:list char) (fuel:nat) : Tot (list frun) (decreases fuel) =
  if fuel = 0 then []
  else
    match cs with
    | [] -> []
    | c :: _ ->
      if is_alnum_fmt_char c then
        let (run, rest) = run_alnum cs [] in
        FR_Alnum run :: tokenize_runs rest (fuel - 1)
      else
        let (run, rest) = run_sep cs [] in
        FR_Sep run :: tokenize_runs rest (fuel - 1)

let classify_token (t:list char) : numfmt_style =
  match t with
  | [] -> NF_Decimal 1
  | c :: _ ->
    if c = 'A' then NF_UpperAlpha
    else if c = 'a' then NF_LowerAlpha
    else if c = 'I' then NF_UpperRoman
    else if c = 'i' then NF_LowerRoman
    else NF_Decimal (List.Tot.length t)

// From the run sequence AFTER any leading separator: the token styles,
// the separators BETWEEN consecutive tokens (length = tokens - 1), and
// the trailing suffix (separator after the last token, if any).
let rec split_tokens (rest:list frun) : Tot (list numfmt_style & list string & string) (decreases rest) =
  match rest with
  | [] -> ([], [], "")
  | [FR_Alnum t] -> ([classify_token t], [], "")
  | FR_Alnum t :: FR_Sep s :: [] -> ([classify_token t], [], str_of_chars s)
  | FR_Alnum t :: FR_Sep s :: more ->
    let (toks, seps, suf) = split_tokens more in
    (classify_token t :: toks, str_of_chars s :: seps, suf)
  | FR_Alnum t :: more ->
    let (toks, seps, suf) = split_tokens more in
    (classify_token t :: toks, seps, suf)
  | FR_Sep _ :: more -> split_tokens more   // stray extra separator (alternation invariant violation)

let parsed_format (fmt:string) : (string & list numfmt_style & list string & string) =
  let cs = chars_of fmt in
  match tokenize_runs cs (List.Tot.length cs + 1) with
  | [] -> ("", [NF_Decimal 1], [], "")
  | FR_Sep s :: rest ->
    let (toks, seps, suf) = split_tokens rest in
    (match toks with
     | [] -> (str_of_chars s, [NF_Decimal 1], [], "")
     | _ -> (str_of_chars s, toks, seps, suf))
  | runs ->
    let (toks, seps, suf) = split_tokens runs in
    ("", toks, seps, suf)

// Style/separator for the i-th (0-based) number: clamp to the LAST
// token/separator once `i` runs past the format's own token count
// (XSLT 1.0 §7.7.1). A single-token format has no inter-token
// separator to reuse, so the default "." applies (§7.7.1).
let rec pick_style (toks:list numfmt_style) (i:nat) : Tot numfmt_style (decreases toks) =
  match toks with
  | [] -> NF_Decimal 1
  | [t] -> t
  | t :: rest -> if i = 0 then t else pick_style rest (i - 1)

let rec pick_sep (seps:list string) (i:nat) : Tot string (decreases seps) =
  match seps with
  | [] -> "."
  | [s] -> s
  | s :: rest -> if i = 0 then s else pick_sep rest (i - 1)

let rec render_numbered (ns:list nat) (toks:list numfmt_style) (seps:list string)
                        (suffix:string) (gsep:string) (gsize:nat) (i:nat)
  : Tot string (decreases ns) =
  match ns with
  | [] -> ""
  | [n] -> strcat (render_num_styled n (pick_style toks i) gsep gsize) suffix
  | n :: rest ->
    strcat (strcat (render_num_styled n (pick_style toks i) gsep gsize) (pick_sep seps i))
      (render_numbered rest toks seps suffix gsep gsize (i + 1))

// The full xsl:number rendering pipeline: tokenize `fmt`, then render
// every number in `numbers` (document order, outermost level first)
// against the token/separator/suffix sequence, prefixed by the
// format's own leading separator (if any). An empty `numbers` list
// (no ancestor-or-self matched `count` -- XSLT 1.0 §7.7: "the result
// is an empty string") renders nothing at all, INCLUDING the prefix.
let render_number_list (numbers:list nat) (fmt:string) (gsep:string) (gsize_s:string) : string =
  let (lead, toks, seps, suffix) = parsed_format fmt in
  match numbers with
  | [] -> ""
  | _ ->
    let gsize = (match parse_nat_chars (chars_of (trim_str gsize_s)) 0 with Some n -> n | None -> 0) in
    strcat lead (render_numbered numbers toks seps suffix gsep gsize 0)

// XSLT 1.0 7.7: a `value=` number that rounds to less than 1, or to
// NaN/an infinity, bypasses format/prefix/suffix entirely and renders
// as the bare arabic string (verified against Apache-Xalan numbering17
// -- value=0 renders "0", not "(0) ", under format="(I) "; and
// numbering79 -- value="wiseguy" (a non-numeric node-set) renders
// "NaN", not "(NaN) "). XSLT 1.0 does not define this corner (1.1
// later made formatting zero/negative an error); this matches what the
// vendored conformance fixtures actually expect.
let value_bypass (n:xpath_number) : option string =
  match xn_round n with
  | XN_Finite v 0 -> if v < 1 then Some (string_of_int v) else None
  | XN_Finite _ _ -> None
  | other -> Some (xn_to_string other)

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

// Highest-import-precedence, then highest-priority template that both
// matches `nd` AND is declared in the active `mode` (default mode = "");
// import precedence (tpl_import_prec, HIGHER wins) is checked BEFORE
// priority (XSLT 1.0 section 5.5: "if there are several matching
// template rules ... the rule with highest import precedence is used
// ... if there are several matching template rules with the same,
// highest, import precedence, ... the rule with highest default or
// specified priority is used"); ties within the SAME precedence resolve
// to the LAST in document order, same as before this field existed.
// Every template in a stylesheet with no xsl:import/xsl:include shares
// the SAME constant tpl_import_prec, so both new comparisons are no-ops
// there and this reduces byte-for-byte to the original priority-only
// logic (protects the pre-existing scores).
let rec pick_template (vars) (nsctx:list (string & string))
                      (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                      (key_table:list key_entry) (mode:string) (tpls:list template) (nd:dnode) (best:option template)
  : Tot (option template) (decreases tpls) =
  match tpls with
  | [] -> best
  | t :: rest ->
    let best' =
      if t.tpl_mode = mode && template_matches vars nsctx id_attrs style_root decfmts key_table t nd then
        (match best with
         | None -> Some t
         | Some b ->
           if t.tpl_import_prec > b.tpl_import_prec then Some t
           else if t.tpl_import_prec < b.tpl_import_prec then best
           else if template_priority t >= template_priority b then Some t
           else best)
      else best
    in
    pick_template vars nsctx id_attrs style_root decfmts key_table mode rest nd best'

// xsl:apply-imports (XSLT 1.0 section 5.6): apply only template rules
// imported into the stylesheet containing the CURRENTLY EXECUTING
// template rule, i.e. those with import precedence STRICTLY LESS than
// `below` (the current template's own tpl_import_prec). Same mode +
// priority tie-break as pick_template, restricted to that subset.
let rec pick_template_below (vars) (nsctx:list (string & string))
                            (id_attrs:list (string & string)) (style_root:xml_node) (decfmts:list decimal_format_symbols)
                            (key_table:list key_entry) (mode:string) (below:int) (tpls:list template) (nd:dnode) (best:option template)
  : Tot (option template) (decreases tpls) =
  match tpls with
  | [] -> best
  | t :: rest ->
    let best' =
      if t.tpl_mode = mode && t.tpl_import_prec < below && template_matches vars nsctx id_attrs style_root decfmts key_table t nd then
        (match best with
         | None -> Some t
         | Some b -> if template_priority t >= template_priority b then Some t else best)
      else best
    in
    pick_template_below vars nsctx id_attrs style_root decfmts key_table mode below rest nd best'

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

// ---- method="html" serialization corners (XSLT 1.0 16.2) ------------
//
// Lower-case an ASCII string for case-insensitive HTML element/attribute
// name comparisons (element/attribute NAMES in the result tree are
// compared case-insensitively against the fixed HTML4 tables below, but
// printed with their ORIGINAL casing -- Xalan output-output34 keeps
// "<bAse>" spelled exactly as the stylesheet wrote it).
let ascii_lower_str (s:string) : string = str_of_chars (List.Tot.map ascii_lower_char (chars_of s))

// HTML4 "EMPTY" content-model elements (Xalan HTMLdtd.m_emptyElements):
// never given a close tag, self-close slash is dropped too (bare
// "<tag ...>"), any (well-formed-source) child content is not printed.
let html_void_elems : list string =
  ["area"; "base"; "basefont"; "br"; "col"; "frame"; "hr"; "img";
   "input"; "isindex"; "link"; "meta"; "param"]

let is_html_void_elem (local:string) : bool = mem_str (ascii_lower_str local) html_void_elems

// HTML4 boolean attributes (Xalan HTMLdtd.m_booleans): when the
// attribute's value equals its own name case-insensitively, only the
// bare name is written (no ="value") -- Xalan output-output35.
let html_boolean_attrs : list string =
  ["checked"; "compact"; "declare"; "defer"; "disabled"; "ismap";
   "multiple"; "noresize"; "noshade"; "nowrap"; "readonly"; "selected"]

let is_html_boolean_attr (name:string) : bool = mem_str (ascii_lower_str name) html_boolean_attrs

// HTML4 Latin-1 (ISO 8859-1) named character references, section 24.2 of
// the HTML4 spec -- the only entity block any output-category fixture
// exercises (output-output04: nbsp/copy/Egrave). Symbols/Greek/math
// entities (HTML4 24.3/24.4) are NOT modelled; a codepoint outside this
// table serializes as the literal character (UTF-8), same as XML method.
let html_latin1_entities : list (int & string) = [
  (0xA0,"nbsp"); (0xA1,"iexcl"); (0xA2,"cent"); (0xA3,"pound"); (0xA4,"curren");
  (0xA5,"yen"); (0xA6,"brvbar"); (0xA7,"sect"); (0xA8,"uml"); (0xA9,"copy");
  (0xAA,"ordf"); (0xAB,"laquo"); (0xAC,"not"); (0xAD,"shy"); (0xAE,"reg");
  (0xAF,"macr"); (0xB0,"deg"); (0xB1,"plusmn"); (0xB2,"sup2"); (0xB3,"sup3");
  (0xB4,"acute"); (0xB5,"micro"); (0xB6,"para"); (0xB7,"middot"); (0xB8,"cedil");
  (0xB9,"sup1"); (0xBA,"ordm"); (0xBB,"raquo"); (0xBC,"frac14"); (0xBD,"frac12");
  (0xBE,"frac34"); (0xBF,"iquest"); (0xC0,"Agrave"); (0xC1,"Aacute"); (0xC2,"Acirc");
  (0xC3,"Atilde"); (0xC4,"Auml"); (0xC5,"Aring"); (0xC6,"AElig"); (0xC7,"Ccedil");
  (0xC8,"Egrave"); (0xC9,"Eacute"); (0xCA,"Ecirc"); (0xCB,"Euml"); (0xCC,"Igrave");
  (0xCD,"Iacute"); (0xCE,"Icirc"); (0xCF,"Iuml"); (0xD0,"ETH"); (0xD1,"Ntilde");
  (0xD2,"Ograve"); (0xD3,"Oacute"); (0xD4,"Ocirc"); (0xD5,"Otilde"); (0xD6,"Ouml");
  (0xD7,"times"); (0xD8,"Oslash"); (0xD9,"Ugrave"); (0xDA,"Uacute"); (0xDB,"Ucirc");
  (0xDC,"Uuml"); (0xDD,"Yacute"); (0xDE,"THORN"); (0xDF,"szlig"); (0xE0,"agrave");
  (0xE1,"aacute"); (0xE2,"acirc"); (0xE3,"atilde"); (0xE4,"auml"); (0xE5,"aring");
  (0xE6,"aelig"); (0xE7,"ccedil"); (0xE8,"egrave"); (0xE9,"eacute"); (0xEA,"ecirc");
  (0xEB,"euml"); (0xEC,"igrave"); (0xED,"iacute"); (0xEE,"icirc"); (0xEF,"iuml");
  (0xF0,"eth"); (0xF1,"ntilde"); (0xF2,"ograve"); (0xF3,"oacute"); (0xF4,"ocirc");
  (0xF5,"otilde"); (0xF6,"ouml"); (0xF7,"divide"); (0xF8,"oslash"); (0xF9,"ugrave");
  (0xFA,"uacute"); (0xFB,"ucirc"); (0xFC,"uuml"); (0xFD,"yacute"); (0xFE,"thorn");
  (0xFF,"yuml")
]

let html_named_entity (cp:int) : option string =
  match List.Tot.find (fun (p:(int & string)) -> fst p = cp) html_latin1_entities with
  | Some (_, nm) -> Some nm
  | None -> None

let html_char_ref (c:char) : string =
  match html_named_entity (FStar.Char.int_of_char c) with
  | Some nm -> String.concat "" ["&"; nm; ";"]
  | None -> soc c

// HTML text escaping: '&' and '<' only (a bare '>' is left alone -- HTML4
// tolerates it and Xalan does not escape it; output-output74/75 pin '<'
// and '>' being left RAW in an HTML attribute value, see
// escape_html_attr_char below, but text content still needs '<' escaped
// so a literal "<" cannot be misread as starting a tag).
let escape_html_text_char (c:char) : string =
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else html_char_ref c

// HTML attribute escaping: '&' and the quote delimiter only -- '<' and
// '>' are written raw (Xalan output-output49/74: "<abcd>" stays literal
// inside a double-quoted attribute value).
let escape_html_attr_char (c:char) : string =
  if c = '&' then "&amp;"
  else if c = '"' then "&quot;"
  else html_char_ref c

let escape_html_text (s:string) : string = escape_with escape_html_text_char (chars_of s)
let escape_html_attr (s:string) : string = escape_with escape_html_attr_char (chars_of s)

let serialize_attr (a:xml_attribute) : string =
  String.concat "" [" "; a.attr_name; "=\""; escape_attr a.attr_value; "\""]

// HTML attribute serialization: a boolean attribute (XSLT 1.0 16.2 /
// HTML4) whose value equals its own name case-insensitively is written
// bare (no ="value"); everything else uses escape_html_attr in place of
// the XML-rules escape_attr.
let serialize_attr_html (a:xml_attribute) : string =
  if is_html_boolean_attr a.attr_name && ascii_lower_str a.attr_value = ascii_lower_str a.attr_name then
    String.concat "" [" "; a.attr_name]
  else
    String.concat "" [" "; a.attr_name; "=\""; escape_html_attr a.attr_value; "\""]

let rec serialize_attrs_html (attrs:list xml_attribute) : Tot string (decreases attrs) =
  match attrs with
  | [] -> ""
  | a :: rest -> strcat (serialize_attr_html a) (serialize_attrs_html rest)

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

// ---- xsl:output serialization settings (XSLT 1.0 section 16) --------
//
// `ser_settings` carries only what serialize_node/serialize_nodes need to
// DEVIATE from the pre-xsl:output default behaviour: which (namespace-URI,
// local-name) pairs are cdata-section-elements, whether indent="yes" is in
// effect, and the declared encoding (consulted ONLY to decide whether a
// codepoint inside a cdata-section element's text must break out of the
// CDATA section as a numeric character reference -- see cdata_wrap_text).
// `default_ser_settings` reproduces the exact prior behaviour (no cdata
// wrapping, no indent), so a caller that never had an xsl:output element
// gets byte-identical output by construction, not by a separate code path.
noeq type ser_settings = {
  ser_cdata : list (option string & string);
  ser_indent : bool;
  ser_encoding : string;
  // method="html" (XSLT 1.0 16.2): void-element/boolean-attribute/
  // script-style-raw/HTML-entity serialization. FALSE (the default)
  // reproduces the exact prior XML-rules serializer byte for byte, so a
  // method="xml"/"text" caller is completely unaffected by anything
  // below that reads this flag.
  ser_html : bool;
}

let default_ser_settings : ser_settings = { ser_cdata = []; ser_indent = false; ser_encoding = "UTF-8"; ser_html = false }

let is_text_node (n:xml_node) : bool =
  match n with XText _ | XCDATA _ -> true | _ -> false

let rec has_text_node (ns:list xml_node) : Tot bool (decreases ns) =
  match ns with
  | [] -> false
  | hd :: tl -> if is_text_node hd then true else has_text_node tl

let matches_cdata_name (targets:list (option string & string)) (ns_uri:option string) (local:string) : bool =
  List.Tot.existsb (fun (tu, tl) -> tl = local && ns_uri_eq tu ns_uri) targets

// Is codepoint `cp` representable in the (xsl:output) declared `encoding`
// without a numeric character reference? Only the two restrictive
// encodings the Xalan cdata-section-elements fixtures actually exercise
// are modelled; every other / unrecognised encoding name (crucially
// "UTF-8", and no encoding at all) is treated as fully representable, so
// this can only ever ADD a char-ref split, never remove one that a wider
// encoding table would have avoided.
let is_representable (encoding:string) (cp:int) : bool =
  if encoding = "US-ASCII" || encoding = "ASCII" then cp < 128
  else if encoding = "ISO-8859-1" || encoding = "Latin1" then cp < 256
  else true

let charref (c:char) : string =
  String.concat "" ["&#"; string_of_int (FStar.Char.int_of_char c); ";"]

// A CDATA section may not contain the literal 3-character sequence
// "]]>" (it would terminate the section early), so any occurrence in the
// wrapped text is split into "]]" (kept in this CDATA section, closed by
// a SYNTHETIC "]]>" of its own) followed by a fresh CDATA section
// reopened for the ">" and everything after -- the standard technique
// real serializers use: "]]>" becomes "]]]]><![CDATA[>" (Xalan
// output-output30/41; render_crun's outer "<![CDATA[" ... "]]>" wrap
// then makes the full text "<![CDATA[]]]]><![CDATA[>]]>", matching both
// fixtures byte for byte). A prior version of this list omitted the
// synthetic closer's '>' (14 chars, not 15), which dropped the original
// ">" character from the output entirely -- caught by output-output41.
let rec replace_cdata_end_chars (cs:list char) : Tot (list char) (decreases cs) =
  match cs with
  | ']' :: ']' :: '>' :: rest ->
    List.Tot.append [']'; ']'; ']'; ']'; '>'; '<'; '!'; '['; 'C'; 'D'; 'A'; 'T'; 'A'; '['; '>'] (replace_cdata_end_chars rest)
  | c :: rest -> c :: replace_cdata_end_chars rest
  | [] -> []

// One run of a cdata-section element's text content: either a maximal
// substring of codepoints representable in the declared encoding (wrapped
// whole in one CDATA section), or a single non-representable codepoint
// escaped as a numeric character reference OUTSIDE any CDATA section
// (character references are not recognised inside CDATA, so a
// non-representable character must break out -- Xalan output-output28).
noeq type crun = | Run_Text : list char -> crun | Run_Escape : char -> crun

let rec build_cdata_runs (encoding:string) (cs:list char) (cur:list char) : Tot (list crun) (decreases cs) =
  match cs with
  | [] -> if Nil? cur then [] else [Run_Text (List.Tot.rev cur)]
  | c :: rest ->
    if is_representable encoding (FStar.Char.int_of_char c) then
      build_cdata_runs encoding rest (c :: cur)
    else
      let before = if Nil? cur then [] else [Run_Text (List.Tot.rev cur)] in
      List.Tot.append before (Run_Escape c :: build_cdata_runs encoding rest [])

let render_crun (r:crun) : string =
  match r with
  | Run_Text [] -> ""
  | Run_Text cs -> String.concat "" ["<![CDATA["; str_of_chars (replace_cdata_end_chars cs); "]]>"]
  | Run_Escape c -> charref c

let cdata_wrap_text (encoding:string) (t:string) : string =
  String.concat "" (List.Tot.map render_crun (build_cdata_runs encoding (chars_of t) []))

// How a direct text-node CHILD of the current element is rendered.
// TM_Raw (method="html" SCRIPT/STYLE, XSLT 1.0 16.2: content is neither
// escaped nor cdata-wrapped -- Xalan output-output01/02) takes priority
// over TM_Cdata (cdata-section-elements) if a stylesheet's
// cdata-section-elements list names "script"/"style" itself (an
// unexercised corner; Raw is the more specific, more correct choice).
// TM_Html vs TM_Xml is escape_html_text vs escape_text.
type text_mode = | TM_Xml | TM_Html | TM_Cdata | TM_Raw

let rec serialize_node (cfg:ser_settings) (scope:list (string & string)) (n:xml_node) : Tot string (decreases n) =
  match n with
  | XText t -> if cfg.ser_html then escape_html_text t else escape_text t
  | XCDATA t -> if cfg.ser_html then escape_html_text t else escape_text t
  | XComment t -> String.concat "" ["<!--"; t; "-->"]
  // method="html" (XSLT 1.0 16.2): a processing instruction is written
  // "<?target data>" -- NO "?" before the closing ">" -- unlike the XML
  // rule's "<?target data?>" (Xalan output-output36/59).
  | XPI tg d -> if cfg.ser_html then String.concat "" ["<?"; tg; " "; d; ">"]
                else String.concat "" ["<?"; tg; " "; d; "?>"]
  | XElement tag attrs children ->
    // Namespace declarations serialize first (deduped against ancestors);
    // then the ordinary attributes.
    let (decls, normal) = List.Tot.partition is_ns_decl attrs in
    let (ns_str, scope') = emit_ns_decls scope decls in
    // cdata-section-elements membership, and the method="html" void/
    // boolean-attribute/script-style/entity treatment, are both keyed by
    // the OUTPUT tree's own resolved (namespace-URI, local-name) identity
    // (default namespace comes from the accumulated output `scope'`,
    // exactly as a real element name would resolve) -- see the
    // cdata-section-elements QName resolution comment on
    // collect_output_settings below for why this differs from an XPath
    // node test's unprefixed-name-means-null-namespace rule. The html
    // treatment additionally requires NULL namespace specifically: an
    // element in a namespace (even the literal string
    // "http://www.w3.org/TR/REC-html40") is NOT an "HTML element" by
    // XSLT 1.0 16.2, and falls back to plain XML-rules serialization --
    // Xalan output-output63 (an <HTML xmlns="..."> subtree reverts to
    // ordinary self-closing tags, no boolean-attribute collapsing).
    let elem_ns = lookup_ns scope' (prefix_of tag) in
    let is_html_here = cfg.ser_html && None? elem_ns in
    let loc = local_name_of tag in
    let loc_lc = ascii_lower_str loc in
    let a = strcat ns_str (if is_html_here then serialize_attrs_html normal else serialize_attrs normal) in
    let is_cdata_elem = matches_cdata_name cfg.ser_cdata elem_ns loc in
    let tmode =
      if is_html_here && (loc_lc = "script" || loc_lc = "style") then TM_Raw
      else if is_cdata_elem then TM_Cdata
      else if is_html_here then TM_Html
      else TM_Xml
    in
    let parts = serialize_children cfg scope' tmode children in
    // indent="yes": XSLT 1.0 does not mandate a specific indentation
    // style, and the vendored Xalan fixtures' own indentation (checked
    // fixture-by-fixture, see the xsl:output design note) is a bare
    // newline before each child and before the closing tag -- NO
    // per-depth leading spaces -- applied only when every child is a
    // non-text node (an element with any text-node child, even
    // whitespace-only, is left exactly as instantiated: indenting mixed
    // content would alter its string-value).
    let do_indent = cfg.ser_indent && Cons? children && not (has_text_node children) in
    let inner =
      if Nil? parts then ""
      else if do_indent then strcat "\n" (strcat (String.concat "\n" parts) "\n")
      else String.concat "" parts
    in
    // HTML4 "EMPTY" elements (area/base/br/hr/img/input/... -- see
    // html_void_elems) are NEVER given a close tag and never a self-close
    // slash, regardless of content (Xalan output-output33/34): "<br>",
    // not "<br/>" or "<br></br>". Otherwise: method="html" writes an
    // empty non-void element as an open/close PAIR ("<P></P>", not
    // "<P/>" -- Xalan output-output03 BODY, output-output35 Option),
    // where XML method keeps the existing self-close ("<t/>").
    if is_html_here && is_html_void_elem loc then String.concat "" ["<"; tag; a; ">"]
    else if inner = "" then
      (if is_html_here then String.concat "" ["<"; tag; a; "></"; tag; ">"]
       else String.concat "" ["<"; tag; a; "/>"])
    else String.concat "" ["<"; tag; a; ">"; inner; "</"; tag; ">"]

// Per-child serialized strings (not yet joined) so the caller can decide
// whether to join with "\n" (indent) or "" (default, byte-identical to
// the pre-xsl:output serializer). `tmode` -- the ENCLOSING element's text
// mode (see text_mode above) -- routes each direct XText/XCDATA child;
// other children (elements, comments, PIs) always recurse into
// serialize_node, and non-text children of a cdata/raw element are
// untouched (XSLT 1.0 16.1: only text node CHILDREN are wrapped, not
// descendant text -- Xalan output-output96/97).
and serialize_children (cfg:ser_settings) (scope:list (string & string)) (tmode:text_mode) (ns:list xml_node)
  : Tot (list string) (decreases ns) =
  match ns with
  | [] -> []
  | hd :: tl ->
    let s =
      (match hd with
       | XText t | XCDATA t ->
         (match tmode with
          | TM_Raw -> t
          | TM_Cdata -> cdata_wrap_text cfg.ser_encoding t
          | TM_Html -> escape_html_text t
          | TM_Xml -> escape_text t)
       | _ -> serialize_node cfg scope hd)
    in
    s :: serialize_children cfg scope tmode tl

// Not itself recursive (serialize_children already walks the whole
// list), so this stays OUTSIDE the mutual `and` group above -- inside it,
// F*'s termination checker would need serialize_nodes's own decreases
// argument to shrink before delegating, which a one-line forwarder never
// does.
let serialize_nodes (cfg:ser_settings) (scope:list (string & string)) (ns:list xml_node) : string =
  String.concat "" (serialize_children cfg scope (if cfg.ser_html then TM_Html else TM_Xml) ns)

let serialize_result (n:xml_node) : string = serialize_node default_ser_settings [] n

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
// The attribute-set expansion added to instantiate_one's xsl:copy/
// xsl:element/literal-result-element branches (expand_attrset_name(s),
// merge_attrs_override) pushes this whole mutual-recursion group's
// combined VC past the default z3rlimit on at least one unrelated
// branch (observed: the plain xsl:if branch's `fuel - 1 : nat`
// obligation) -- a resource-budget issue, not a real proof gap (the
// SAME obligations discharge cleanly at rlimit_factor 4; bisected by
// reverting the new call sites one at a time until the failure
// disappeared, confirming it's query-budget pressure from the bigger
// combined VC, not a broken proof). Genuinely more search budget for
// a real proof, NOT --lax / --admit_smt_queries (iron rule #10).
#push-options "--z3rlimit_factor 4"
let rec dispatch (fuel:nat) (st:xstyle) (nd:dnode) (pos size:nat) (mode:string)
                 (svars:list (string & xp_value)) (srtf:list (string & list rnode))
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match pick_template st.xs_globals st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table mode st.xs_templates nd None with
    | Some tpl -> instantiate_seq (fuel - 1) st nd pos size svars srtf mode tpl.tpl_import_prec tpl.tpl_body
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
    // XSLT 1.0 built-in template rules match only text and attribute
    // nodes; namespace nodes produce nothing.
    | D_Item (CI_Namespace _ _ _ _ _) -> []

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
// across siblings. `cur_mode`/`cur_prec` are the AMBIENT template-rule
// context (the mode + tpl_import_prec of whichever template rule is
// currently being applied, as picked by dispatch/pick_template_below) --
// threaded (not recomputed) so a nested xsl:apply-imports anywhere in
// this body sees the CORRECT "current template rule" per XSLT 1.0
// section 5.6, including through xsl:if/xsl:choose/xsl:for-each/
// xsl:copy nesting within the same template instantiation.
and instantiate_seq (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                    (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                    (cur_mode:string) (cur_prec:int) (nodes:list xml_node)
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
           if already then instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl
           else
             (match attr_opt "select" attrs with
              | Some sel ->
                let v = eval_val_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel in
                instantiate_seq (fuel - 1) st ctx pos size ((nm, v) :: vars) rtf cur_mode cur_prec tl
              | None ->
                // Result-tree-fragment: instantiate the body, bind its
                // string-value for XPath and its nodes for copy-of.
                let frag = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
                let sval = text_value_nodes (only_nodes frag) in
                instantiate_seq (fuel - 1) st ctx pos size ((nm, XV_Str sval) :: vars) ((nm, frag) :: rtf) cur_mode cur_prec tl)
         else
           let here = instantiate_one (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec hd in
           here @ instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl
       | _ ->
         let here = instantiate_one (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec hd in
         here @ instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl)

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
// caller's locals into the callee. `cur_mode`/`cur_prec` are the CALLER's
// ambient template-rule context, used only if a with-param's body itself
// contains an xsl:apply-imports (unusual, but kept consistent).
and bind_with_params_scoped (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                            (evars:list (string & xp_value)) (ertf:list (string & list rnode))
                            (cur_mode:string) (cur_prec:int)
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
              let v = eval_val_dn ctx pos size evars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel in
              bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf cur_mode cur_prec ((nm, v) :: svars) srtf tl
            | None ->
              let frag = instantiate_seq (fuel - 1) st ctx pos size evars ertf cur_mode cur_prec pchildren in
              let sval = text_value_nodes (only_nodes frag) in
              bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf cur_mode cur_prec ((nm, XV_Str sval) :: svars) ((nm, frag) :: srtf) tl)
         else bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf cur_mode cur_prec svars srtf tl
       | _ -> bind_with_params_scoped (fuel - 1) st ctx pos size evars ertf cur_mode cur_prec svars srtf tl)

and instantiate_one (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                    (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                    (cur_mode:string) (cur_prec:int) (node:xml_node)
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
          [R_Node (XText (eval_string_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table (attr_or "select" "." attrs)))]
        else if ln = "text" then
          [R_Node (XText (raw_text children))]
        else if ln = "if" then
          (if eval_bool_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table (attr_or "test" "false()" attrs)
           then instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children
           else [])
        else if ln = "choose" then
          instantiate_choose (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children
        else if ln = "for-each" then
          let sel = attr_or "select" "." attrs in
          // XSLT 1.0 §5.4: the current node list is the selected node-set
          // in DOCUMENT ORDER with duplicates removed (only overridden by
          // an xsl:sort). doc_sort_dedup fixes reverse-axis proximity
          // order (preceding::, ancestor::) and de-duplicates descendant
          // (//) selects before iteration.
          let items0 = doc_sort_dedup (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel) in
          let items = sort_maybe (dnode_ci ctx) pos size st.xs_pfx vars st.xs_nsctx children items0 in
          for_each_items (fuel - 1) st children vars rtf cur_mode cur_prec items 1 (List.Tot.length items)
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
            bind_with_params_scoped (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec st.xs_globals [] children in
          (match attr_opt "select" attrs with
           | Some sel ->
             let items0 = doc_sort_dedup (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel) in
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
        else if ln = "apply-imports" then
          // XSLT 1.0 section 5.6: apply only template rules imported into
          // the stylesheet containing the CURRENT template rule (strictly
          // lower tpl_import_prec than cur_prec), same node + same mode,
          // seeded with globals only (NOT the caller's vars/rtf --
          // impincl28/29 confirm a with-param bound on the enclosing
          // apply-templates does NOT reach the apply-imports target; it
          // falls back to that target's own xsl:param default). The
          // instantiated body's OWN cur_prec becomes the found template's
          // tpl_import_prec, so a NESTED apply-imports inside it "takes
          // its own view of the import tree" (impincl26).
          (match pick_template_below st.xs_globals st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table cur_mode cur_prec st.xs_templates ctx None with
           | Some tpl -> instantiate_seq (fuel - 1) st ctx pos size st.xs_globals [] cur_mode tpl.tpl_import_prec tpl.tpl_body
           | None -> builtin_rule (fuel - 1) st ctx cur_mode)
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
             // The callee's OWN tpl_import_prec becomes cur_prec for its
             // body (an xsl:apply-imports after xsl:call-template is a
             // spec grey area; this is the more sensible reading).
             let (cvars, crtf) = bind_with_params_scoped (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec st.xs_globals [] children in
             instantiate_seq (fuel - 1) st ctx pos size cvars crtf cur_mode tpl.tpl_import_prec tpl.tpl_body
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
              | None -> List.Tot.map mk (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel))
           | None -> List.Tot.map mk (select_nodes ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table sel))
        else if ln = "copy" then
          let use_attrs =
            expand_attrset_names (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec []
              (parse_qname_list (attr_or "use-attribute-sets" "" attrs)) in
          instantiate_copy (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec use_attrs children
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
          let use_attrs =
            expand_attrset_names (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec []
              (parse_qname_list (attr_or "use-attribute-sets" "" attrs)) in
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
          [R_Node (build_element nm (List.Tot.append use_attrs nsdecls) body)]
        else if ln = "attribute" then
          let nm = expand_avt (dnode_ci ctx) pos size vars st.xs_nsctx (attr_or "name" "" attrs) in
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
          [R_Attr ({ attr_name = nm; attr_value = rnodes_text body })]
        else if ln = "comment" then
          let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
          [R_Node (XComment (rnodes_text body))]
        else if ln = "number" then
          let dctx = dnode_ci ctx in
          let level = expand_avt dctx pos size vars st.xs_nsctx (attr_or "level" "single" attrs) in
          let count_pat = attr_or "count" "" attrs in
          let from_pat = attr_or "from" "" attrs in
          let fmt = expand_avt dctx pos size vars st.xs_nsctx (attr_or "format" "1" attrs) in
          let gsep = expand_avt dctx pos size vars st.xs_nsctx (attr_or "grouping-separator" "" attrs) in
          let gsize_s = expand_avt dctx pos size vars st.xs_nsctx (attr_or "grouping-size" "" attrs) in
          let text =
            (match attr_opt "value" attrs with
             | Some vexpr ->
               let n = to_number_val (eval_val_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table vexpr) in
               (match value_bypass n with
                | Some s -> s
                | None ->
                  (match xn_finite_int (xn_round n) with
                   | Some v -> render_number_list [v] fmt gsep gsize_s
                   | None -> ""))
             | None ->
               (match ctx with
                | D_Item it -> render_number_list (level_numbers vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table level count_pat from_pat it) fmt gsep gsize_s
                | D_Doc _ _ -> ""))
          in
          [R_Node (XText text)]
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
        let use_attrs =
          expand_attrset_names (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec []
            (parse_qname_list (attr_or (strcat st.xs_pfx ":use-attribute-sets") "" attrs)) in
        let literal_attrs = merge_attrs_override use_attrs out_attrs in
        let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
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
        [R_Node (build_element tag (default_ns_fixup @ st.xs_nsscope @ literal_attrs) body)]

and instantiate_choose (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                       (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                       (cur_mode:string) (cur_prec:int) (branches:list xml_node)
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
             (if eval_bool_dn ctx pos size vars st.xs_nsctx st.xs_id_attrs st.xs_style_root st.xs_decfmts st.xs_key_table (attr_or "test" "false()" attrs)
              then instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children
              else instantiate_choose (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl)
           else if ln = "otherwise" then
             instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children
           else instantiate_choose (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl
         else instantiate_choose (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl
       | _ -> instantiate_choose (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec tl)

and instantiate_copy (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                     (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                     (cur_mode:string) (cur_prec:int)
                     (use_attrs:list xml_attribute) (children:list xml_node)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match ctx with
    | D_Doc _ _ -> instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children
    | D_Item (CI_Elem _ anc n) ->
      (match n with
       | XElement t _ _ ->
         let body = instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children in
         // xsl:copy copies the element's namespace nodes (its in-scope
         // declarations), but not its attributes or content; the
         // serializer dedups against output ancestors. All in-scope
         // namespaces are copied, including one bound to the XSLT
         // namespace: when the copied node comes from document("") (the
         // stylesheet loaded as a source document) its xmlns:xsl is an
         // ordinary namespace node that xsl:copy must preserve
         // (namespace-4801). A source node in a normal transform never has
         // the XSLT namespace in scope, so this is a no-op for those.
         // use_attrs (this xsl:copy's use-attribute-sets, already
         // expanded) is a lower-precedence layer than the copy's own
         // content -- an xsl:attribute child in `body` overrides it in
         // place (build_element's merge_attrs_override).
         let nsnodes = inscope_ns [] [] (n :: anc) in
         [R_Node (build_element t (List.Tot.append nsnodes use_attrs) body)]
       | _ -> instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec children)
    | D_Item (CI_Text _ _ _ t) -> [R_Node (XText t)]
    | D_Item (CI_Comment _ _ _ t) -> [R_Node (XComment t)]
    | D_Item (CI_PI _ _ _ tg d) -> [R_Node (XPI tg d)]
    | D_Item (CI_Attr _ _ _ a) -> [R_Attr a]
    // xsl:copy of a namespace node copies its namespace declaration.
    | D_Item (CI_Namespace _ _ _ pfx uri) ->
      [R_Attr ({ attr_name = (if pfx = "" then "xmlns" else strcat "xmlns:" pfx); attr_value = uri })]

// Expand a single named xsl:attribute-set (already merged across
// duplicate-name decls, see attrset_entry) into the concrete
// xml_attribute list it contributes when used, in the CURRENT
// instantiation context (its own xsl:attribute children are AVT-
// expanded / value-computed against `ctx`/`vars`/`rtf` exactly like any
// other xsl:attribute). Order (XSLT 1.0 §7.1.4): attribute-sets this
// set itself uses (its own use-attribute-sets=, expanded left to right)
// are added FIRST, then this set's own xsl:attribute children override
// in place. `visited` guards a circular use-attribute-sets chain (a
// static error per the spec): a name already being expanded on the
// current path contributes nothing rather than looping -- fuel bounds
// termination regardless (Tot), this just avoids burning it needlessly.
and expand_attrset_name (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                        (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                        (cur_mode:string) (cur_prec:int)
                        (visited:list string) (name:string)
  : Tot (list xml_attribute) (decreases fuel) =
  if fuel = 0 then []
  else if mem_str name visited then []
  else
    match find_attrset_entry st.xs_attrsets name with
    | None -> []
    | Some e ->
      let deps_expanded = expand_attrset_names (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec (name :: visited) e.ase_deps in
      let own_attrs = only_attrs (instantiate_seq (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec e.ase_own) in
      merge_attrs_override deps_expanded own_attrs

// Expand a use-attribute-sets name LIST (space-separated on the using
// element), left to right: an EARLIER-named set's attributes are added
// first, a LATER-named set's attributes override same-name ones in
// place (still XSLT 1.0 §7.1.4's "in the order listed" merge).
and expand_attrset_names (fuel:nat) (st:xstyle) (ctx:dnode) (pos size:nat)
                         (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                         (cur_mode:string) (cur_prec:int)
                         (visited:list string) (names:list string)
  : Tot (list xml_attribute) (decreases fuel) =
  if fuel = 0 then []
  else
    match names with
    | [] -> []
    | hd :: tl ->
      let a = expand_attrset_name (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec visited hd in
      let b = expand_attrset_names (fuel - 1) st ctx pos size vars rtf cur_mode cur_prec visited tl in
      merge_attrs_override a b

and for_each_items (fuel:nat) (st:xstyle) (body:list xml_node)
                   (vars:list (string & xp_value)) (rtf:list (string & list rnode))
                   (cur_mode:string) (cur_prec:int)
                   (items:list xctx_item) (pos size:nat)
  : Tot (list rnode) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | it :: rest ->
      let here = instantiate_seq (fuel - 1) st (D_Item it) pos size vars rtf cur_mode cur_prec body in
      here @ for_each_items (fuel - 1) st body vars rtf cur_mode cur_prec rest (pos + 1) size
#pop-options

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

// Precedence-tagged template collection: `prec` is stamped onto every
// xsl:template found here as tpl_import_prec. Used both for a plain
// single-file stylesheet (collect_templates below, prec = 0 always) and
// per-compilation-unit by build_style_from_units (prec = that unit's
// postorder-numbered import precedence).
let rec collect_templates_prec (pfx:string) (prec:int) (children:list xml_node) : Tot (list template) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs body ->
       if is_xsl pfx tag && xsl_instr pfx tag = "template" then
         let m = attr_or "match" "" attrs in
         let nm = attr_or "name" "" attrs in
         if m = "" && nm = "" then collect_templates_prec pfx prec tl
         else
           let t = { tpl_match = m; tpl_name = nm;
                     tpl_mode = attr_or "mode" "" attrs;
                     tpl_prio = (match attr_opt "priority" attrs with
                                 | Some p -> parse_priority p | None -> None);
                     tpl_body = body; tpl_import_prec = prec } in
           t :: collect_templates_prec pfx prec tl
       else collect_templates_prec pfx prec tl
     | _ -> collect_templates_prec pfx prec tl)

let collect_templates (pfx:string) (children:list xml_node) : list template =
  collect_templates_prec pfx 0 children

// xsl:decimal-format symbol attributes: single-char symbols take the
// first codepoint of the attribute value (a picture-string meta
// character is a single character in every fixture this engine sees;
// XSLT does not define behavior for a multi-char symbol attribute).
// infinity/NaN are the only symbols that are full strings, not chars.
let first_char_or (dflt:char) (s:string) : char =
  match chars_of s with
  | c :: _ -> c
  | [] -> dflt

let char_attr (attrs:list xml_attribute) (name:string) (dflt:char) : char =
  match attr_opt name attrs with
  | Some s -> first_char_or dflt s
  | None -> dflt

let string_attr (attrs:list xml_attribute) (name:string) (dflt:string) : string =
  match attr_opt name attrs with
  | Some s -> s
  | None -> dflt

// An unset attribute falls back to the BUILT-IN default (never to
// another xsl:decimal-format's setting) -- each declaration is
// independent (XSLT 1.0 §12.3).
let decimal_format_of_attrs (attrs:list xml_attribute) : decimal_format_symbols =
  { dfs_name         = attr_or "name" "" attrs;
    dfs_decimal_sep  = char_attr attrs "decimal-separator" default_decimal_format_symbols.dfs_decimal_sep;
    dfs_grouping_sep = char_attr attrs "grouping-separator" default_decimal_format_symbols.dfs_grouping_sep;
    dfs_infinity     = string_attr attrs "infinity" default_decimal_format_symbols.dfs_infinity;
    dfs_minus_sign   = char_attr attrs "minus-sign" default_decimal_format_symbols.dfs_minus_sign;
    dfs_nan          = string_attr attrs "NaN" default_decimal_format_symbols.dfs_nan;
    dfs_percent      = char_attr attrs "percent" default_decimal_format_symbols.dfs_percent;
    dfs_per_mille    = char_attr attrs "per-mille" default_decimal_format_symbols.dfs_per_mille;
    dfs_zero_digit   = char_attr attrs "zero-digit" default_decimal_format_symbols.dfs_zero_digit;
    dfs_digit        = char_attr attrs "digit" default_decimal_format_symbols.dfs_digit;
    dfs_pattern_sep  = char_attr attrs "pattern-separator" default_decimal_format_symbols.dfs_pattern_sep;
  }

let rec collect_decimal_formats (pfx:string) (children:list xml_node) : Tot (list decimal_format_symbols) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag && xsl_instr pfx tag = "decimal-format" then
         decimal_format_of_attrs attrs :: collect_decimal_formats pfx tl
       else collect_decimal_formats pfx tl
     | _ -> collect_decimal_formats pfx tl)

(* ================================================================ *)
(* xsl:key (XSLT 1.0 §12.2): top-level declarations + the flat table   *)
(* build_style materialises from them by walking the source document. *)
(* ================================================================ *)

noeq type key_decl = { kd_name : string; kd_match : string; kd_use : string }

// Top-level xsl:key name/match/use declarations, in document order. A
// declaration missing any of the three required attributes is dropped
// (defensive; no idkey fixture omits one).
let rec collect_keys (pfx:string) (children:list xml_node) : Tot (list key_decl) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag && xsl_instr pfx tag = "key" then
         (match attr_opt "name" attrs, attr_opt "match" attrs, attr_opt "use" attrs with
          | Some nm, Some m, Some u -> { kd_name = nm; kd_match = m; kd_use = u } :: collect_keys pfx tl
          | _, _, _ -> collect_keys pfx tl)
       else collect_keys pfx tl
     | _ -> collect_keys pfx tl)

// One key_decl's contribution at one already-matched node: the `use`
// expression is evaluated with that node as context (position/size 1 --
// no idkey fixture's use expression reads position()/last()). A
// node-set result contributes ONE entry per node in it, keyed by THAT
// node's own string-value (not the whole set's, e.g. idkey59's
// `use="x | y | z"` union); any other value contributes a single entry
// keyed by its string form (e.g. idkey05's `use="'foo'"`, idkey08's
// `use="number(q)"`).
let key_entries_for_use (nsctx:list (string & string)) (id_attrs:list (string & string))
                        (style_root:xml_node) (decfmts:list decimal_format_symbols)
                        (kname:(option string & string)) (it:xctx_item) (use_expr:string)
  : list key_entry =
  match eval_val it 1 1 [] nsctx id_attrs style_root decfmts [] use_expr with
  | XV_Nodes ns -> List.Tot.map (fun (n:xctx_item) -> (kname, item_string_value n, it)) ns
  | other -> [(kname, to_string_val other, it)]

// One key_decl's contribution over every candidate node (all_document_
// items of the source document: the root element + every element/text/
// comment/PI descendant -- the same scope id() already accepts; no
// idkey fixture's `match` targets an attribute node).
let rec key_entries_for_decl (nsctx:list (string & string)) (id_attrs:list (string & string))
                             (style_root:xml_node) (decfmts:list decimal_format_symbols)
                             (kname:(option string & string)) (match_alts:list string) (use_expr:string)
                             (items:list xctx_item)
  : Tot (list key_entry) (decreases items) =
  match items with
  | [] -> []
  | it :: rest ->
    let here =
      // key_table is [] here -- a key's own `match`/`use` cannot see the
      // (not-yet-built) key table, so a key() call inside another key's
      // match/use pattern always selects nothing (self/mutually
      // referential keys: a disclosed, narrow gap -- no idkey fixture
      // needs one key's match/use to call key()).
      if any_alt_matches [] nsctx id_attrs style_root decfmts [] match_alts (D_Item it)
      then key_entries_for_use nsctx id_attrs style_root decfmts kname it use_expr
      else []
    in
    here @ key_entries_for_decl nsctx id_attrs style_root decfmts kname match_alts use_expr rest

// The whole stylesheet's key table: every key_decl's contribution,
// concatenated (a node registered under two different key names, or
// twice under the same one via two use-values, keeps both entries --
// idkey12/13 exercise multiple keys / multiple nodes per value).
let rec build_key_table (nsctx:list (string & string)) (id_attrs:list (string & string))
                        (style_root:xml_node) (decfmts:list decimal_format_symbols)
                        (decls:list key_decl) (items:list xctx_item)
  : Tot (list key_entry) (decreases decls) =
  match decls with
  | [] -> []
  | kd :: rest ->
    let kname = resolve_key_qname nsctx kd.kd_name in
    let alts = split_on_char '|' kd.kd_match in
    List.Tot.append
      (key_entries_for_decl nsctx id_attrs style_root decfmts kname alts kd.kd_use items)
      (build_key_table nsctx id_attrs style_root decfmts rest items)

// Resolve a cdata-section-elements QName against the stylesheet's
// namespace context. Unlike an XPath node test (name_test_matches_elem,
// which per XPath 1.0 2.5.3 treats an unprefixed name as the NULL
// namespace even when a default xmlns is in scope), a QName in this
// XML-attribute-value list picks up the default namespace like an
// ordinary element name would -- confirmed by Xalan output-output99 (no
// default xmlns: unprefixed "out" does NOT match <baz:out>) vs.
// output-output102 (default xmlns="http://baz.com" on the stylesheet: it
// DOES match).
let resolve_qname_ns (nsctx:list (string & string)) (qn:string) : (option string & string) =
  (lookup_nsctx nsctx (prefix_of qn), local_name_of qn)

// Fold one xsl:output element's attributes into the running merged
// settings. Every scalar attribute is last-wins (an element that omits
// an attribute leaves the running value from an earlier element alone);
// cdata-section-elements is the one exception -- its value is the UNION
// of every element's list (XSLT 1.0 16: "cdata-section-elements
// attribute... is the union"), so it is APPENDED, never overwritten.
let merge_one_output (nsctx:list (string & string)) (cfg:output_settings) (attrs:list xml_attribute) : output_settings =
  { os_method_raw = (match attr_opt "method" attrs with Some m -> m | None -> cfg.os_method_raw);
    os_omit_decl = (match attr_opt "omit-xml-declaration" attrs with Some v -> v = "yes" | None -> cfg.os_omit_decl);
    os_standalone = (match attr_opt "standalone" attrs with Some v -> v | None -> cfg.os_standalone);
    os_indent_raw = (match attr_opt "indent" attrs with Some v -> v | None -> cfg.os_indent_raw);
    os_encoding = (match attr_opt "encoding" attrs with Some v -> v | None -> cfg.os_encoding);
    os_version = (match attr_opt "version" attrs with Some v -> v | None -> cfg.os_version);
    os_doctype_public = (match attr_opt "doctype-public" attrs with Some v -> v | None -> cfg.os_doctype_public);
    os_doctype_system = (match attr_opt "doctype-system" attrs with Some v -> v | None -> cfg.os_doctype_system);
    os_cdata =
      List.Tot.append cfg.os_cdata
        (match attr_opt "cdata-section-elements" attrs with
         | Some v -> List.Tot.map (resolve_qname_ns nsctx) (parse_qname_list v)
         | None -> []);
  }

let rec collect_output_settings (pfx:string) (nsctx:list (string & string)) (children:list xml_node) (cfg:output_settings)
  : Tot output_settings (decreases children) =
  match children with
  | [] -> cfg
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag && xsl_instr pfx tag = "output" then
         collect_output_settings pfx nsctx tl (merge_one_output nsctx cfg attrs)
       else collect_output_settings pfx nsctx tl cfg
     | _ -> collect_output_settings pfx nsctx tl cfg)

// Whether at least one top-level xsl:output element is present at all --
// the gate that keeps a stylesheet with none byte-identical to the
// pre-xsl:output-support engine (see xs_output_present).
let rec any_output_decl (pfx:string) (children:list xml_node) : Tot bool (decreases children) =
  match children with
  | [] -> false
  | hd :: tl ->
    (match hd with
     | XElement tag _ _ -> if is_xsl pfx tag && xsl_instr pfx tag = "output" then true else any_output_decl pfx tl
     | _ -> any_output_decl pfx tl)

(* ================================================================ *)
(* xsl:attribute-set top-level declarations (XSLT 1.0 section 7.1.4). *)
(* ================================================================ *)

// Append `deps`/`own` onto the entry already recorded for `nm` (if
// any), or start a fresh one. Used by collect_attribute_sets, which
// walks decls in DOCUMENT order but recurses tail-first, so by the
// time a decl is folded in here `entries` already holds every LATER
// decl's contribution; appending (not prepending) `deps`/`own` after
// the existing entry places this (earlier) decl's own material AFTER
// every later-declared same-name decl's material -- i.e. the combined
// list ends up in REVERSE declaration order overall (see attrset_entry
// doc comment for why that matches Xalan's merge).
let rec attrset_upsert_append (entries:list attrset_entry) (nm:string) (deps:list string) (own:list xml_node)
  : Tot (list attrset_entry) (decreases entries) =
  match entries with
  | [] -> [{ ase_name = nm; ase_deps = deps; ase_own = own }]
  | e :: rest ->
    if e.ase_name = nm
    then { e with ase_deps = List.Tot.append e.ase_deps deps; ase_own = List.Tot.append e.ase_own own } :: rest
    else e :: attrset_upsert_append rest nm deps own

let rec collect_attribute_sets (pfx:string) (children:list xml_node) : Tot (list attrset_entry) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    let rest = collect_attribute_sets pfx tl in
    (match hd with
     | XElement tag attrs body ->
       if is_xsl pfx tag && xsl_instr pfx tag = "attribute-set" then
         let nm = attr_or "name" "" attrs in
         if nm = "" then rest
         else
           let deps = parse_qname_list (attr_or "use-attribute-sets" "" attrs) in
           attrset_upsert_append rest nm deps body
       else rest
     | _ -> rest)

// The stylesheet element's full namespace context (prefix -> URI),
// UNfiltered by exclude-result-prefixes -- see the xs_nsctx field.
let rec build_nsctx (attrs:list xml_attribute) : Tot (list (string & string)) (decreases attrs) =
  match attrs with
  | [] -> []
  | a :: rest ->
    (match ns_decl_prefix a.attr_name with
     | Some pfx -> (pfx, a.attr_value) :: build_nsctx rest
     | None -> build_nsctx rest)

(* ================================================================ *)
(* xsl:strip-space / xsl:preserve-space (XSLT 1.0 section 3.4):       *)
(* whitespace-only text-node stripping from the SOURCE tree, applied  *)
(* before any other processing (so key()/id()/position()/last() all  *)
(* see the ALREADY-stripped tree -- see the call sites in the         *)
(* "Entry point" section, which strip source_kids/root BEFORE handing *)
(* them to build_style/build_style_from_units and dispatch).          *)
(*                                                                    *)
(* Scope landed: the "elements" NameTest list (bare "*", "pfx:*", and  *)
(* exact "pfx:local"/"local" tokens, resolved against the stylesheet's *)
(* own in-scope namespaces -- same nsctx used for cdata-section-       *)
(* elements/resolve_qname_ns), xml:space="preserve"/"default" override *)
(* (nearest ancestor-or-self wins, tracked top-down while walking the   *)
(* source tree), and NameTest specificity (exact QName > pfx:* >        *)
(* bare "*", XSLT 1.0 section 2.6.5) with last-in-document-order        *)
(* breaking a same-specificity tie. A maximal run of adjacent            *)
(* XText/XCDATA siblings (no comment/PI/element in between -- those      *)
(* are non-text boundaries, so e.g. whitespace05's `<b> <!--c-->b</b>`   *)
(* still lets the lone leading space strip independently of the "b"      *)
(* that follows the comment) is treated as ONE whitespace-only-or-not     *)
(* unit: whitespace13-shaped `<out> <![CDATA[test]]> </out>` (three        *)
(* sibling nodes after CDATA parsing keeps XCDATA distinct from XText)      *)
(* must keep ALL three verbatim because the concatenated run contains       *)
(* "test", even though the leading/trailing pieces are individually          *)
(* whitespace-only.                                                           *)
(*                                                                             *)
(* NOT landed (reported, not chased): full XSLT 1.0 2.6.5 import-             *)
(* precedence-BEFORE-specificity resolution across xsl:include/xsl:import     *)
(* boundaries. collect_ws_decls is handed the already precedence-ordered      *)
(* (ascending) `all_children_desc` list build_style_from_units builds for     *)
(* every other top-level decl, and resolve_ws_strip picks the HIGHEST-        *)
(* specificity match with last-in-list breaking a tie -- correct for a        *)
(* single stylesheet (100% of the Xalan whitespace/ fixtures, none of which   *)
(* combine xsl:import/xsl:include with xsl:strip-space) and correct WITHIN    *)
(* one import-precedence layer, but a lower-precedence exact-QName decl in    *)
(* an imported file could out-rank a higher-precedence wildcard from the      *)
(* importing stylesheet here, where real XSLT 1.0 would let precedence win    *)
(* unconditionally. Same documented simplification the module already makes   *)
(* for prefixed match/select patterns inside an included/imported file (see   *)
(* the xsl:import/xsl:include banner above build_nsscope). Also not landed:    *)
(* the built-in "the STYLESHEET's own whitespace is stripped like strip-      *)
(* space=* applied to it, except inside xsl:text" rule (XSLT 1.0 3.4's last    *)
(* paragraph) -- whitespace09/13/20 need it (their fixtures declare no         *)
(* xsl:strip-space at all; the gap is in literal template whitespace, not      *)
(* source-tree whitespace) but landing it means walking and rewriting EVERY    *)
(* stylesheet's literal-result-element bodies before collect_templates/        *)
(* collect_attribute_sets/collect_globals run, which touches how every         *)
(* passing Xalan/xslt/xml-conformance fixture's literal output whitespace is    *)
(* built -- too large a blast radius for this change; left as a follow-up.      *)

// A single whitespace-only text run is all XML whitespace (space, tab, CR,
// LF) -- reuses the existing is_all_ws (defined above, `all_ws_chars`).
let text_or_cdata (n:xml_node) : option string =
  match n with
  | XText s -> Some s
  | XCDATA s -> Some s
  | _ -> None

// Whether the maximal run of contiguous XText/XCDATA nodes starting at the
// head of `nodes` is, taken together, ALL whitespace. A non-text node (an
// element, comment, or PI) ends the run without contributing (comments and
// PIs are ignored for whitespace-stripping purposes per XSLT 1.0 3.4, but
// they are NOT part of the same text run -- they don't merge adjacent text
// the way two XText/XCDATA siblings from a parsed CDATA boundary do).
let rec run_is_all_ws (nodes:list xml_node) : Tot bool (decreases nodes) =
  match nodes with
  | [] -> true
  | hd :: tl ->
    (match text_or_cdata hd with
     | Some s -> is_all_ws s && run_is_all_ws tl
     | None -> true)

// Effective xml:space at one element: its own attribute if present
// ("preserve"/"default"), else the inherited value from an ancestor.
// An unrecognised value defensively falls back to the inherited setting
// (no whitespace fixture supplies one; XSLT 1.0 doesn't define behavior
// for it either).
let xml_space_here (attrs:list xml_attribute) (inherited:bool) : bool =
  match find_attr "xml:space" attrs with
  | Some "preserve" -> true
  | Some "default" -> false
  | Some _ -> inherited
  | None -> inherited

// One NameTest token from a strip-space/preserve-space "elements" list.
// Specificity (XSLT 1.0 2.6.5): WNT_Qual (exact name) > WNT_NsStar
// (namespace-qualified wildcard) > WNT_Star (bare "*") -- see
// wnt_specificity below.
noeq type ws_name_test =
  | WNT_Star : ws_name_test
  | WNT_NsStar : option string -> ws_name_test
  | WNT_Qual : option string -> string -> ws_name_test

noeq type ws_decl = { wsd_test : ws_name_test; wsd_strip : bool }

// Parse one "elements" token against the stylesheet's namespace context
// (the SAME nsctx cdata-section-elements/resolve_qname_ns use -- a
// top-level xsl:strip-space/preserve-space's own in-scope namespaces).
// "*" is the bare wildcard; "pfx:*" is a namespace-qualified wildcard;
// anything else is an exact (possibly prefixed) name, unprefixed meaning
// the null namespace (XSLT 1.0 NameTest resolution, same as an XPath
// unprefixed name test -- no implicit default-namespace pickup for a
// bare local name written directly in this attribute).
let parse_ws_name_test (nsctx:list (string & string)) (tok:string) : ws_name_test =
  if tok = "*" then WNT_Star
  else
    match split_on_char ':' tok with
    | [pfx; "*"] -> WNT_NsStar (lookup_nsctx nsctx pfx)
    | [pfx; local] -> WNT_Qual (lookup_nsctx nsctx pfx) local
    | _ -> WNT_Qual None tok

let rec ws_decls_of_tokens (strip:bool) (tests:list string) (nsctx:list (string & string))
  : Tot (list ws_decl) (decreases tests) =
  match tests with
  | [] -> []
  | t :: rest -> { wsd_test = parse_ws_name_test nsctx t; wsd_strip = strip } :: ws_decls_of_tokens strip rest nsctx

// Top-level xsl:strip-space (wsd_strip = true) / xsl:preserve-space
// (wsd_strip = false) declarations, one ws_decl PER TOKEN in their
// "elements" list, in document order (mirrors collect_keys/
// collect_attribute_sets: called over the SAME already precedence-
// ordered `children`/`all_children_desc` list every other top-level
// decl collector uses). A decl missing "elements" is dropped
// (defensive; no whitespace fixture omits it).
let rec collect_ws_decls (pfx:string) (nsctx:list (string & string)) (children:list xml_node)
  : Tot (list ws_decl) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       let instr = if is_xsl pfx tag then xsl_instr pfx tag else "" in
       if instr = "strip-space" || instr = "preserve-space" then
         (match attr_opt "elements" attrs with
          | Some v -> List.Tot.append (ws_decls_of_tokens (instr = "strip-space") (parse_qname_list v) nsctx)
                                       (collect_ws_decls pfx nsctx tl)
          | None -> collect_ws_decls pfx nsctx tl)
       else collect_ws_decls pfx nsctx tl
     | _ -> collect_ws_decls pfx nsctx tl)

// NameTest specificity (XSLT 1.0 2.6.5): exact QName highest, then a
// namespace-qualified wildcard, then the bare wildcard lowest.
let wnt_specificity (t:ws_name_test) : int =
  match t with
  | WNT_Star -> 0
  | WNT_NsStar _ -> 1
  | WNT_Qual _ _ -> 2

let wnt_matches (elem_ns:option string) (elem_local:string) (t:ws_name_test) : bool =
  match t with
  | WNT_Star -> true
  | WNT_NsStar ns -> Some? ns && ns = elem_ns
  | WNT_Qual ns local -> ns = elem_ns && local = elem_local

// Resolve whether an element (elem_ns, elem_local) has its whitespace-only
// text children stripped: the HIGHEST-specificity matching decl wins;
// a tie is broken by the LAST matching decl in `decls`' order (which is
// document order within one stylesheet -- see the module banner above
// for the cross-file-precedence caveat). No match at all => preserve
// (XSLT 1.0's default whitespace handling).
let rec resolve_ws_strip (decls:list ws_decl) (elem_ns:option string) (elem_local:string)
                         (best:option (int & bool))
  : Tot bool (decreases decls) =
  match decls with
  | [] -> (match best with Some (_, s) -> s | None -> false)
  | d :: rest ->
    if wnt_matches elem_ns elem_local d.wsd_test then
      let sp = wnt_specificity d.wsd_test in
      let best' = (match best with
                   | None -> Some (sp, d.wsd_strip)
                   | Some (bsp, _) -> if sp >= bsp then Some (sp, d.wsd_strip) else best) in
      resolve_ws_strip rest elem_ns elem_local best'
    else resolve_ws_strip rest elem_ns elem_local best

// A SOURCE element's own (namespace-URI, local-name) identity, resolved
// against the incrementally-accumulated source-document namespace context
// (nearest declaration wins -- same idiom as resolve_ns_anc/elem_ns_uri in
// XPath.Eval, but threaded top-down here since strip_ws_source_node is
// already walking the tree top-down for xml:space). An unprefixed tag
// picks up the in-scope DEFAULT namespace if declared (prefix "" in
// nsctx), matching Namespaces-in-XML element-name resolution.
let source_elem_identity (nsctx:list (string & string)) (tag:string) : (option string & string) =
  (lookup_nsctx nsctx (name_prefix tag), local_name tag)

// Recursively strip whitespace-only text (XText/XCDATA runs) from the
// SOURCE tree per xsl:strip-space/xsl:preserve-space + xml:space. `nsctx`
// is the source document's accumulated in-scope namespaces (prefix ->
// URI) at THIS node's parent; `space_here` is the effective xml:space
// inherited from an ancestor-or-self (true = preserve, overriding
// `decls` entirely for this subtree).
let rec strip_ws_source_node (decls:list ws_decl) (nsctx:list (string & string)) (space_here:bool) (n:xml_node)
  : Tot xml_node (decreases n) =
  match n with
  | XElement tag attrs kids ->
    let nsctx' = List.Tot.append (build_nsctx attrs) nsctx in
    let space' = xml_space_here attrs space_here in
    let (ns, local) = source_elem_identity nsctx' tag in
    let strip_here = resolve_ws_strip decls ns local None in
    XElement tag attrs (strip_ws_source_nodes decls nsctx' space' strip_here kids)
  | other -> other

and strip_ws_source_nodes (decls:list ws_decl) (nsctx:list (string & string)) (space_here:bool) (strip_here:bool)
                          (nodes:list xml_node)
  : Tot (list xml_node) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    (match text_or_cdata hd with
     | Some _ ->
       if strip_here && not space_here && run_is_all_ws nodes
       then strip_ws_source_nodes decls nsctx space_here strip_here tl
       else hd :: strip_ws_source_nodes decls nsctx space_here strip_here tl
     | None ->
       (match hd with
        | XElement _ _ _ -> strip_ws_source_node decls nsctx space_here hd
        | other -> other)
       :: strip_ws_source_nodes decls nsctx space_here strip_here tl)

// Entry points for the "Entry point" section below: resolve strip-space/
// preserve-space decls from the stylesheet's own top-level children (the
// no-import/include case) or from an already-flattened, precedence-
// ordered unit list (the combining-stylesheets case, XSLT 1.0 2.6), and
// apply strip_ws_source_node to the source document's root element. A
// stylesheet that declares neither directive returns `root` completely
// unchanged (no tree walk at all) -- the byte-identical-when-no-strip-
// space guarantee the protect suites rely on.
let strip_source_whitespace_simple (stylesheet:xml_node) (root:xml_node) : xml_node =
  match stylesheet with
  | XElement tag attrs children ->
    let pfx = xsl_prefix_of stylesheet in
    if is_xsl pfx tag && (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform") then
      (match collect_ws_decls pfx (build_nsctx attrs) children with
       | [] -> root
       | decls -> strip_ws_source_node decls [] false root)
    else root
  | _ -> root

let strip_source_whitespace_units (units:list (int & list xml_node)) (root_pfx:string)
                                   (root_attrs:list xml_attribute) (root:xml_node)
  : xml_node =
  let all_children_desc = List.Tot.flatten (List.Tot.map snd (List.Tot.rev units)) in
  (match collect_ws_decls root_pfx (build_nsctx root_attrs) all_children_desc with
   | [] -> root
   | decls -> strip_ws_source_node decls [] false root)

// Splice a (whitespace-stripped) replacement root element back into a
// document-node children list in place of the original root -- XML
// well-formedness guarantees exactly one XElement among `kids` (the
// prolog/epilog Comment/PI Misc nodes pass through untouched).
let rec replace_doc_root (kids:list xml_node) (new_root:xml_node) : Tot (list xml_node) (decreases kids) =
  match kids with
  | [] -> []
  | (XElement _ _ _) :: tl -> new_root :: tl
  | hd :: tl -> hd :: replace_doc_root tl new_root

(* ================================================================ *)

// Top-level xsl:variable / xsl:param with a select= expression,
// evaluated once against the source DOCUMENT node (XSLT 1.0 §11.4: the
// context node for a global variable is the root node, not the document
// element). Using the document-node evaluator makes a relative location
// path like `data/row` resolve as the absolute `/data/row` — evaluating
// it against the root ELEMENT instead (the earlier behaviour) looked for
// a `data` CHILD of `<data>` and returned the empty node-set, so
// `for-each select="$var"` over such a global silently produced nothing
// (namespace-1701).
// `st` is a not-yet-fully-populated xstyle (xs_globals still the
// placeholder the caller is in the middle of computing -- see
// build_style/build_style_from_units) whose OTHER fields (templates,
// attribute-sets, decimal-formats, key table, ...) are already final, so
// an RTF body containing xsl:apply-templates/xsl:call-template resolves
// against the real stylesheet. A body that itself references another
// global variable still sees it unbound (XV_Str "" from lookup_var),
// exactly the pre-existing limitation of the select= branch below (which
// also evaluates with vars=[], no cross-global visibility) -- collect_globals
// has never supported forward/sibling references between globals, and this
// change does not add or remove that.
let rec collect_globals (fuel:nat) (st:xstyle) (children:list xml_node) (source:xml_node) (doc_kids:list xml_node)
  : Tot (list (string & xp_value)) (decreases children) =
  if fuel = 0 then [] else
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs body ->
       if is_xsl st.xs_pfx tag &&
          (let ln = xsl_instr st.xs_pfx tag in ln = "variable" || ln = "param") then
         (match attr_opt "select" attrs, attr_opt "name" attrs with
          | Some sel, Some nm ->
            let v = eval_val_dn (D_Doc source doc_kids) 1 1 [] st.xs_nsctx st.xs_id_attrs xnode_none st.xs_decfmts [] sel in
            (nm, v) :: collect_globals (fuel - 1) st tl source doc_kids
          | None, Some nm ->
            // Result-tree-fragment global (no select=): instantiate the
            // body and bind its string-value, mirroring the LOCAL
            // xsl:variable/param RTF handling above (instantiate_seq +
            // text_value_nodes (only_nodes ...)). Global RTF variables
            // have no separate node-sequence table (xstyle carries no
            // global analogue of the local `rtf` accumulator), so
            // xsl:copy-of on a global RTF variable is not covered by
            // this fix -- only its string-value (boolean()/=/!=/string
            // contexts, the fixtures this fixes) is.
            let frag = instantiate_seq (fuel - 1) st (D_Doc source doc_kids) 1 1 [] [] "" 0 body in
            let sval = text_value_nodes (only_nodes frag) in
            (nm, XV_Str sval) :: collect_globals (fuel - 1) st tl source doc_kids
          | _, _ -> collect_globals (fuel - 1) st tl source doc_kids)
       else collect_globals (fuel - 1) st tl source doc_kids
     | _ -> collect_globals (fuel - 1) st tl source doc_kids)

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

(* ================================================================ *)
(* Combining stylesheets: xsl:import / xsl:include (XSLT 1.0 section  *)
(* 2.6). File I/O and href-to-path resolution are NOT here (rule #11: *)
(* that lives in bin/xslt-runner/xslt_runner.ml, pure I/O plumbing).  *)
(* This module owns every combining/precedence DECISION:              *)
(*   - stylesheet_href_directives: pure query the runner uses to      *)
(*     discover which files to read next (bool=true is xsl:import,    *)
(*     false is xsl:include; order = document order).                 *)
(*   - sheet_tree: the runner hands back one of these once it has     *)
(*     read+parsed every transitively-referenced file (cycle detection*)
(*     is the runner's bounded-visited-set I/O concern; a skipped/     *)
(*     cyclic reference is represented as an empty placeholder node,   *)
(*     which this module's process_node treats as contributing zero    *)
(*     content -- never a crash).                                     *)
(*   - process_node/process_children/expand_include: xsl:include       *)
(*     SPLICES a target's top-level elements in place, at the SAME     *)
(*     import precedence as the includer (XSLT 1.0 2.6.1); xsl:import  *)
(*     gets its own STRICTLY LOWER precedence, assigned by a postorder *)
(*     counter (each import's whole subtree numbered before moving to  *)
(*     the next sibling import, so a LATER xsl:import gets a HIGHER    *)
(*     precedence than an EARLIER one, both still below the importing  *)
(*     stylesheet -- matches the worked examples in the impincl Xalan  *)
(*     fixtures: impincl05 "(low) DBECA (high)", impincl07's reversed   *)
(*     import order, impincl22 "(high) h, f, g (low)", impincl23        *)
(*     "(high) i23sub, h (low)"). Fuel-bound (same idiom as dispatch)   *)
(*     rather than relying on sheet_tree's own structural subterm order,*)
(*     since the include/import cross-branch recursion does not fit a  *)
(*     single structural decreases measure.                            *)
(*   - build_style_from_units: folds the flattened (precedence,        *)
(*     children) list into one xstyle via the SAME collect_* helpers    *)
(*     build_style itself uses, so a stylesheet with zero import/include*)
(*     directives (units = [(0, its own children)]) produces the        *)
(*     IDENTICAL xstyle build_style would -- protects the pre-existing  *)
(*     Xalan/xslt/xml-conformance scores, since the runner only takes   *)
(*     this path when stylesheet_href_directives is non-empty.          *)
(*   - Namespace context (xs_nsctx/xs_nsscope), xs_id_attrs and          *)
(*     xs_style_root come from the ROOT stylesheet ONLY, never merged:  *)
(*     impincl09 documents "No namespaces should be copied over" from   *)
(*     an xsl:include target's own xmlns declarations.                  *)
(* ================================================================ *)

// (is_import, href) pairs for a stylesheet's top-level xsl:import /
// xsl:include children, in document order. Pure query -- no I/O, no
// combining decision; the runner uses this to know which hrefs to
// resolve+read next (recursively, for each fetched file in turn).
let rec collect_href_directives (pfx:string) (children:list xml_node) : Tot (list (bool & string)) (decreases children) =
  match children with
  | [] -> []
  | hd :: tl ->
    (match hd with
     | XElement tag attrs _ ->
       if is_xsl pfx tag && xsl_instr pfx tag = "import" then
         (match attr_opt "href" attrs with
          | Some h -> (true, h) :: collect_href_directives pfx tl
          | None -> collect_href_directives pfx tl)
       else if is_xsl pfx tag && xsl_instr pfx tag = "include" then
         (match attr_opt "href" attrs with
          | Some h -> (false, h) :: collect_href_directives pfx tl
          | None -> collect_href_directives pfx tl)
       else collect_href_directives pfx tl
     | _ -> collect_href_directives pfx tl)

let stylesheet_href_directives (root:xml_node) : list (bool & string) =
  match root with
  | XElement tag attrs children ->
    let pfx = xsl_prefix_of root in
    if is_xsl pfx tag && (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform")
    then collect_href_directives pfx children
    else []
  | _ -> []

// One resolved stylesheet file plus its OWN resolved xsl:include /
// xsl:import targets (already read+parsed by the runner, recursively,
// relative to THAT file's own base directory -- impincl04/impincl08
// exercise an included file whose OWN xsl:include is relative to ITS
// directory, not the root stylesheet's). `includes`/`imports` are in
// document order, 1:1 with collect_href_directives' output for `root`.
noeq type sheet_tree =
  | Sheet_Node : root:xml_node -> includes:list sheet_tree -> imports:list sheet_tree -> sheet_tree

let rec sheet_tree_xml_count (t:sheet_tree) : Tot nat (decreases t) =
  match t with
  | Sheet_Node root incs imps -> xml_node_count root + sheet_tree_list_xml_count incs + sheet_tree_list_xml_count imps
and sheet_tree_list_xml_count (ts:list sheet_tree) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | hd :: tl -> sheet_tree_xml_count hd + sheet_tree_list_xml_count tl

// Flatten a sheet_tree into (precedence, top-level-children) units, one
// per compilation unit (a file, with its OWN xsl:include targets already
// spliced into its children -- see expand_include), in ASCENDING
// precedence order (lowest/most-imported first, the tree's own root
// last). Fuel-bound: `counter` is threaded functionally (not mutated),
// starts at 0, and every xsl:import bumps it by processing that import's
// ENTIRE subtree (postorder) before moving to the next sibling import or
// assigning the current node its own (highest-so-far) precedence.
let rec process_node (fuel:nat) (counter:int) (t:sheet_tree)
  : Tot (int & list (int & list xml_node)) (decreases fuel) =
  if fuel = 0 then (counter, [])
  else
    match t with
    | Sheet_Node root includes imports ->
      let pfx = xsl_prefix_of root in
      (match root with
       | XElement tag attrs children ->
         if is_xsl pfx tag && (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform")
         then
           let (counter1, ordinary, import_units) =
             process_children (fuel - 1) counter pfx children includes imports in
           let my_prec = counter1 + 1 in
           (my_prec, List.Tot.append import_units [(my_prec, ordinary)])
         else (counter, [])  // not a <xsl:stylesheet>: contributes nothing (defensive; no impincl fixture hits this)
       | _ -> (counter, []))

// Walk one stylesheet's top-level children: splice xsl:include targets
// in place (their own ordinary content joins THIS unit; their own
// nested xsl:import targets join the returned import_units, positioned
// exactly where the xsl:include appeared -- impincl23's "i23incl imports
// i23sub" case), and pull out xsl:import targets (each numbered via
// process_node, in document order, BEFORE any later sibling import).
and process_children (fuel:nat) (counter:int) (pfx:string) (children:list xml_node)
                     (includes:list sheet_tree) (imports:list sheet_tree)
  : Tot (int & list xml_node & list (int & list xml_node)) (decreases fuel) =
  if fuel = 0 then (counter, [], [])
  else
    match children with
    | [] -> (counter, [], [])
    | hd :: tl ->
      (match hd with
       | XElement tag attrs _ ->
         if is_xsl pfx tag && xsl_instr pfx tag = "include" then
           (match includes with
            | [] -> process_children (fuel - 1) counter pfx tl [] imports
            | inc :: more_incs ->
              let (counter1, sub_ordinary, sub_units) = expand_include (fuel - 1) counter inc in
              let (counter2, rest_ordinary, rest_units) = process_children (fuel - 1) counter1 pfx tl more_incs imports in
              (counter2, List.Tot.append sub_ordinary rest_ordinary, List.Tot.append sub_units rest_units))
         else if is_xsl pfx tag && xsl_instr pfx tag = "import" then
           (match imports with
            | [] -> process_children (fuel - 1) counter pfx tl includes []
            | imp :: more_imps ->
              let (counter1, imp_units) = process_node (fuel - 1) counter imp in
              let (counter2, rest_ordinary, rest_units) = process_children (fuel - 1) counter1 pfx tl includes more_imps in
              (counter2, rest_ordinary, List.Tot.append imp_units rest_units))
         else
           let (counter1, rest_ordinary, rest_units) = process_children (fuel - 1) counter pfx tl includes imports in
           (counter1, hd :: rest_ordinary, rest_units)
       | _ ->
         let (counter1, rest_ordinary, rest_units) = process_children (fuel - 1) counter pfx tl includes imports in
         (counter1, hd :: rest_ordinary, rest_units))

// An xsl:include target's own top-level children (SAME precedence as
// the includer -- no new unit is created for it), with its OWN nested
// xsl:include/xsl:import handled recursively exactly like a top-level
// stylesheet's children would be.
and expand_include (fuel:nat) (counter:int) (t:sheet_tree)
  : Tot (int & list xml_node & list (int & list xml_node)) (decreases fuel) =
  if fuel = 0 then (counter, [], [])
  else
    match t with
    | Sheet_Node root includes imports ->
      let pfx = xsl_prefix_of root in
      (match root with
       | XElement tag attrs children ->
         if is_xsl pfx tag && (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform")
         then process_children (fuel - 1) counter pfx children includes imports
         else (counter, [], [])
       | _ -> (counter, [], []))

// Public entry for the runner: flatten the whole tree into ascending-
// precedence (precedence, children) units. Fuel generously sized off
// the tree's total node count (same idiom as dispatch's own fuel sizing).
let sheet_units (t:sheet_tree) : list (int & list xml_node) =
  let fuel = op_Multiply 4 (sheet_tree_xml_count t + 1) + 1000 in
  let (_, units) = process_node fuel 0 t in
  units

// Merge a flattened unit list into one xstyle, using the SAME collect_*
// helpers build_style uses (so a no-import/include stylesheet, units =
// [(0, children)], produces byte-identical output to build_style).
// Globals are merged HIGHEST-precedence-first (units_desc) so a same-
// named global at higher import precedence shadows a lower one
// (lookup_var / collect_globals is first-match-wins) -- XSLT 1.0 section
// 11.4's rule for global variables. Attribute-sets/decimal-formats/
// output settings merge over the same list; no impincl fixture exercises
// a cross-file name clash for those, so the concatenation order used for
// them is a reasonable default rather than a precedence-exact merge.
let build_style_from_units (units:list (int & list xml_node)) (root_pfx:string) (root_attrs:list xml_attribute)
                            (root_node:xml_node) (source:xml_node) (doc_kids:list xml_node)
                            (id_attrs:list (string & string))
  : xstyle =
  let nsctx = build_nsctx root_attrs in
  let units_desc = List.Tot.rev units in
  let all_children_desc = List.Tot.flatten (List.Tot.map snd units_desc) in
  let decfmts = collect_decimal_formats root_pfx all_children_desc in
  let out_settings = collect_output_settings root_pfx nsctx all_children_desc default_output_settings in
  let key_decls = collect_keys root_pfx all_children_desc in
  let key_table =
    (match key_decls with
     | [] -> []
     | _ -> build_key_table nsctx id_attrs root_node decfmts key_decls (all_document_items (CI_Elem [] [] source))) in
  // st0 has every field final EXCEPT xs_globals (placeholder []) -- this
  // xstyle is then handed to collect_globals so an RTF global variable's
  // body can dispatch through the real templates/attrsets/key-table (see
  // collect_globals' banner). xs_globals itself never feeds collect_globals
  // (no cross-global visibility, unchanged from before this fix).
  let st0 = {
    xs_pfx = root_pfx;
    xs_templates = List.Tot.concatMap (fun (pc:(int & list xml_node)) -> collect_templates_prec root_pfx (fst pc) (snd pc)) units;
    xs_attrsets = collect_attribute_sets root_pfx all_children_desc;
    xs_method = (if out_settings.os_method_raw = "text" then "text" else "xml");
    xs_output_present = any_output_decl root_pfx all_children_desc;
    xs_output = out_settings;
    xs_globals = [];
    xs_nsscope = build_nsscope root_attrs;
    xs_nsctx = nsctx;
    xs_id_attrs = id_attrs;
    xs_style_root = root_node;
    xs_decfmts = decfmts;
    xs_key_table = key_table } in
  let gfuel = op_Multiply 4 (xml_nodes_count all_children_desc + 1) + 1000 in
  { st0 with xs_globals = collect_globals gfuel st0 all_children_desc source doc_kids }

let build_style (stylesheet:xml_node) (source:xml_node) (doc_kids:list xml_node) (id_attrs:list (string & string)) : xstyle =
  match stylesheet with
  | XElement tag attrs children ->
    let pfx = xsl_prefix_of stylesheet in
    if is_xsl pfx tag &&
       (let ln = xsl_instr pfx tag in ln = "stylesheet" || ln = "transform") then
      let nsctx = build_nsctx attrs in
      let decfmts = collect_decimal_formats pfx children in
      let out_settings = collect_output_settings pfx nsctx children default_output_settings in
      let key_decls = collect_keys pfx children in
      let key_table =
        (match key_decls with
         | [] -> []
         | _ -> build_key_table nsctx id_attrs stylesheet decfmts key_decls (all_document_items (CI_Elem [] [] source))) in
      // st0/gfuel: see build_style_from_units' matching comment above --
      // same two-phase (build everything but globals, then collect_globals
      // against that near-final xstyle) construction.
      let st0 = {
        xs_pfx = pfx;
        xs_templates = collect_templates pfx children;
        xs_attrsets = collect_attribute_sets pfx children;
        xs_method = (if out_settings.os_method_raw = "text" then "text" else "xml");
        xs_output_present = any_output_decl pfx children;
        xs_output = out_settings;
        xs_globals = [];
        xs_nsscope = build_nsscope attrs;
        xs_nsctx = nsctx;
        xs_id_attrs = id_attrs;
        xs_style_root = stylesheet;
        xs_decfmts = decfmts;
        xs_key_table = key_table } in
      let gfuel = op_Multiply 4 (xml_nodes_count children + 1) + 1000 in
      { st0 with xs_globals = collect_globals gfuel st0 children source doc_kids }
    else
      // Simplified stylesheet: the literal result element IS the body
      // of a single template matching the document root. Its own
      // namespace declarations are on the element itself, so no
      // inherited scope is threaded. A simplified stylesheet has no
      // top-level siblings, so it cannot carry xsl:decimal-format or
      // xsl:output either.
      { xs_pfx = pfx;
        xs_templates = [ { tpl_match = "/"; tpl_name = ""; tpl_mode = ""; tpl_prio = None; tpl_body = [stylesheet]; tpl_import_prec = 0 } ];
        xs_attrsets = [];
        xs_method = "xml";
        xs_output_present = false;
        xs_output = default_output_settings;
        xs_globals = [];
        xs_nsscope = [];
        xs_nsctx = build_nsctx attrs;
        xs_id_attrs = id_attrs;
        xs_style_root = stylesheet;
        xs_decfmts = [];
        xs_key_table = [] }
  | _ ->
    { xs_pfx = "xsl"; xs_templates = []; xs_attrsets = []; xs_method = "xml";
      xs_output_present = false; xs_output = default_output_settings;
      xs_globals = []; xs_nsscope = []; xs_nsctx = [];
      xs_id_attrs = id_attrs; xs_style_root = stylesheet; xs_decfmts = []; xs_key_table = [] }

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

// XML declaration line for an xsl:output-bearing stylesheet (only ever
// emitted when xs_output_present -- see finalize_output). Attribute
// defaults per XSLT 1.0 16.1/16.2: version "1.0", encoding "UTF-8",
// standalone omitted unless the stylesheet specified one.
let make_decl (cfg:output_settings) : string =
  let ver = if cfg.os_version = "" then "1.0" else cfg.os_version in
  let enc = if cfg.os_encoding = "" then "UTF-8" else cfg.os_encoding in
  let standalone_part =
    if cfg.os_standalone = "" then ""
    else String.concat "" [" standalone=\""; cfg.os_standalone; "\""] in
  String.concat "" ["<?xml version=\""; ver; "\" encoding=\""; enc; "\""; standalone_part; "?>\n"]

// The result tree's root element tag (skipping any leading top-level
// comment/PI), used as the DOCTYPE's root-name.
let rec root_tag_of (nodes:list xml_node) : Tot (option string) (decreases nodes) =
  match nodes with
  | [] -> None
  | XElement t _ _ :: _ -> Some t
  | _ :: rest -> root_tag_of rest

// XSLT 1.0 16.1's method-default rule: "if there is no xsl:output element,
// or the xsl:output element that is present has no method attribute...
// if the first node of the result tree ... is an element node whose
// expanded-name is html ... then ... html; otherwise ... xml." This is
// checked ONLY when method_raw is unset (Xalan output-output27/71: a
// stylesheet with NO xsl:output at all still gets html-method's default
// indent="yes"). `prefix_of tag = ""` approximates "no namespace" --
// cheap and correct for every fixture (none gives the actual html root
// element its OWN xmlns and expects the default-method check to still
// fire; output-output63's xmlns is on a stylesheet with an EXPLICIT
// method="html", not relying on this default-detection path).
let implicit_html_root (nodes:list xml_node) : bool =
  match root_tag_of nodes with
  | Some tag -> prefix_of tag = "" && ascii_lower_str (local_name_of tag) = "html"
  | None -> false

// doctype-public / doctype-system (XSLT 1.0 16.1/16.2). For method="xml"
// (and "text", though text ignores this entirely), doctype-public alone
// (no doctype-system) has no PUBLIC-without-SYSTEM form in XML and is
// simply not emitted (Xalan output-output14: doctype-public alone on an
// xml-method stylesheet produces NO DOCTYPE line at all). For
// method="html", Xalan's ToHTMLStream instead accepts doctype-public
// alone and writes a PUBLIC-only DOCTYPE line, and -- unlike xml method,
// which names the result tree's actual root element -- ALWAYS uses the
// literal root name "HTML" regardless of the real root element's
// spelling or case (Xalan output-output40/48/60: a <root>/<html
// lang="en">-rooted document still gets "<!DOCTYPE HTML ...>").
let make_doctype (is_html:bool) (cfg:output_settings) (nodes:list xml_node) : string =
  if is_html then
    (if cfg.os_doctype_system = "" && cfg.os_doctype_public = "" then ""
     else
       let tag = "HTML" in
       if cfg.os_doctype_public <> "" && cfg.os_doctype_system <> "" then
         String.concat "" ["<!DOCTYPE "; tag; " PUBLIC \""; cfg.os_doctype_public; "\" \""; cfg.os_doctype_system; "\">\n"]
       else if cfg.os_doctype_public <> "" then
         String.concat "" ["<!DOCTYPE "; tag; " PUBLIC \""; cfg.os_doctype_public; "\">\n"]
       else
         String.concat "" ["<!DOCTYPE "; tag; " SYSTEM \""; cfg.os_doctype_system; "\">\n"])
  else
    (if cfg.os_doctype_system = "" then ""
     else
       match root_tag_of nodes with
       | None -> ""
       | Some tag ->
         if cfg.os_doctype_public <> "" then
           String.concat "" ["<!DOCTYPE "; tag; " PUBLIC \""; cfg.os_doctype_public; "\" \""; cfg.os_doctype_system; "\">\n"]
         else
           String.concat "" ["<!DOCTYPE "; tag; " SYSTEM \""; cfg.os_doctype_system; "\">\n"])

// method="html" (XSLT 1.0 16.2): "if there is a HEAD element..., add a
// META element right after the start-tag of the HEAD element" naming the
// output encoding's charset, UNLESS a META http-equiv="Content-Type"
// child is already present. `is_meta_content_type`/`has_meta_content_type`
// implement the "already present" check; `inject_meta_in_elem`/
// `inject_meta_in_list` are a depth-first search+splice over the WHOLE
// result tree (mirrors the serialize_node/serialize_children mutual-
// recursion shape so F*'s termination checker accepts descending into
// `children`, a strict sub-term of the list head, the same way
// xml_node_count/serialize_node already do) that stops at the FIRST head
// element found in document order (Xalan output-output01 et al. only
// ever have one HEAD).
let is_meta_content_type (n:xml_node) : bool =
  match n with
  | XElement tag attrs _ ->
    ascii_lower_str (local_name_of tag) = "meta" &&
    (match attr_opt "http-equiv" attrs with
     | Some v -> ascii_lower_str v = "content-type"
     | None -> false)
  | _ -> false

let rec has_meta_content_type (kids:list xml_node) : Tot bool (decreases kids) =
  match kids with
  | [] -> false
  | hd :: tl -> if is_meta_content_type hd then true else has_meta_content_type tl

let make_meta_elem (encoding:string) : xml_node =
  XElement "meta"
    [ { attr_name = "http-equiv"; attr_value = "Content-Type" };
      { attr_name = "content"; attr_value = String.concat "" ["text/html; charset="; encoding] } ]
    []

let rec inject_meta_in_elem (encoding:string) (n:xml_node) : Tot (xml_node & bool) (decreases n) =
  match n with
  | XElement tag attrs children ->
    if ascii_lower_str (local_name_of tag) = "head" then
      let children' =
        if has_meta_content_type children then children
        else (make_meta_elem encoding) :: children in
      (XElement tag attrs children', true)
    else
      let (children', found) = inject_meta_in_list encoding children in
      (XElement tag attrs children', found)
  | _ -> (n, false)
and inject_meta_in_list (encoding:string) (kids:list xml_node) : Tot (list xml_node & bool) (decreases kids) =
  match kids with
  | [] -> ([], false)
  | hd :: tl ->
    let (hd', found) = inject_meta_in_elem encoding hd in
    if found then (hd' :: tl, true)
    else
      let (tl', found2) = inject_meta_in_list encoding tl in
      (hd' :: tl', found2)

let html_inject_meta (encoding:string) (nodes:list xml_node) : list xml_node =
  fst (inject_meta_in_list encoding nodes)

// Final serialization step, shared by all three entry points below.
// `present` (xs_output_present) is the hard compatibility gate: FALSE
// reproduces the pre-xsl:output-support engine byte for byte (no
// declaration, no DOCTYPE, no indent, no CDATA wrapping, no method="html"
// treatment at all -- see implicit_html_root's doc comment on why the
// no-xsl:output-element default-method-detection corner, output27/71,
// is deliberately NOT reproduced here) via the exact same serialize_nodes
// call with default_ser_settings, so a stylesheet with no xsl:output
// element cannot be affected by anything in this module however
// xsl:output's semantics evolve. `method` is xs_method ("text"/"xml") --
// text output ignores every xsl:output serialization setting other than
// method itself (XSLT 1.0 16.3).
let finalize_output (present:bool) (cfg:output_settings) (method:string) (nodes:list xml_node) : string =
  if method = "text" then text_value_nodes nodes
  else if not present then serialize_nodes default_ser_settings [] nodes
  else
    // method="html": void-element/boolean-attribute/script-style-raw/
    // HTML-entity serialization (see ser_html), a META charset injection,
    // and a DOCTYPE naming the literal root "HTML" -- all gated on
    // `is_html`, which is TRUE for an explicit method="html" AND for the
    // XSLT 1.0 16.1 default-method-detection corner (an xsl:output
    // element IS present -- this whole branch is behind `present` -- but
    // omits method, and the result tree's root is literally named
    // "html"/"HTML"). The one OTHER observable difference honoured for
    // html method is XSLT 1.0's own default-indent rule ("yes" if the
    // method is html; "no" otherwise), consulted only when the
    // stylesheet didn't set indent explicitly.
    let is_html = cfg.os_method_raw = "html" || (cfg.os_method_raw = "" && implicit_html_root nodes) in
    let indent_on =
      if cfg.os_indent_raw = "yes" then true
      else if cfg.os_indent_raw = "no" then false
      else is_html in
    let ser = { ser_cdata = cfg.os_cdata; ser_indent = indent_on; ser_encoding = cfg.os_encoding; ser_html = is_html } in
    let charset = if cfg.os_encoding = "" then "UTF-8" else cfg.os_encoding in
    let nodes' = if is_html then html_inject_meta charset nodes else nodes in
    let body = serialize_nodes ser [] nodes' in
    let decl = if cfg.os_omit_decl then "" else make_decl cfg in
    let doctype = make_doctype is_html cfg nodes in
    String.concat "" [decl; doctype; body]

(* ================================================================ *)
(* Entry point.                                                       *)
(* ================================================================ *)

// Legacy entry: `source` is the root element alone (the document node has
// no prolog/epilog Misc). GRDDL and the js/npm bridge use this; behavior
// is byte-for-byte what it was before the document-node model existed.
// `strip_source_whitespace_simple` (XSLT 1.0 3.4) runs FIRST, before
// build_style/dispatch, so key()/id()/position()/last() all see the
// already-stripped tree; it is a no-op (returns `source` unchanged) for
// any stylesheet that declares neither xsl:strip-space nor
// xsl:preserve-space, which is every stylesheet in the pre-existing
// protect suites (xslt slice-1, xml-conformance, and all but 12 of the
// Xalan corpus's ~1690 stylesheets) -- so this stays byte-identical there.
let transform (stylesheet:xml_node) (source:xml_node) : string =
  let source' = strip_source_whitespace_simple stylesheet source in
  let st = build_style stylesheet source' [source'] [] in
  // Fuel: generous multiple of the combined tree sizes -- every
  // apply-templates / instantiate step consumes one unit.
  let sz = xml_node_count stylesheet + xml_node_count source' in
  let fuel = op_Multiply (sz + 1) 256 + 100000 in
  let result = dispatch fuel st (D_Doc source' [source']) 1 1 "" st.xs_globals [] in
  let nodes = only_nodes result in
  finalize_output st.xs_output_present st.xs_output st.xs_method nodes

// Document-node aware entry: `source_kids` is the full ordered child list
// of the source document node (prolog Comment/PI Misc, root element,
// epilog Misc), from Parser.XML.parse_xml_document_children. The XSLT
// document node then exposes those Misc nodes, so `//comment()` reaches a
// prolog comment (select-1001) and the identity transform copies a leading
// comment (copy-2601). With no Misc (source_kids = [root]) it reduces to
// `transform` exactly. Whitespace-stripped the same way `transform` is
// (see its banner) via replace_doc_root splicing the stripped root back
// into source_kids.
let transform_doc (stylesheet:xml_node) (source_kids:list xml_node) : string =
  match doc_root_elem source_kids with
  | None -> ""
  | Some root ->
    let root' = strip_source_whitespace_simple stylesheet root in
    let source_kids' = replace_doc_root source_kids root' in
    let st = build_style stylesheet root' source_kids' [] in
    let sz = xml_node_count stylesheet + xml_nodes_count_sum source_kids' in
    let fuel = op_Multiply (sz + 1) 256 + 100000 in
    let result = dispatch fuel st (D_Doc root' source_kids') 1 1 "" st.xs_globals [] in
    let nodes = only_nodes result in
    finalize_output st.xs_output_present st.xs_output st.xs_method nodes

// Document-node aware entry that ALSO threads the SOURCE document's DTD
// internal-subset ATTLIST ID-type declarations (from
// Parser.XML.parse_xml_document_children_with_ids). id() and id()-anchored
// match patterns need it; document("") uses the stylesheet root (recorded
// in build_style). Reduces to transform_doc when source_id_attrs = [].
let transform_doc_ids (stylesheet:xml_node) (source_kids:list xml_node) (source_id_attrs:list (string & string)) : string =
  match doc_root_elem source_kids with
  | None -> ""
  | Some root ->
    let root' = strip_source_whitespace_simple stylesheet root in
    let source_kids' = replace_doc_root source_kids root' in
    let st = build_style stylesheet root' source_kids' source_id_attrs in
    let sz = xml_node_count stylesheet + xml_nodes_count_sum source_kids' in
    let fuel = op_Multiply (sz + 1) 256 + 100000 in
    let result = dispatch fuel st (D_Doc root' source_kids') 1 1 "" st.xs_globals [] in
    let nodes = only_nodes result in
    finalize_output st.xs_output_present st.xs_output st.xs_method nodes

// Combining-stylesheets entry point (XSLT 1.0 section 2.6): `t` is a
// sheet_tree the runner built by following the ROOT stylesheet's
// xsl:import/xsl:include hrefs (via stylesheet_href_directives),
// recursively reading+parsing every referenced file relative to ITS OWN
// base directory, and reporting a cycle/skip as an empty placeholder
// node (see the sheet_tree doc comment). Everything from here on --
// splicing, import-precedence numbering, template conflict resolution,
// xsl:apply-imports -- is this module's own logic (process_node /
// build_style_from_units / pick_template / pick_template_below), not the
// runner's. Reduces to transform_doc_ids's own xstyle byte-for-byte when
// `t` has no includes/imports (units = [(0, root's own children)]), so
// the runner only needs to route here when stylesheet_href_directives
// on the root stylesheet is non-empty -- every other stylesheet keeps
// using transform_doc_ids unchanged (zero regression risk).
let transform_doc_ids_merged (t:sheet_tree) (source_kids:list xml_node) (source_id_attrs:list (string & string)) : string =
  match doc_root_elem source_kids with
  | None -> ""
  | Some root ->
    (match t with
     | Sheet_Node root_style_node _ _ ->
       let root_pfx = xsl_prefix_of root_style_node in
       let root_attrs = element_attrs root_style_node in
       let units = sheet_units t in
       let root' = strip_source_whitespace_units units root_pfx root_attrs root in
       let source_kids' = replace_doc_root source_kids root' in
       let st = build_style_from_units units root_pfx root_attrs root_style_node root' source_kids' source_id_attrs in
       let sz = sheet_tree_xml_count t + xml_nodes_count_sum source_kids' in
       let fuel = op_Multiply (sz + 1) 256 + 100000 in
       let result = dispatch fuel st (D_Doc root' source_kids') 1 1 "" st.xs_globals [] in
       let nodes = only_nodes result in
       finalize_output st.xs_output_present st.xs_output st.xs_method nodes)
