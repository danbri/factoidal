module XForms.Bind

// XForms model-layer bind + recalculation engine (Stage 2 of the
// browserless-XForms program plan,
// docs/designissues/2026-07-05-xforms-model-program-plan.md).
//
// Scope, per that plan's owner directive: the "spreadsheet half" of
// XForms only — an XML instance + a bind sheet carrying Model Item
// Properties (MIPs) + a dependency graph over `calculate` expressions
// + a pure recalculation function. No UI controls, no XML Events, no
// submission. This is deliberately NOT conformant XForms; it is the
// reactive computation core.
//
// Everything here is Tot (no --lax, no admit, no runtime loop guard):
//   * expression evaluation reuses XPath.Eval (Stage 1);
//   * the instance is a Parser.XML `xml_node` (no bespoke parser);
//   * the `type` MIP dispatches to XSD.Datatypes lexical checks;
//   * termination of the topological recalculation pass is what
//     REJECTS a cyclic `calculate` graph — see `topo_pass` below.
//
// F* comment discipline (CLAUDE.md syntax trap): only `//` line
// comments in this file, never nesting block comments, so a stray
// close cannot swallow the module.

open FStar.String
open FStar.List.Tot
open Parser.XML
open Parser.XPath
open XPath.Eval
open XSD.Datatypes

// ================================================================
// Model Item Property (MIP) `type` — XForms 1.1 §6.2.1
// ================================================================
//
// The `type` MIP names an XSD datatype; validation dispatches to the
// same XSD.Datatypes lexical predicates SHACL/CSVW already use, rather
// than a second type-checking layer. An unrecognised QName becomes
// `MipTypeUnsupported`, which validates as INVALID (an explicit
// "we do not know", not a silent pass) per the project's soundness
// discipline.

type xf_mip_type =
  | MipTypeNone
  | MipTypeString
  | MipTypeBoolean
  | MipTypeInteger
  | MipTypeDecimal
  | MipTypeFloat
  | MipTypeDouble
  | MipTypeUnsupported

let mip_type_of_qname (q:string) : xf_mip_type =
  if q = "" then MipTypeNone
  else if q = "xsd:string"  || q = "xs:string"  then MipTypeString
  else if q = "xsd:boolean" || q = "xs:boolean" then MipTypeBoolean
  else if q = "xsd:integer" || q = "xs:integer" then MipTypeInteger
  else if q = "xsd:decimal" || q = "xs:decimal" then MipTypeDecimal
  else if q = "xsd:float"   || q = "xs:float"   then MipTypeFloat
  else if q = "xsd:double"  || q = "xs:double"  then MipTypeDouble
  else MipTypeUnsupported

// Lexical well-formedness for the declared `type`. Boolean's lexical
// space is XSD's four tokens (§3.2.2); the numeric families reuse
// XSD.Datatypes directly.
let type_wellformed (t:xf_mip_type) (lex:string) : bool =
  match t with
  | MipTypeNone | MipTypeString -> true
  | MipTypeBoolean -> lex = "true" || lex = "false" || lex = "0" || lex = "1"
  | MipTypeInteger -> is_integer_lexical lex
  | MipTypeDecimal -> is_decimal_lexical lex
  | MipTypeFloat | MipTypeDouble -> is_float_lexical lex
  | MipTypeUnsupported -> false

// ================================================================
// Bind model — XForms 1.1 §7.3
// ================================================================
//
// A bind targets a single named leaf element of a FLAT instance root
// (the shape a headless engine receives, plan Open-decision 1; nested
// binds and repeats are out of scope, plan Open-decision 2). Each MIP
// is an optional XPath expression string, evaluated (Stage 1) with the
// bound leaf as context node so that `.` denotes the node's own value
// and sibling references use `../name` or `/root/name`.

noeq type xf_bind = {
  bind_id         : string;
  bind_target     : string;          // leaf element name (the `nodeset`)
  bind_calculate  : option string;   // §7.6  calculate MIP  (XPath -> value)
  bind_constraint : option string;   // §7.7  constraint MIP (XPath -> boolean)
  bind_relevant   : option string;   // §7.4  relevant MIP   (XPath -> boolean)
  bind_required   : option string;   // §7.5  required MIP   (XPath -> boolean)
  bind_readonly   : option string;   // §7.8  readonly MIP   (XPath -> boolean)
  bind_type       : xf_mip_type;     // §6.2.1 type MIP
}

// ================================================================
// Instance leaf access over Parser.XML's xml_node
// ================================================================

// Locate the first child element of `root` whose tag = `name`.
let find_leaf (root:xml_node) (name:string) : option xml_node =
  child_element name root

// Current string value of a named leaf (XPath string-value = descendant
// text concatenation, Parser.XML.text_content). Absent leaf -> "".
let get_leaf_text (root:xml_node) (name:string) : string =
  match find_leaf root name with
  | Some n -> text_content n
  | None -> ""

// Replace the FIRST child element named `name` with one carrying a
// single text child = `v`. Pure: returns a new tree, mutates nothing.
let rec set_child_text (children:list xml_node) (name:string) (v:string)
  : Tot (list xml_node) (decreases children) =
  match children with
  | [] -> []
  | h :: rest ->
    (match h with
     | XElement t a _ ->
       if t = name then XElement t a [XText v] :: rest
       else h :: set_child_text rest name v
     | _ -> h :: set_child_text rest name v)

let set_leaf_text (root:xml_node) (name:string) (v:string) : xml_node =
  match root with
  | XElement tag attrs children -> XElement tag attrs (set_child_text children name v)
  | other -> other

// ================================================================
// Evaluate a MIP expression with the bound leaf as context node
// ================================================================
//
// `.` refers to the leaf, `../sib`/`/root/sib` reach siblings. Reuses
// XPath.Eval.eval_xpath_from_item with the single-element ancestor
// chain [root]. Returns None when the leaf is absent or the expression
// fails to parse.
let eval_mip_value (root:xml_node) (target:string) (expr:string) : option xp_value =
  match find_leaf root target with
  | None -> None
  | Some leaf -> eval_xpath_from_item [root] leaf [] expr

// ================================================================
// Dependency extraction — XForms 1.1 §7.6.1 recalculation order
// ================================================================
//
// Bind B depends on bind B' when B's `calculate` expression READS the
// node B' computes, i.e. B'.bind_target occurs as a name test inside
// B's calculate AST. Names are collected structurally from the parsed
// XPath expression (Parser.XPath's xp_expr / xp_step), not by string
// scanning, so a substring of some other token cannot forge an edge.

let rec names_expr (e:xp_expr) : Tot (list string) (decreases e) =
  match e with
  | XE_Path _ steps -> names_steps steps
  | XE_FilterPath p preds steps ->
    names_expr p @ names_exprs preds @ names_steps steps
  | XE_Union a b | XE_Or a b | XE_And a b -> names_expr a @ names_expr b
  | XE_Compare _ a b | XE_Arith _ a b -> names_expr a @ names_expr b
  | XE_Neg a -> names_expr a
  | XE_FunCall _ args -> names_exprs args
  | XE_Number _ _ | XE_Literal _ | XE_VarRef _ -> []

and names_exprs (es:list xp_expr) : Tot (list string) (decreases es) =
  match es with
  | [] -> []
  | h :: t -> names_expr h @ names_exprs t

and names_steps (ss:list xp_step) : Tot (list string) (decreases ss) =
  match ss with
  | [] -> []
  | s :: t ->
    let here = (match s.step_test with NT_Name n -> [n] | _ -> []) in
    here @ names_exprs s.step_preds @ names_steps t

let all_targets (bs:list xf_bind) : list string =
  map (fun (b:xf_bind) -> b.bind_target) bs

// The instance-node names a bind's calculate reads.
let calc_names (b:xf_bind) : list string =
  match b.bind_calculate with
  | None -> []
  | Some c -> (match parse_xpath c with
               | None -> []
               | Some e -> names_expr e)

// Predecessor targets = referenced names that are themselves some
// bind's target (references to raw source leaves impose no ordering
// constraint; a reference to a bind's own target is a self-cycle and
// is intentionally kept, so it is rejected by topo_pass).
let preds_of (bs:list xf_bind) (b:xf_bind) : list string =
  let tgts = all_targets bs in
  filter (fun (n:string) -> mem n tgts) (calc_names b)

noeq type graph_node = { gn_bind : xf_bind; gn_preds : list string }

let build_graph (bs:list xf_bind) : list graph_node =
  map (fun (b:xf_bind) -> { gn_bind = b; gn_preds = preds_of bs b }) bs

let node_ready (emitted:list string) (g:graph_node) : bool =
  for_all (fun (p:string) -> mem p emitted) g.gn_preds

// Lengths of the two complementary filters sum to the source length.
// Two-line induction; gives topo_pass its `decreases` proof.
let rec filter_complement_length (#a:Type) (p:a -> bool) (l:list a)
  : Lemma (ensures (length (filter p l) + length (filter (fun x -> not (p x)) l) = length l))
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: t -> filter_complement_length p t

// ================================================================
// Topological recalculation order — CYCLE REJECTION AS A TERMINATION
// PROOF (the interesting part).
// ================================================================
//
// Kahn's algorithm as a fold over the not-yet-emitted set. Each pass
// emits every node whose predecessors are all already emitted (a DAG
// "layer"), then recurses on the strict remainder. The measure is
// `length remaining`, and the ONLY recursive call is on `notready`,
// which the complement-length lemma proves strictly shorter WHENEVER
// `ready` is non-empty. A cyclic `calculate` graph has NO in-degree-0
// node among its remaining members, so `ready` is empty, and the
// function returns `None` WITHOUT recursing. In other words: the proof
// obligation that this function terminates is exactly what forces a
// cycle onto the `None` branch instead of looping. Cycle detection is
// not a runtime counter — it is the shape of the termination argument
// (XForms 1.1 §7.6.1: a `calculate` cycle is a document error).
let rec topo_pass (remaining:list graph_node) (emitted:list string)
  : Tot (option (list xf_bind)) (decreases (length remaining)) =
  match remaining with
  | [] -> Some []
  | _ ->
    let rdy : graph_node -> bool = node_ready emitted in
    let ready = filter rdy remaining in
    let notready = filter (fun (g:graph_node) -> not (rdy g)) remaining in
    (match ready with
     | [] -> None   // no progress possible => cyclic calculate graph => document error
     | _ :: _ ->
       filter_complement_length rdy remaining;   // length notready < length remaining
       let new_emitted = emitted @ map (fun (g:graph_node) -> g.gn_bind.bind_target) ready in
       (match topo_pass notready new_emitted with
        | None -> None
        | Some rest -> Some (map (fun (g:graph_node) -> g.gn_bind) ready @ rest)))

// Some sorted-bind-list if the calculate dependency graph is acyclic,
// None if it contains a cycle (document error).
let topo_sort (bs:list xf_bind) : option (list xf_bind) =
  topo_pass (build_graph bs) []

// ================================================================
// The recalculation fold — XForms 1.1 §7.6
// ================================================================
//
// Apply each bind's `calculate` in dependency order, threading the
// updated instance so a later calculate observes earlier results. A
// calculate that fails to parse is a document error (None). Pure: the
// only "mutation" is the returned new instance tree.
let rec apply_calcs (sorted:list xf_bind) (xdoc:xml_node)
  : Tot (option xml_node) (decreases sorted) =
  match sorted with
  | [] -> Some xdoc
  | b :: rest ->
    (match b.bind_calculate with
     | None -> apply_calcs rest xdoc
     | Some c ->
       (match eval_mip_value xdoc b.bind_target c with
        | None -> None
        | Some v -> apply_calcs rest (set_leaf_text xdoc b.bind_target (to_string_val v))))

// ================================================================
// Validity report — XForms 1.1 §7.4/§7.5/§7.7 + §6.2.1
// ================================================================

noeq type node_validity = {
  nv_target     : string;
  nv_value      : string;
  nv_type_valid : bool;   // §6.2.1 lexical value matches declared type
  nv_constraint : bool;   // §7.7   constraint satisfied (or none)
  nv_relevant   : bool;   // §7.4   node relevant (default true)
  nv_required   : bool;   // §7.5   node required (default false)
  nv_readonly   : bool;   // §7.8   node readonly (default false)
  nv_valid      : bool;   // overall validity, see below
}

// Evaluate a boolean MIP (constraint/relevant/required/readonly). An
// absent MIP takes `dflt`; an unparseable one is treated as `false`.
let eval_bool_mip (root:xml_node) (target:string) (eo:option string) (dflt:bool) : bool =
  match eo with
  | None -> dflt
  | Some e -> (match eval_mip_value root target e with
               | None -> false
               | Some v -> to_bool_val v)

let build_validity (root:xml_node) (b:xf_bind) : node_validity =
  let value = get_leaf_text root b.bind_target in
  let tv   = type_wellformed b.bind_type value in
  let cons = eval_bool_mip root b.bind_target b.bind_constraint true in
  let rel  = eval_bool_mip root b.bind_target b.bind_relevant  true in
  let req  = eval_bool_mip root b.bind_target b.bind_required  false in
  let ro   = eval_bool_mip root b.bind_target b.bind_readonly  false in
  let required_ok = not req || String.length value > 0 in
  // §7.4: a non-relevant node is exempt from constraint/required/type
  // validity — it simply does not contribute invalidity.
  let valid = not rel || (tv && cons && required_ok) in
  { nv_target = b.bind_target; nv_value = value;
    nv_type_valid = tv; nv_constraint = cons; nv_relevant = rel;
    nv_required = req; nv_readonly = ro; nv_valid = valid }

// ================================================================
// Public entry points — the pure snapshot-in / snapshot-out API
// ================================================================

// Full recalculation: sort by calculate dependencies, run the
// calculate fold, then build the per-bind validity report against the
// recomputed instance. None iff the model is a document error (a
// calculate cycle, or a calculate that fails to parse).
let recalculate (binds:list xf_bind) (xdoc:xml_node)
  : option (xml_node & list node_validity) =
  match topo_sort binds with
  | None -> None
  | Some sorted ->
    (match apply_calcs sorted xdoc with
     | None -> None
     | Some inst2 -> Some (inst2, map (build_validity inst2) binds))

// A single edit, per the plan's `old_state -> edit -> (new_state &
// validity_report)` signature: write the edited leaf, then recalc.
let apply_edit (binds:list xf_bind) (xdoc:xml_node)
               (edit_target:string) (edit_value:string)
  : option (xml_node & list node_validity) =
  recalculate binds (set_leaf_text xdoc edit_target edit_value)

// ================================================================
// Optional: decode a standalone <xf:bind .../> tree (plan Open-dec 1)
// ================================================================
//
// Reads a flat list of bind elements (any tag; nodeset attribute is
// the leaf name). Provided so Stage 3's npm surface can hand the
// engine an XML bindings sheet parsed by the same Parser.XML. Nested
// binds are not resolved (Open-decision 2).

let mk_bind_from (attrs:list xml_attribute) (tgt:string) : xf_bind =
  { bind_id        = (match find_attr "id" attrs with Some i -> i | None -> "");
    bind_target    = tgt;
    bind_calculate = find_attr "calculate"  attrs;
    bind_constraint= find_attr "constraint" attrs;
    bind_relevant  = find_attr "relevant"   attrs;
    bind_required  = find_attr "required"   attrs;
    bind_readonly  = find_attr "readonly"   attrs;
    bind_type      = (match find_attr "type" attrs with
                      | Some q -> mip_type_of_qname q
                      | None -> MipTypeNone); }

let decode_bind (el:xml_node) : option xf_bind =
  let attrs = element_attrs el in
  match find_attr "nodeset" attrs with
  | Some tgt -> Some (mk_bind_from attrs tgt)
  | None -> (match find_attr "ref" attrs with
             | Some tgt -> Some (mk_bind_from attrs tgt)
             | None -> None)

// Decode every child element of a <xf:bind>-list container into binds
// (skipping any that name no target).
let rec decode_binds_list (nodes:list xml_node) : Tot (list xf_bind) (decreases nodes) =
  match nodes with
  | [] -> []
  | h :: t ->
    (match h with
     | XElement _ _ _ -> (match decode_bind h with
                          | Some b -> b :: decode_binds_list t
                          | None -> decode_binds_list t)
     | _ -> decode_binds_list t)

let decode_binds (container:xml_node) : list xf_bind =
  decode_binds_list (element_children container)
