module Schematron.Validate

open FStar.String
open FStar.List.Tot
open Parser.XML
open Parser.XPath
open XPath.Eval
open XSLT.Transform

// ISO/IEC 19757-3 (Schematron) validator, XSLT-1 / XPath-1 query
// binding, slice 1. The Schematron schema (a .sch file) is itself XML,
// so BOTH the schema and the instance document are parsed by the
// existing verified Parser.XML.parse_xml_document (Iron Rule #1/#4).
// Rule contexts and assert/report tests are XPath 1.0, evaluated by the
// existing verified XPath.Eval engine — this module adds NO new XPath
// logic. Rule-context PATTERN matching reuses XSLT.Transform's
// `any_alt_matches` (the XSLT template-match predicate), which is
// exactly the ISO Schematron "does this node match the rule context"
// question and, crucially, tests each candidate node against its own
// ancestor chain (true node identity) rather than by set membership.
//
// Firing semantics (ISO/IEC 19757-3 section 6.5): within a single
// pattern a node is processed by THE FIRST rule (document order) whose
// context selects it; later rules in the same pattern do NOT fire on
// that node. Patterns are independent of one another. For each matched
// context node, each child assert/report is evaluated as an XPath
// boolean with that node as the context node:
//   * an <assert> FAILS (is reported) when its @test is FALSE;
//   * a  <report> FIRES        when its @test is TRUE.
//
// Soundness discipline: when the underlying XPath engine cannot even
// PARSE a @test (e.g. the sibling/following/preceding axes that
// Parser.XPath defers to Stage 1.5, or any construct it rejects), the
// assertion is recorded as INDETERMINATE — never silently passed or
// failed.
//
// Known limitation (documented, not silent): rule-context first-match
// de-duplication is exact for distinct nodes. Two structurally-
// identical sibling elements selected by a POSITIONAL context predicate
// (e.g. a slash b index-1) cannot be told apart by the pattern matcher,
// an inherited property of the XSLT.Transform predicate matcher. The
// spec-cited corpus avoids that pathological shape.

(* ================================================================ *)
(* Internal schema AST (extracted from the parsed .sch XML tree).    *)
(* ================================================================ *)

type sch_assertion = {
  sa_is_assert : bool;   // true = assert element, false = report element
  sa_test      : string; // @test XPath (boolean)
  sa_message   : string; // human-readable message (element text)
}

type sch_let = { sl_name : string; sl_value : string }

noeq type sch_rule = {
  sr_context : string;             // @context XPath pattern
  sr_lets    : list sch_let;       // rule-local let bindings
  sr_asserts : list sch_assertion; // asserts + reports in document order
}

noeq type sch_pattern = { sp_id : string; sp_rules : list sch_rule }

noeq type sch_schema = {
  ss_ns       : list (string & string); // ns prefix uri (best-effort)
  ss_lets     : list sch_let;            // top-level let bindings
  ss_patterns : list sch_pattern;
}

(* ================================================================ *)
(* Findings (the validation report).                                 *)
(* ================================================================ *)

type finding =
  | Assert_fail   : ctx:string -> test:string -> msg:string -> path:string -> finding
  | Report_hit    : ctx:string -> test:string -> msg:string -> path:string -> finding
  | Indeterminate : ctx:string -> test:string -> msg:string -> path:string -> reason:string -> finding

// Stable string API for the (unverified, I/O-only) bin/ runner.
let finding_kind (f:finding) : string =
  match f with
  | Assert_fail _ _ _ _ -> "assert-fail"
  | Report_hit _ _ _ _ -> "report-hit"
  | Indeterminate _ _ _ _ _ -> "indeterminate"

let finding_context (f:finding) : string =
  match f with
  | Assert_fail c _ _ _ -> c
  | Report_hit c _ _ _ -> c
  | Indeterminate c _ _ _ _ -> c

let finding_test (f:finding) : string =
  match f with
  | Assert_fail _ t _ _ -> t
  | Report_hit _ t _ _ -> t
  | Indeterminate _ t _ _ _ -> t

let finding_message (f:finding) : string =
  match f with
  | Assert_fail _ _ m _ -> m
  | Report_hit _ _ m _ -> m
  | Indeterminate _ _ m _ _ -> m

let finding_path (f:finding) : string =
  match f with
  | Assert_fail _ _ _ p -> p
  | Report_hit _ _ _ p -> p
  | Indeterminate _ _ _ p _ -> p

(* ================================================================ *)
(* Small generic helpers.                                            *)
(* ================================================================ *)

let rec flatmap (#a:Type) (#b:Type) (f:a -> list b) (xs:list a)
  : Tot (list b) (decreases xs) =
  match xs with
  | [] -> []
  | x :: r -> f x @ flatmap f r

let attr_or_empty (name:string) (n:xml_node) : string =
  match find_attr name (element_attrs n) with Some v -> v | None -> ""

// local-name of an element's tag (namespace prefix dropped). Schematron
// elements are matched by local-name so sch:schema / schema / iso:schema
// all work; XPath.Eval itself remains namespace-naive (documented), so
// instance-document prefixes are matched literally.
let el_local (n:xml_node) : string =
  match element_tag n with Some t -> local_name t | None -> ""

let el_is (lname:string) (n:xml_node) : bool = el_local n = lname

(* ================================================================ *)
(* Schema extraction (structural recursion over the parsed tree).    *)
(* ================================================================ *)

// A rule element's children: assert, report (assertions, in document
// order) and let (rule-local variables).
let assertion_of (n:xml_node) : option sch_assertion =
  if el_is "assert" n then
    Some { sa_is_assert = true; sa_test = attr_or_empty "test" n; sa_message = text_content n }
  else if el_is "report" n then
    Some { sa_is_assert = false; sa_test = attr_or_empty "test" n; sa_message = text_content n }
  else None

let rec collect_assertions (nodes:list xml_node) : Tot (list sch_assertion) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    (match assertion_of hd with
     | Some a -> a :: collect_assertions tl
     | None -> collect_assertions tl)

let let_of (n:xml_node) : option sch_let =
  if el_is "let" n then Some { sl_name = attr_or_empty "name" n; sl_value = attr_or_empty "value" n }
  else None

let rec collect_lets (nodes:list xml_node) : Tot (list sch_let) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    (match let_of hd with
     | Some l -> l :: collect_lets tl
     | None -> collect_lets tl)

let rule_of (n:xml_node) : sch_rule =
  let kids = element_children n in
  { sr_context = attr_or_empty "context" n;
    sr_lets = collect_lets kids;
    sr_asserts = collect_assertions kids }

let rec collect_rules (nodes:list xml_node) : Tot (list sch_rule) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    if el_is "rule" hd then rule_of hd :: collect_rules tl
    else collect_rules tl

let pattern_of (n:xml_node) : sch_pattern =
  { sp_id = attr_or_empty "id" n; sp_rules = collect_rules (element_children n) }

let rec collect_patterns (nodes:list xml_node) : Tot (list sch_pattern) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    if el_is "pattern" hd then pattern_of hd :: collect_patterns tl
    else collect_patterns tl

let rec collect_ns (nodes:list xml_node) : Tot (list (string & string)) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    if el_is "ns" hd then (attr_or_empty "prefix" hd, attr_or_empty "uri" hd) :: collect_ns tl
    else collect_ns tl

let extract_schema (schema_root:xml_node) : sch_schema =
  // Accept the root whether or not its local-name is literally "schema"
  // (some corpora wrap it), but the standard is a schema element.
  let kids = element_children schema_root in
  { ss_ns = collect_ns kids;
    ss_lets = collect_lets kids;
    ss_patterns = collect_patterns kids }

(* ================================================================ *)
(* Node enumeration over the instance (document order).              *)
(* ================================================================ *)

// Every element also contributes its attribute nodes (so a rule
// context of the form @name can select them). Text/comment context
// items are included as produced by descendant_items. Attributes are
// listed right after their owning element.
let node_with_attrs (it:xctx_item) : list xctx_item =
  match it with
  | CI_Elem p anc n -> it :: attribute_items p anc n
  | _ -> [it]

let all_doc_items (root:xml_node) : list xctx_item =
  flatmap node_with_attrs (CI_Elem [] [] root :: descendant_items [] [] root)

(* ================================================================ *)
(* XPath call-outs (all logic delegated to XPath.Eval).              *)
(* ================================================================ *)

// Evaluate expr with `it` as the context node. None means the engine
// could not PARSE the expression (=> INDETERMINATE, never a silent
// pass/fail). Mirrors XSLT.Transform.eval_val but preserves the
// parse-failure signal instead of substituting the empty string.
let sch_eval (it:xctx_item) (vars:list (string & xp_value)) (expr:string) : option xp_value =
  match parse_xpath expr with
  | None -> None
  | Some e ->
    let fuel = initial_eval_fuel e (xml_node_count (root_of_item it)) in
    let env = { env_item = it; env_pos = 1; env_size = 1; env_vars = vars } in
    Some (eval_expr fuel env e)

// Does node `it` match rule context pattern ctx? Delegated to the
// XSLT template-match predicate (union-aware, ancestor-chain based).
let context_matches (ctx:string) (vars:list (string & xp_value)) (it:xctx_item) : bool =
  if trim_str ctx = "" then false
  else any_alt_matches vars (split_on_char '|' ctx) (D_Item it)

(* ================================================================ *)
(* Firing-node path (for the report; not used in pass/fail compare). *)
(* ================================================================ *)

let item_self_label (it:xctx_item) : string =
  match it with
  | CI_Elem _ _ n -> (match element_tag n with Some t -> t | None -> "")
  | CI_Attr _ _ _ a -> strcat "@" a.attr_name
  | CI_Text _ _ _ _ -> "text()"
  | CI_Comment _ _ _ _ -> "comment()"
  | CI_PI _ _ _ tg _ -> strcat "processing-instruction()::" tg

let item_path (it:xctx_item) : string =
  let anc = List.Tot.rev (ancestor_tags_of it) in  // ancestor_tags_of: nearest-first; rev => root-first
  strcat "/" (String.concat "/" (anc @ [item_self_label it]))

(* ================================================================ *)
(* let evaluation (best-effort; later lets may reference earlier).    *)
(* ================================================================ *)

let rec eval_lets (it:xctx_item) (base:list (string & xp_value)) (lets:list sch_let)
  : Tot (list (string & xp_value)) (decreases lets) =
  match lets with
  | [] -> base
  | l :: rest ->
    let v = (match sch_eval it base l.sl_value with Some x -> x | None -> XV_Str "") in
    eval_lets it ((l.sl_name, v) :: base) rest

(* ================================================================ *)
(* Assertion evaluation + per-node / per-pattern firing.             *)
(* ================================================================ *)

let eval_assertion (ctx:string) (it:xctx_item) (vars:list (string & xp_value)) (a:sch_assertion)
  : list finding =
  match sch_eval it vars a.sa_test with
  | None ->
    [ Indeterminate ctx a.sa_test a.sa_message (item_path it)
        "test did not parse in XPath.Eval (unsupported XPath construct such as a deferred axis)" ]
  | Some v ->
    let b = to_bool_val v in
    if a.sa_is_assert then
      (if b then [] else [ Assert_fail ctx a.sa_test a.sa_message (item_path it) ])
    else
      (if b then [ Report_hit ctx a.sa_test a.sa_message (item_path it) ] else [])

// First rule (document order) in this pattern whose context selects it.
let rec first_matching_rule (rules:list sch_rule) (gvars:list (string & xp_value)) (it:xctx_item)
  : Tot (option sch_rule) (decreases rules) =
  match rules with
  | [] -> None
  | r :: rest ->
    if context_matches r.sr_context gvars it then Some r
    else first_matching_rule rest gvars it

let validate_item_in_pattern (rules:list sch_rule) (gvars:list (string & xp_value)) (it:xctx_item)
  : list finding =
  match first_matching_rule rules gvars it with
  | None -> []
  | Some r ->
    let rvars = eval_lets it gvars r.sr_lets in
    flatmap (fun a -> eval_assertion r.sr_context it rvars a) r.sr_asserts

let validate_pattern (pat:sch_pattern) (items:list xctx_item) (gvars:list (string & xp_value))
  : list finding =
  flatmap (fun it -> validate_item_in_pattern pat.sp_rules gvars it) items

(* ================================================================ *)
(* Entry point.                                                      *)
(* ================================================================ *)

// Validate an already-parsed instance against an already-parsed schema.
// Returns the full list of findings (assert-failures, report-hits, and
// indeterminates) across all patterns, in pattern-then-document order.
let validate (schema_root:xml_node) (instance_root:xml_node) : list finding =
  let sch = extract_schema schema_root in
  let items = all_doc_items instance_root in
  let gvars = eval_lets (CI_Elem [] [] instance_root) [] sch.ss_lets in
  flatmap (fun pat -> validate_pattern pat items gvars) sch.ss_patterns

// A document is "valid" for this slice iff no assert failed and no
// report fired (indeterminates are neither pass nor fail — they are
// surfaced separately by the caller).
let has_hard_finding (f:finding) : bool =
  match f with
  | Assert_fail _ _ _ _ -> true
  | Report_hit _ _ _ _ -> true
  | Indeterminate _ _ _ _ _ -> false

let rec any_hard (fs:list finding) : Tot bool (decreases fs) =
  match fs with
  | [] -> false
  | f :: rest -> if has_hard_finding f then true else any_hard rest

let is_valid (schema_root:xml_node) (instance_root:xml_node) : bool =
  not (any_hard (validate schema_root instance_root))
