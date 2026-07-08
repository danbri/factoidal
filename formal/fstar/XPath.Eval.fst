module XPath.Eval

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.XML
open Parser.XPath

// XPath 1.0 evaluator over Parser.XML's already-parsed xml_node tree.
// Pairs with Parser.XPath.fst's AST (parse_xpath). See
// docs/designissues/2026-07-05-xforms-model-program-plan.md for the
// Stage 1 scope, the axis-coverage table, and the disclosed IEEE-754
// divergences summarized again just above `xpath_number` below.
//
// TWO RECURSION STYLES, deliberately different, mirroring how
// Parser.XML.fst itself splits "parsing" (fuel-based) from "walking
// an already-parsed tree" (plain structural recursion):
//
// - Axis builders (`descendant_items`/`ancestor_items`/etc.) walk the
//   xml_node tree ALONE — no xp_expr involved — and use plain
//   structural `decreases node`/`decreases nodes`/`decreases
//   ancestors`, the same idiom as Parser.XML's `text_content`/
//   `text_content_list`.
// - The expression evaluator (`eval_expr` and its step/predicate
//   helpers) has a genuine mutual-recursion cycle back to itself:
//   evaluating a location step's predicate can require evaluating an
//   arbitrary sub-expression (including a nested location path), and
//   that sub-expression is evaluated once per candidate node in a
//   list that is NOT a subterm of the expression AST — so there is no
//   single structurally-decreasing measure across "iterate this
//   runtime node list" and "recurse into this AST". This family uses
//   an explicit `fuel:nat`, decremented by exactly 1 on every call
//   (including "same expression, next item in the list"), sized from
//   BOTH the expression's own size and the document's node count (see
//   `initial_eval_fuel` below) — never a bare constant.

(* ================================================================ *)
(* Numbers                                                           *)
(*                                                                   *)
(* xpath_number mirrors, without importing, SPARQL11.Algebra's       *)
(* promoted-type numeric representation (ER_Dbl/ER_Dec as scaled     *)
(* decimals, `parse_to_scaled`/`format_as_double`, lines ~1281-1400   *)
(* of SPARQL11.Algebra.fst) rather than a bit-level IEEE 754 double.  *)
(* Two disclosed divergences from strict IEEE 754 follow (full        *)
(* discussion in the program plan's "Number semantics" section):     *)
(* no signed zero (mantissa is a plain `int`, `-0` normalizes to      *)
(* `0`), and NaN/Infinity are tagged sentinels with EXACT rational    *)
(* arithmetic on finite values rather than binary floating-point      *)
(* rounding (materially more precise on values representable exactly *)
(* in decimal, at the cost of not bit-matching IEEE 754 rounding      *)
(* artifacts on pathological inputs).                                *)
(* ================================================================ *)

type xpath_number =
  | XN_NaN
  | XN_PosInf
  | XN_NegInf
  // value = mantissa / 10^scale
  | XN_Finite : mantissa:int -> scale:nat -> xpath_number

let rec xn_pow10 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (xn_pow10 (n - 1))

let xn_abs (n:int) : int = if n >= 0 then n else 0 - n

// Align two (mantissa,scale) pairs to a common scale, returning the
// aligned mantissas.
let xn_align (v1:int) (s1:nat) (v2:int) (s2:nat) : (int & int & nat) =
  if s1 >= s2 then (v1, op_Multiply v2 (xn_pow10 (s1 - s2)), s1)
  else (op_Multiply v1 (xn_pow10 (s2 - s1)), v2, s2)

let xn_neg (n:xpath_number) : xpath_number =
  match n with
  | XN_NaN -> XN_NaN
  | XN_PosInf -> XN_NegInf
  | XN_NegInf -> XN_PosInf
  | XN_Finite v s -> XN_Finite (0 - v) s

let xn_compare (a b:xpath_number) : option int =
  match a, b with
  | XN_NaN, _ | _, XN_NaN -> None
  | XN_PosInf, XN_PosInf -> Some 0
  | XN_NegInf, XN_NegInf -> Some 0
  | XN_PosInf, XN_NegInf -> Some 1
  | XN_NegInf, XN_PosInf -> Some (-1)
  | XN_PosInf, XN_Finite _ _ -> Some 1
  | XN_Finite _ _, XN_PosInf -> Some (-1)
  | XN_NegInf, XN_Finite _ _ -> Some (-1)
  | XN_Finite _ _, XN_NegInf -> Some 1
  | XN_Finite v1 s1, XN_Finite v2 s2 ->
    let (n1, n2, _) = xn_align v1 s1 v2 s2 in
    Some (if n1 < n2 then -1 else if n1 > n2 then 1 else 0)

let xn_arith (op:xp_arith_op) (a b:xpath_number) : xpath_number =
  match a, b with
  | XN_NaN, _ | _, XN_NaN -> XN_NaN
  | XN_PosInf, XN_PosInf ->
    (match op with
     | Ar_Add -> XN_PosInf | Ar_Sub -> XN_NaN | Ar_Mul -> XN_PosInf
     | Ar_Div -> XN_NaN | Ar_Mod -> XN_NaN)
  | XN_NegInf, XN_NegInf ->
    (match op with
     | Ar_Add -> XN_NegInf | Ar_Sub -> XN_NaN | Ar_Mul -> XN_PosInf
     | Ar_Div -> XN_NaN | Ar_Mod -> XN_NaN)
  | XN_PosInf, XN_NegInf ->
    (match op with
     | Ar_Add -> XN_NaN | Ar_Sub -> XN_PosInf | Ar_Mul -> XN_NegInf
     | Ar_Div -> XN_NaN | Ar_Mod -> XN_NaN)
  | XN_NegInf, XN_PosInf ->
    (match op with
     | Ar_Add -> XN_NaN | Ar_Sub -> XN_NegInf | Ar_Mul -> XN_NegInf
     | Ar_Div -> XN_NaN | Ar_Mod -> XN_NaN)
  | XN_PosInf, XN_Finite v _ ->
    (match op with
     | Ar_Add -> XN_PosInf | Ar_Sub -> XN_PosInf
     | Ar_Mul -> if v = 0 then XN_NaN else if v > 0 then XN_PosInf else XN_NegInf
     | Ar_Div -> if v = 0 then XN_NaN else if v > 0 then XN_PosInf else XN_NegInf
     | Ar_Mod -> XN_NaN)
  | XN_NegInf, XN_Finite v _ ->
    (match op with
     | Ar_Add -> XN_NegInf | Ar_Sub -> XN_NegInf
     | Ar_Mul -> if v = 0 then XN_NaN else if v > 0 then XN_NegInf else XN_PosInf
     | Ar_Div -> if v = 0 then XN_NaN else if v > 0 then XN_NegInf else XN_PosInf
     | Ar_Mod -> XN_NaN)
  | XN_Finite v _, XN_PosInf ->
    (match op with
     | Ar_Add -> XN_PosInf | Ar_Sub -> XN_NegInf
     | Ar_Mul -> if v = 0 then XN_NaN else if v > 0 then XN_PosInf else XN_NegInf
     | Ar_Div -> XN_Finite 0 0 | Ar_Mod -> XN_NaN)
  | XN_Finite v _, XN_NegInf ->
    (match op with
     | Ar_Add -> XN_NegInf | Ar_Sub -> XN_PosInf
     | Ar_Mul -> if v = 0 then XN_NaN else if v > 0 then XN_NegInf else XN_PosInf
     | Ar_Div -> XN_Finite 0 0 | Ar_Mod -> XN_NaN)
  | XN_Finite v1 s1, XN_Finite v2 s2 ->
    (match op with
     | Ar_Add -> let (n1, n2, s) = xn_align v1 s1 v2 s2 in XN_Finite (n1 + n2) s
     | Ar_Sub -> let (n1, n2, s) = xn_align v1 s1 v2 s2 in XN_Finite (n1 - n2) s
     | Ar_Mul -> XN_Finite (op_Multiply v1 v2) (s1 + s2)
     | Ar_Div ->
       if v2 = 0 then (if v1 = 0 then XN_NaN else if v1 > 0 then XN_PosInf else XN_NegInf)
       else
         // Fixed-precision decimal division (10^12 extra digits),
         // same shape as SPARQL11.Algebra's int_div_decimal but
         // returning a scaled pair instead of a formatted string.
         // rv/10^rs = v1/10^s1 / (v2/10^s2); choose rs = s1+extra so
         // rv = v1 * 10^(s2+extra) / v2 (all-nat exponents, no
         // subtraction that could go negative).
         let extra = 12 in
         let scaled = op_Multiply v1 (xn_pow10 (s2 + extra)) in
         XN_Finite (scaled / v2) (s1 + extra)
     | Ar_Mod ->
       if v2 = 0 then XN_NaN
       else
         let (n1, n2, s) = xn_align v1 s1 v2 s2 in
         if n2 = 0 then XN_NaN else XN_Finite (n1 - op_Multiply (n1 / n2) n2) s)

// Number ('.' Digits?)? production values arrive pre-scaled from the
// parser (XE_Number). String -> number (the `number()` function and
// numeric §3.4 coercions) follows the same grammar: optional
// whitespace, optional '-', Digits ('.' Digits?)? | '.' Digits; no
// E-notation (disclosed in the plan doc's Number-semantics section —
// this is what the XPath 1.0 grammar's own `Number` production
// defines, not a limitation this engine adds).
let rec xn_list_drop_while (#a:Type) (f: a -> bool) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> if f x then xn_list_drop_while f xs else x :: xs

let string_to_xn (s:string) : xpath_number =
  let len = String.length s in
  let cs = String.list_of_string s in
  let is_sp (c:FStar.Char.char) = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
  let trimmed = List.Tot.rev (xn_list_drop_while is_sp (List.Tot.rev (xn_list_drop_while is_sp cs))) in
  match trimmed with
  | [] -> XN_NaN
  | hd :: tl ->
    let (neg, digits) = if hd = '-' then (true, tl) else (false, trimmed) in
    let s' = String.string_of_list digits in
    match Parser.XPath.parse_number_lit s' 0 with
    | Some (v, scale, pos') ->
      if pos' = String.length s' && pos' > 0 then XN_Finite (if neg then 0 - v else v) scale
      else XN_NaN
    | None -> XN_NaN

// Integers print without a decimal point; non-integers in plain
// decimal (never E-notation — that's an xsd:double convention, not
// XPath 1.0's `Number` production). No signed zero (see banner).
let xn_to_string (n:xpath_number) : string =
  match n with
  | XN_NaN -> "NaN"
  | XN_PosInf -> "Infinity"
  | XN_NegInf -> "-Infinity"
  | XN_Finite v s ->
    if s = 0 then string_of_int v
    else
      let neg = v < 0 in
      let av = xn_abs v in
      let p = xn_pow10 s in
      let ip = if p = 0 then av else av / p in
      let fp = if p = 0 then 0 else av - op_Multiply ip p in
      if fp = 0 then (if neg && ip <> 0 then "-" else "") ^ string_of_int ip
      else
        let rec pad (n:string) (target:nat) : Tot string (decreases target) =
          if String.length n >= target then n else pad ("0" ^ n) (target - 1)
        in
        let frac_str = pad (string_of_int fp) s in
        // strip trailing zeros, keep at least one digit
        let rev_chars = List.Tot.rev (String.list_of_string frac_str) in
        let rev_stripped = xn_list_drop_while (fun c -> c = '0') rev_chars in
        let stripped_chars = if Nil? rev_stripped then ['0'] else List.Tot.rev rev_stripped in
        let stripped = String.string_of_list stripped_chars in
        (if neg then "-" else "") ^ string_of_int ip ^ "." ^ stripped

let xn_is_zero (n:xpath_number) : bool =
  match n with
  | XN_Finite 0 _ -> true
  | _ -> false

let xn_to_bool (n:xpath_number) : bool =
  match n with
  | XN_NaN -> false
  | XN_PosInf | XN_NegInf -> true
  | XN_Finite v _ -> v <> 0

// xn_pow10 s > 0 for every s (10^s >= 1), but xn_pow10's own return
// type carries no such refinement, so every division below is guarded
// by an explicit `if p = 0` branch — division only happens in the
// branch where F* can refine `p` to nonzero from that check, the same
// defensive pattern already used above in `xn_to_string`.

let xn_round (n:xpath_number) : xpath_number =
  match n with
  | XN_Finite v s ->
    if s = 0 then n
    else
      let p = xn_pow10 s in
      if p = 0 then n
      else
        // XPath round(): round to nearest, .5 rounds toward positive
        // infinity (spec §4.4), not round-half-to-even.
        let half = p / 2 in
        let q = if v >= 0 then (v + half) / p else 0 - ((0 - v + (p - half - 1)) / p) in
        XN_Finite q 0
  | _ -> n

let xn_floor (n:xpath_number) : xpath_number =
  match n with
  | XN_Finite v s ->
    if s = 0 then n
    else
      let p = xn_pow10 s in
      if p = 0 then n
      else
        let q = if v >= 0 then v / p else (0 - (((0 - v) + p - 1) / p)) in
        XN_Finite q 0
  | _ -> n

let xn_ceiling (n:xpath_number) : xpath_number =
  match n with
  | XN_Finite v s ->
    if s = 0 then n
    else
      let p = xn_pow10 s in
      if p = 0 then n
      else
        let q = if v >= 0 then (v + p - 1) / p else 0 - ((0 - v) / p) in
        XN_Finite q 0
  | _ -> n


(* ================================================================ *)
(* Node-set items                                                    *)
(*                                                                   *)
(* `ancestors` is always the PROPER ancestors of the item's own node, *)
(* nearest-first (immediate parent head, root last) — this ordering  *)
(* choice is what makes `ancestor`/`ancestor-or-self` naturally       *)
(* produce the reverse-document-order "proximity position" XPath     *)
(* 1.0 §2.4 defines for reverse axes, with no separate bookkeeping.   *)
(* ================================================================ *)

// Every item carries a `path : list int` — the child-index chain from
// the document root (root = []; child index i of a node with path P has
// path P @ [i]; attribute j of an element with path P has path
// P @ [-1; j], the -1 marker sorting attributes after their element but
// before its children). Lexicographic compare of paths IS document
// order (a proper prefix sorts first, so element-before-attributes-
// before-children-before-following-sibling all fall out), and path
// equality IS node identity (distinct nodes never share a path). This
// is what powers the reverse/forward document-order axes and the
// document-order + duplicate-removed union, neither of which the
// ancestor list alone can express.
noeq type xctx_item =
  | CI_Elem    : path:list int -> ancestors:list xml_node -> node:xml_node -> xctx_item
  | CI_Attr    : path:list int -> ancestors:list xml_node -> owner:xml_node -> attr:xml_attribute -> xctx_item
  | CI_Text    : path:list int -> ancestors:list xml_node -> parent:xml_node -> text:string -> xctx_item
  | CI_Comment : path:list int -> ancestors:list xml_node -> parent:xml_node -> text:string -> xctx_item
  | CI_PI      : path:list int -> ancestors:list xml_node -> parent:xml_node -> target:string -> data:string -> xctx_item

let item_path (it:xctx_item) : list int =
  match it with
  | CI_Elem p _ _ -> p
  | CI_Attr p _ _ _ -> p
  | CI_Text p _ _ _ -> p
  | CI_Comment p _ _ _ -> p
  | CI_PI p _ _ _ _ -> p

// Drop the last element of a path (the parent-of operation on a
// child path); [] for the root's empty/singleton path.
let rec path_drop_last (l:list int) : Tot (list int) (decreases l) =
  match l with
  | [] -> []
  | [_] -> []
  | x :: tl -> x :: path_drop_last tl

// The owner-element path of an attribute (its path ends in [-1; j]).
let attr_owner_path (p:list int) : list int = path_drop_last (path_drop_last p)

// Lexicographic path compare: <0 / 0 / >0 for document order.
let rec path_compare (a b:list int) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys -> if x < y then -1 else if x > y then 1 else path_compare xs ys

// Is `a` a (non-strict) prefix of `b`? (ancestor/descendant test.)
let rec path_is_prefix (a b:list int) : Tot bool (decreases a) =
  match a, b with
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys -> x = y && path_is_prefix xs ys

// Children of `node` with document-order paths (parent_path @ [i]),
// `i` the 0-based index over ALL children (element/text/comment/pi).
let rec children_with_paths (parent_path:list int) (new_anc:list xml_node) (parent:xml_node)
                            (nodes:list xml_node) (i:nat)
  : Tot (list xctx_item) (decreases nodes) =
  match nodes with
  | [] -> []
  | c :: rest ->
    let cpath = parent_path @ [i] in
    let item =
      match c with
      | XElement _ _ _ -> CI_Elem cpath new_anc c
      | XText t -> CI_Text cpath new_anc parent t
      | XCDATA t -> CI_Text cpath new_anc parent t
      | XComment t -> CI_Comment cpath new_anc parent t
      | XPI tg d -> CI_PI cpath new_anc parent tg d
    in
    item :: children_with_paths parent_path new_anc parent rest (i + 1)

let child_items (path:list int) (ancestors:list xml_node) (node:xml_node) : list xctx_item =
  children_with_paths path (node :: ancestors) node (element_children node) 0

// Attribute nodes: path = owner_path @ [-1; j], the -1 marker sorting
// them after the owner element but before its children.
let rec attrs_with_paths (owner_path:list int) (ancestors:list xml_node) (owner:xml_node)
                         (attrs:list xml_attribute) (j:nat)
  : Tot (list xctx_item) (decreases attrs) =
  match attrs with
  | [] -> []
  | a :: rest ->
    CI_Attr (owner_path @ [(-1); j]) ancestors owner a
      :: attrs_with_paths owner_path ancestors owner rest (j + 1)

let attribute_items (path:list int) (ancestors:list xml_node) (node:xml_node) : list xctx_item =
  attrs_with_paths path ancestors node (element_attrs node) 0

let rec descendant_items (path:list int) (ancestors:list xml_node) (node:xml_node)
  : Tot (list xctx_item) (decreases node) =
  match node with
  | XElement _ _ children -> descendant_items_children path (node :: ancestors) node children 0
  | _ -> []

and descendant_items_children (parent_path:list int) (new_anc:list xml_node) (parent:xml_node)
                              (nodes:list xml_node) (i:nat)
  : Tot (list xctx_item) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl ->
    let cpath = parent_path @ [i] in
    let self_item =
      match hd with
      | XElement _ _ _ -> [CI_Elem cpath new_anc hd]
      | XText t -> [CI_Text cpath new_anc parent t]
      | XCDATA t -> [CI_Text cpath new_anc parent t]
      | XComment t -> [CI_Comment cpath new_anc parent t]
      | XPI tg d -> [CI_PI cpath new_anc parent tg d]
    in
    self_item @ descendant_items cpath new_anc hd @ descendant_items_children parent_path new_anc parent tl (i + 1)

// Nearest-first: p1 (immediate parent) :: p2 :: ... — see the module
// banner for why this ordering directly gives reverse-axis proximity
// position.
let rec ancestor_items (self_path:list int) (ancestors:list xml_node)
  : Tot (list xctx_item) (decreases ancestors) =
  match ancestors with
  | [] -> []
  | p :: rest ->
    let ppath = path_drop_last self_path in
    CI_Elem ppath rest p :: ancestor_items ppath rest

let item_ancestors (it:xctx_item) : list xml_node =
  match it with
  | CI_Elem _ anc _ -> anc
  | CI_Attr _ anc _ _ -> anc
  | CI_Text _ anc _ _ -> anc
  | CI_Comment _ anc _ _ -> anc
  | CI_PI _ anc _ _ _ -> anc

// parent axis: the owner element for an attribute; the immediate
// ancestor for anything else (empty if already at the document root).
let parent_axis (it:xctx_item) : list xctx_item =
  match it with
  | CI_Attr p anc owner _ -> [CI_Elem (attr_owner_path p) anc owner]
  | CI_Elem p anc _ | CI_Text p anc _ _ | CI_Comment p anc _ _ | CI_PI p anc _ _ _ ->
    (match anc with [] -> [] | q :: rest -> [CI_Elem (path_drop_last p) rest q])

// ancestor axis (nearest-first): for CI_Attr, the owner element is
// itself the nearest ancestor (XPath 1.0 §2.3), then its own ancestors.
let ancestor_axis (it:xctx_item) : list xctx_item =
  match it with
  | CI_Attr p anc owner _ ->
    let opath = attr_owner_path p in
    CI_Elem opath anc owner :: ancestor_items opath anc
  | CI_Elem p anc _ | CI_Text p anc _ _ | CI_Comment p anc _ _ | CI_PI p anc _ _ _ ->
    ancestor_items p anc

let child_axis (it:xctx_item) : list xctx_item =
  match it with
  | CI_Elem p anc n -> child_items p anc n
  | _ -> []   // attribute/text/comment/pi nodes have no children

let descendant_axis (it:xctx_item) : list xctx_item =
  match it with
  | CI_Elem p anc n -> descendant_items p anc n
  | _ -> []

let attribute_axis (it:xctx_item) : list xctx_item =
  match it with
  | CI_Elem p anc n -> attribute_items p anc n
  | _ -> []

// Sibling axes. `siblings_of` rebuilds the parent's child list (in
// document order, with paths) from the item's ancestor chain; the
// item's own path locates it among them. Attributes have no siblings
// via these axes (XPath 1.0 §2.2).
let siblings_of (it:xctx_item) : list xctx_item =
  match it with
  | CI_Elem p anc _ | CI_Text p anc _ _ | CI_Comment p anc _ _ | CI_PI p anc _ _ _ ->
    (match anc with
     | [] -> []                       // the root has no parent, hence no siblings
     | parent :: grand -> child_items (path_drop_last p) grand parent)
  | CI_Attr _ _ _ _ -> []

// following-sibling (forward axis, document order).
let following_sibling_axis (it:xctx_item) : list xctx_item =
  let p = item_path it in
  List.Tot.filter (fun s -> path_compare (item_path s) p > 0) (siblings_of it)

// preceding-sibling (reverse axis: nearest first = reverse document order).
let preceding_sibling_axis (it:xctx_item) : list xctx_item =
  let p = item_path it in
  List.Tot.rev (List.Tot.filter (fun s -> path_compare (item_path s) p < 0) (siblings_of it))


(* ================================================================ *)
(* Node tests                                                        *)
(*                                                                   *)
(* A name/wildcard test matches only the axis's PRINCIPAL node type   *)
(* (element for every axis here except `attribute`) — XPath 1.0 §2.3: *)
(* `child::*` selects element children only, never text/comment.     *)
(* ================================================================ *)

let string_starts_with (s prefix:string) : bool =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let matches_node_test (test:xp_nodetest) (it:xctx_item) : bool =
  match test, it with
  | NT_Node, _ -> true
  | NT_Text, CI_Text _ _ _ _ -> true
  | NT_Text, _ -> false
  | NT_Comment, CI_Comment _ _ _ _ -> true
  | NT_Comment, _ -> false
  | NT_PI None, CI_PI _ _ _ _ _ -> true
  | NT_PI (Some tgt), CI_PI _ _ _ t _ -> t = tgt
  | NT_PI _, _ -> false
  | NT_Any, CI_Elem _ _ _ -> true
  | NT_Any, CI_Attr _ _ _ _ -> true
  | NT_Any, _ -> false
  | NT_Name nm, CI_Elem _ _ n -> (match element_tag n with Some t -> t = nm | None -> false)
  | NT_Name nm, CI_Attr _ _ _ a -> a.attr_name = nm
  | NT_Name _, _ -> false
  | NT_Prefix pfx, CI_Elem _ _ n ->
    (match element_tag n with Some t -> string_starts_with t (pfx ^ ":") | None -> false)
  | NT_Prefix pfx, CI_Attr _ _ _ a -> string_starts_with a.attr_name (pfx ^ ":")
  | NT_Prefix _, _ -> false

let filter_by_node_test (test:xp_nodetest) (items:list xctx_item) : list xctx_item =
  List.Tot.filter (matches_node_test test) items

let rec list_last_or (default_val:xml_node) (l:list xml_node) : Tot xml_node (decreases l) =
  match l with
  | [] -> default_val
  | [x] -> x
  | _ :: tl -> list_last_or default_val tl

// The document root as seen from any item — the outermost element of
// its ancestor chain, or the item's own node if it has none.
let root_of_item (it:xctx_item) : xml_node =
  let self_node =
    match it with
    | CI_Elem _ _ n -> n
    | CI_Attr _ _ owner _ -> owner
    | CI_Text _ _ parent _ -> parent
    | CI_Comment _ _ parent _ -> parent
    | CI_PI _ _ parent _ _ -> parent
  in
  list_last_or self_node (item_ancestors it)

// All document node-items (root element + every descendant), in
// document order, keyed by path — the substrate for the following /
// preceding axes and for locating a context node's position.
let all_document_items (it:xctx_item) : list xctx_item =
  let root = root_of_item it in
  CI_Elem [] [] root :: descendant_items [] [] root

// following axis: nodes after the context node in document order,
// excluding its descendants (XPath 1.0 §2.2). Ancestors sort before
// the context node so are excluded by the path_compare > 0 test.
let following_axis (it:xctx_item) : list xctx_item =
  let p = item_path it in
  List.Tot.filter
    (fun x -> path_compare (item_path x) p > 0 && not (path_is_prefix p (item_path x)))
    (all_document_items it)

// preceding axis: nodes before the context node in document order,
// excluding its ancestors; reverse axis, so reverse document order.
let preceding_axis (it:xctx_item) : list xctx_item =
  let p = item_path it in
  List.Tot.rev
    (List.Tot.filter
      (fun x -> path_compare (item_path x) p < 0 && not (path_is_prefix (item_path x) p))
      (all_document_items it))

let apply_axis (ax:xp_axis) (it:xctx_item) : list xctx_item =
  match ax with
  | Ax_Self -> [it]
  | Ax_Child -> child_axis it
  | Ax_Descendant -> descendant_axis it
  | Ax_DescendantOrSelf -> it :: descendant_axis it
  | Ax_Parent -> parent_axis it
  | Ax_Ancestor -> ancestor_axis it
  | Ax_AncestorOrSelf -> it :: ancestor_axis it
  | Ax_Attribute -> attribute_axis it
  | Ax_FollowingSibling -> following_sibling_axis it
  | Ax_PrecedingSibling -> preceding_sibling_axis it
  | Ax_Following -> following_axis it
  | Ax_Preceding -> preceding_axis it


(* ================================================================ *)
(* Values: the four-way sum XPath 1.0 §1 defines                     *)
(* ================================================================ *)

noeq type xp_value =
  | XV_Nodes : list xctx_item -> xp_value
  | XV_Bool  : bool -> xp_value
  | XV_Num   : xpath_number -> xp_value
  | XV_Str   : string -> xp_value

noeq type xp_env = {
  env_item : xctx_item;
  env_pos  : nat;
  env_size : nat;
  env_vars : list (string & xp_value);
}

let lookup_var (vars:list (string & xp_value)) (name:string) : option xp_value =
  match List.Tot.find (fun (kv:(string & xp_value)) -> fst kv = name) vars with
  | Some (_, v) -> Some v
  | None -> None

// String-value of a node (XPath 1.0 §5): element = concatenation of
// all descendant text, attribute = its value, text/comment = their
// content. `Parser.XML.text_content` already computes exactly the
// element case (descendant text concatenation), reused directly.
let item_string_value (it:xctx_item) : string =
  match it with
  | CI_Elem _ _ n -> text_content n
  | CI_Attr _ _ _ a -> a.attr_value
  | CI_Text _ _ _ t -> t
  | CI_Comment _ _ _ t -> t
  | CI_PI _ _ _ _ d -> d

// String-value of a node-SET: the string-value of the node "first in
// document order" (§1.1). Simplification, disclosed in the program
// plan: this engine takes the head of the list AS GENERATED, which is
// correct document order for every forward axis (child, descendant,
// descendant-or-self, self, attribute) but is the REVERSE of true
// document order when the set came from a bare ancestor/
// ancestor-or-self axis (nearest-nearest-first, by design, for
// correct reverse-axis position() numbering — see the module banner).
let nodeset_string_value (items:list xctx_item) : string =
  match items with
  | [] -> ""
  | hd :: _ -> item_string_value hd

let to_string_val (v:xp_value) : string =
  match v with
  | XV_Str s -> s
  | XV_Num n -> xn_to_string n
  | XV_Bool b -> if b then "true" else "false"
  | XV_Nodes items -> nodeset_string_value items

let to_bool_val (v:xp_value) : bool =
  match v with
  | XV_Bool b -> b
  | XV_Num n -> xn_to_bool n
  | XV_Str s -> String.length s > 0
  | XV_Nodes items -> not (Nil? items)

let to_number_val (v:xp_value) : xpath_number =
  match v with
  | XV_Num n -> n
  | XV_Bool b -> XN_Finite (if b then 1 else 0) 0
  | XV_Str s -> string_to_xn s
  | XV_Nodes items -> string_to_xn (nodeset_string_value items)

let xn_finite_int (n:xpath_number) : option int =
  match n with
  | XN_Finite v 0 -> Some v
  | XN_Finite v s -> let p = xn_pow10 s in if p = 0 then None else Some (v / p)
  | _ -> None


(* ================================================================ *)
(* Comparisons (§3.4) — see the program plan's comparison-semantics  *)
(* note for why relational ops involving a node-set convert to       *)
(* numbers while '='/'!=' compare strings.                           *)
(* ================================================================ *)

let apply_comp_bool (op:xp_comp_op) (a b:bool) : bool =
  match op with
  | Cmp_Eq -> a = b
  | Cmp_Ne -> a <> b
  | Cmp_Lt -> (not a) && b
  | Cmp_Le -> (not a) || b
  | Cmp_Gt -> a && (not b)
  | Cmp_Ge -> a || (not b)

// XN_NaN comparisons: '!=' is true (NaN is never equal to anything,
// including itself), the other five are all false — IEEE 754
// unordered-compare semantics.
let apply_comp_num (op:xp_comp_op) (a b:xpath_number) : bool =
  match xn_compare a b with
  | None -> op = Cmp_Ne
  | Some c ->
    (match op with
     | Cmp_Eq -> c = 0
     | Cmp_Ne -> c <> 0
     | Cmp_Lt -> c < 0
     | Cmp_Le -> c <= 0
     | Cmp_Gt -> c > 0
     | Cmp_Ge -> c >= 0)

let apply_comp_str (op:xp_comp_op) (a b:string) : bool =
  match op with
  | Cmp_Eq -> a = b
  | Cmp_Ne -> a <> b
  | Cmp_Lt -> String.compare a b < 0
  | Cmp_Le -> String.compare a b <= 0
  | Cmp_Gt -> String.compare a b > 0
  | Cmp_Ge -> String.compare a b >= 0

let rec exists_str (pred:string -> bool) (items:list xctx_item) : Tot bool (decreases items) =
  match items with
  | [] -> false
  | hd :: tl -> pred (item_string_value hd) || exists_str pred tl

let is_relational_op (op:xp_comp_op) : bool =
  match op with Cmp_Lt | Cmp_Le | Cmp_Gt | Cmp_Ge -> true | _ -> false

let xp_compare (op:xp_comp_op) (a b:xp_value) : bool =
  match a, b with
  | XV_Nodes na, XV_Nodes nb ->
    if is_relational_op op then
      exists_str (fun sa -> exists_str (fun sb -> apply_comp_num op (string_to_xn sa) (string_to_xn sb)) nb) na
    else
      exists_str (fun sa -> exists_str (fun sb -> apply_comp_str op sa sb) nb) na
  | XV_Nodes na, XV_Num nb -> exists_str (fun sa -> apply_comp_num op (string_to_xn sa) nb) na
  | XV_Num na, XV_Nodes nb -> exists_str (fun sb -> apply_comp_num op na (string_to_xn sb)) nb
  | XV_Nodes na, XV_Str sb ->
    if is_relational_op op then exists_str (fun sa -> apply_comp_num op (string_to_xn sa) (string_to_xn sb)) na
    else exists_str (fun sa -> apply_comp_str op sa sb) na
  | XV_Str sa, XV_Nodes nb ->
    if is_relational_op op then exists_str (fun sb -> apply_comp_num op (string_to_xn sa) (string_to_xn sb)) nb
    else exists_str (fun sb -> apply_comp_str op sa sb) nb
  | XV_Nodes na, XV_Bool bb -> apply_comp_bool op (not (Nil? na)) bb
  | XV_Bool ba, XV_Nodes nb -> apply_comp_bool op ba (not (Nil? nb))
  | XV_Bool _, _ -> apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | _, XV_Bool _ -> apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | XV_Num _, _ -> apply_comp_num op (to_number_val a) (to_number_val b)
  | _, XV_Num _ -> apply_comp_num op (to_number_val a) (to_number_val b)
  | _, _ -> apply_comp_str op (to_string_val a) (to_string_val b)


(* ================================================================ *)
(* String function-library helpers (plain FStar.String — these       *)
(* operate on already-decoded content strings, not the raw document, *)
(* so there is no byte/codepoint hot-path concern the way there is   *)
(* for Parser.XPath's own lexer; same posture SPARQL11.Algebra takes *)
(* for its string built-ins).                                        *)
(* ================================================================ *)

let rec str_find_from (s sub:string) (pos:nat) (slen:nat{slen = String.length s}) (sublen:nat{sublen = String.length sub})
  : Tot (option (n:nat{n + String.length sub <= String.length s})) (decreases (if slen + 1 > pos then slen + 1 - pos else 0)) =
  if pos + sublen > slen then None
  else if String.sub s pos sublen = sub then Some pos
  else if pos >= slen then None
  else str_find_from s sub (pos + 1) slen sublen

let str_find (s sub:string) : option (n:nat{n + String.length sub <= String.length s}) =
  let slen = String.length s in
  let sublen = String.length sub in
  if sublen = 0 then Some 0 else str_find_from s sub 0 slen sublen

let string_starts_with2 (s prefix:string) : bool = string_starts_with s prefix

let is_xp_space (c:FStar.Char.char) : bool = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let rec normalize_space_chars (cs:list FStar.Char.char) (in_space:bool)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    if is_xp_space c then
      (if in_space then normalize_space_chars rest true else ' ' :: normalize_space_chars rest true)
    else c :: normalize_space_chars rest false

let normalize_space (s:string) : string =
  let collapsed = normalize_space_chars (String.list_of_string s) true in
  let rev = List.Tot.rev collapsed in
  let rev' = match rev with ' ' :: rest -> rest | _ -> rev in
  String.string_of_list (List.Tot.rev rev')

let xn_le_int (a:xpath_number) (k:int) : bool =
  match xn_compare a (XN_Finite k 0) with Some c -> c <= 0 | None -> false

let xn_lt_int (k:int) (a:xpath_number) : bool =
  match xn_compare (XN_Finite k 0) a with Some c -> c < 0 | None -> false

// substring(string, start, length?) per XPath 1.0 §4.2: keep 1-based
// positions P with round(start) <= P < round(start) + round(length).
// No explicit length is defined as length = +Infinity (spec: "all
// characters after the position specified"). Composing via xn_arith
// for the end bound (rather than hand-matching Inf/NaN combinations)
// is what gets `substring("12345", -1 div 0, 1 div 0) = ""` right:
// -Infinity + Infinity = NaN, and NaN fails every comparison.
let rec substring_collect (s:string) (start_r end_bound:xpath_number) (p:nat{p >= 1}) (slen:nat{slen = String.length s})
  : Tot string (decreases (if slen + 1 > p then slen + 1 - p else 0)) =
  if p > slen then ""
  else
    let rest = substring_collect s start_r end_bound (p + 1) slen in
    if xn_le_int start_r p && xn_lt_int p end_bound then
      String.concat "" [String.sub s (p - 1) 1; rest]
    else rest

let substring_impl (s:string) (start_n len_n:xpath_number) : string =
  let start_r = xn_round start_n in
  let len_r = xn_round len_n in
  let end_bound = xn_arith Ar_Add start_r len_r in
  substring_collect s start_r end_bound 1 (String.length s)

let item_qname (it:xctx_item) : string =
  match it with
  | CI_Elem _ _ n -> (match element_tag n with Some t -> t | None -> "")
  | CI_Attr _ _ _ a -> a.attr_name
  | CI_PI _ _ _ tg _ -> tg   // name()/local-name() of a PI is its target
  | _ -> ""

let rec find_char_from (s:string) (c:FStar.Char.char) (pos:nat) (len:nat{len = String.length s})
  : Tot (option (n:nat{n < String.length s})) (decreases (if len > pos then len - pos else 0)) =
  if pos >= len then None
  else if String.index s pos = c then Some pos
  else find_char_from s c (pos + 1) len

let local_name_of (qn:string) : string =
  match find_char_from qn ':' 0 (String.length qn) with
  | Some i -> String.sub qn (i + 1) (String.length qn - i - 1)
  | None -> qn

let rec sum_items (items:list xctx_item) : Tot xpath_number (decreases items) =
  match items with
  | [] -> XN_Finite 0 0
  | hd :: tl -> xn_arith Ar_Add (string_to_xn (item_string_value hd)) (sum_items tl)

// Insertion into a document-ordered list, dropping duplicates (a node
// already present by path). Used to realise XPath 1.0 §3.3 union
// semantics: result in document order with duplicates removed.
let rec insert_by_doc (x:xctx_item) (l:list xctx_item) : Tot (list xctx_item) (decreases l) =
  match l with
  | [] -> [x]
  | y :: ys ->
    let c = path_compare (item_path x) (item_path y) in
    if c < 0 then x :: l
    else if c = 0 then l              // same node (identical path): keep existing
    else y :: insert_by_doc x ys

let rec doc_sort_dedup (l:list xctx_item) : Tot (list xctx_item) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> insert_by_doc x (doc_sort_dedup xs)


(* ================================================================ *)
(* Fuel sizing for the evaluator                                     *)
(*                                                                   *)
(* Plain structural recursion over xp_expr/xp_step and over          *)
(* xml_node — neither touches xctx_item or the fuel-based evaluator  *)
(* below, so both are as safe as Parser.XML's own                    *)
(* text_content/text_content_list (same structural-decrease idiom    *)
(* across a type and its list).                                      *)
(* ================================================================ *)

let rec xp_expr_size (e:xp_expr) : Tot nat (decreases e) =
  match e with
  | XE_Path _ steps -> 1 + xp_steps_size steps
  | XE_FilterPath primary preds steps -> 1 + xp_expr_size primary + xp_exprs_size preds + xp_steps_size steps
  | XE_Union a b -> 1 + xp_expr_size a + xp_expr_size b
  | XE_Or a b -> 1 + xp_expr_size a + xp_expr_size b
  | XE_And a b -> 1 + xp_expr_size a + xp_expr_size b
  | XE_Compare _ a b -> 1 + xp_expr_size a + xp_expr_size b
  | XE_Arith _ a b -> 1 + xp_expr_size a + xp_expr_size b
  | XE_Neg a -> 1 + xp_expr_size a
  | XE_Number _ _ -> 1
  | XE_Literal _ -> 1
  | XE_VarRef _ -> 1
  | XE_FunCall _ args -> 1 + xp_exprs_size args

and xp_exprs_size (es:list xp_expr) : Tot nat (decreases es) =
  match es with
  | [] -> 0
  | hd :: tl -> 1 + xp_expr_size hd + xp_exprs_size tl

and xp_steps_size (ss:list xp_step) : Tot nat (decreases ss) =
  match ss with
  | [] -> 0
  | hd :: tl -> 1 + xp_step_size hd + xp_steps_size tl

and xp_step_size (s:xp_step) : Tot nat (decreases s) =
  1 + xp_exprs_size s.step_preds

let rec xml_node_count (n:xml_node) : Tot nat (decreases n) =
  match n with
  | XElement _ _ children -> 1 + xml_nodes_count children
  | _ -> 1

and xml_nodes_count (ns:list xml_node) : Tot nat (decreases ns) =
  match ns with
  | [] -> 0
  | hd :: tl -> xml_node_count hd + xml_nodes_count tl

// Threaded from BOTH the expression's own size and the document's
// node count — never a bare constant (extraction-semantics trap #3).
// See the module banner for why a single fuel decrement per call
// (rather than a structural measure) is the safe choice for this
// mutual-recursion shape.
let initial_eval_fuel (e:xp_expr) (doc_nodes:nat) : nat =
  op_Multiply (xp_expr_size e + 1) (op_Multiply (doc_nodes + 1) 24) + 4096


(* ================================================================ *)
(* The evaluator — fuel-threaded, one call = one fuel unit, always.   *)
(* ================================================================ *)

let rec eval_expr (fuel:nat) (env:xp_env) (e:xp_expr) : Tot xp_value (decreases fuel) =
  if fuel = 0 then XV_Str ""
  else
    match e with
    | XE_Number v s -> XV_Num (XN_Finite v s)
    | XE_Literal s -> XV_Str s
    | XE_VarRef name -> (match lookup_var env.env_vars name with Some v -> v | None -> XV_Str "")
    | XE_Neg e1 -> XV_Num (xn_neg (to_number_val (eval_expr (fuel - 1) env e1)))
    | XE_Arith op a b ->
      XV_Num (xn_arith op (to_number_val (eval_expr (fuel - 1) env a)) (to_number_val (eval_expr (fuel - 1) env b)))
    | XE_Compare op a b ->
      XV_Bool (xp_compare op (eval_expr (fuel - 1) env a) (eval_expr (fuel - 1) env b))
    | XE_And a b ->
      XV_Bool (to_bool_val (eval_expr (fuel - 1) env a) && to_bool_val (eval_expr (fuel - 1) env b))
    | XE_Or a b ->
      XV_Bool (to_bool_val (eval_expr (fuel - 1) env a) || to_bool_val (eval_expr (fuel - 1) env b))
    | XE_Union a b ->
      // XPath 1.0 §3.3: the union result is the two node-sets combined,
      // in document order, with duplicates removed. Each item carries a
      // document-order path (see xctx_item's banner); `doc_sort_dedup`
      // sorts by that path and drops any node already present, so an
      // overlapping union no longer over-counts.
      (match eval_expr (fuel - 1) env a, eval_expr (fuel - 1) env b with
       | XV_Nodes na, XV_Nodes nb -> XV_Nodes (doc_sort_dedup (na @ nb))
       | XV_Nodes na, _ -> XV_Nodes (doc_sort_dedup na)
       | _, XV_Nodes nb -> XV_Nodes (doc_sort_dedup nb)
       | _, _ -> XV_Nodes [])
    | XE_FunCall name args -> eval_funcall (fuel - 1) env name args
    | XE_Path absolute steps ->
      if absolute then XV_Nodes (eval_absolute_steps (fuel - 1) env.env_vars (root_of_item env.env_item) steps)
      else XV_Nodes (eval_steps (fuel - 1) env.env_vars [env.env_item] steps)
    | XE_FilterPath primary preds steps ->
      let pv = eval_expr (fuel - 1) env primary in
      (match pv with
       | XV_Nodes items0 ->
         let items1 = filter_items_by_preds (fuel - 1) env.env_vars items0 preds in
         XV_Nodes (eval_steps (fuel - 1) env.env_vars items1 steps)
       | other -> if Nil? preds && Nil? steps then other else XV_Nodes [])

// Absolute-path bootstrap (see the program plan's "bare '/'" note):
// this engine's xml_node IS the document's root element (Parser.XML
// has no separate document-node wrapper), so the very first step of
// an absolute path is matched directly against the root item (as a
// "self" test) rather than against the root's children — the
// practically-useful reading of `/tagName`, at the cost of `name(/)`
// returning the root's own tag rather than strict XPath 1.0's empty
// document-node name (disclosed divergence).
and eval_absolute_steps (fuel:nat) (vars:list (string & xp_value)) (root_node:xml_node) (steps:list xp_step)
  : Tot (list xctx_item) (decreases fuel) =
  if fuel = 0 then []
  else
    let root_item = CI_Elem [] [] root_node in
    match steps with
    | [] -> [root_item]
    | s :: rest ->
      let expansion =
        match s.step_axis with
        | Ax_Child -> filter_by_node_test s.step_test [root_item]
        | Ax_Self -> filter_by_node_test s.step_test [root_item]
        | Ax_DescendantOrSelf -> filter_by_node_test s.step_test (root_item :: descendant_items [] [] root_node)
        | _ -> []
      in
      let kept = filter_items_by_preds (fuel - 1) vars expansion s.step_preds in
      eval_steps (fuel - 1) vars kept rest

and eval_steps (fuel:nat) (vars:list (string & xp_value)) (items:list xctx_item) (steps:list xp_step)
  : Tot (list xctx_item) (decreases fuel) =
  if fuel = 0 then items
  else
    match steps with
    | [] -> items
    | s :: rest ->
      let expanded = expand_step_over_items (fuel - 1) vars s items in
      eval_steps (fuel - 1) vars expanded rest

and expand_step_over_items (fuel:nat) (vars:list (string & xp_value)) (s:xp_step) (items:list xctx_item)
  : Tot (list xctx_item) (decreases fuel) =
  if fuel = 0 then []
  else
    match items with
    | [] -> []
    | it :: rest ->
      let raw = apply_axis s.step_axis it in
      let tested = filter_by_node_test s.step_test raw in
      let kept = filter_items_by_preds (fuel - 1) vars tested s.step_preds in
      kept @ expand_step_over_items (fuel - 1) vars s rest

// Predicates apply in sequence; each predicate's position()/last()
// are recomputed against the SURVIVING list from the previous
// predicate (spec-correct chained-predicate renumbering — e.g.
// `foo[@bar][2]` means "2nd of the @bar-holding foo's", not "2nd foo
// overall, if it also has @bar").
and filter_items_by_preds (fuel:nat) (vars:list (string & xp_value)) (items:list xctx_item) (preds:list xp_expr)
  : Tot (list xctx_item) (decreases fuel) =
  if fuel = 0 then items
  else
    match preds with
    | [] -> items
    | p :: rest ->
      let size = List.Tot.length items in
      let kept = filter_one_pred (fuel - 1) vars p items size 1 in
      filter_items_by_preds (fuel - 1) vars kept rest

// Numeric predicate shorthand (§2.4): `[N]` keeps the node whose
// proximity position equals N; any other value is boolean()-converted
// (`boolean(node)` shorthand and, spec-strictly, boolean(number) is
// value<>0, NOT position=value — but a bare `[N]` is parsed as an
// XE_Number, so the XV_Num branch below IS specifically the numeric
// shorthand, not a general boolean(number) coercion of some other
// numeric expression like `[1+1]`, which XPath 1.0 also treats as the
// SAME positional shorthand since §2.4 keys off the predicate
// EXPRESSION's result type being number, not off its AST shape).
and filter_one_pred (fuel:nat) (vars:list (string & xp_value)) (p:xp_expr) (items:list xctx_item) (size:nat) (pos:nat)
  : Tot (list xctx_item) (decreases fuel) =
  if fuel = 0 then [] // fuel exhaustion: fail closed (empty), never silently include
  else
    match items with
    | [] -> []
    | it :: rest ->
      let e = { env_item = it; env_pos = pos; env_size = size; env_vars = vars } in
      let v = eval_expr (fuel - 1) e p in
      let keep =
        match v with
        | XV_Num n -> (match xn_finite_int (xn_round n) with Some k -> k = pos | None -> false)
        | _ -> to_bool_val v
      in
      let tail = filter_one_pred (fuel - 1) vars p rest size (pos + 1) in
      if keep then it :: tail else tail

and eval_concat_args (fuel:nat) (env:xp_env) (args:list xp_expr) : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match args with
    | [] -> ""
    | a :: rest -> to_string_val (eval_expr (fuel - 1) env a) ^ eval_concat_args (fuel - 1) env rest

and eval_funcall (fuel:nat) (env:xp_env) (name:string) (args:list xp_expr)
  : Tot xp_value (decreases fuel) =
  if fuel = 0 then XV_Str ""
  else
    if name = "position" then XV_Num (XN_Finite env.env_pos 0)
    else if name = "last" then XV_Num (XN_Finite env.env_size 0)
    else if name = "count" then
      (match args with
       | [a] ->
         (match eval_expr (fuel - 1) env a with
          | XV_Nodes items -> XV_Num (XN_Finite (List.Tot.length items) 0)
          | _ -> XV_Num (XN_Finite 0 0))
       | _ -> XV_Num (XN_Finite 0 0))
    else if name = "name" || name = "local-name" then
      let items =
        match args with
        | [] -> [env.env_item]
        | a :: _ -> (match eval_expr (fuel - 1) env a with XV_Nodes its -> its | _ -> [])
      in
      (match items with
       | [] -> XV_Str ""
       | it :: _ ->
         let qn = item_qname it in
         XV_Str (if name = "local-name" then local_name_of qn else qn))
    else if name = "current" then
      // XSLT current(): the node the XSLT template is processing. This
      // engine threads it as env_item at each XPath call-out, so at the
      // outermost expression current() = the context node. Inside a
      // location-step predicate the context node changes but env_item
      // tracks it, so current() there returns the step's context rather
      // than the XSLT current node (disclosed divergence; the faithful
      // reading needs a separate current-node slot in xp_env).
      XV_Nodes [env.env_item]
    else if name = "string" then
      (match args with
       | [] -> XV_Str (item_string_value env.env_item)
       | a :: _ -> XV_Str (to_string_val (eval_expr (fuel - 1) env a)))
    else if name = "concat" then XV_Str (eval_concat_args (fuel - 1) env args)
    else if name = "contains" then
      (match args with
       | [a; b] ->
         let s = to_string_val (eval_expr (fuel - 1) env a) in
         let sub = to_string_val (eval_expr (fuel - 1) env b) in
         XV_Bool (Some? (str_find s sub))
       | _ -> XV_Bool false)
    else if name = "starts-with" then
      (match args with
       | [a; b] ->
         XV_Bool (string_starts_with2 (to_string_val (eval_expr (fuel - 1) env a)) (to_string_val (eval_expr (fuel - 1) env b)))
       | _ -> XV_Bool false)
    else if name = "substring-before" then
      (match args with
       | [a; b] ->
         let s = to_string_val (eval_expr (fuel - 1) env a) in
         let sub = to_string_val (eval_expr (fuel - 1) env b) in
         (match str_find s sub with Some i -> XV_Str (String.sub s 0 i) | None -> XV_Str "")
       | _ -> XV_Str "")
    else if name = "substring-after" then
      (match args with
       | [a; b] ->
         let s = to_string_val (eval_expr (fuel - 1) env a) in
         let sub = to_string_val (eval_expr (fuel - 1) env b) in
         (match str_find s sub with
          | Some i ->
            let sl = String.length sub in
            XV_Str (String.sub s (i + sl) (String.length s - i - sl))
          | None -> XV_Str "")
       | _ -> XV_Str "")
    else if name = "substring" then
      (match args with
       | [a; b] ->
         let s = to_string_val (eval_expr (fuel - 1) env a) in
         let sv = to_number_val (eval_expr (fuel - 1) env b) in
         XV_Str (substring_impl s sv XN_PosInf)
       | [a; b; c] ->
         let s = to_string_val (eval_expr (fuel - 1) env a) in
         let sv = to_number_val (eval_expr (fuel - 1) env b) in
         let lv = to_number_val (eval_expr (fuel - 1) env c) in
         XV_Str (substring_impl s sv lv)
       | _ -> XV_Str "")
    else if name = "string-length" then
      let s = match args with [] -> item_string_value env.env_item | a :: _ -> to_string_val (eval_expr (fuel - 1) env a) in
      XV_Num (XN_Finite (String.length s) 0)
    else if name = "normalize-space" then
      let s = match args with [] -> item_string_value env.env_item | a :: _ -> to_string_val (eval_expr (fuel - 1) env a) in
      XV_Str (normalize_space s)
    else if name = "not" then
      (match args with [a] -> XV_Bool (not (to_bool_val (eval_expr (fuel - 1) env a))) | _ -> XV_Bool true)
    else if name = "true" then XV_Bool true
    else if name = "false" then XV_Bool false
    else if name = "boolean" then
      (match args with [a] -> XV_Bool (to_bool_val (eval_expr (fuel - 1) env a)) | _ -> XV_Bool false)
    else if name = "number" then
      (match args with
       | [] -> XV_Num (to_number_val (XV_Str (item_string_value env.env_item)))
       | a :: _ -> XV_Num (to_number_val (eval_expr (fuel - 1) env a)))
    else if name = "sum" then
      (match args with
       | [a] -> (match eval_expr (fuel - 1) env a with XV_Nodes items -> XV_Num (sum_items items) | _ -> XV_Num (XN_Finite 0 0))
       | _ -> XV_Num (XN_Finite 0 0))
    else if name = "floor" then
      (match args with [a] -> XV_Num (xn_floor (to_number_val (eval_expr (fuel - 1) env a))) | _ -> XV_Num XN_NaN)
    else if name = "ceiling" then
      (match args with [a] -> XV_Num (xn_ceiling (to_number_val (eval_expr (fuel - 1) env a))) | _ -> XV_Num XN_NaN)
    else if name = "round" then
      (match args with [a] -> XV_Num (xn_round (to_number_val (eval_expr (fuel - 1) env a))) | _ -> XV_Num XN_NaN)
    else XV_Str "" // unknown function name: Stage 1 scope, no crash


(* ================================================================ *)
(* Entry points                                                      *)
(* ================================================================ *)

// Locate `target` among `nodes` by structural identity, returning its
// index (0 if absent — best-effort, see path_of_chain).
let rec find_child_index (nodes:list xml_node) (target:xml_node) (i:nat)
  : Tot nat (decreases nodes) =
  match nodes with
  | [] -> 0
  | x :: rest -> if x = target then i else find_child_index rest target (i + 1)

// Document-order path of a root-to-node chain [root; ...; parent; ctx],
// each hop the child index of the next node within the current node.
let rec path_of_chain (chain:list xml_node) : Tot (list int) (decreases chain) =
  match chain with
  | [] -> []
  | [_] -> []
  | parent :: rest ->
    (match rest with
     | [] -> []
     | child :: _ ->
       let i = find_child_index (element_children parent) child 0 in
       i :: path_of_chain rest)

// Reconstruct a context node's path from its ancestor chain
// (nearest-first). Best-effort: structurally-identical siblings on the
// ancestor path are indistinguishable, affecting only the document-order
// axes from such a mid-document entry (eval_xpath_from_root is exact).
let compute_ctx_path (ancestors:list xml_node) (ctx:xml_node) : list int =
  path_of_chain (List.Tot.append (List.Tot.rev ancestors) [ctx])

// Evaluate `expr_text` with the document root as the initial context
// node (position 1, size 1) — the common case for a fresh document.
let eval_xpath_from_root (root_node:xml_node) (vars:list (string & xp_value)) (expr_text:string)
  : option xp_value =
  match parse_xpath expr_text with
  | None -> None
  | Some e ->
    let fuel = initial_eval_fuel e (xml_node_count root_node) in
    let env = { env_item = CI_Elem [] [] root_node; env_pos = 1; env_size = 1; env_vars = vars } in
    Some (eval_expr fuel env e)

// Evaluate with an arbitrary context node deeper in the document,
// supplying its proper ancestors (nearest-first — see the xctx_item
// banner) so relative axes (parent, ancestor, following absolute
// paths via root_of_item) resolve correctly.
let eval_xpath_from_item (ancestors:list xml_node) (context_node:xml_node) (vars:list (string & xp_value)) (expr_text:string)
  : option xp_value =
  match parse_xpath expr_text with
  | None -> None
  | Some e ->
    let doc_nodes = xml_node_count context_node + xml_nodes_count ancestors in
    let fuel = initial_eval_fuel e doc_nodes in
    let env = { env_item = CI_Elem (compute_ctx_path ancestors context_node) ancestors context_node;
                env_pos = 1; env_size = 1; env_vars = vars } in
    Some (eval_expr fuel env e)
