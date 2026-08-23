/-
L4Factoidal.XPath.Eval — the XPath 1.0 EVALUATOR.

Spec: XPath 1.0 §1 (Introduction, the four object types), §2 (Location
Paths), §3 (Expressions), §4 (Core Function Library). Section numbers
below cite that Recommendation.

## Four types, and the conversions between them are not symmetric

An XPath value is a node-set, a string, a number or a boolean. Almost
every defect in a path language comes from applying the wrong
conversion: `boolean(node-set)` is "is it non-empty", `string(node-set)`
is the string-value of its FIRST node in document order, and
`number(node-set)` goes through the string. The comparison operators
do not convert at all in the usual sense — `nodeset = string` is TRUE
when SOME node matches, so `a != b` is not `not(a = b)` when either
side is a node-set. That existential reading is written out in
`cmpValues` rather than left to the reader.

## A function this module does not have is `none`, not a wrong value

`evalExpr` returns `Option Value`. Every unimplemented function, every
unresolvable variable and every unreadable expression is `none`, which
the XSLT engine turns into a REPORTED refusal to transform. A default
of "empty node-set" or "empty string" would let a stylesheet produce a
document of the right shape with the content missing — the failure
mode this project has paid for in five other suites.
-/
import L4Factoidal.XPath.Data
import L4Factoidal.XPath.Expr

namespace L4Factoidal.XPath.Full

open L4Factoidal.XPath

open L4Factoidal.XML

/-! ## Values -/

/-- The four XPath object types, plus the XSLT result-tree fragment.

    An RTF is what `xsl:variable` with CONTENT holds. XSLT 1.0 makes
    it a fifth type on purpose: it may be converted to a string or
    copied, but a location path may NOT be applied to it. Modelling
    it as a node-set would silently license `$v/x`, which XSLT 1.0
    forbids and which has no meaning against the source document's
    addresses. -/
inductive Value where
  | nodes (ns : List Item)
  | str   (s : String)
  | num   (n : Num)
  | bool  (b : Bool)
  | frag  (ns : List Node)
deriving Repr, Inhabited

/-- The evaluation context: §1's (node, position, size) plus the
    variable bindings and the namespace declarations in scope AT THE
    EXPRESSION, which is the stylesheet element, not the source node. -/
structure Ctx where
  doc   : Doc
  item  : Item
  pos   : Nat := 1
  size  : Nat := 1
  vars  : List (String × Value) := []
  nsctx : List (String × String) := []
  /-- The document node of the stylesheet's own source, for
      `document('')`. Absent when there is none to give. -/
  self? : Option Doc := none
  /-- Documents `document(uri)` may return, keyed by the URI as the
      stylesheet writes it.

      I/O is a PARAMETER, not a capability of this module: nothing
      here opens a file. The caller decides which documents exist and
      supplies them, so `document('missing.xml')` is `none` — a
      refusal — rather than an empty tree that a stylesheet would
      quietly transform into nothing. -/
  docs : List (String × Doc) := []
deriving Inhabited

/-! ## Conversions (§4.2, §4.3) -/

def Value.toStr (v : Value) : String :=
  match v with
  | .str s   => s
  | .num n   => n.toXString
  | .bool b  => if b then "true" else "false"
  | .nodes ns => match (normalize ns).head? with
      | some i => i.stringValue
      | none   => ""
  | .frag ns => String.join (ns.map nodeText)

def Value.toNum (v : Value) : Num :=
  match v with
  | .num n  => n
  | .bool b => if b then .finite 1 0 else .finite 0 0
  | other   => Num.ofString other.toStr

def Value.toBool (v : Value) : Bool :=
  match v with
  | .bool b   => b
  | .num n    => n.toBool
  | .str s    => s.length > 0
  | .nodes ns => !ns.isEmpty
  | .frag ns  => !ns.isEmpty

/-! ## Name tests -/

/-- The expanded name of an item: `(namespace URI, local part)`.

    An unprefixed ATTRIBUTE name is in no namespace even when a
    default namespace is declared (Namespaces in XML §6.2). Applying
    the default to attributes makes `@class` stop matching the moment
    a document declares `xmlns=`, which is the shape of a bug that
    only appears on real-world input. -/
def expandedName (d : Doc) (it : Item) : String × String :=
  let q := it.qname
  let pfx := prefixOf q
  let loc := localOf q
  match it.kind with
  | .attribute =>
      if pfx == "" then ("", loc)
      else
        let owner := itemAt d { path := it.loc.path }
        let nss := (owner.map (namespacesOf d)).getD []
        (((nss.find? (fun n => n.qname == pfx)).map (fun n => n.stringValue)).getD "", loc)
  | .element | .pi =>
      let nss := namespacesOf d it
      (((nss.find? (fun n => n.qname == pfx)).map (fun n => n.stringValue)).getD "", loc)
  | _ => ("", loc)

/-- Expand a name written in an EXPRESSION. An unprefixed name has no
    namespace — XPath 1.0 §2.3 says so explicitly, and it is the one
    place where XPath and XSLT literal result elements differ in how
    they read a bare name. -/
def expandTestName (nsctx : List (String × String)) (q : String) : String × String :=
  let pfx := prefixOf q
  if pfx == "" then ("", q)
  else (((nsctx.find? (fun (p, _) => p == pfx)).map (·.2)).getD " unbound", localOf q)

/-- The node type an axis selects by default (§2.3). -/
def principalKind : Ax → Kind
  | .attribute => .attribute
  | .namespace => .namespace
  | _          => .element

def matchesTest (d : Doc) (nsctx : List (String × String)) (ax : Ax)
    (t : NodeTest) (it : Item) : Bool :=
  match t with
  | .nodeT     => true
  | .textT     => it.kind == .text
  | .commentT  => it.kind == .comment
  | .piT none  => it.kind == .pi
  | .piT (some tgt) => it.kind == .pi && it.qname == tgt
  | .anyName   => it.kind == principalKind ax
  | .anyInPrefix p =>
      it.kind == principalKind ax &&
      (expandedName d it).1 == (expandTestName nsctx (p ++ ":x")).1
  | .name q =>
      it.kind == principalKind ax &&
      (if it.kind == .namespace then it.qname == q
       else expandedName d it == expandTestName nsctx q)

/-! ## Axis navigation -/

def axisItems (d : Doc) (ax : Ax) (it : Item) : List Item :=
  match ax with
  | .child             => childrenOf it
  | .descendant        => descendantsOf it
  | .descendantOrSelf  => it :: descendantsOf it
  | .parent            => (parentOf d it).toList
  | .ancestor          => ancestorsOf d it
  | .ancestorOrSelf    => it :: ancestorsOf d it
  | .self              => [it]
  | .attribute         => attributesOf it
  | .namespace         => namespacesOf d it
  | .following         => followingOf d it
  | .preceding         => precedingOf d it
  | .followingSibling  => followingSiblingsOf d it
  | .precedingSibling  => precedingSiblingsOf d it

/-- Is this a REVERSE axis? `position()` inside a predicate counts
    along the axis's own direction, so on a reverse axis the NEAREST
    node is position 1. `ancestor::*[1]` is the parent, not the
    document element — reading it forward silently returns the wrong
    end of the chain. -/
def isReverse : Ax → Bool
  | .ancestor | .ancestorOrSelf | .preceding | .precedingSibling => true
  | _ => false

/-! ## String helpers -/

private def substrChars (s : String) (from' len : Int) : String :=
  let cs := s.toList
  let lo := max 1 from'
  let hi := from' + len
  String.ofList ((cs.zipIdx).filterMap (fun (c, i) =>
    let p : Int := (i : Int) + 1
    if lo ≤ p && p < hi then some c else none))

private def isWsC (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def wordsOf (s : String) : List String :=
  (s.toList.foldr (fun c acc =>
      if isWsC c then [] :: acc
      else match acc with
           | w :: r => (c :: w) :: r
           | []     => [[c]]) [[]]).filterMap (fun w =>
    if w.isEmpty then none else some (String.ofList w))

def normalizeSpaceStr (s : String) : String :=
  String.intercalate " " (wordsOf s)

/-- Split on XML whitespace, dropping empties. -/
def splitWs (s : String) : List String := wordsOf s

def translateStr (s from' to' : String) : String :=
  let f := from'.toList
  let t := to'.toList
  String.ofList (s.toList.filterMap (fun c =>
    match f.findIdx? (· == c) with
    | none   => some c
    | some i => t[i]?))

/-- The index of `needle` in `hay`, by codepoint. -/
def substrIndex (hay needle : String) : Option Nat :=
  let h := hay.toList
  let n := needle.toList
  let rec go (i : Nat) : List Char → Option Nat
    | []          => if n.isEmpty then some i else none
    | x :: tl     => if (x :: tl).take n.length == n then some i else go (i + 1) tl
  if n.isEmpty then some 0 else go 0 h

/-! ## `id()` -/

/-- `id()` resolves an IDREF against attributes DECLARED of type ID.

    Our XML parser is non-validating and keeps the DTD's internal
    subset as text, so the declared-type information is not on the
    tree. This resolves against attributes literally NAMED `id` (any
    case) and against `xml:id`. That is a NARROWER rule than the
    specification's, and it is stated here rather than hidden: a
    document whose ID attribute is called something else resolves to
    nothing, which shows up as a missing node and not as a wrong
    one. -/
def idAttrNamed (a : Attribute) : Bool :=
  a.name == "xml:id" || a.name.toLower == "id"

def resolveIds (d : Doc) (refs : List String) : List Item :=
  normalize ((allItems d).filter (fun it =>
    it.kind == .element &&
    (attributesOf it).any (fun x =>
      match x with
      | .attr _ a => idAttrNamed a && refs.contains a.value
      | _         => false)))

/-! ## The function library this module implements -/

def knownFunctions : List String :=
  ["last", "position", "count", "id", "local-name", "namespace-uri", "name",
   "string", "concat", "starts-with", "contains", "substring-before",
   "substring-after", "substring", "string-length", "normalize-space",
   "translate", "boolean", "not", "true", "false", "lang", "number", "sum",
   "floor", "ceiling", "round", "current", "generate-id", "document",
   "function-available", "element-available", "system-property"]

def availableElements : List String :=
  ["xsl:apply-templates", "xsl:attribute", "xsl:call-template", "xsl:choose",
   "xsl:comment", "xsl:copy", "xsl:copy-of", "xsl:element", "xsl:for-each",
   "xsl:if", "xsl:otherwise", "xsl:param", "xsl:processing-instruction",
   "xsl:sort", "xsl:template", "xsl:text", "xsl:value-of", "xsl:variable",
   "xsl:when", "xsl:with-param"]

/-! ## The XPath 2.0 value comparisons -/

/-- The XPath 2.0 VALUE comparisons `eq ne lt le gt ge`.

    They are not XPath 1.0 and are named apart for that reason. Two
    numbers compare numerically; anything else compares as strings by
    codepoint. That is what the corpus asks for and no more:
    `boolean-026` compares numbers, `boolean-027` compares string
    literals, and `'20' lt '180.3'` is FALSE there because `2` follows
    `1`. Widening this to the full 2.0 type system would be inventing
    behaviour no test states. -/
def valueCmp (op : String) (x y : Value) : Bool :=
  let numeric := match x, y with
    | .num _, .num _ => true
    | _, _           => false
  if numeric then
    let m := x.toNum
    let n := y.toNum
    if op == "eq" then Num.eq m n
    else if op == "ne" then !(Num.eq m n)
    else if op == "lt" then Num.lt m n
    else if op == "le" then Num.le m n
    else if op == "gt" then Num.lt n m
    else Num.le n m
  else
    let a := x.toStr
    let b := y.toStr
    if op == "eq" then a == b
    else if op == "ne" then a != b
    else if op == "lt" then a < b
    else if op == "le" then a ≤ b
    else if op == "gt" then b < a
    else b ≤ a

def isValueOp (op : String) : Bool :=
  op == "eq" || op == "ne" || op == "lt" || op == "le" || op == "gt" || op == "ge"


/-! ## The evaluator -/

mutual

partial def evalExpr (c : Ctx) : Expr → Option Value
  | .num n    => some (.num n)
  | .str s    => some (.str s)
  | .varRef v => (c.vars.find? (fun (k, _) => k == v)).map (·.2)
  | .call f args => evalCall c f args
  | .or a b => do
      let x ← evalExpr c a
      if x.toBool then some (.bool true)
      else (evalExpr c b).map (fun y => Value.bool y.toBool)
  | .and a b => do
      let x ← evalExpr c a
      if !x.toBool then some (.bool false)
      else (evalExpr c b).map (fun y => Value.bool y.toBool)
  | .cmp op a b => do
      let x ← evalExpr c a
      let y ← evalExpr c b
      some (.bool (cmpValues op x y))
  | .arith op a b => do
      let x ← evalExpr c a
      let y ← evalExpr c b
      let m := x.toNum
      let n := y.toNum
      some (.num (if op == "+" then Num.add m n
                  else if op == "-" then Num.sub m n
                  else if op == "*" then Num.mul m n
                  else if op == "div" then Num.div m n
                  else Num.modN m n))
  | .negate a => (evalExpr c a).map (fun x => Value.num (Num.neg x.toNum))
  | .union a b => do
      let x ← evalExpr c a
      let y ← evalExpr c b
      match x, y with
      | .nodes p, .nodes q => some (.nodes (normalize (p ++ q)))
      | _, _ => none                      -- `|` is defined on node-sets only
  | .filter base preds => do
      let v ← evalExpr c base
      match v with
      | .nodes ns =>
          let sorted := normalize ns
          (applyPreds c sorted preds).map Value.nodes
      | _ => none
  | .path abs start steps =>
      match start with
      | none   => evalSteps c (if abs then [Item.doc c.doc] else [c.item]) steps
      | some e => do
          let v ← evalExpr c e
          match v with
          | .nodes ns =>
              if abs then evalSteps c [Item.doc c.doc] steps
              else
                -- A node-set that came from ANOTHER document carries
                -- addresses that only mean something against THAT
                -- document. Walking them against the current one
                -- reads the wrong tree and returns a plausible,
                -- wrong node-set — which is exactly what
                -- `document('')//ped:test` did: it silently selected
                -- nothing (XSLT namespace-4801).
                let d2 := match ns with
                  | [.doc kids] => kids
                  | _           => c.doc
                evalSteps { c with doc := d2 } ns steps
          | _ => none

/-- A step list applied to a node-set: each step maps every node of
    the current set and the results are merged INTO DOCUMENT ORDER
    with duplicates removed (§2.1). -/
partial def evalSteps (c : Ctx) (base : List Item) : List Step → Option Value
  | []      => some (.nodes (normalize base))
  | s :: rest => do
      let out ← base.foldlM (fun acc it => (evalStep c it s).map (fun got => acc ++ got)) []
      evalSteps c (normalize out) rest

partial def evalStep (c : Ctx) (it : Item) (s : Step) : Option (List Item) :=
  applyPreds c ((axisItems c.doc s.ax it).filter (matchesTest c.doc c.nsctx s.ax s.test))
    s.preds

/-- Apply a predicate list to a node list, in the list's own order. -/
partial def applyPreds (c : Ctx) (cands : List Item) (preds : List Expr)
    : Option (List Item) :=
  preds.foldlM (fun (cur : List Item) (p : Expr) =>
    let n := cur.length
    (cur.zipIdx).foldlM (fun (acc : List Item) (x : Item × Nat) => do
      let v ← evalExpr { c with item := x.1, pos := x.2 + 1, size := n } p
      -- §3.3: a NUMERIC predicate is a POSITION test; anything else
      -- is a boolean. `[1]` selects one node, `[@a]` selects many —
      -- reading the number as a boolean would keep every node.
      let keep := match v with
        | .num k => Num.eq k (Num.finite ((x.2 : Int) + 1) 0)
        | other  => other.toBool
      some (if keep then acc ++ [x.1] else acc)) []) cands

/-- §3.4 comparison. The node-set cases are EXISTENTIAL. -/
partial def cmpValues (op : String) (x y : Value) : Bool :=
  if isValueOp op then valueCmp op x y else
  let strsOf (v : Value) : Option (List String) :=
    match v with
    | .nodes ns => some ((normalize ns).map (·.stringValue))
    | _         => none
  match strsOf x, strsOf y with
  | some a, some b => a.any (fun s => b.any (fun t => scalarCmp op (.str s) (.str t)))
  | some a, none   => a.any (fun s => scalarCmp op (.str s) y)
  | none,   some b => b.any (fun t => scalarCmp op x (.str t))
  | none,   none   => scalarCmp op x y

/-- Comparison of two non-node-set values. `=` and `!=` convert by the
    §3.4 precedence boolean > number > string; the relational
    operators always convert to number. -/
partial def scalarCmp (op : String) (x y : Value) : Bool :=
  let isB (v : Value) := match v with | .bool _ => true | _ => false
  let isN (v : Value) := match v with | .num _ => true | _ => false
  if op == "=" || op == "!=" then
    let same :=
      if isB x || isB y then x.toBool == y.toBool
      else if isN x || isN y then Num.eq x.toNum y.toNum
      else x.toStr == y.toStr
    if op == "=" then same else !same
  else
    let m := x.toNum
    let n := y.toNum
    if op == "<" then Num.lt m n
    else if op == "<=" then Num.le m n
    else if op == ">" then Num.lt n m
    else Num.le n m

partial def evalCall (c : Ctx) (f : String) (args : List Expr) : Option Value := do
  let vals ← args.foldlM (fun acc a => (evalExpr c a).map (fun v => acc ++ [v])) []
  let s0 : String := match vals.head? with
    | some v => v.toStr
    | none   => c.item.stringValue
  let n0 : Num := match vals.head? with
    | some v => v.toNum
    | none   => Num.ofString c.item.stringValue
  let firstNode : Option Item := match vals with
    | []          => some c.item
    | [.nodes ns] => (normalize ns).head?
    | _           => none
  match f, vals with
  | "last", _      => some (.num (.finite (c.size : Int) 0))
  | "position", _  => some (.num (.finite (c.pos : Int) 0))
  | "true", _      => some (.bool true)
  | "false", _     => some (.bool false)
  | "current", _   => some (.nodes [c.item])
  | "count", [.nodes ns] => some (.num (.finite ((normalize ns).length : Int) 0))
  | "sum", [.nodes ns] =>
      some (.num ((normalize ns).foldl (fun acc i =>
        Num.add acc (Num.ofString i.stringValue)) (Num.finite 0 0)))
  | "id", [v] =>
      let refs := match v with
        | .nodes ns => (normalize ns).flatMap (fun i => splitWs i.stringValue)
        | other     => splitWs other.toStr
      some (.nodes (resolveIds c.doc refs))
  | "local-name", _ =>
      some (.str (match firstNode with | some i => localOf i.qname | none => ""))
  | "name", _ =>
      some (.str (match firstNode with | some i => i.qname | none => ""))
  | "namespace-uri", _ =>
      some (.str (match firstNode with
        | some i => (expandedName c.doc i).1
        | none   => ""))
  | "generate-id", _ =>
      some (.str (match firstNode with
        | some i => "id" ++ String.intercalate "-"
            (i.loc.key.map (fun k => if k < 0 then "n" ++ toString (-k) else toString k))
        | none   => ""))
  | "string", _          => some (.str s0)
  | "number", _          => some (.num n0)
  | "boolean", [v]       => some (.bool v.toBool)
  | "not", [v]           => some (.bool (!v.toBool))
  | "string-length", _   => some (.num (.finite (s0.toList.length : Int) 0))
  | "normalize-space", _ => some (.str (normalizeSpaceStr s0))
  | "concat", _          => some (.str (String.join (vals.map (·.toStr))))
  | "starts-with", [a, b] => some (.bool (a.toStr.startsWith b.toStr))
  | "contains", [a, b]   => some (.bool (substrIndex a.toStr b.toStr).isSome)
  | "substring-before", [a, b] =>
      some (.str (match substrIndex a.toStr b.toStr with
        | some i => String.ofList (a.toStr.toList.take i)
        | none   => ""))
  | "substring-after", [a, b] =>
      some (.str (match substrIndex a.toStr b.toStr with
        | some i => String.ofList (a.toStr.toList.drop (i + b.toStr.toList.length))
        | none   => ""))
  | "substring", [a, b] =>
      some (.str (match Num.roundN b.toNum with
        | .finite m 0 => substrChars a.toStr m 1000000000
        | _           => ""))
  | "substring", [a, b, l] =>
      some (.str (match Num.roundN b.toNum, Num.roundN l.toNum with
        | .finite m 0, .finite k 0 => substrChars a.toStr m k
        | _, _                     => ""))
  | "translate", [a, b, cc] => some (.str (translateStr a.toStr b.toStr cc.toStr))
  | "floor", [v]   => some (.num (Num.floorN v.toNum))
  | "ceiling", [v] => some (.num (Num.ceilingN v.toNum))
  | "round", [v]   => some (.num (Num.roundN v.toNum))
  | "lang", [v] =>
      -- §4.3: the nearest `xml:lang` on the node or an ancestor,
      -- matched case-insensitively, with a hyphenated suffix allowed.
      let want := v.toStr.toLower
      let chain := c.item :: ancestorsOf c.doc c.item
      let found := chain.findSome? (fun i =>
        (attributesOf i).findSome? (fun a =>
          match a with
          | .attr _ t => if t.name == "xml:lang" then some t.value.toLower else none
          | _         => none))
      some (.bool (match found with
        | some l => l == want || l.startsWith (want ++ "-")
        | none   => false))
  | "function-available", [v] => some (.bool (knownFunctions.contains v.toStr))
  | "element-available", [v]  => some (.bool (availableElements.contains v.toStr))
  | "system-property", [v] =>
      some (.str (if v.toStr == "xsl:version" then "1.0"
                  else if v.toStr == "xsl:vendor" then "Factoidal"
                  else if v.toStr == "xsl:vendor-url" then "https://github.com/danbri/factoidal"
                  else ""))
  | "document", [v] =>
      -- `document('')` is the stylesheet's own tree. Any other URI is
      -- answered from `c.docs`, which the caller supplies; a URI that
      -- is not there is `none`, so the transform is REFUSED rather
      -- than run against an empty tree.
      if v.toStr == "" then (c.self?.map (fun d => Value.nodes [Item.doc d]))
      else ((c.docs.find? (fun (u, _) => u == v.toStr)).map
             (fun (_, d) => Value.nodes [Item.doc d]))
  | _, _ => none

end

/-- Evaluate a parsed expression. -/
def eval (c : Ctx) (e : Expr) : Option Value := evalExpr c e

/-- Parse and evaluate. -/
def evalText (c : Ctx) (s : String) : Option Value := do
  let e ← parseExpr s
  evalExpr c e

end L4Factoidal.XPath.Full
