/-
L4Factoidal.XForms.Bind — the XForms model layer: Model Item
Properties, a dependency graph over `calculate` expressions, and a
pure recalculation.

Port of `formal/fstar/XForms.Bind.fst`. Spec: XForms 1.1
(https://www.w3.org/TR/xforms11/) §6.2.1 (`type`), §7.3 (bind), §7.4
(`relevant`), §7.5 (`required`), §7.6 (`calculate` and the
recalculation order), §7.7 (`constraint`), §7.8 (`readonly`).

## Scope: the spreadsheet half of XForms, and nothing else

An XML instance plus a bind sheet plus a dependency graph plus a pure
recalculation. No UI controls, no XML Events, no submission. This is
deliberately NOT conformant XForms — it is the reactive computation
core, and calling it anything more would be a claim the module cannot
support.

## Cycle rejection IS the termination argument

`topoPass` is Kahn's algorithm as a fold over the not-yet-emitted
set. Each pass emits every node whose predecessors are already
emitted, then recurses on the strict remainder. A CYCLIC `calculate`
graph has no in-degree-zero node among the remainder, so the ready
set is empty and the function returns `none` WITHOUT recursing. Cycle
detection is not a runtime counter bolted on the side; it is the
shape of the recursion. XForms §7.6.1 makes a `calculate` cycle a
document error, which is what `none` says.
-/
import L4Factoidal.XPath.Eval
import L4Factoidal.XML.Parser

namespace L4Factoidal.XForms

open L4Factoidal.XML
open L4Factoidal.XPath
open L4Factoidal.XPath.Full

/-! ## The `type` MIP — §6.2.1 -/

inductive MipType where
  | absent | string | boolean | integer | decimal | float | double
  /-- A QName this module does not recognise. It validates as
      INVALID: an explicit "we do not know", never a silent pass. -/
  | unsupported
deriving Repr, DecidableEq, Inhabited

def mipTypeOfQName (q : String) : MipType :=
  if q == "" then .absent
  else if q == "xsd:string"  || q == "xs:string"  then .string
  else if q == "xsd:boolean" || q == "xs:boolean" then .boolean
  else if q == "xsd:integer" || q == "xs:integer" then .integer
  else if q == "xsd:decimal" || q == "xs:decimal" then .decimal
  else if q == "xsd:float"   || q == "xs:float"   then .float
  else if q == "xsd:double"  || q == "xs:double"  then .double
  else .unsupported

private def isDigitC (c : Char) : Bool := '0' <= c && c <= '9'

private def dropSign (cs : List Char) : List Char :=
  match cs with
  | '+' :: r => r
  | '-' :: r => r
  | r        => r

private def signedDigits (cs : List Char) : Bool :=
  let r := dropSign cs
  !r.isEmpty && r.all isDigitC

/-- XSD `integer`: an optional sign, then digits. -/
def isIntegerLexical (s : String) : Bool := signedDigits s.toList

/-- XSD `decimal`: an optional sign, then digits with at most one
    point and at least one digit. -/
def isDecimalLexical (s : String) : Bool :=
  let cs := dropSign s.toList
  match cs.splitOn '.' with
  | [ip]     => !ip.isEmpty && ip.all isDigitC
  | [ip, fp] => (!ip.isEmpty || !fp.isEmpty) && ip.all isDigitC && fp.all isDigitC
  | _        => false

/-- XSD `float` and `double`: a decimal with an optional exponent, or
    one of the three special values. Those three are VALUES of the
    type, not error states, so a check that rejected them would reject
    a legal document. -/
def isFloatLexical (s : String) : Bool :=
  if s == "NaN" || s == "INF" || s == "-INF" then true
  else
    match s.toList.findIdx? (fun c => c == 'e' || c == 'E') with
    | none   => isDecimalLexical s
    | some i =>
        isDecimalLexical (String.ofList (s.toList.take i)) &&
        signedDigits (s.toList.drop (i + 1))

def typeWellformed (t : MipType) (lex : String) : Bool :=
  match t with
  | .absent | .string => true
  | .boolean => lex == "true" || lex == "false" || lex == "0" || lex == "1"
  | .integer => isIntegerLexical lex
  | .decimal => isDecimalLexical lex
  | .float | .double => isFloatLexical lex
  | .unsupported => false

/-! ## The bind — §7.3

A bind targets ONE named leaf element of a flat instance root, which
is the shape a headless engine receives. Nested binds and repeats are
out of scope. Each MIP is an XPath expression evaluated with the bound
leaf as the context node, so `.` denotes the node's own value and a
sibling is reached by `../name`. -/

structure Bind where
  id         : String := ""
  /-- The leaf element name — the `nodeset`. -/
  target     : String
  calculate  : Option String := none
  constraint : Option String := none
  relevant   : Option String := none
  required   : Option String := none
  readonly   : Option String := none
  mipType    : MipType := .absent
deriving Repr, Inhabited

/-! ## Instance access -/

def tagOf : Node → String
  | .element t _ _ => t
  | _              => ""

def elemChildrenOf : Node → List Node
  | .element _ _ ks => ks.filter (fun k => match k with | .element .. => true | _ => false)
  | _ => []

def findLeafIndex (root : Node) (name : String) : Option Nat :=
  match root with
  | .element _ _ ks => ks.findIdx? (fun k => tagOf k == name)
  | _               => none

def getLeafText (root : Node) (name : String) : String :=
  match root with
  | .element _ _ ks =>
      match ks.find? (fun k => tagOf k == name) with
      | some n => nodeText n
      | none   => ""
  | _ => ""

/-- Replace the FIRST child element named `name` with one carrying a
    single text child. Pure: a new tree, nothing mutated. -/
def setLeafText (root : Node) (name : String) (v : String) : Node :=
  let rec go : List Node → List Node
    | []     => []
    | h :: r =>
        match h with
        | .element t a _ => if t == name then .element t a [.text v] :: r else h :: go r
        | _              => h :: go r
  match root with
  | .element tag attrs ks => .element tag attrs (go ks)
  | other                 => other

/-! ## Evaluating a MIP -/

/-- The document a MIP expression runs against: one document node
    whose single child is the instance root. -/
def instanceDoc (root : Node) : Doc := [root]

/-- Evaluate a MIP expression with the bound LEAF as the context node.
    `none` when the leaf is absent or the expression does not parse —
    both are a document error to the caller, never a value. -/
def evalMipValue (root : Node) (target : String) (expr : String) : Option Value :=
  match findLeafIndex root target with
  | none   => none
  | some k =>
      match (kidsOf root)[k]? with
      | none      => none
      | some leaf =>
          evalText { doc := instanceDoc root,
                     item := .tree { path := [0, k] } leaf } expr

/-! ## Dependencies — §7.6.1

Bind B depends on bind B' when B's `calculate` READS the node B'
computes: `B'.target` occurs as a NAME TEST inside B's parsed
expression. Names are collected structurally from the AST, never by
scanning the expression text, so a substring of some other token
cannot forge an edge. -/

mutual

partial def namesOfExpr : Expr → List String
  | .path _ st steps =>
      (match st with | some e => namesOfExpr e | none => []) ++ namesOfSteps steps
  | .filter b preds  => namesOfExpr b ++ preds.flatMap namesOfExpr
  | .union a b       => namesOfExpr a ++ namesOfExpr b
  | .or a b          => namesOfExpr a ++ namesOfExpr b
  | .and a b         => namesOfExpr a ++ namesOfExpr b
  | .cmp _ a b       => namesOfExpr a ++ namesOfExpr b
  | .arith _ a b     => namesOfExpr a ++ namesOfExpr b
  | .negate a        => namesOfExpr a
  | .call _ args     => args.flatMap namesOfExpr
  | .num _ | .str _ | .varRef _ => []

partial def namesOfSteps : List Step → List String
  | []     => []
  | s :: r =>
      (match s.test with
       | .name n => [n]
       | _       => []) ++ s.preds.flatMap namesOfExpr ++ namesOfSteps r

end

def allTargets (bs : List Bind) : List String := bs.map (·.target)

def calcNames (b : Bind) : List String :=
  match b.calculate with
  | none   => []
  | some c => match parseExpr c with
      | none   => []
      | some e => namesOfExpr e

/-- The targets a bind's `calculate` reads. A reference to a raw
    source leaf imposes no ordering, so only names that are themselves
    some bind's target count. A reference to the bind's OWN target is
    kept deliberately: it is a self-cycle, and `topoPass` rejects
    it. -/
def predsOf (bs : List Bind) (b : Bind) : List String :=
  let tgts := allTargets bs
  (calcNames b).filter (fun n => tgts.contains n)

structure GraphNode where
  bind  : Bind
  preds : List String
deriving Repr, Inhabited

def buildGraph (bs : List Bind) : List GraphNode :=
  bs.map (fun b => { bind := b, preds := predsOf bs b })

def nodeReady (emitted : List String) (g : GraphNode) : Bool :=
  g.preds.all (fun p => emitted.contains p)

/-- Kahn's algorithm. The ONLY recursive call is on the not-ready
    remainder, which is strictly shorter whenever the ready set is
    non-empty; a cyclic graph makes the ready set empty and returns
    `none` without recursing. -/
def topoPass : List GraphNode → List String → Nat → Option (List Bind)
  | [],        _,       _     => some []
  | _ :: _,    _,       0     => none
  | remaining, emitted, f + 1 =>
      let ready := remaining.filter (nodeReady emitted)
      let notReady := remaining.filter (fun g => !(nodeReady emitted g))
      if ready.isEmpty then none            -- a cyclic calculate graph
      else
        match topoPass notReady (emitted ++ ready.map (·.bind.target)) f with
        | none      => none
        | some rest => some (ready.map (·.bind) ++ rest)

/-- The binds in recalculation order, or `none` when the `calculate`
    graph has a cycle — a document error under §7.6.1. -/
def topoSort (bs : List Bind) : Option (List Bind) :=
  topoPass (buildGraph bs) [] (bs.length + 1)

/-! ## Recalculation — §7.6 -/

/-- Apply each bind's `calculate` in dependency order, threading the
    updated instance so a later `calculate` sees earlier results. A
    `calculate` that does not evaluate is a document error. -/
def applyCalcs : List Bind → Node → Option Node
  | [],     x => some x
  | b :: r, x =>
      match b.calculate with
      | none   => applyCalcs r x
      | some c => match evalMipValue x b.target c with
          | none   => none
          | some v => applyCalcs r (setLeafText x b.target v.toStr)

/-! ## The validity report — §6.2.1, §7.4, §7.5, §7.7, §7.8 -/

structure NodeValidity where
  target     : String
  value      : String
  typeValid  : Bool
  constraint : Bool
  relevant   : Bool
  required   : Bool
  readonly   : Bool
  valid      : Bool
deriving Repr, Inhabited

/-- A boolean MIP. An ABSENT one takes its default; an unevaluable one
    is `false`, which is the conservative reading — an expression
    nobody could evaluate must not certify a node as valid. -/
def evalBoolMip (root : Node) (target : String) (e? : Option String) (dflt : Bool)
    : Bool :=
  match e? with
  | none   => dflt
  | some e => match evalMipValue root target e with
      | none   => false
      | some v => v.toBool

def buildValidity (root : Node) (b : Bind) : NodeValidity :=
  let value := getLeafText root b.target
  let tv := typeWellformed b.mipType value
  let cons := evalBoolMip root b.target b.constraint true
  let rel  := evalBoolMip root b.target b.relevant true
  let req  := evalBoolMip root b.target b.required false
  let ro   := evalBoolMip root b.target b.readonly false
  let requiredOk := !req || value.length > 0
  -- §7.4: a NON-RELEVANT node is exempt from constraint, required and
  -- type validity. It does not contribute invalidity, which is not
  -- the same as being valid for a reason.
  { target := b.target, value := value,
    typeValid := tv, constraint := cons, relevant := rel,
    required := req, readonly := ro,
    valid := !rel || (tv && cons && requiredOk) }

/-! ## The entry points — snapshot in, snapshot out -/

/-- A full recalculation: sort by `calculate` dependencies, run the
    fold, then report validity against the RECOMPUTED instance.
    `none` exactly when the model is a document error — a `calculate`
    cycle, or a `calculate` that does not evaluate. -/
def recalculate (binds : List Bind) (x : Node)
    : Option (Node × List NodeValidity) :=
  match topoSort binds with
  | none        => none
  | some sorted =>
      match applyCalcs sorted x with
      | none   => none
      | some y => some (y, binds.map (buildValidity y))

/-- One edit: write the leaf, then recalculate. -/
def applyEdit (binds : List Bind) (x : Node) (target value : String)
    : Option (Node × List NodeValidity) :=
  recalculate binds (setLeafText x target value)

/-! ## Reading a bind sheet -/

def attrOf (attrs : List Attribute) (n : String) : Option String :=
  (attrs.find? (fun a => a.name == n)).map (·.value)

def mkBindFrom (attrs : List Attribute) (tgt : String) : Bind :=
  { id := (attrOf attrs "id").getD "",
    target := tgt,
    calculate := attrOf attrs "calculate",
    constraint := attrOf attrs "constraint",
    relevant := attrOf attrs "relevant",
    required := attrOf attrs "required",
    readonly := attrOf attrs "readonly",
    mipType := match attrOf attrs "type" with
      | some q => mipTypeOfQName q
      | none   => .absent }

/-- One `<bind …/>` element. `nodeset` first, then `ref`; an element
    naming neither target is not a bind and contributes nothing. -/
def decodeBind : Node → Option Bind
  | .element _ attrs _ =>
      match attrOf attrs "nodeset" with
      | some t => some (mkBindFrom attrs t)
      | none   => (attrOf attrs "ref").map (mkBindFrom attrs)
  | _ => none

def decodeBinds (container : Node) : List Bind :=
  (elemChildrenOf container).filterMap decodeBind

end L4Factoidal.XForms
