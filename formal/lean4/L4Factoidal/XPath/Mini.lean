/-
L4Factoidal.XPath.Mini — the XPath 1.0 SUBSET a Schematron `@test` and
`@context` need, evaluated over the project's own XML tree.

## This is a subset, and here is exactly which one

Grammar accepted, in full:

    Expr    ::= OrExpr
    OrExpr  ::= AndExpr ('or' AndExpr)*
    AndExpr ::= CmpExpr ('and' CmpExpr)*
    CmpExpr ::= Primary (('='|'!='|'<='|'>='|'<'|'>') Primary)?
    Primary ::= Number | Literal | FnCall | Path | '(' Expr ')'
    FnCall  ::= Name '(' (Expr (',' Expr)*)? ')'
    Path    ::= '@' Name | Step ('/' Step)*
    Step    ::= (Axis '::')? (Name | '*')
    Axis    ::= 'child' | 'self' | 'attribute' | 'preceding-sibling'
              | 'following-sibling' | 'parent'

Functions: `count`, `not`, `true`, `false`, `string-length`,
`normalize-space`, `string`, `number`, `local-name`, `name`.

ANYTHING ELSE IS `undecided`, never `false`. A test the evaluator
cannot read must not be reported as a violation nor as a pass — which
is exactly what `Schematron.TestResult.undecided` is for, and why that
constructor carries its reason.

## Numbers are exact

Comparisons go through `Int`, not a float. Every number the Schematron
corpus compares is a count or a small literal; a float would be a
gratuitous approximation on a path where the values are integers by
construction.

## Nodes are addressed by PATH

`Schematron.Validate` speaks of nodes as `String`s, deliberately —
its `select` and `evalTest` are parameters, so the node
representation is the caller's business. This module uses a
`/name[i]/name[j]` path, which is stable, readable in a finding, and
enough to walk back to the node.
-/
import L4Factoidal.XML.Document

namespace L4Factoidal.XPath

open L4Factoidal.XML

/-! ## Addressing nodes by path -/

/-- The element children of a node. -/
def elemChildren : Node → List Node
  | .element _ _ cs => cs.filter (fun c => match c with
      | .element _ _ _ => true | _ => false)
  | _ => []

def tagOf : Node → String
  | .element t _ _ => t
  | _ => ""

def attrsOf : Node → List Attribute
  | .element _ a _ => a
  | _ => []

mutual

/-- All element paths in a document, in document order. The root is
    `/tag[1]`.

    A mutual pair with `allPathsChildren`, over the LITERAL `children`
    field of `.element`, in the `checkElement` / `checkChildren` idiom
    (`XML.Namespaces`) — Lean's nested-inductive structural recursion
    accepts this shape with no `termination_by`. The previous
    single-declaration form first filtered to `elemChildren n`, then for each
    element at position `i` counted same-tag elements in
    `kids.take i`; that filtered list broke automatic structural
    recursion (`allPaths p c` was a call on a value reached through
    `.filter`/`.map`, not a matched constructor field), and gave no
    proof obligation smaller than `n` for `c`. `allPathsChildren`
    below walks the RAW children instead and keeps `seen`, the tags of
    already-visited ELEMENT children in order; `(seen.filter
    (· == tag)).length` at an element counts exactly the same
    same-tag predecessors `kids.take i |>.filter (tagOf · ==
    tag)` did, since `seen` only ever grows on an element child and
    `kids` was the raw children with non-elements dropped in the same
    left-to-right order. -/
def allPaths (prefix' : String) (n : Node) : List String :=
  match n with
  | .element _ _ cs => allPathsChildren prefix' [] cs
  | _               => []

/-- `allPaths`'s children walk. `seen` carries the tag of every
    ELEMENT child of the same parent visited so far, left to right;
    non-element children are skipped without extending `seen` or
    emitting a path, matching `elemChildren`'s filter. -/
def allPathsChildren (prefix' : String) (seen : List String)
    : List Node → List String
  | []      => []
  | c :: rest =>
      match c with
      | .element tag _ _ =>
          let sameBefore := (seen.filter (· == tag)).length
          let p := prefix' ++ "/" ++ tag ++ "[" ++ toString (sameBefore + 1) ++ "]"
          (p :: allPaths p c) ++ allPathsChildren prefix' (seen ++ [tag]) rest
      | _ => allPathsChildren prefix' seen rest

end

/-- The document's element paths, root included. -/
def documentPaths (root : Node) : List String :=
  let rootPath := "/" ++ tagOf root ++ "[1]"
  rootPath :: allPaths rootPath root

/-- Split a path into its `(tag, index)` steps. -/
def pathSteps (p : String) : List (String × Nat) :=
  (p.splitOn "/").filterMap (fun seg =>
    if seg == "" then none
    else match seg.splitOn "[" with
      | [t, idx] => some (t, ((String.ofList (idx.toList.dropLast)).toNat?).getD 1)
      | [t]      => some (t, 1)
      | _        => none)

/-- The node a path names, its POSITION among its parent's element
    children, and its ANCESTOR chain (nearest first), each ancestor
    paired with its own such position.

    The position is not decoration. XPath's sibling axes need to know
    WHICH child the context node is, and two sibling elements can be
    structurally identical — `<row/><row/>` is the corpus's own case.
    Locating the context node by structural equality made the second
    `row` look like the first, so `preceding-sibling::row` counted
    zero for both and the assertion never fired (schematron
    `preceding-sibling-reverse-axis`). An index is IDENTITY here; a
    value comparison is not. -/
def resolvePath (root : Node) (p : String)
    : Option (Node × Nat × List (Node × Nat)) :=
  match pathSteps p with
  | []            => none
  | (t, i) :: rest =>
      if tagOf root != t || i != 1 then none
      else
        let rec walk (n : Node) (ix : Nat) (anc : List (Node × Nat))
            : List (String × Nat) → Option (Node × Nat × List (Node × Nat))
          | []            => some (n, ix, anc)
          | (t2, j) :: tl =>
              let sibs := ((elemChildren n).zipIdx).filter (fun (c, _) => tagOf c == t2)
              match sibs[j - 1]? with
              | some (c, ci) => walk c ci ((n, ix) :: anc) tl
              | none         => none
        walk root 0 [] rest

/-! ## The expression language -/

inductive Axis where
  | child | self | attribute | precedingSibling | followingSibling | parent
deriving Repr, DecidableEq, Inhabited

structure Step where
  axis : Axis
  test : String     -- a name, or `*`
deriving Repr, Inhabited

inductive XExpr where
  | num   (n : Int)
  | str   (s : String)
  | call  (fn : String) (args : List XExpr)
  | path  (steps : List Step)
  | binop (op : String) (a b : XExpr)
deriving Repr, Inhabited

/-! ## Parsing -/

private def isNameC (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == ':'

private def skipWs (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)

/-- `[5] Name`, stopping BEFORE an axis separator.

    `:` is a name character — a QName writes `sch:pattern` — but `::`
    is the axis separator, and a plain `takeWhile isNameC` cannot tell
    the two apart. It read `preceding-sibling::row` as ONE name, which
    then parsed as a child step whose element name happened to contain
    a colon. Nothing in the document matched that name, so
    `count(...)` returned 0, `0 < 1` was TRUE, and the assertion that
    should have fired reported a clean document instead
    (schematron `preceding-sibling-reverse-axis`). A misparse that
    yields a DEFINITE answer is worse than one that refuses: the
    refusal is counted as undecided, the wrong answer is counted as a
    pass. -/
private def takeNameGo (acc : List Char) : List Char → String × List Char
  | []      => (String.ofList acc.reverse, [])
  | c :: rest =>
      if c == ':' && (rest.head?.map (· == ':')).getD false then
        (String.ofList acc.reverse, c :: rest)
      else if isNameC c then takeNameGo (c :: acc) rest
      else (String.ofList acc.reverse, c :: rest)

private def takeName (cs : List Char) : String × List Char := takeNameGo [] cs

def axisOf (s : String) : Option Axis :=
  if s == "child" then some .child
  else if s == "self" then some .self
  else if s == "attribute" then some .attribute
  else if s == "preceding-sibling" then some .precedingSibling
  else if s == "following-sibling" then some .followingSibling
  else if s == "parent" then some .parent
  else none

/- The six functions below (`pOr` through `pPathFrom`) stay `partial`.
   They are a precedence-climbing recursive-descent parser: `pOr`
   delegates to `pAnd`, `pAnd` to `pCmp`, `pCmp` to `pPrimary`, and
   `pArgs` to `pOr`, each on the SAME remaining `cs` before any
   character is read. A well-founded `termination_by`/`decreasing_by`
   proof can rank that first, same-length delegation by a fixed
   priority (`pArgs` > `pOr` > `pAnd` > `pCmp` > `pPrimary`), and every
   call that itself reads a character (`'(' :: r`, `.drop 1`, `.drop
   2`, `takeName`) decreases structurally on its own.

   The blocker is `pOr`'s SECOND call, `pOr (r.drop 2)`, taken after
   `pAnd cs` returns `some (a, r)` and `r` starts with `"or"`. Its
   decrease obligation is `(r.drop 2).length < cs.length`, which needs
   `r.length ≤ cs.length` — a fact about what `pAnd` RETURNS. `pAnd` is
   a sibling in the SAME mutual clique whose own termination is not
   yet established at the point its decrease obligations are checked,
   so no theorem about its output is available to cite (proving one
   requires `pAnd` to already be defined, which requires the whole
   clique's termination, which is what this proof is for). `pAnd`'s
   parallel call into `pCmp`, and `pArgs`'s call into `pOr`, are the
   same shape. This is not a proof-effort gap; it is the standard
   result that call-graph well-founded recursion cannot rank a "used
   how much of the input did my sibling consume" edge.

   The fix in this repository's own style is method 3 of GitHub issue
   https://github.com/danbri/factoidal/issues/617: add a `fuel : Nat`
   parameter that every one of the six functions decrements on ENTRY
   (unconditionally, so termination is by that Nat alone and needs no
   fact about any sibling), keep the six definitions here as
   `pOrSpec`/`pAndSpec`/... in the style of
   `L4Factoidal/Syntax/TurtleFuelTheorems.lean`, and prove the fueled
   and spec forms agree whenever `fuel ≥ cs.length` (a mutual
   induction over the six functions together, since the equivalence
   claim for one calls the others). Not attempted in this landing —
   the six proofs plus their mutual induction are a session-sized
   piece of work on their own. -/
mutual

/-- `OrExpr`. -/
partial def pOr (cs : List Char) : Option (XExpr × List Char) :=
  match pAnd cs with
  | none => none
  | some (a, r) =>
      let r := skipWs r
      if (String.ofList (r.take 2)) == "or" then
        match pOr (r.drop 2) with
        | some (b, r2) => some (.binop "or" a b, r2)
        | none         => none
      else some (a, r)

partial def pAnd (cs : List Char) : Option (XExpr × List Char) :=
  match pCmp cs with
  | none => none
  | some (a, r) =>
      let r := skipWs r
      if (String.ofList (r.take 3)) == "and" then
        match pAnd (r.drop 3) with
        | some (b, r2) => some (.binop "and" a b, r2)
        | none         => none
      else some (a, r)

partial def pCmp (cs : List Char) : Option (XExpr × List Char) :=
  match pPrimary cs with
  | none => none
  | some (a, r) =>
      let r := skipWs r
      let two := String.ofList (r.take 2)
      let one := String.ofList (r.take 1)
      if two == "!=" || two == "<=" || two == ">=" then
        match pPrimary (r.drop 2) with
        | some (b, r2) => some (.binop two a b, r2)
        | none         => none
      else if one == "=" || one == "<" || one == ">" then
        match pPrimary (r.drop 1) with
        | some (b, r2) => some (.binop one a b, r2)
        | none         => none
      else some (a, r)

partial def pArgs (cs : List Char) (acc : List XExpr)
    : Option (List XExpr × List Char) :=
  let cs := skipWs cs
  match cs with
  | ')' :: r => some (acc, r)
  | _ =>
      match pOr cs with
      | none => none
      | some (e, r) =>
          let r := skipWs r
          match r with
          | ',' :: r2 => pArgs r2 (acc ++ [e])
          | ')' :: r2 => some (acc ++ [e], r2)
          | _         => none

partial def pPrimary (cs : List Char) : Option (XExpr × List Char) :=
  let cs := skipWs cs
  match cs with
  | [] => none
  | '(' :: r =>
      (match pOr r with
       | some (e, r2) => (match skipWs r2 with
           | ')' :: r3 => some (e, r3)
           | _         => none)
       | none => none)
  | '\'' :: r =>
      let body := r.takeWhile (· != '\'')
      some (.str (String.ofList body), (r.dropWhile (· != '\'')).drop 1)
  | '"' :: r =>
      let body := r.takeWhile (· != '"')
      some (.str (String.ofList body), (r.dropWhile (· != '"')).drop 1)
  | '@' :: r =>
      let (nm, r2) := takeName r
      some (.path [{ axis := .attribute, test := nm }], r2)
  | c :: _ =>
      if c.isDigit then
        let ds := cs.takeWhile (·.isDigit)
        some (.num ((String.ofList ds).toInt?.getD 0), cs.dropWhile (·.isDigit))
      else if c == '*' then some (.path [{ axis := .child, test := "*" }], cs.drop 1)
      else if isNameC c then
        let (nm, r) := takeName cs
        match skipWs r with
        | '(' :: r2 =>
            (match pArgs r2 [] with
             | some (args, r3) => some (.call nm args, r3)
             | none            => none)
        | _ => pPathFrom nm r
      else none

/-- A location path whose first name has already been read. -/
partial def pPathFrom (first : String) (cs : List Char)
    : Option (XExpr × List Char) :=
  let step0 : Step × List Char :=
    if (String.ofList (cs.take 2)) == "::" then
      match axisOf first with
      | some ax =>
          let (nm, r) := takeName (cs.drop 2)
          ({ axis := ax, test := nm }, r)
      | none => ({ axis := .child, test := first }, cs)
    else ({ axis := .child, test := first }, cs)
  let rec more (acc : List Step) (r : List Char) : List Step × List Char :=
    match r with
    | '/' :: r2 =>
        let (nm, r3) := takeName r2
        if (String.ofList (r3.take 2)) == "::" then
          match axisOf nm with
          | some ax =>
              let (nm2, r4) := takeName (r3.drop 2)
              more (acc ++ [{ axis := ax, test := nm2 }]) r4
          | none => (acc, r)
        else if nm == "" then
          (match r2 with
           | '*' :: r3' => more (acc ++ [{ axis := .child, test := "*" }]) r3'
           | _          => (acc, r))
        else more (acc ++ [{ axis := .child, test := nm }]) r3
    | _ => (acc, r)
  let (steps, rest) := more [step0.1] step0.2
  some (.path steps, rest)

end

def parseXPath (s : String) : Option XExpr :=
  match pOr s.toList with
  | some (e, r) => if (skipWs r).isEmpty then some e else none
  | none        => none

/-! ## Evaluation -/

/-- A value. `nodes` carries elements; `attrs` carries attribute
    VALUES, which XPath treats as string-valued nodes. -/
inductive XVal where
  | nodes (ns : List Node)
  | attrs (vs : List String)
  | num   (n : Int)
  | str   (s : String)
  | bool  (b : Bool)
deriving Inhabited

mutual

/-- The string-value of an element: its character data, descendants
    included. Written as a mutual pair with `stringValueChildren` over
    the LITERAL `children` field, matching the `checkElement` /
    `checkChildren` idiom in `XML.Namespaces` — Lean's nested-inductive
    structural recursion sees straight through that shape with no
    `termination_by`. The previous single declaration folded with
    `cs.foldl (fun acc c => acc ++ stringValue c) ""`, which is the
    same left-to-right concatenation `stringValueChildren` performs
    below. -/
def stringValue : Node → String
  | .element _ _ cs => stringValueChildren cs
  | .text t         => t
  | .cdata t        => t
  | _               => ""

def stringValueChildren : List Node → String
  | []          => ""
  | c :: rest   => stringValue c ++ stringValueChildren rest

end

/-- One axis step. Node results keep each node's POSITION among its
    parent's element children, so the next step's sibling axes can
    address it; `Sum.inr` carries attribute VALUES, which have no
    position. -/
def stepIndexed (ctx : Node) (ctxIdx : Nat) (anc : List (Node × Nat)) (st : Step)
    : List (Node × Nat) ⊕ List String :=
  let nameOk := fun (n : Node) => st.test == "*" || tagOf n == st.test
  match st.axis with
  | .child     => .inl (((elemChildren ctx).zipIdx).filter (fun (n, _) => nameOk n))
  | .self      => .inl (if nameOk ctx then [(ctx, ctxIdx)] else [])
  | .parent    => .inl (match anc.head? with
                        | some (p, pi) => if nameOk p then [(p, pi)] else []
                        | none         => [])
  | .attribute => .inr ((attrsOf ctx).filterMap (fun a =>
                    if st.test == "*" || a.name == st.test then some a.value else none))
  | .precedingSibling | .followingSibling =>
      match anc.head? with
      | none        => .inl []
      | some (p, _) =>
          let sibs := (elemChildren p).zipIdx
          let side := if st.axis == .precedingSibling
                      then sibs.filter (fun (_, i) => i < ctxIdx)
                      else sibs.filter (fun (_, i) => i > ctxIdx)
          .inl (side.filter (fun (n, _) => nameOk n))

/-- Walk a location path from the context node. -/
def evalPath (ctx : Node) (ctxIdx : Nat) (anc : List (Node × Nat))
    : List Step → XVal
  | []      => .nodes [ctx]
  | st :: t =>
      match stepIndexed ctx ctxIdx anc st with
      | .inr vs => .attrs vs
      | .inl ns =>
          if t.isEmpty then .nodes (ns.map (·.1))
          else
            .nodes (ns.flatMap (fun (n, i) =>
              match evalPath n i ((ctx, ctxIdx) :: anc) t with
              | .nodes ms => ms
              | _         => []))

def toBool : XVal → Bool
  | .nodes ns => !ns.isEmpty
  | .attrs vs => !vs.isEmpty
  | .num n    => n != 0
  | .str s    => !s.isEmpty
  | .bool b   => b

def toNum : XVal → Option Int
  | .num n    => some n
  | .str s    => s.toInt?
  | .bool b   => some (if b then 1 else 0)
  | .nodes ns => (ns.head?.map stringValue).bind (·.toInt?)
  | .attrs vs => vs.head?.bind (·.toInt?)

def toStrs : XVal → List String
  | .nodes ns => ns.map stringValue
  | .attrs vs => vs
  | .num n    => [toString n]
  | .str s    => [s]
  | .bool b   => [if b then "true" else "false"]

/-- An evaluation either yields a value or REFUSES with a reason. -/
inductive XOut where
  | val  (v : XVal)
  | undecided (reason : String)
deriving Inhabited

mutual

/-- Evaluate an expression. A mutual pair with `evalArgs` over the
    LITERAL `args` field of `.call`, in the same idiom as `allPaths` /
    `allPathsChildren` above and `checkElement` / `checkChildren` in
    `XML.Namespaces` — Lean's nested-inductive structural recursion
    accepts this shape with no `termination_by`. The previous single
    declaration computed `args.map (eval ctx ctxIdx anc)`, which is
    the same left-to-right per-argument evaluation `evalArgs`
    performs below. -/
def eval (ctx : Node) (ctxIdx : Nat) (anc : List (Node × Nat))
    : XExpr → XOut
  | .num n => .val (.num n)
  | .str s => .val (.str s)
  | .path steps => .val (evalPath ctx ctxIdx anc steps)
  | .call fn args =>
      let vals := evalArgs ctx ctxIdx anc args
      if vals.any (fun v => match v with | .undecided _ => true | _ => false) then
        .undecided ("an argument of " ++ fn ++ "() was undecided")
      else
        let vs := vals.filterMap (fun v => match v with | .val x => some x | _ => none)
        if fn == "true" then .val (.bool true)
        else if fn == "false" then .val (.bool false)
        else if fn == "not" then
          (match vs with
           | [a] => .val (.bool (!(toBool a)))
           | _   => .undecided "not() takes one argument")
        else if fn == "count" then
          (match vs with
           | [.nodes ns] => .val (.num ns.length)
           | [.attrs as] => .val (.num as.length)
           | _ => .undecided "count() takes a node-set")
        else if fn == "string-length" then
          (match vs with
           | [a] => .val (.num ((toStrs a).head?.getD "").length)
           | _   => .undecided "string-length() takes one argument")
        else if fn == "local-name" || fn == "name" then
          (match vs with
           | [.nodes (n :: _)] => .val (.str (tagOf n))
           | []                => .val (.str (tagOf ctx))
           | _                 => .undecided (fn ++ "() takes a node-set"))
        else .undecided ("function " ++ fn ++ "() is outside this subset")
  | .binop op a b =>
      match eval ctx ctxIdx anc a, eval ctx ctxIdx anc b with
      | .undecided r, _ => .undecided r
      | _, .undecided r => .undecided r
      | .val x, .val y =>
          if op == "and" then .val (.bool (toBool x && toBool y))
          else if op == "or" then .val (.bool (toBool x || toBool y))
          else
            -- A comparison is NUMERIC when both sides read as numbers,
            -- and a string comparison otherwise. XPath 1.0's rule for
            -- node-sets is existential: the comparison holds when SOME
            -- member satisfies it.
            match toNum x, toNum y with
            | some m, some n =>
                .val (.bool (if op == "=" then m == n
                             else if op == "!=" then m != n
                             else if op == "<" then m < n
                             else if op == ">" then m > n
                             else if op == "<=" then m ≤ n
                             else m ≥ n))
            | _, _ =>
                let xs := toStrs x
                let ys := toStrs y
                if op == "=" then .val (.bool (xs.any (fun s => ys.contains s)))
                else if op == "!=" then .val (.bool (xs.any (fun s => !(ys.contains s))))
                else .undecided "an ordering comparison on non-numbers"

/-- `eval`'s per-argument walk over `.call`'s literal `args` field. -/
def evalArgs (ctx : Node) (ctxIdx : Nat) (anc : List (Node × Nat))
    : List XExpr → List XOut
  | []        => []
  | a :: rest => eval ctx ctxIdx anc a :: evalArgs ctx ctxIdx anc rest

end

/-- Evaluate a `@test` at a node named by `path`, for
    `Schematron.Validate`'s `evalTest` parameter. -/
def evalTestAt (root : Node) (test path : String) : Option Bool ⊕ String :=
  match parseXPath test with
  | none => .inr ("the expression is outside this XPath subset: " ++ test)
  | some e =>
      match resolvePath root path with
      | none => .inr ("no node at " ++ path)
      | some (n, ix, anc) =>
          match eval n ix anc e with
          | .undecided r => .inr r
          | .val v       => .inl (some (toBool v))

/-- Does a Schematron `@context` pattern select the node at `path`?
    The corpus's contexts are a name or `*`; a compound pattern is
    matched on its LAST step, which is what a Schematron context
    means. -/
def contextSelects (root : Node) (pattern path : String) : Bool :=
  match resolvePath root path with
  | none => false
  | some (n, _, _) =>
      let last := (pattern.splitOn "/").getLast?.getD pattern
      last == "*" || tagOf n == last

end L4Factoidal.XPath
