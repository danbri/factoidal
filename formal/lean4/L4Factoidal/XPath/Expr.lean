/-
L4Factoidal.XPath.Expr — the XPath 1.0 EXPRESSION grammar and its
parser.

Spec: XPath 1.0 §2 (Location Paths), §3 (Expressions), Appendix A
(the grammar productions, cited by number below).

This is the whole of XPath 1.0's SYNTAX, not a subset: all thirteen
axes, all node tests, predicates on every step, the abbreviations
(`@`, `//`, `.`, `..`), unions, the four arithmetic operators,
equality and relational comparison, `and`/`or`, variable references,
function calls, and filter expressions. What is a subset is the
FUNCTION LIBRARY the evaluator implements — see `Eval.lean`, which
names every function it does not have rather than returning a wrong
value for it.

## An unparsable expression is `none`, never an empty node-set

Returning an empty node-set for an expression the parser could not
read makes a stylesheet emit nothing where it should have emitted
something, and nothing is a plausible answer. Every failure here is
`none`, and the XSLT engine turns that into a REPORTED refusal.

## `*` is a multiplication operator OR a name test

XPath resolves the ambiguity by the PRECEDING token (§3.7,
"Special-Rules for the Lexical Structure"): after a name, a number, a
literal, `)`, `]` or `*`, an asterisk is the operator; otherwise it is
the wildcard. `div`, `mod`, `and` and `or` are operator names in
exactly the same positions and element names elsewhere. Getting this
wrong turns `count(*)` into a parse error and `a*b` into a name test.
-/
import L4Factoidal.XPath.Number

namespace L4Factoidal.XPath.Full

open L4Factoidal.XPath

/-! ## Axes — `[6] AxisName` -/

inductive Ax where
  | ancestor | ancestorOrSelf | attribute | child | descendant
  | descendantOrSelf | following | followingSibling | namespace
  | parent | preceding | precedingSibling | self
deriving Repr, DecidableEq, Inhabited

def axOfName : String → Option Ax
  | "ancestor"           => some .ancestor
  | "ancestor-or-self"   => some .ancestorOrSelf
  | "attribute"          => some .attribute
  | "child"              => some .child
  | "descendant"         => some .descendant
  | "descendant-or-self" => some .descendantOrSelf
  | "following"          => some .following
  | "following-sibling"  => some .followingSibling
  | "namespace"          => some .namespace
  | "parent"             => some .parent
  | "preceding"          => some .preceding
  | "preceding-sibling"  => some .precedingSibling
  | "self"               => some .self
  | _                    => none

/-! ## Node tests — `[7] NodeTest` -/

inductive NodeTest where
  /-- `[37] NameTest ::= '*'`. -/
  | anyName
  /-- `[37] NameTest ::= NCName ':' '*'`. -/
  | anyInPrefix (pfx : String)
  /-- `[37] NameTest ::= QName`. -/
  | name (q : String)
  | textT | commentT | nodeT
  /-- `processing-instruction()` or `processing-instruction('t')`. -/
  | piT (target : Option String)
deriving Repr, DecidableEq, Inhabited

/-! ## Expressions -/

mutual

/-- `[14] Expr`. -/
inductive Expr where
  | num      (n : Num)
  | str      (s : String)
  | varRef   (name : String)
  | call     (name : String) (args : List Expr)
  | or       (a b : Expr)
  | and      (a b : Expr)
  /-- `=`, `!=`, `<`, `<=`, `>`, `>=` — the operator kept verbatim. -/
  | cmp      (op : String) (a b : Expr)
  /-- `+`, `-`, `*`, `div`, `mod`. -/
  | arith    (op : String) (a b : Expr)
  | negate   (a : Expr)
  | union    (a b : Expr)
  /-- `[3] PathExpr`: a filter expression followed by a relative path.
      `absolute` marks a path rooted at the document node. -/
  | path     (absolute : Bool) (start : Option Expr) (steps : List Step)
  /-- `[20] FilterExpr ::= PrimaryExpr Predicate*`.

      Its own node-set is the context for the predicate, so `last()`
      is the SIZE OF THAT SET. Encoding it as a `self::node()` step
      with the predicate attached — which is what this module first
      did — gives every node a one-element context, so `last()` is
      always 1 and `(a|b|c)[last()]` keeps everything
      (position-6901). -/
  | filter   (base : Expr) (preds : List Expr)
deriving Repr, Inhabited

/-- `[4] Step ::= AxisSpecifier NodeTest Predicate*`. -/
inductive Step where
  | mk (ax : Ax) (test : NodeTest) (preds : List Expr)
deriving Repr, Inhabited

end

def Step.ax : Step → Ax | .mk a _ _ => a
def Step.test : Step → NodeTest | .mk _ t _ => t
def Step.preds : Step → List Expr | .mk _ _ p => p

/-! ## Tokens — `[28] ExprToken` -/

inductive Tok where
  | name   (s : String)
  | number (n : Num)
  | lit    (s : String)
  | varRef (s : String)
  | op     (s : String)
deriving Repr, DecidableEq, Inhabited

private def isNameStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isNameCh (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == ':'

/-- Name characters EXCLUDING the colon: `[4] NCName`. -/
private def isNameCh0 (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.'

private def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Tokenize. The two-character operators are recognised before the
    one-character ones, so `!=` never becomes `!` followed by `=`. -/
partial def tokenize (cs : List Char) : Option (List Tok) :=
  match cs with
  | [] => some []
  | c :: rest =>
    if isWs c then tokenize rest
    else if c == '\'' || c == '"' then
      let body := rest.takeWhile (· != c)
      let after := rest.dropWhile (· != c)
      match after with
      | _ :: r2 => (tokenize r2).map (fun ts => .lit (String.ofList body) :: ts)
      | []      => none                     -- unterminated literal
    else if isDigitC c || (c == '.' && (rest.head?.map isDigitC).getD false) then
      let ip := (c :: rest).takeWhile isDigitC
      let r1 := (c :: rest).dropWhile isDigitC
      let (fp, r2) := match r1 with
        | '.' :: r => ('.' :: r.takeWhile isDigitC, r.dropWhile isDigitC)
        | _        => ([], r1)
      (tokenize r2).map (fun ts =>
        .number (Num.ofString (String.ofList (ip ++ fp))) :: ts)
    else if c == '$' then
      let nm := rest.takeWhile isNameCh
      if nm.isEmpty then none
      else (tokenize (rest.dropWhile isNameCh)).map (fun ts =>
        .varRef (String.ofList nm) :: ts)
    else if isNameStart c then
      -- A `[5] QName` carries AT MOST ONE colon, and `::` is the axis
      -- separator. Taking every colon into the name made `self::a`
      -- one token that `pNodeTest` then read as a CHILD name test
      -- called `self::a` — a pattern that parsed cleanly and matched
      -- nothing, which is worse than a parse error.
      let first := (c :: rest).takeWhile isNameCh0
      let r1 := (c :: rest).dropWhile isNameCh0
      let (nm, r2) := match r1 with
        | ':' :: d :: tl =>
            if isNameStart d then
              (first ++ [':', d] ++ (tl.takeWhile isNameCh0), tl.dropWhile isNameCh0)
            else (first, r1)
        | _ => (first, r1)
      (tokenize r2).map (fun ts => .name (String.ofList nm) :: ts)
    else
      let two := match rest with
        | d :: _ => String.ofList [c, d]
        | []     => ""
      if two == "//" || two == "!=" || two == "<=" || two == ">=" || two == "::"
         || two == ".." then
        (tokenize rest.tail!).map (fun ts => .op two :: ts)
      else if "/@[]()=<>+-*|,.:".toList.contains c then
        (tokenize rest).map (fun ts => .op (String.ofList [c]) :: ts)
      else none

/-- The `[38] OperatorName` disambiguation: is the token at this point
    an operator, given what came before? -/
def prevAllowsOperator : Option Tok → Bool
  | some (.name _)   => true
  | some (.number _) => true
  | some (.lit _)    => true
  | some (.varRef _) => true
  | some (.op s)     => s == ")" || s == "]" || s == "*"
  | none             => false

/-- Rewrite the `name`-shaped operator tokens (`and`, `or`, `div`,
    `mod`) and the ambiguous `*` into operator tokens, using the
    preceding token. `*` after `::` or `@` stays a name test even
    though `::` is an operator, because a wildcard is what an axis
    or an attribute specifier expects. -/
def disambiguate (ts : List Tok) : List Tok :=
  let rec go (prev : Option Tok) : List Tok → List Tok
    | []      => []
    | t :: r =>
      let t' := match t with
        | .name n =>
            if (n == "and" || n == "or" || n == "div" || n == "mod")
               && prevAllowsOperator prev
            then Tok.op n else t
        | .op "*" =>
            let afterAxis := match prev with
              | some (.op s) => s == "::" || s == "@"
              | _            => false
            if prevAllowsOperator prev && !afterAxis then Tok.op "*mul" else t
        | _ => t
      t' :: go (some t') r
  go none ts

/-! ## The parser

A hand-written recursive descent over the token list, one function per
production, each returning the value and the remaining tokens. -/

private abbrev P (a : Type) := List Tok → Option (a × List Tok)

private def expect (s : String) : P Unit
  | .op x :: r => if x == s then some ((), r) else none
  | _          => none


mutual

/-- `[21] OrExpr`. -/
partial def pOr (ts : List Tok) : Option (Expr × List Tok) :=
  match pAnd ts with
  | none        => none
  | some (l, r) => pOrTail l r

partial def pOrTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op "or" :: r2 =>
      match pAnd r2 with
      | some (b, r3) => pOrTail (.or acc b) r3
      | none         => none
  | r => some (acc, r)

/-- `[22] AndExpr`. -/
partial def pAnd (ts : List Tok) : Option (Expr × List Tok) :=
  match pEquality ts with
  | none        => none
  | some (l, r) => pAndTail l r

partial def pAndTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op "and" :: r2 =>
      match pEquality r2 with
      | some (b, r3) => pAndTail (.and acc b) r3
      | none         => none
  | r => some (acc, r)

/-- `[23] EqualityExpr` and `[24] RelationalExpr`, left-associative. -/
partial def pEquality (ts : List Tok) : Option (Expr × List Tok) :=
  match pAdditive ts with
  | none        => none
  | some (l, r) => pEqTail l r

partial def pEqTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op o :: r2 =>
      if o == "=" || o == "!=" || o == "<" || o == "<=" || o == ">" || o == ">=" then
        match pAdditive r2 with
        | some (b, r3) => pEqTail (.cmp o acc b) r3
        | none         => none
      else some (acc, .op o :: r2)
  | r => some (acc, r)

/-- `[25] AdditiveExpr`. -/
partial def pAdditive (ts : List Tok) : Option (Expr × List Tok) :=
  match pMultiplicative ts with
  | none        => none
  | some (l, r) => pAddTail l r

partial def pAddTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op o :: r2 =>
      if o == "+" || o == "-" then
        match pMultiplicative r2 with
        | some (b, r3) => pAddTail (.arith o acc b) r3
        | none         => none
      else some (acc, .op o :: r2)
  | r => some (acc, r)

/-- `[26] MultiplicativeExpr`. -/
partial def pMultiplicative (ts : List Tok) : Option (Expr × List Tok) :=
  match pUnary ts with
  | none        => none
  | some (l, r) => pMulTail l r

partial def pMulTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op o :: r2 =>
      if o == "*mul" || o == "div" || o == "mod" then
        match pUnary r2 with
        | some (b, r3) => pMulTail (.arith (if o == "*mul" then "*" else o) acc b) r3
        | none         => none
      else some (acc, .op o :: r2)
  | r => some (acc, r)

/-- `[27] UnaryExpr`. -/
partial def pUnary : List Tok → Option (Expr × List Tok)
  | .op "-" :: r => (pUnary r).map (fun (e, r2) => (.negate e, r2))
  | ts           => pUnion ts

/-- `[18] UnionExpr`. -/
partial def pUnion (ts : List Tok) : Option (Expr × List Tok) :=
  match pPath ts with
  | none        => none
  | some (l, r) => pUnionTail l r

partial def pUnionTail (acc : Expr) : List Tok → Option (Expr × List Tok)
  | .op "|" :: r2 =>
      match pPath r2 with
      | some (b, r3) => pUnionTail (.union acc b) r3
      | none         => none
  | r => some (acc, r)

/-- `[19] PathExpr` and `[2] AbsoluteLocationPath`. -/
partial def pPath (ts : List Tok) : Option (Expr × List Tok) :=
  match ts with
  | .op "/" :: r =>
      (match pRelative r with
       | some (steps, r2) => some (.path true none steps, r2)
       | none             => some (.path true none [], r))
  | .op "//" :: r =>
      (match pRelative r with
       | some (steps, r2) =>
           some (.path true none (Step.mk .descendantOrSelf .nodeT [] :: steps), r2)
       | none => none)
  | _ =>
      match pFilterStart ts with
      | some (e, r) =>
          (match r with
           | .op "/" :: r2 =>
               (match pRelative r2 with
                | some (steps, r3) => some (.path false (some e) steps, r3)
                | none             => none)
           | .op "//" :: r2 =>
               (match pRelative r2 with
                | some (steps, r3) =>
                    some (.path false (some e)
                      (Step.mk .descendantOrSelf .nodeT [] :: steps), r3)
                | none => none)
           | _ => some (e, r))
      | none =>
          match pRelative ts with
          | some (steps, r) => some (.path false none steps, r)
          | none            => none

/-- `[20] FilterExpr` — the primary expressions that are NOT a step,
    with their predicates. `none` when the tokens begin a step
    instead, which is how a bare name is told from a function call. -/
partial def pFilterStart (ts : List Tok) : Option (Expr × List Tok) :=
  let prim : Option (Expr × List Tok) :=
    match ts with
    | .lit s :: r    => some (.str s, r)
    | .number n :: r => some (.num n, r)
    | .varRef v :: r => some (.varRef v, r)
    | .op "(" :: r   =>
        (match pOr r with
         | some (e, .op ")" :: r3) => some (e, r3)
         | _                       => none)
    | .name n :: .op "(" :: r =>
        -- A NodeType keyword followed by `(` is a node test, not a
        -- function: `text()` in a step position must not be read as
        -- a call to a function named `text`.
        if n == "text" || n == "comment" || n == "node"
           || n == "processing-instruction" then none
        else pArgs r |>.map (fun (args, r2) => (Expr.call n args, r2))
    | _ => none
  match prim with
  | none        => none
  | some (e, r) =>
      match pPredicates r with
      | none          => none
      | some ([], r2) => some (e, r2)
      | some (ps, r2) => some (.filter e ps, r2)

/-- `[16] FunctionCall` argument list, the opening `(` consumed. -/
partial def pArgs : List Tok → Option (List Expr × List Tok)
  | .op ")" :: r => some ([], r)
  | ts =>
      match pOr ts with
      | none        => none
      | some (a, r) => pArgsTail [a] r

partial def pArgsTail (acc : List Expr) : List Tok → Option (List Expr × List Tok)
  | .op "," :: r2 =>
      match pOr r2 with
      | some (b, r3) => pArgsTail (acc ++ [b]) r3
      | none         => none
  | .op ")" :: r2 => some (acc, r2)
  | _ => none

/-- `[3] RelativeLocationPath`. -/
partial def pRelative (ts : List Tok) : Option (List Step × List Tok) :=
  match pStep ts with
  | none        => none
  | some (s, r) => pRelTail [s] r

partial def pRelTail (acc : List Step) : List Tok → Option (List Step × List Tok)
  | .op "/" :: r2 =>
      (match pStep r2 with
       | some (s2, r3) => pRelTail (acc ++ [s2]) r3
       | none          => none)
  | .op "//" :: r2 =>
      (match pStep r2 with
       | some (s2, r3) => pRelTail (acc ++ [Step.mk .descendantOrSelf .nodeT [], s2]) r3
       | none          => none)
  | r => some (acc, r)

/-- `[4] Step`, including `[12] AbbreviatedStep` (`.` and `..`). -/
partial def pStep (ts : List Tok) : Option (Step × List Tok) :=
  match ts with
  | .op "." :: r  => some (Step.mk .self .nodeT [], r)
  | .op ".." :: r => some (Step.mk .parent .nodeT [], r)
  | _ =>
    let axr : Option (Ax × List Tok) := match ts with
      | .name a :: .op "::" :: r => (axOfName a).map (fun x => (x, r))
      | .op "@" :: r             => some (.attribute, r)
      | _                        => some (.child, ts)
    match axr with
    | none          => none            -- an unknown axis name is NOT `child::`
    | some (ax, r1) =>
        match pNodeTest r1 with
        | none         => none
        | some (nt, r2) =>
            match pPredicates r2 with
            | none          => none
            | some (ps, r3) => some (Step.mk ax nt ps, r3)

/-- `[7] NodeTest`. -/
partial def pNodeTest : List Tok → Option (NodeTest × List Tok)
  | .op "*" :: r => some (.anyName, r)
  | .name n :: .op "(" :: .op ")" :: r =>
      if n == "text" then some (.textT, r)
      else if n == "comment" then some (.commentT, r)
      else if n == "node" then some (.nodeT, r)
      else if n == "processing-instruction" then some (.piT none, r)
      else none
  | .name n :: .op "(" :: .lit t :: .op ")" :: r =>
      if n == "processing-instruction" then some (.piT (some t), r) else none
  | .name n :: .op ":" :: .op "*" :: r => some (.anyInPrefix n, r)
  | .name n :: r =>
      if n.endsWith ":" then some (.anyInPrefix (String.ofList n.toList.dropLast), r)
      else some (.name n, r)
  | _ => none

/-- `[8] Predicate*`. -/
partial def pPredicates (ts : List Tok) : Option (List Expr × List Tok) :=
  match ts with
  | .op "[" :: r =>
      (match pOr r with
       | some (e, .op "]" :: r3) =>
           (match pPredicates r3 with
            | some (rest, r4) => some (e :: rest, r4)
            | none            => none)
       | _ => none)
  | _ => some ([], ts)

end

/-- Parse a whole expression. `none` when the text is not XPath 1.0 or
    when tokens are left over — a partial parse is a wrong answer
    wearing the shape of a right one. -/
def parseExpr (s : String) : Option Expr := do
  let ts ← tokenize s.toList
  let (e, rest) ← pOr (disambiguate ts)
  if rest.isEmpty then some e else none

end L4Factoidal.XPath.Full
