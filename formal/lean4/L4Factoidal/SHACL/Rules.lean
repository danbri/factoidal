/-
L4Factoidal.SHACL.Rules — the `.srl` rule-language evaluator.

Port of `formal/fstar/SHACL.Rules.fst` (438 lines). SHACL 1.2 Rules,
the shacl12 `rules` suite.

An `.srl` file is a small surface syntax:

```
PREFIX ex: <http://example.org/> .
RULE { ?x ex:q ?y } WHERE { ?x ex:p ?y }
DATA { ex:a ex:p ex:b }
## comment
```

Each `RULE` / `DATA` block translates to a SPARQL CONSTRUCT query with
the prologue prepended, and evaluation is a bottom-up fixpoint: apply
every construct to the accumulating graph, add the new triples, repeat
until nothing is added. `NOT { … }` in a body becomes
`FILTER NOT EXISTS { … }`.

## What the module holds

| Suite | Entry point |
|---|---|
| `rules/eval` | `runRules` |
| `rules/syntax` | `srlValidSyntax` |
| `rules/wellformed` | `srlWellFormed` |
| `rules/stratification` | `srlStratifiable` |

## ⚠️ Two approximations, carried over from F\* with its own words

`srlStratifiable` is described in the F\* module as "a conservative
approximation": it reports a ruleset non-stratifiable when a rule mints
a fresh blank node in its head and reads a predicate its own head
derives, or when a `NOT` block negates data some head derives. Its own
comment says "a full dependency-graph analyzer (negative-cycle
detection over the predicate graph) is future work".

`filterSafe` checks only the FIRST `FILTER` in a body.

Both are ported as they are, because changing them would change which
tests pass, and that is a decision about the engine rather than about
the port. Both are marked here so a reader does not take them for the
full analysis.

## The scanners work on `List Char`

As in F\*. The blocks are brace-aware and the recursion is fuel-bounded
where the input is not structurally decreasing, which is the same
totality device the F\* module uses.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SHACL

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Small string helpers -/

def dropWs : List Char → List Char
  | ' ' :: r  => dropWs r
  | '\t' :: r => dropWs r
  | cs        => cs

def lstrip (s : String) : String := String.ofList (dropWs s.toList)

def charsPrefixMatch : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | a :: n', b :: h' => a == b && charsPrefixMatch n' h'

def charsDrop : Nat → List Char → List Char
  | 0, l => l
  | _, [] => []
  | k + 1, _ :: t => charsDrop k t

/-- Plain replacement of every occurrence of `needle`. Fuel-bounded, as
    in F\*: each step consumes at least one character. -/
def replaceAllChars : Nat → List Char → List Char → List Char → List Char
  | 0, cs, _, _ => cs
  | _ + 1, [], _, _ => []
  | f + 1, c :: rest, needle, repl =>
      if !needle.isEmpty && charsPrefixMatch needle (c :: rest)
      then repl ++ replaceAllChars f (charsDrop needle.length (c :: rest)) needle repl
      else c :: replaceAllChars f rest needle repl

def replaceAll (s needle repl : String) : String :=
  String.ofList (replaceAllChars (s.length + 1) s.toList needle.toList repl.toList)

/-! ## `.srl` to CONSTRUCT -/

inductive BlockKind where
  | rule
  | data
  deriving DecidableEq, Repr

def lineKind (line : String) : Option BlockKind :=
  let t := lstrip line
  if t.startsWith "RULE" then some .rule
  else if t.startsWith "DATA" then some .data
  else none

/-- Everything after the leading keyword. Both keywords are four
    characters. -/
def lineBody (line : String) : String :=
  let t := lstrip line
  if t.length ≥ 4 then String.ofList (t.toList.drop 4) else ""

def isBlockKw (cs : List Char) : Bool :=
  charsPrefixMatch "RULE".toList cs || charsPrefixMatch "DATA".toList cs ||
  charsPrefixMatch "PREFIX".toList cs || charsPrefixMatch "BASE".toList cs

def isPrefixSeg (s : String) : Bool :=
  let t := lstrip s
  t.startsWith "PREFIX" || t.startsWith "BASE"

/-- SPARQL wants the prologue up front and `.srl` allows `PREFIX`
    between rules, so every prologue segment is hoisted into the
    header. -/
def computeHeader (first : String) (segs : List String) : String :=
  String.intercalate "\n" (first :: segs.filter isPrefixSeg)

/-- Brace-aware split: a new segment starts at each depth-zero
    `RULE` / `DATA` / `PREFIX` / `BASE` that follows whitespace. The
    first segment is the header. -/
def scanBlocksAux : List Char → Int → Bool → List Char → List String → Nat →
    List String
  | cs, _, _, curr, blocks, 0 =>
      (String.ofList curr.reverse :: blocks).reverse
  | [], _, _, curr, blocks, _ =>
      (String.ofList curr.reverse :: blocks).reverse
  | c :: rest, depth, prevWs, curr, blocks, f + 1 =>
      if depth == 0 && prevWs && isBlockKw (c :: rest) then
        scanBlocksAux rest depth false [c]
          (String.ofList curr.reverse :: blocks) f
      else
        let depth' := if c == '{' then depth + 1
                      else if c == '}' then depth - 1 else depth
        let ws := c == ' ' || c == '\n' || c == '\t' || c == '\r'
        scanBlocksAux rest depth' ws (c :: curr) blocks f

def scanBlocks (srl : String) : List String :=
  scanBlocksAux srl.toList 0 true [] [] (srl.length + 2)

/-- `RULE {H} WHERE {B}` becomes `CONSTRUCT {H} WHERE {B}`; `DATA {T}`
    becomes `CONSTRUCT {T} WHERE {}`. -/
def ruleTexts (header : String) : List String → List String
  | [] => []
  | l :: rest =>
      match lineKind l with
      | some .rule =>
          (header ++ "\nCONSTRUCT " ++
            replaceAll (lineBody l) "NOT {" "FILTER NOT EXISTS {") :: ruleTexts header rest
      | some .data =>
          (header ++ "\nCONSTRUCT " ++ lineBody l ++ " WHERE {}") :: ruleTexts header rest
      | none => ruleTexts header rest

def translateSrl (srl : String) : List String :=
  match scanBlocks srl with
  | [] => []
  | first :: blocks => ruleTexts (computeHeader first blocks) blocks

/-! ## Syntax validation — the `rules/syntax` suite -/

def parses12 (txt : String) : Bool :=
  match parseSparql txt none .v12 with
  | .ok _ => true
  | .error _ => false

def strHasChar (c : Char) (s : String) : Bool := s.toList.contains c

/-- A block is valid when its translated CONSTRUCT parses. A `DATA`
    block must additionally be GROUND: asserted data, not a pattern. -/
def blockValid (header : String) (block : String) : Bool :=
  match lineKind block with
  | some .rule =>
      parses12 (header ++ "\nCONSTRUCT " ++
        replaceAll (lineBody block) "NOT {" "FILTER NOT EXISTS {")
  | some .data =>
      let body := lineBody block
      if strHasChar '?' body || strHasChar '$' body then false
      else parses12 (header ++ "\nCONSTRUCT " ++ body ++ " WHERE {}")
  | none => true

def srlValidSyntax (srl : String) : Bool :=
  match scanBlocks srl with
  | [] => true
  | first :: blocks =>
      blocks.all (blockValid (computeHeader first blocks))

/-! ## Well-formedness — the `rules/wellformed` suite -/

/-- A variable-name continuation character: anything that is not a
    SPARQL token delimiter, so `?name` runs to the next delimiter. -/
def isVarNameChar (c : Char) : Bool :=
  !(c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '.' || c == '{' ||
    c == '}' || c == '(' || c == ')' || c == ';' || c == ',' || c == '?' ||
    c == '$' || c == '<' || c == '>' || c == '"' || c == '\'' || c == '[' ||
    c == ']')

def takeWhileC (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: r => if p c then c :: takeWhileC p r else []

def dropWhileC (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: r => if p c then dropWhileC p r else c :: r

def collectVars : List Char → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, f + 1 =>
      if c == '?' || c == '$' then
        match takeWhileC isVarNameChar rest with
        | [] => collectVars rest f
        | nm => String.ofList nm :: collectVars (dropWhileC isVarNameChar rest) f
      else collectVars rest f

def varsIn (s : String) : List String := collectVars s.toList (s.length + 1)

/-- Split at the first occurrence of `needle`; `none` when it is
    absent. -/
def splitAtNeedle : List Char → List Char → List Char → Nat →
    Option (String × String)
  | _, _, _, 0 => none
  | [], _, _, _ => none
  | c :: rest, needle, acc, f + 1 =>
      if charsPrefixMatch needle (c :: rest) then
        some (String.ofList acc.reverse,
              String.ofList (charsDrop needle.length (c :: rest)))
      else splitAtNeedle rest needle (c :: acc) f

def allMem (xs ys : List String) : Bool := xs.all (fun x => ys.contains x)

/-- Characters up to the paren closing the current group. -/
def captureParens : List Char → Int → List Char → Nat → String × List Char
  | cs, _, acc, 0 => (String.ofList acc.reverse, cs)
  | [], _, acc, _ => (String.ofList acc.reverse, [])
  | ')' :: rest, depth, acc, f + 1 =>
      if depth == 0 then (String.ofList acc.reverse, rest)
      else captureParens rest (depth - 1) (')' :: acc) f
  | '(' :: rest, depth, acc, f + 1 => captureParens rest (depth + 1) ('(' :: acc) f
  | c :: rest, depth, acc, f + 1 => captureParens rest depth (c :: acc) f

/-- The Datalog range restriction on a FILTER: every variable in the
    expression must already be bound by a pattern before it. SPARQL
    scopes FILTER over the whole group; SHACL Rules requires the safe
    left-to-right order (`rules/wellformed` bad-02).

    ⚠️ Only the FIRST `FILTER` in the body is checked, as in F\*. -/
def filterSafe (body : String) : Bool :=
  match splitAtNeedle body.toList "FILTER".toList [] (body.length + 1) with
  | some (before, after) =>
      match dropWs after.toList with
      | '(' :: inner =>
          let (expr, _) := captureParens inner 0 [] (body.length + 1)
          allMem (varsIn expr) (varsIn before)
      | _ => true
  | none => true

/-- A rule is well-formed when every variable in its HEAD is bound by
    its body — an unbound head variable cannot be instantiated — and its
    SPARQL body is well-scoped, which the 1.2 parser decides. -/
def blockWellFormed (header : String) (block : String) : Bool :=
  match lineKind block with
  | some .rule =>
      let hvOk :=
        match splitAtNeedle (lineBody block).toList "WHERE".toList []
                (block.length + 1) with
        | some (head, body) => allMem (varsIn head) (varsIn body) && filterSafe body
        | none => true
      let parseOk :=
        parses12 (header ++ "\nCONSTRUCT " ++
          replaceAll (lineBody block) "NOT {" "FILTER NOT EXISTS {")
      hvOk && parseOk
  | _ => true

def srlWellFormed (srl : String) : Bool :=
  match scanBlocks srl with
  | [] => true
  | first :: blocks => blocks.all (blockWellFormed (computeHeader first blocks))

/-! ## Stratification — the `rules/stratification` suite

⚠️ A conservative approximation, in the F\* module's own words. It
reports a ruleset non-stratifiable when a rule mints a fresh blank node
in its head yet reads a predicate its own head derives — new-term
recursion never reaches a fixpoint — or when a `NOT` block negates data
some head derives. A full negative-cycle analysis over the predicate
graph is not done in either tree. -/

def strContains (s needle : String) : Bool :=
  (splitAtNeedle s.toList needle.toList [] (s.length + 1)).isSome

/-- Maximal variable-name-character runs containing a `:` — the
    prefixed names, excluding plain variables. -/
def collectPnames : List Char → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, f + 1 =>
      if isVarNameChar c then
        let run := takeWhileC isVarNameChar (c :: rest)
        let s := String.ofList run
        (if strContains s ":" then [s] else []) ++
          collectPnames (dropWhileC isVarNameChar (c :: rest)) f
      else collectPnames rest f

def ruleHead (block : String) : String :=
  match splitAtNeedle (lineBody block).toList "WHERE".toList [] (block.length + 1) with
  | some (h, _) => h
  | none => lineBody block

def ruleBody (block : String) : String :=
  match splitAtNeedle (lineBody block).toList "WHERE".toList [] (block.length + 1) with
  | some (_, b) => b
  | none => ""

def anyMem (xs ys : List String) : Bool := xs.any (fun x => ys.contains x)

def blockNewTermRecursive (block : String) (allBodyPnames : List String) : Bool :=
  match lineKind block with
  | some .rule =>
      let h := ruleHead block
      if strContains h "[]" || strContains h "_:" then
        anyMem (collectPnames h.toList (h.length + 1)) allBodyPnames
      else false
  | _ => false

def captureBraces : List Char → Int → List Char → Nat → String × List Char
  | cs, _, acc, 0 => (String.ofList acc.reverse, cs)
  | [], _, acc, _ => (String.ofList acc.reverse, [])
  | '}' :: rest, depth, acc, f + 1 =>
      if depth == 0 then (String.ofList acc.reverse, rest)
      else captureBraces rest (depth - 1) ('}' :: acc) f
  | '{' :: rest, depth, acc, f + 1 => captureBraces rest (depth + 1) ('{' :: acc) f
  | c :: rest, depth, acc, f + 1 => captureBraces rest depth (c :: acc) f

def extractNotContents : List Char → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, f + 1 =>
      if charsPrefixMatch "NOT".toList (c :: rest) then
        match dropWs (charsDrop 3 (c :: rest)) with
        | '{' :: inner =>
            let (content, after) := captureBraces inner 0 [] (f + 1)
            content :: extractNotContents after f
        | _ => extractNotContents rest f
      else extractNotContents rest f

def collectLiterals : List Char → Nat → List String
  | _, 0 => []
  | [], _ => []
  | '"' :: rest, f + 1 =>
      let run := takeWhileC (fun c => c != '"') rest
      ("\"" ++ String.ofList run ++ "\"") ::
        collectLiterals (charsDrop 1 (dropWhileC (fun c => c != '"') rest)) f
  | _ :: rest, f + 1 => collectLiterals rest f

def sigTokens (s : String) : List String :=
  collectPnames s.toList (s.length + 1) ++ collectLiterals s.toList (s.length + 1)

def allContained (toks : List String) (hay : String) : Bool :=
  toks.all (fun t => strContains hay t)

/-- A `NOT` block negates DERIVED data when some rule head contains all
    of its significant tokens. -/
def negMatchesHead (notContent : String) (heads : List String) : Bool :=
  let toks := sigTokens notContent
  !toks.isEmpty && heads.any (fun h => allContained toks h)

def srlStratifiable (srl : String) : Bool :=
  match scanBlocks srl with
  | [] => true
  | _ :: blocks =>
      let allBodyPnames := blocks.flatMap (fun b =>
        let bd := ruleBody b
        collectPnames bd.toList (bd.length + 1))
      let heads := blocks.flatMap (fun b =>
        match lineKind b with | some .rule => [ruleHead b] | _ => [])
      let notBlocks := blocks.flatMap (fun b =>
        match lineKind b with
        | some .rule => extractNotContents (ruleBody b).toList (b.length + 1)
        | _ => [])
      !(blocks.any (fun b => blockNewTermRecursive b allBodyPnames) ||
        notBlocks.any (fun nb => negMatchesHead nb heads))

/-! ## Fixpoint evaluation -/

def parseConstructs (srl : String) : List Query :=
  (translateSrl srl).flatMap (fun t =>
    match parseSparql t none .v12 with
    | .ok q => [q]
    | .error _ => [])

def dedupTriples (g : Graph) : Graph :=
  (g.foldl (fun acc t => acc.add t) Graph.empty)

/-- One inference step: the current graph unioned with every
    construct's output. -/
def rulesStep (g : Graph) (qs : List Query) : Graph :=
  let inferred := qs.flatMap (fun q =>
    evalConstruct emptyEnv { default := g, named := [] } q)
  dedupTriples (g ++ inferred)

/-- Bottom-up fixpoint: stop when a step adds nothing, or on fuel. -/
def rulesFixpoint (g : Graph) (qs : List Query) : Nat → Graph
  | 0 => g
  | f + 1 =>
      let g' := rulesStep g qs
      if g'.length == g.length then g' else rulesFixpoint g' qs f

/-- The triples INFERRED from `data` by the rules in `srl`. The suite's
    `mf:result` asserts only the newly derived triples, so the original
    data is removed. -/
def runRules (data : Graph) (srl : String) : Graph :=
  let qs := parseConstructs srl
  let closure := rulesFixpoint (dedupTriples data) qs (data.length + 100)
  closure.filter (fun t => !data.contains t)

end L4Factoidal.SHACL
