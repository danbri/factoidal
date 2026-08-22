/-
L4Factoidal.Testing.Gen — PURE, SEEDED generators for property-based
tests of the Lean engine.

Lean core ships no QuickCheck. This module is the small replacement
the design note asked for (`docs/designissues/2026-08-22-lean4-w3c-
harness.md`, "Tests that truly exercise an implementation"): a
splitmix64 step over `Nat`, a state-passing generator monad on top of
it, and generators for

  * RDF graphs over a bounded vocabulary — three subject IRIs, two
    blank nodes, three predicates, and literals that cover the cases
    the engine treats specially: plain strings, language-tagged
    strings (RDF 1.1 Concepts §3.3), and typed numerics of the three
    SPARQL numeric datatypes (xsd:integer / xsd:decimal / xsd:double,
    SPARQL 1.1 §17.1) plus xsd:boolean;
  * Basic Graph Patterns over variables `?x ?y ?z` and the same
    vocabulary (SPARQL 1.1 §18.1.7);
  * a small query grammar — BGP, OPTIONAL, FILTER on comparisons and
    BOUND, UNION, MINUS (§18.2.2), with DISTINCT / ORDER BY / LIMIT
    (§15) and the three evaluable query forms (§16) — rendered BOTH as
    SPARQL text (so the F* binary and the Lean parser read the same
    bytes) and as the Lean algebra AST (so invariants can be checked
    on the algebra directly).

Everything is total and deterministic: the same seed gives the same
case, which `L4Factoidal/Testing/GenTests.lean` pins with `#guard`s.
No I/O, no `sorry`, no `axiom`, no `native_decide`, no `partial`.

The choice of a bounded vocabulary is deliberate: with three subjects
and three predicates a random graph of up to eight triples has joins
that actually join and OPTIONALs that sometimes bind and sometimes do
not, so the invariants are exercised on non-empty solution sequences.
A sparse vocabulary would make every property vacuously true on empty
inputs — the "negative test that passes by deriving nothing" trap of
`skills/measuring-inference/SKILL.md`.
-/
import L4Factoidal.SPARQL.Expr
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Testing

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## The random source — splitmix64 over `Nat` -/

/-- 2^64: every state and output is reduced modulo this, so the
arithmetic below is exactly the 64-bit splitmix64 of Steele, Lea and
Flood (2014) — chosen because its step is four lines and its output
for seed 0 is a published constant (pinned in `GenTests.lean`). -/
def word : Nat := 18446744073709551616

structure Rng where
  state : Nat
  deriving Repr, DecidableEq

/-- One splitmix64 step: the next 64-bit output and the next state. -/
def Rng.next (r : Rng) : Nat × Rng :=
  let s  := (r.state + 0x9E3779B97F4A7C15) % word
  let z1 := ((s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9) % word
  let z2 := ((z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB) % word
  (z2 ^^^ (z2 >>> 31), ⟨s⟩)

def Rng.seed (n : Nat) : Rng := ⟨n % word⟩

/-! ## The generator monad -/

/-- A generator: a state-passing function over the random source. -/
structure Gen (α : Type) where
  run : Rng → α × Rng

instance : Monad Gen where
  pure a := ⟨fun r => (a, r)⟩
  bind g f := ⟨fun r => let p := g.run r; (f p.1).run p.2⟩

/-- Run a generator from a numeric seed, dropping the final state. -/
def Gen.runSeed (g : Gen α) (seed : Nat) : α := (g.run (Rng.seed seed)).1

/-- A uniform-ish number below `n` (below 1 when `n = 0`). -/
def natLt (n : Nat) : Gen Nat :=
  ⟨fun r => let p := r.next; (p.1 % (max n 1), p.2)⟩

def bool : Gen Bool := do return (← natLt 2) == 1

/-- One element of a non-empty list; `dflt` only for the empty list. -/
def pick (xs : List α) (dflt : α) : Gen α := do
  let i ← natLt xs.length
  return xs.getD i dflt

def listOf (n : Nat) (g : Gen α) : Gen (List α) :=
  match n with
  | 0     => pure []
  | n + 1 => do
      let x ← g
      let xs ← listOf n g
      return x :: xs

/-! ## Vocabulary -/

def exNs : String := "http://example.org/"

/-- `http://example.org/<name>`; the fallback arm is unreachable for a
non-empty name (the string always contains the colon of `http:`) but
keeps the function total without a proof obligation. -/
def mkIri (name : String) : WfIri :=
  let s := exNs ++ name
  if h : isIri s then ⟨s, h⟩ else ⟨"http://example.org/fallback", rfl⟩

def subjectIris : List WfIri := [mkIri "s1", mkIri "s2", mkIri "s3"]
def predIris    : List WfIri := [mkIri "p", mkIri "q", mkIri "r"]
def bnodeIds    : List BNodeId := ["b1", "b2"]

/-- A typed literal; falls back to a plain string for a datatype the
well-formedness rule rejects (none of the datatypes used here is). -/
def typedLit (lex : String) (dt : WfIri) : WfLiteral :=
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := none, direction := none }
  if h : literalWf l then ⟨l, h⟩ else Literal.string lex

/-- The literal vocabulary: plain, language-tagged (including a tag
differing only in case, which `Literal.eqb` identifies — RDF 1.1
Concepts §3.3), and typed numerics whose lexical forms are NOT all
canonical (`"2.0"`, `"1.0E0"`), so value-versus-lexical confusions
show. -/
def literals : List WfLiteral :=
  [ Literal.string "a", Literal.string "b",
    Literal.langString "a" "en", Literal.langString "b" "fr", Literal.langString "a" "EN",
    typedLit "1" xsdInteger, typedLit "2" xsdInteger, typedLit "10" xsdInteger,
    typedLit "1.5" xsdDecimal, typedLit "2.0" xsdDecimal,
    typedLit "1.0E0" xsdDouble, typedLit "2.5E1" xsdDouble,
    typedLit "true" xsdBoolean ]

/-! ## Graphs -/

def genSubject : Gen Subject := do
  if (← natLt 4) == 0 then return .bnode (← pick bnodeIds "b1")
  else return .iri (← pick subjectIris (mkIri "s1"))

def genObject : Gen Term := do
  match ← natLt 3 with
  | 0 => return (← genSubject).toTerm
  | _ => return .literal (← pick literals (Literal.string "a"))

def genTriple : Gen Triple := do
  let s ← genSubject
  let p ← pick predIris (mkIri "p")
  let o ← genObject
  return { s, p, o }

/-- Three to ten triples, set-deduplicated through `Graph.add`. -/
def genGraph : Gen Graph := do
  let n ← natLt 8
  let n := n + 3
  let ts ← listOf n genTriple
  return ts.foldl (fun g t => g.add t) Graph.empty

/-! ## Queries — a small grammar with two renderings -/

/-- A query-side term. Blank nodes are deliberately absent from the
query grammar: a query blank node is a non-distinguished variable
(§18.1.6), and the W3C corpus already covers that rewrite. -/
inductive GTerm where
  | var (v : String)
  | iri (i : WfIri)
  | lit (l : WfLiteral)
  deriving Repr

structure GTriple where
  s : GTerm
  p : GTerm
  o : GTerm
  deriving Repr

inductive GCmp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq

/-- FILTER expressions: comparisons (§17.4.1.7) and BOUND (§17.4.1.1). -/
inductive GExpr where
  | cmpVar   (a : String) (op : GCmp) (b : String)
  | cmpConst (a : String) (op : GCmp) (c : WfLiteral)
  | bound    (v : String)
  | notBound (v : String)
  deriving Repr

inductive GPattern where
  | bgp      (ts : List GTriple)
  | optional (l : GPattern) (r : List GTriple)
  | filter   (p : GPattern) (e : GExpr)
  | union    (l r : GPattern)
  | minus    (l : GPattern) (r : List GTriple)
  deriving Repr

inductive GForm where
  | select
  | selectVars (vs : List String)
  | ask
  | construct
  deriving Repr

/-- `orderBy`: every variable, each with its own direction — ordering
on ALL variables leaves a tie only between identical rows, so a LIMIT
(generated only together with ORDER BY) selects a determinate
multiset. Ordering on one variable would make LIMIT implementation-
defined (§15.1 fixes nothing about ties), which is not a property to
test. -/
structure GQuery where
  form     : GForm
  pattern  : GPattern
  distinct : Bool
  orderBy  : Option (List (String × Bool))
  limit    : Option Nat
  deriving Repr

def vars : List String := ["x", "y", "z"]

def genVar : Gen String := pick vars "x"

def genGSubject : Gen GTerm := do
  if (← natLt 4) == 0 then return .iri (← pick subjectIris (mkIri "s1"))
  else return .var (← genVar)

def genGPredicate : Gen GTerm := do
  if (← natLt 4) == 0 then return .var (← genVar)
  else return .iri (← pick predIris (mkIri "p"))

def genGObject : Gen GTerm := do
  match ← natLt 8 with
  | 0 => return .iri (← pick subjectIris (mkIri "s1"))
  | 1 => return .lit (← pick literals (Literal.string "a"))
  | 2 => return .lit (← pick literals (Literal.string "a"))
  | _ => return .var (← genVar)

def genGTriple : Gen GTriple := do
  let s ← genGSubject
  let p ← genGPredicate
  let o ← genGObject
  return { s, p, o }

/-- One or two triple patterns. -/
def genBgp : Gen (List GTriple) := do
  let n ← natLt 2
  listOf (n + 1) genGTriple

def genCmp : Gen GCmp := pick [.lt, .le, .eq, .ne, .gt, .ge] .eq

def genExpr : Gen GExpr := do
  match ← natLt 4 with
  | 0 => return .cmpVar (← genVar) (← genCmp) (← genVar)
  | 1 => return .cmpConst (← genVar) (← genCmp) (← pick literals (Literal.string "a"))
  | 2 => return .bound (← genVar)
  | _ => return .notBound (← genVar)

def genPattern : Nat → Gen GPattern
  | 0     => do return .bgp (← genBgp)
  | d + 1 => do
      match ← natLt 5 with
      | 0 => return .bgp (← genBgp)
      | 1 => return .optional (← genPattern d) (← genBgp)
      | 2 => return .filter (← genPattern d) (← genExpr)
      | 3 => return .union (← genPattern d) (← genPattern d)
      | _ => return .minus (← genPattern d) (← genBgp)

def genQuery : Gen GQuery := do
  let pattern ← genPattern 2
  let form ← (do
    match ← natLt 6 with
    | 0 => pure GForm.ask
    | 1 => pure GForm.construct
    | 2 => pure (GForm.selectVars ["x", "y"])
    | _ => pure GForm.select)
  let distinct ← bool
  let orderBy ← (do
    if (← natLt 3) == 0 then pure none
    else
      let d1 ← bool
      let d2 ← bool
      let d3 ← bool
      pure (some [("x", d1), ("y", d2), ("z", d3)]))
  let limit ← (do
    if orderBy.isSome && (← bool) then return some (← natLt 4) else pure none)
  return { form, pattern, distinct, orderBy, limit }

/-! ### Rendering 1 — SPARQL text -/

def literalText (l : WfLiteral) : String :=
  match L4Factoidal.Syntax.Term.toNTriples .rdf11 (.literal l) with
  | .ok s    => s
  | .error _ => "\"\""

def GTerm.toSparql : GTerm → String
  | .var v => "?" ++ v
  | .iri i => "<" ++ i.val ++ ">"
  | .lit l => literalText l

def GTriple.toSparql (t : GTriple) : String :=
  t.s.toSparql ++ " " ++ t.p.toSparql ++ " " ++ t.o.toSparql ++ " ."

def bgpText (ts : List GTriple) : String :=
  String.intercalate " " (ts.map GTriple.toSparql)

def GCmp.toSparql : GCmp → String
  | .lt => "<" | .le => "<=" | .eq => "=" | .ne => "!=" | .gt => ">" | .ge => ">="

def GExpr.toSparql : GExpr → String
  | .cmpVar a op b   => "?" ++ a ++ " " ++ op.toSparql ++ " ?" ++ b
  | .cmpConst a op c => "?" ++ a ++ " " ++ op.toSparql ++ " " ++ literalText c
  | .bound v         => "BOUND(?" ++ v ++ ")"
  | .notBound v      => "!BOUND(?" ++ v ++ ")"

def GPattern.toSparql : GPattern → String
  | .bgp ts       => bgpText ts
  | .optional l r => l.toSparql ++ " OPTIONAL { " ++ bgpText r ++ " }"
  | .filter p e   => p.toSparql ++ " FILTER(" ++ e.toSparql ++ ")"
  | .union l r    => "{ " ++ l.toSparql ++ " } UNION { " ++ r.toSparql ++ " }"
  | .minus l r    => l.toSparql ++ " MINUS { " ++ bgpText r ++ " }"

/-- The CONSTRUCT template every generated CONSTRUCT uses. A solution
leaving `?x` or `?y` unbound, or binding `?x` to a literal, yields no
triple (§16.2.1) — both trees have to agree on that too. -/
def constructTemplate : String := "{ ?x <http://example.org/made> ?y }"

def GQuery.toSparql (q : GQuery) : String :=
  let body := "{ " ++ q.pattern.toSparql ++ " }"
  let order := match q.orderBy with
    | none    => ""
    | some cs => " ORDER BY " ++ String.intercalate " " (cs.map fun (v, desc) =>
        if desc then "DESC(?" ++ v ++ ")" else "?" ++ v)
  let lim := match q.limit with
    | none   => ""
    | some n => " LIMIT " ++ toString n
  let dist := if q.distinct then "DISTINCT " else ""
  match q.form with
  | .select        => "SELECT " ++ dist ++ "* WHERE " ++ body ++ order ++ lim
  | .selectVars vs => "SELECT " ++ dist ++ String.intercalate " " (vs.map ("?" ++ ·)) ++
                      " WHERE " ++ body ++ order ++ lim
  | .ask           => "ASK WHERE " ++ body
  | .construct     => "CONSTRUCT " ++ constructTemplate ++ " WHERE " ++ body ++ order ++ lim

/-! ### Rendering 2 — the Lean algebra AST -/

def GTerm.toPatternSubject : GTerm → PatternSubject
  | .var v => .var v
  | .iri i => .iri i
  | .lit _ => .var "x"   -- a literal subject is never generated

def GTerm.toPatternTerm : GTerm → PatternTerm
  | .var v => .var v
  | .iri i => .iri i
  | .lit l => .literal l

def GTriple.toTriplePattern (t : GTriple) : TriplePattern :=
  { s := t.s.toPatternSubject, p := t.p.toPatternTerm, o := t.o.toPatternTerm }

def toBgp (ts : List GTriple) : Bgp := ts.map GTriple.toTriplePattern

def GCmp.toCompOp : GCmp → CompOp
  | .lt => .lt | .le => .le | .eq => .eq | .ne => .ne | .gt => .gt | .ge => .ge

def GExpr.toExpr : GExpr → Expr
  | .cmpVar a op b   => .compare op.toCompOp (.var a) (.var b)
  | .cmpConst a op c => .compare op.toCompOp (.var a) (.lit c)
  | .bound v         => .bound v
  | .notBound v      => .not (.bound v)

/-! ## One property-test case -/

/-- Everything one seed yields: a graph, an extra triple (for the
monotonicity instance), two BGPs and a FILTER expression (for the
algebra laws), and a full query (for the parsers, the query evaluator
and the differential harness). -/
structure Case where
  seed  : Nat
  graph : Graph
  extra : Triple
  bgpA  : List GTriple
  bgpB  : List GTriple
  expr  : GExpr
  query : GQuery
  deriving Repr

def genCaseWith (seed : Nat) : Gen Case := do
  let graph ← genGraph
  let extra ← genTriple
  let bgpA ← genBgp
  let bgpB ← genBgp
  let expr ← genExpr
  let query ← genQuery
  return { seed, graph, extra, bgpA, bgpB, expr, query }

/-- THE entry point: the case for a seed. Same seed, same case. -/
def genCase (seed : Nat) : Case := (genCaseWith seed).runSeed seed

/-- The graph as N-Triples text — what the differential harness writes
to disk for the F* binary and what the round-trip properties re-parse.
Generated graphs hold no RDF 1.2 term, so `.rdf11` cannot fail; the
fallback is unreachable. -/
def Case.graphText (c : Case) : String :=
  match L4Factoidal.Syntax.Graph.toNTriples c.graph .rdf11 with
  | .ok s    => s
  | .error _ => ""

def Case.queryText (c : Case) : String := c.query.toSparql

end L4Factoidal.Testing
