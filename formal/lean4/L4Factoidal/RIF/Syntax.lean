/-
L4Factoidal.RIF.Syntax — the RIF Core abstract syntax, as the
Presentation Syntax writes it.

Spec: RIF Core (https://www.w3.org/TR/rif-core/) §2 (Abstract Syntax)
and §3 (Presentation Syntax), with the datatype and built-in library
of RIF-DTB (https://www.w3.org/TR/rif-dtb/).

## A constant is a LEXICAL FORM plus a SYMBOL SPACE

RIF does not have "IRIs and literals": it has constants in symbol
spaces, and `rif:iri` and `rif:local` are two of them beside every
XSD datatype. That distinction is not decoration —
`pred:literal-not-identical` compares the PAIR, so
`"1"^^xs:integer` and `"1"^^xs:string` are different constants with
the same lexical form, and a model that flattened them to RDF terms
could not state the test the corpus writes.

This REPLACES the earlier `RIF/Core.lean`, which modelled a RIF rule
as RDF triples. Two models of one thing is the confusion this header
warns about, and the triple-shaped one could not state what the
corpus asks: it had no membership, no subclass, no positional atoms
and no built-ins, so `ex:a # ex:D` and
`pred:literal-not-identical("1"^^xs:integer "1"^^xs:string)` were
both unsayable. The RDF-compatibility mapping — a triple as a frame,
`rdf:type` as membership, `rdfs:subClassOf` as subclass — belongs
where a graph is READ, and lives in `Harness/RifRun.lean`.
-/

namespace L4Factoidal.RIF

/-- The `rif:iri` symbol space, written out because it is compared
    against constantly. -/
def iriSpace : String := "http://www.w3.org/2007/rif#iri"
def localSpace : String := "http://www.w3.org/2007/rif#local"
def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

/-- A GROUND term: a constant in a symbol space, or a list. -/
inductive GTerm where
  | const (lex : String) (space : String)
  | list  (xs : List GTerm)
  /-- A ground uninterpreted function term. -/
  | fapp  (fn : String) (space : String) (args : List GTerm)
deriving Repr, Inhabited

mutual
protected def GTerm.decEq : (a b : GTerm) → Decidable (a = b)
  | .const l1 s1, .const l2 s2 =>
      if h1 : l1 = l2 then
        if h2 : s1 = s2 then .isTrue (by subst h1; subst h2; rfl)
        else .isFalse (by intro h; cases h; exact h2 rfl)
      else .isFalse (by intro h; cases h; exact h1 rfl)
  | .list xs, .list ys =>
      match GTerm.decEqList xs ys with
      | .isTrue h  => .isTrue (by subst h; rfl)
      | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
  | .fapp f1 s1 a1, .fapp f2 s2 a2 =>
      if h1 : f1 = f2 then
        if h2 : s1 = s2 then
          match GTerm.decEqList a1 a2 with
          | .isTrue h  => .isTrue (by subst h1; subst h2; subst h; rfl)
          | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
        else .isFalse (by intro h; cases h; exact h2 rfl)
      else .isFalse (by intro h; cases h; exact h1 rfl)
  | .const _ _, .list _ => .isFalse (by intro h; cases h)
  | .const _ _, .fapp _ _ _ => .isFalse (by intro h; cases h)
  | .list _, .const _ _ => .isFalse (by intro h; cases h)
  | .list _, .fapp _ _ _ => .isFalse (by intro h; cases h)
  | .fapp _ _ _, .const _ _ => .isFalse (by intro h; cases h)
  | .fapp _ _ _, .list _ => .isFalse (by intro h; cases h)

protected def GTerm.decEqList : (a b : List GTerm) → Decidable (a = b)
  | [],      []      => .isTrue rfl
  | _ :: _,  []      => .isFalse (by intro h; cases h)
  | [],      _ :: _  => .isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
      match GTerm.decEq x y with
      | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
      | .isTrue hx =>
          match GTerm.decEqList xs ys with
          | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
          | .isTrue ht => .isTrue (by subst hx; subst ht; rfl)
end

instance : DecidableEq GTerm := GTerm.decEq

/-- An IRI constant. -/
def gIri (s : String) : GTerm := .const s iriSpace
/-- A typed literal constant. -/
def gLit (lex dt : String) : GTerm := .const lex dt
/-- A plain string is `xs:string`, which is what RIF-PS `"abc"` means. -/
def gStr (s : String) : GTerm := .const s (xsdNs ++ "string")

/-- A term PATTERN: a ground term with variables and applications. -/
inductive Tm where
  | var      (name : String)
  | const    (lex : String) (space : String)
  | list     (xs : List Tm)
  /-- `External( func:… ( args ) )` — a built-in FUNCTION call. -/
  | external (fn : String) (args : List Tm)
  /-- An UNINTERPRETED function term, `f(a b)` with no `External`
      around it. RIF has these; nothing evaluates them, so two such
      terms are equal exactly when their function and arguments are. -/
  | fapp     (fn : String) (space : String) (args : List Tm)
deriving Repr, Inhabited

/-- An ATOMIC formula. -/
inductive Atom where
  | pos          (fn : String) (space : String) (args : List Tm)
  | frame        (o : Tm) (p : Tm) (v : Tm)
  | member       (o c : Tm)
  | sub          (c d : Tm)
  | equal        (a b : Tm)
  /-- `External( pred:… ( args ) )` — a built-in PREDICATE. -/
  | externalPred (fn : String) (args : List Tm)
deriving Repr, Inhabited

inductive Formula where
  | atom   (a : Atom)
  | and    (fs : List Formula)
  | or     (fs : List Formula)
  | exists (vars : List String) (f : Formula)
deriving Repr, Inhabited

/-- A rule: universally quantified variables, a head atom, and an
    optional body. A FACT is a rule with no body. -/
structure Rule where
  vars : List String := []
  head : Atom
  body : Option Formula := none
deriving Repr, Inhabited

structure Document where
  base     : Option String := none
  prefixes : List (String × String) := []
  /-- Each `Import`: the document IRI and the ENTAILMENT PROFILE it
      names. The profile is what says which semantics the imported
      graph is read under, and dropping it made an OWL-Direct import
      look like a plain RDF one. -/
  imports  : List (String × Option String) := []
  rules    : List Rule := []
deriving Repr, Inhabited

end L4Factoidal.RIF
