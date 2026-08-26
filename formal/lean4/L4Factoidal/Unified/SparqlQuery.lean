/-
L4Factoidal.Unified.SparqlQuery — SPARQL 1.1 basic graph patterns as
satisfaction queries over the unified LBase/IKL theory.

Stage 6 of https://github.com/danbri/factoidal/issues/598, per the
design document `docs/designissues/2026-08-25-unified-semantics-lean.md`
§3 (stage 6 signatures), §4.6 (adequacy statements) and §5.4 (the
bag-versus-set delimitation). This module carries the DEFINITIONS and
the syntactic bridge; the model-theoretic gate theorems are in
`Unified/SparqlAdequacy.lean`.

## What a query is here

A basic graph pattern is read as an open sentence: one binary
predication per triple pattern, with a variable spelled as the
reserved free name `varName v` (a `?` followed by the colon-escaped
variable name — colon-free, so it is fresh with respect to every
well-formed IRI, and `?`-initial, so it is disjoint from the
`_`-initial bound blank-node names of `Unified/RdfEmbed.lean`).
Instantiating the query by a solution mapping replaces each bound
variable's name by the embedding of the term it is bound to.

## Three delimitations, stated here and repeated in every theorem

1. **Pattern blank nodes are matched as CONSTANTS.**
   `SPARQL/Algebra.lean`'s `tryBindSubject` / `tryBindTerm` match a
   pattern `.bnode b` only against a graph term `.bnode b'` with
   `b == b'`. SPARQL 1.1 Query §18.3.1 defines BGP matching through a
   *pattern instance mapping*, in which a blank node of the query
   pattern is a NON-DISTINGUISHED VARIABLE that may match any RDF
   term. The engine is narrower. That narrowing is tracked as
   https://github.com/danbri/factoidal/issues/607.
   The narrowing AGREES with the Skolem reading `rdfToTheorySk` used
   here (both then read the label as one free constant), so the gate
   theorem below is a full iff — but on patterns that contain a blank
   node it is adequate TO THE ENGINE, not to the specification.
   `bgpBnodeFree` is the decidable fragment guard on which the two
   readings coincide, and `unified_adequate_bgp_bnodeFree` is the
   corollary that carries it.
2. **No multiplicity claim** (design document §5.4). Everything here
   is at the solution-mapping level: `Answers` is a `Prop`, and the
   evaluator side speaks of MEMBERSHIP in `evalBgp b g`. How many
   copies of a mapping the algebra returns is not addressed, and no
   downstream theorem supplies it either — `SPARQL/AlgebraSpec.lean`
   keeps the §18.5 set layer and the cardinality layer apart, and the
   F\* bag-refinement proof is not ported.
3. **Engine term equality is COARSER than syntactic identity.**
   `RDF.Term.eqb` identifies literals that differ in language-tag CASE
   and `rdf:XMLLiteral` lexical forms that are exclusive-canonical-XML
   equal, and `RDF.Graph.mem` is stated over it. Two such literals
   embed to DIFFERENT CL terms, so a plain CL interpretation may
   separate them. The unified layer therefore evaluates BGP answers
   under `termEqSchema` — one `eq` sentence per `Term.eqb`-equal pair
   — which is the LBase §2.4 axiom-schema mechanism already used for
   the D-entailment value rows (`Unified/DSchema.lean`). Without it
   the soundness direction is FALSE; `SparqlAdequacy.lean` pins the
   separating pair.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfsSchema
import L4Factoidal.Unified.DatalogClosures
import L4Factoidal.Unified.OwlRlSchema
import L4Factoidal.SPARQL.BgpRefinement
import L4Factoidal.RDFS.RegimeDispatch
import L4Factoidal.CL.IklRegime

namespace L4Factoidal.Unified

open L4Factoidal

/-! ## Variable names -/

/-- The reserved CL name of a SPARQL variable: `?` followed by the
colon-escaped variable name. Colon-free (hence distinct from every
well-formed IRI and every `urn:cl:def:` operator) and `?`-initial
(hence distinct from every bound blank-node name, which starts with
`_`). -/
def varName (v : SPARQL.VarName) : String :=
  String.ofList ('?' :: escape v.toList)

theorem varName_toList (v : SPARQL.VarName) :
    (varName v).toList = '?' :: escape v.toList := by
  simp [varName]

theorem varName_no_colon (v : SPARQL.VarName) : ':' ∉ (varName v).toList := by
  rw [varName_toList]
  simp only [List.mem_cons]
  rintro (h | h)
  · exact absurd h (by decide)
  · exact escape_no_colon _ h

theorem varName_ne_iri (v : SPARQL.VarName) (i : RDF.WfIri) :
    varName v ≠ i.val :=
  fun he => varName_no_colon v (he ▸ isIri_has_colon i.property)

theorem varName_ne_bnodeName (v : SPARQL.VarName) (b : RDF.BNodeId) :
    varName v ≠ bnodeName b := by
  intro he
  have h2 := congrArg String.toList he
  rw [varName_toList, bnodeName_toList] at h2
  exact absurd (List.cons.inj h2).1 (by decide)

theorem varName_injective {v w : SPARQL.VarName} (h : varName v = varName w) :
    v = w := by
  have h2 := congrArg String.toList h
  rw [varName_toList, varName_toList] at h2
  exact String.toList_inj.mp (escape_injective (List.cons.inj h2).2)

/-! ## Embedding a pattern position

The concrete-term cases agree with `Unified.embedTerm` /
`Unified.embedSubject` on the nose — that is what makes
`patternAtom_eq_tripleAtom` below a syntactic EQUALITY rather than a
satisfaction lemma. -/

/-- A pattern term under a solution mapping. An unbound variable keeps
its reserved free name. -/
def embedPatternTerm (mu : SPARQL.Binding) : SPARQL.PatternTerm → CL.Term
  | .var v =>
      match mu.lookup v with
      | some t => embedTerm t
      | none => .name (varName v)
  | .iri i => .name i.val
  | .bnode b => .name (bnodeName b)
  | .literal l => .funapp (.name litOp) (embedLiteralArgs l)
  | .tripleTerm s p o =>
      .funapp (.name ttOp)
        [.term (embedPatternTerm mu s), .term (embedPatternTerm mu p),
         .term (embedPatternTerm mu o)]

/-- A pattern subject under a solution mapping. -/
def embedPatternSubject (mu : SPARQL.Binding) : SPARQL.PatternSubject → CL.Term
  | .var v =>
      match mu.lookup v with
      | some t => embedTerm t
      | none => .name (varName v)
  | .iri i => .name i.val
  | .bnode b => .name (bnodeName b)
  | .tripleTerm s p o =>
      .funapp (.name ttOp)
        [.term (embedPatternTerm mu s), .term (embedPatternTerm mu p),
         .term (embedPatternTerm mu o)]

/-- One triple pattern as one binary predication — the same shape
`Unified.tripleAtom` gives a concrete triple. -/
def patternAtom (mu : SPARQL.Binding) (tp : SPARQL.TriplePattern) : CL.Sentence :=
  .atom (embedPatternTerm mu tp.p)
    [.term (embedPatternSubject mu tp.s), .term (embedPatternTerm mu tp.o)]

/-- A basic graph pattern's body: the conjunction of its patterns'
predications. -/
def bgpBody (mu : SPARQL.Binding) (b : SPARQL.Bgp) : CL.Sentence :=
  .conj (b.map (patternAtom mu))

/-! ## Queries -/

/-- A satisfaction query (design document §3, stage 6).

DEVIATION from the document's `structure UQuery where vars : List
VarName; body : CL.Sentence`: the pattern is carried, and `body` is a
derived accessor. The document's shape needs a capture-avoiding
name-substitution over `CL.Sentence` to define `instantiate`; the
bodies this stage produces are quantifier-free conjunctions of atoms,
where substitution and the compositional definition below agree, so
carrying the pattern buys the same statements without a substitution
engine and its non-capture lemma. `UQuery.body` is exactly the open
body the document names (the empty mapping binds nothing). -/
structure UQuery where
  vars : List SPARQL.VarName
  pattern : SPARQL.Bgp
  deriving Repr, DecidableEq

/-- The OPEN body: every variable free under its reserved name. -/
def UQuery.body (q : UQuery) : CL.Sentence := bgpBody [] q.pattern

/-- The body with a solution mapping applied to its free variables. -/
def UQuery.instantiate (q : UQuery) (mu : SPARQL.Binding) : CL.Sentence :=
  bgpBody mu q.pattern

/-- The variables of a pattern term, in occurrence order. -/
def patternTermVars : SPARQL.PatternTerm → List SPARQL.VarName
  | .var v => [v]
  | .iri _ => []
  | .bnode _ => []
  | .literal _ => []
  | .tripleTerm s p o => patternTermVars s ++ patternTermVars p ++ patternTermVars o

def patternSubjectVars : SPARQL.PatternSubject → List SPARQL.VarName
  | .var v => [v]
  | .iri _ => []
  | .bnode _ => []
  | .tripleTerm s p o => patternTermVars s ++ patternTermVars p ++ patternTermVars o

def tpVars (tp : SPARQL.TriplePattern) : List SPARQL.VarName :=
  patternSubjectVars tp.s ++ patternTermVars tp.p ++ patternTermVars tp.o

/-- The variables of a basic graph pattern (duplicates preserved;
every statement below quantifies over MEMBERSHIP). -/
def bgpVars (b : SPARQL.Bgp) : List SPARQL.VarName := b.flatMap tpVars

/-- The query a basic graph pattern poses: its variables are
distinguished, its body is the pattern. -/
def sparqlBgpToQuery (b : SPARQL.Bgp) : UQuery := ⟨bgpVars b, b⟩

/-- μ answers q from `premises`, under a condition bundle and a
schema (design document §3). A `Prop`: no multiplicity is claimed —
delimitation 2 of the module header. -/
def Answers (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (q : UQuery) (mu : SPARQL.Binding) : Prop :=
  EntailsSchema conds S premises (q.instantiate mu)

/-! ## The engine-term-equality schema

Delimitation 3 of the module header. One `eq` row per pair of RDF
terms the engine's `Term.eqb` identifies. The `Term.eqb`-reflexive
rows are trivially true in every interpretation; the rows that do work
are the language-tag-case and `rdf:XMLLiteral` pairs. -/

/-- The engine-term-equality schema: `x = y` for every pair
`RDF.Term.eqb` accepts. -/
def termEqSchema : Schema := fun s =>
  ∃ x y : RDF.Term, RDF.Term.eqb x y = true ∧ s = .eq (embedTerm x) (embedTerm y)

/-- A BGP query's schema over a regime schema: the regime's rows plus
the engine-term-equality rows. -/
def bgpSchema (S : Schema) : Schema := schemaUnion termEqSchema S

/-- Reading the schema back: a satisfying interpretation gives equal
denotations to the embeddings of `Term.eqb`-equal terms. -/
theorem denot_embedTerm_congr_of_schema {i : CL.Interp}
    (hS : SatisfiesSchema i termEqSchema) {x y : RDF.Term}
    (h : RDF.Term.eqb x y = true) :
    CL.denotTerm i i.iName (fun _ => []) (embedTerm x)
      = CL.denotTerm i i.iName (fun _ => []) (embedTerm y) := by
  simpa [CL.Satisfies, CL.Sat] using hS _ ⟨x, y, h, rfl⟩

/-! ## The syntactic bridge

When a solution mapping instantiates a triple pattern to a concrete
triple, the pattern's predication and that triple's predication are
THE SAME SENTENCE. Everything the stage proves about answers goes
through this equality, so the model theory never has to reason about
pattern syntax. -/

section Bridge

open L4Factoidal.SPARQL

theorem embedTerm_of_toSubject? {t : RDF.Term} {s : RDF.Subject}
    (h : t.toSubject? = some s) : embedTerm t = embedSubject s := by
  cases t
  · simp only [RDF.Term.toSubject?, Option.some.injEq] at h; subst h; rfl
  · simp only [RDF.Term.toSubject?, Option.some.injEq] at h; subst h; rfl
  · simp [RDF.Term.toSubject?] at h
  · simp [RDF.Term.toSubject?] at h

theorem embedPatternSubject_inst {mu : Binding} {ps : PatternSubject}
    {s : RDF.Subject} (h : instSubject id mu ps = some s) :
    embedPatternSubject mu ps = embedSubject s := by
  cases ps with
  | iri i => simp only [instSubject, Option.some.injEq] at h; subst h; rfl
  | bnode b => simp only [instSubject, Option.some.injEq] at h; subst h; rfl
  | tripleTerm a b c => simp [instSubject] at h
  | var v =>
      simp only [instSubject] at h
      simp only [embedPatternSubject]
      split at h <;>
        first
          | (simp only [Option.some.injEq] at h; subst h;
             simp_all [embedTerm, embedSubject])
          | simp at h

theorem embedPatternTerm_inst {mu : Binding} :
    ∀ {pt : PatternTerm} {t : RDF.Term},
      instObject id mu pt = some t → embedPatternTerm mu pt = embedTerm t
  | .iri i, t, h => by
      simp only [instObject, Option.some.injEq] at h; subst h; rfl
  | .bnode b, t, h => by
      simp only [instObject, Option.some.injEq] at h; subst h; rfl
  | .literal l, t, h => by
      simp only [instObject, Option.some.injEq] at h; subst h; rfl
  | .var v, t, h => by
      simp only [instObject] at h
      simp [embedPatternTerm, h]
  | .tripleTerm ps pp po, t, h => by
      simp only [instObject] at h
      split at h
      · exact absurd h (by simp)
      · next st h1 =>
          split at h
          · exact absurd h (by simp)
          · next ss h2 =>
              split at h
              · next pi h3 =>
                  split at h
                  · exact absurd h (by simp)
                  · next ot h4 =>
                      cases h
                      simp only [embedPatternTerm, embedTerm]
                      rw [embedPatternTerm_inst h1, embedTerm_of_toSubject? h2,
                          embedPatternTerm_inst h3, embedPatternTerm_inst h4]
                      simp [embedTerm]
              · exact absurd h (by simp)

theorem embedPatternTerm_constructPredicate {mu : Binding} {pt : PatternTerm}
    {p : RDF.WfIri} (h : constructPredicate pt mu = some p) :
    embedPatternTerm mu pt = .name p.val := by
  cases pt with
  | iri i => simp_all [constructPredicate, embedPatternTerm]
  | bnode b => simp [constructPredicate] at h
  | literal l => simp [constructPredicate] at h
  | tripleTerm a b c => simp [constructPredicate] at h
  | var v =>
      simp only [constructPredicate] at h
      simp only [embedPatternTerm]
      split at h <;> simp_all [embedTerm]

/-- **The bridge**: a pattern that a solution mapping instantiates to
a concrete triple has THAT TRIPLE's predication as its own. -/
theorem patternAtom_eq_tripleAtom {mu : Binding} {tp : TriplePattern}
    {t : RDF.Triple} (h : instTriple id mu tp = some t) :
    patternAtom mu tp = tripleAtom t := by
  simp only [instTriple] at h
  split at h
  · exact absurd h (by simp)
  · next s h1 =>
      split at h
      · exact absurd h (by simp)
      · next p h2 =>
          split at h
          · exact absurd h (by simp)
          · next o h3 =>
              cases h
              simp only [patternAtom, tripleAtom]
              rw [embedPatternSubject_inst h1,
                  embedPatternTerm_constructPredicate h2,
                  embedPatternTerm_inst h3]

end Bridge

/-! ## The pivot relation

`BgpMatches` is the syntactic condition both halves of the stage meet
at: every triple pattern instantiates under μ, and the triple it
instantiates to is a triple of the graph by ENGINE equality
(`Graph.mem`, i.e. `Term.eqb` — delimitation 3). -/

/-- Every pattern of `b` instantiates under `mu` into `g`. -/
def BgpMatches (mu : SPARQL.Binding) (b : SPARQL.Bgp) (g : RDF.Graph) : Prop :=
  ∀ tp ∈ b, ∃ t : RDF.Triple,
    SPARQL.instTriple id mu tp = some t ∧ RDF.Graph.mem t g = true

/-! ## Fragment guards -/

/-- A pattern term with no triple-term position — the RDF 1.2
quarantine predicate of `RDF/EntailmentSimpleSpec.lean`, at pattern
level. The model-theoretic completeness half needs it for the same
reason `RDF.herbrand` does: a triple term has no denotation in the
baseline model theory, and the constant the term model gives it would
identify distinct triple terms. -/
def PatternTermTtFree : SPARQL.PatternTerm → Prop
  | .var _ => True
  | .iri _ => True
  | .bnode _ => True
  | .literal _ => True
  | .tripleTerm _ _ _ => False

def PatternSubjectTtFree : SPARQL.PatternSubject → Prop
  | .var _ => True
  | .iri _ => True
  | .bnode _ => True
  | .tripleTerm _ _ _ => False

def TpTtFree (tp : SPARQL.TriplePattern) : Prop :=
  PatternSubjectTtFree tp.s ∧ PatternTermTtFree tp.p ∧ PatternTermTtFree tp.o

def BgpTtFree (b : SPARQL.Bgp) : Prop := ∀ tp ∈ b, TpTtFree tp

/-- Decidable check for a pattern position free of blank nodes. -/
def patternTermBnodeFree : SPARQL.PatternTerm → Bool
  | .var _ => true
  | .iri _ => true
  | .bnode _ => false
  | .literal _ => true
  | .tripleTerm s p o =>
      patternTermBnodeFree s && patternTermBnodeFree p && patternTermBnodeFree o

def patternSubjectBnodeFree : SPARQL.PatternSubject → Bool
  | .var _ => true
  | .iri _ => true
  | .bnode _ => false
  | .tripleTerm s p o =>
      patternTermBnodeFree s && patternTermBnodeFree p && patternTermBnodeFree o

/-- **The §18.3.1 fragment guard** (delimitation 1;
https://github.com/danbri/factoidal/issues/607): a basic graph pattern
with no blank node anywhere. On this fragment the engine's
constant reading of pattern blank nodes and the specification's
pattern-instance-mapping reading cannot differ, because there is no
pattern blank node to read either way. -/
def bgpBnodeFree (b : SPARQL.Bgp) : Bool :=
  b.all (fun tp =>
    patternSubjectBnodeFree tp.s && patternTermBnodeFree tp.p &&
    patternTermBnodeFree tp.o)

/-! ## Regime dispatch

The design document's `regimeToSchema`. Two deviations, both forced
by what the tree contains:

* the RDFS rows need a `RDF.DatatypeSet` (stage 2 correction note 9b),
  so that is a parameter alongside the recognised `D`;
* the `x-ikl-*` family is a dataset TRANSFORM, not a closure and not a
  schema (`CL/IklRegime.lean`'s `extendDataset`). It maps to the empty
  schema here, and its content is the premise-list transform
  `iklPremises` in `SparqlAdequacy.lean`.

**Which closure a regime string actually selects.** `regimeToSchema`
is the SPECIFICATION table: it resolves the four W3C names of
`RDF.Regime.ofName?` and the two experimental names of
`RDFS/RegimeDispatch.lean`. The ENGINE dispatcher
`RDFS.entailmentClosureForQueryExt` is narrower: it recognises
`x-rdfscore` and `x-rdfsplus` and routes EVERY other string —
`"RDFS"`, `"OWL-RL"`, `"simple"`, a typo — to `OWL.RL.closure`. The
two tables therefore disagree on `"RDFS"`; `regimeDispatchSchema`
below is what the dispatcher selects, and
`regime_tables_disagree_on_rdfs` pins the disagreement so no row of
this stage can be read as a claim about the other table. -/

/-- The specification table: regime string to schema plus condition
bundle. -/
def regimeToSchema (regime : String) (Dset : RDF.DatatypeSet)
    (D : List RDF.WfIri) : Option (Schema × (CL.Interp → Prop)) :=
  match RDF.Regime.ofName? regime with
  | some .simple => some (emptySchema, condTrue)
  | some .d => some (dSchema D, condTrue)
  | some .rdf => some (rdfSchema, condTrue)
  | some .rdfs => some (rdfsSchema Dset, condTrue)
  | none =>
      if regime = RDFS.regimeXRdfsCore then some (rdfsCoreSchema, condTrue)
      else if regime = RDFS.regimeXRdfsPlus then
        some (rdfsPlusProgram.toSchema, condTrue)
      else match CL.IklRegime.parse? regime with
        | some _ => some (emptySchema, condTrue)
        | none => none

/-- The schema of the closure `RDFS.entailmentClosureForQueryExt`
ACTUALLY selects for a regime string — the engine table, including its
fall-through. -/
def regimeDispatchSchema (regime : String) : Schema × (CL.Interp → Prop) :=
  if regime = RDFS.regimeXRdfsCore then (rdfsCoreSchema, condTrue)
  else if regime = RDFS.regimeXRdfsPlus then
    (rdfsPlusProgram.toSchema, condTrue)
  else (owlRlSchema, OwlRlInterpCond)

/-! ## Build-time checks -/

section Checks

#guard varName "x" == "?x"
#guard varName "a:b" == "?a%cb"
#guard decide (varName "x" ≠ bnodeName "x")
#guard bgpBnodeFree []
#guard bgpBnodeFree [{ s := .var "s", p := .var "p", o := .var "o" }]
#guard ! bgpBnodeFree [{ s := .bnode "b", p := .var "p", o := .var "o" }]
#guard ! bgpBnodeFree [{ s := .var "s", p := .var "p", o := .bnode "b" }]
#guard (regimeToSchema "nonsense" RDF.dMinimal []).isNone
#guard (regimeToSchema "simple" RDF.dMinimal []).isSome
#guard (regimeToSchema "RDFS" RDF.dMinimal []).isSome
#guard (regimeToSchema "x-rdfscore" RDF.dMinimal []).isSome
#guard (regimeToSchema "x-rdfsplus" RDF.dMinimal []).isSome
#guard (regimeToSchema "x-ikl-flat" RDF.dMinimal []).isSome

/-! The engine dispatcher sends `"RDFS"` to the OWL RL closure, which
is NOT the RDFS schema the specification table names. Pinned, per the
module header. -/
#guard RDFS.entailmentClosureForQueryExt "RDFS" [] 1 ==
  L4Factoidal.OWL.RL.closure [] 1

end Checks

end L4Factoidal.Unified
