/-
L4Factoidal.Unified.RifEmbed — RIF Core as an instance of the stage 3
Datalog class of the unified model theory
(https://github.com/danbri/factoidal/issues/612; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §4.7).

## What this module delivers

* `rifCoreToTheory : RifRuleSet → List CL.Sentence` — a RIF Core rule
  set as universally closed implications over the SAME binary triple
  predications the rest of the unified layer uses
  (`Unified/RdfEmbed.lean`'s `tripleAtom`), through the frame /
  member / subclass desugaring the RIF/RDF/OWL combination
  specification fixes (https://www.w3.org/TR/rif-rdf-owl/ §5) and
  `RIF/Translation.lean` already implements:

      o[p -> v]   =>  (o, p, v)
      o # c       =>  (o, rdf:type, c)
      sub ## sup  =>  (sub, rdfs:subClassOf, sup)

  A positional atom `p(a1 … an)` becomes the n-ary predication
  `p(a1 … an)` directly, at ANY arity, through the n-ary `DAtom`
  machinery of `Unified/Datalog.lean`. At arity 2 that IS the triple
  predication, so `p(s,o)` and `s[p -> o]` coincide — the same
  identification `RIF/Translation.lean` makes.
* `rifDRules` / `rifCoreProgram?` — the rule set as a value of the
  stage 3 class, `DRule.wfB` discharged as a PROOF field, so an
  existential head (a head variable no body atom binds) cannot be
  written into the program at all.
* `rifCore_lfp_iff_entails_atom` and `rifCore_lfp_iff_entails` — the
  gate theorems, FULL IFFs, obtained by instantiating the two generic
  least-fixpoint theorems of `Unified/Datalog.lean` rather than by
  re-proving them.
* Non-vacuity: the schema is satisfiable for every rule set
  (`rifCoreToTheory_satisfiable`) and the entailment relation is not
  the everything-relation (`rifCore_demo_not_entailed`).

## THE DEVIATION FROM §4.7, STATED PLAINLY

The design document sketches

    theorem unified_adequate_rifCore (rs : RIF.RuleSet) (g : RDF.Graph)
        (t : RDF.Triple) :
        t ∈ RIF.Engine.saturate rs g fuel ↔ EntailsSchema …

with the NATIVE forward-chaining engine on the left. That theorem is
NOT landed, and not because of an accident of effort:

`RIF/Engine.lean`'s `groundTm`, `matchFormula` and `qualifyTm` are
`partial def`. A Lean `partial def` is compiled to an opaque constant
with no equation lemmas and no kernel reduction. Nothing about what
`matchFormula` COMPUTES is available to a proof, and `decide` cannot
evaluate it either. `RIF/EngineTheorems.lean` is written around that
limit: its `Licensed` predicate mentions `matchFormula`'s output
rather than characterising it, which is why it proves PROVENANCE and
explicitly declines to call itself soundness. Any theorem relating
`RIF.closure` (or `RIF.Saturate.saturateGraph`, which calls it) to
the Datalog fixpoint needs exactly the missing fact — that a
substitution `matchFormula` returns makes the body true in the fact
set — so it cannot be stated, let alone proved, while those three
definitions are `partial`.

What is landed instead: the left-hand side is
`DatalogProgram.lfp`, the total least fixpoint of the SAME rules read
as a Datalog program. Agreement with the native engine is pinned by
build-time `#guard`s over `RIF.Saturate.saturateGraph`
(`rifEngineDatalogAgrees`), which run under compiled evaluation and
therefore CAN see through the `partial def`s. That is evidence, at
the strength `Unified/DatalogClosures.lean` labels its RDFS-Plus
demos with — not a theorem. Making the three definitions total is the
prerequisite for the §4.7 statement; it is recorded in the registry
and in correction note 16 of the design document.

Two further, smaller deviations:

* There is no `RIF.RuleSet` type in the tree; a rule set is
  `List RIF.Rule`. `RifRuleSet` abbreviates it here rather than
  editing `RIF/Syntax.lean` and rebuilding the RIF subtree.
* `RIF.Engine.saturate` does not exist either. The graph-level
  entry point is `RIF.Saturate.saturateGraph`.

## THE FRAGMENT GUARDS, AND WHAT THEY EXCLUDE

`rifCoreFragmentB` is the class gate on the rule side. It rejects:

* `Equal` and `External(pred:…)` body atoms — the Datalog class has
  no equality atom and no built-in predicate. RIF-DTB built-ins are
  therefore outside; the native engine answers `.undecided` for the
  ones it cannot decide, and the unified layer says nothing at all.
* `Or` and `Exists` bodies — no disjunctive bodies in a definite Horn
  program, and an existentially quantified body variable is not a
  Datalog variable. `RIF/Translation.lean` refuses the same two.
* `List`, `External(func:…)` and uninterpreted function terms — the
  class has NO function symbols (`DTerm` is a variable or a
  constant).
* Constants outside `rif:iri` space, and `rif:iri` constants whose
  lexical form is not a well-formed IRI. This is what keeps
  `rifCoreConstName` the IDENTITY on the fragment, which in turn is
  what makes the Datalog sentences literally equal to
  `Unified/RdfEmbed.lean`'s `tripleAtom` sentences instead of living
  in a tagged vocabulary of their own (the price
  `Unified/DatalogClosures.lean` pays with its `"i:"` / `"b:"` tags).
  Off the fragment `rifCoreConstName` mints a `urn:rif:c:` name;
  nothing is proved about those.
* Variable names containing a colon — the colon discipline of
  `Unified/Datalog.lean`, which is what makes the universal closure
  capture-free.
* Rules whose head carries a variable the body does not bind. RIF's
  own `RIF.ruleSafe` rejects these too; here they are rejected by the
  class's `DRule.definiteB`, so the program cannot be built.

On the DATA side the guards are `TripleIriOnly` / `GraphIriOnly`: the
subject and object of every triple must be an IRI. Blank nodes are
excluded because `Unified/RdfEmbed.lean` spells a blank-node bound
name COLON-FREE by construction, which is exactly what the Datalog
class forbids in a constant; literals are excluded because
`embedTerm` maps a literal to a FUNCTIONAL term and the class has no
function symbols. Both exclusions are consequences of the class, not
of the encoding chosen here.

## A DIVERGENCE FROM THE NATIVE ENGINE, RECORDED

`RIF/Saturate.lean` reads a triple `s p o` as the frame `s[p -> o]`,
and additionally as `s # o` when `p` is `rdf:type` and as `s ## o`
when `p` is `rdfs:subClassOf`. Facts the engine DERIVES do not get
that treatment: a derived `member` atom is not also entered as a
frame. Under the desugaring here both readings collapse onto the one
triple predication, so a rule with a `?x[rdf:type -> ?c]` body fires
on a derived membership in the Datalog reading and does not in the
engine. Programs of that shape are outside what the `#guard`s pin;
the theorems below are unaffected, since they never mention the
engine.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.Datalog
import L4Factoidal.Unified.SparqlAdequacy
import L4Factoidal.RIF.Translation
import L4Factoidal.RIF.Saturate

namespace L4Factoidal.Unified

/-- A RIF Core rule set. `RIF/Syntax.lean` has no `RuleSet` type; a
document's rules are a `List RIF.Rule`. -/
abbrev RifRuleSet := List RIF.Rule

/-! ## Constants -/

/-- A RIF constant as a Datalog constant. On the fragment
(`rif:iri` space, well-formed IRI lexical form) this is the IDENTITY,
which is what makes the resulting sentences the unified layer's own
triple predications. Off the fragment it mints a reserved
`urn:rif:c:` name, length-prefixed on the symbol space so the
encoding is injective; no theorem below depends on those. -/
def rifCoreConstName (lex space : String) : String :=
  if space == RIF.iriSpace && RDF.isIri lex then lex
  else "urn:rif:c:" ++ toString space.length ++ ":" ++ space ++ lex

/-! ## Terms -/

def rifTmOk : RIF.Tm → Bool
  | .var v => !(v.toList.contains ':')
  | .const lex space => space == RIF.iriSpace && RDF.isIri lex
  | .list _ => false
  | .external _ _ => false
  | .fapp _ _ _ => false

def rifTmD : RIF.Tm → DTerm
  | .var v => .v v
  | .const lex space => .c (rifCoreConstName lex space)
  | .list _ => .c "urn:rif:unsupported:list"
  | .external f _ => .c ("urn:rif:unsupported:external:" ++ f)
  | .fapp f _ _ => .c ("urn:rif:unsupported:fapp:" ++ f)

/-! ## Atoms — the combination specification's desugaring -/

def rdfTypeD : DTerm := .c RDFS.rdfType.val
def rdfsSubClassOfD : DTerm := .c RDFS.rdfsSubClassOf.val

def rifAtomOk : RIF.Atom → Bool
  | .frame o p v => rifTmOk o && rifTmOk p && rifTmOk v
  | .member o c => rifTmOk o && rifTmOk c
  | .sub c d => rifTmOk c && rifTmOk d
  | .pos fn space args =>
      space == RIF.iriSpace && RDF.isIri fn && args.all rifTmOk
  | .equal _ _ => false
  | .externalPred _ _ => false

def rifAtomD : RIF.Atom → DAtom
  | .frame o p v => ⟨rifTmD p, [rifTmD o, rifTmD v]⟩
  | .member o c => ⟨rdfTypeD, [rifTmD o, rifTmD c]⟩
  | .sub c d => ⟨rdfsSubClassOfD, [rifTmD c, rifTmD d]⟩
  | .pos fn space args => ⟨.c (rifCoreConstName fn space), args.map rifTmD⟩
  | .equal a b => ⟨.c "urn:rif:unsupported:equal", [rifTmD a, rifTmD b]⟩
  | .externalPred f args =>
      ⟨.c ("urn:rif:unsupported:pred:" ++ f), args.map rifTmD⟩

/-! ## Rules -/

/-! ### Flattening a conjunctive body

`RIF/Translation.lean`'s `collectAtoms` has exactly these clauses, and
this is its structural twin, clause for clause. It is restated rather
than reused for one reason: `collectAtoms` recurses through a `foldr`
closure, so Lean compiles it by WELL-FOUNDED recursion, and a
well-founded definition does not reduce in the kernel — `decide` gets
stuck on it. The mutual pair below is structural over the nested
`Formula` / `List Formula` inductive, so every fragment check and every
demo instance below is `decide`-dischargeable. `rifCollect_agrees` pins
the two against each other on the demo rules. -/

mutual

def rifCollect : RIF.Formula → Option (List RIF.Atom)
  | .atom a => some [a]
  | .and fs => rifCollectList fs
  | .or _ => none
  | .exists _ _ => none

def rifCollectList : List RIF.Formula → Option (List RIF.Atom)
  | [] => some []
  | f :: r =>
      match rifCollect f, rifCollectList r with
      | some xs, some ys => some (xs ++ ys)
      | _, _ => none

end

/-- The body atoms of a rule. A FACT (no body) has none. -/
def rifBodyAtoms (r : RIF.Rule) : Option (List RIF.Atom) :=
  match r.body with
  | none => some []
  | some f => rifCollect f

def rifRuleD (r : RIF.Rule) : Option DRule :=
  match rifBodyAtoms r with
  | none => none
  | some bs => some ⟨rifAtomD r.head, bs.map rifAtomD⟩

/-- The class gate on one rule: the body flattens, every atom is in
the fragment, and the resulting Datalog rule meets the class's own
well-formedness (colon discipline plus definiteness). -/
def rifRuleOk (r : RIF.Rule) : Bool :=
  match rifBodyAtoms r with
  | none => false
  | some bs =>
      rifAtomOk r.head && bs.all rifAtomOk &&
        DRule.wfB ⟨rifAtomD r.head, bs.map rifAtomD⟩

def rifCoreFragmentB (rs : RifRuleSet) : Bool := rs.all rifRuleOk

def rifDRules (rs : RifRuleSet) : List DRule := rs.filterMap rifRuleD

/-- The rule set as a program of the stage 3 class, when every rule is
in the fragment. -/
def rifCoreProgram? (rs : RifRuleSet) : Option DatalogProgram :=
  if h : (rifDRules rs).all DRule.wfB = true then some ⟨rifDRules rs, h⟩
  else none

/-- **RIF Core rules as sentences** (design document §4.7): one
universally closed implication per rule, over the unified layer's
triple predications. -/
def rifCoreToTheory (rs : RifRuleSet) : List CL.Sentence :=
  (rifDRules rs).map DRule.sentence

/-! ### The program's rules are the translated rules -/

theorem rifRuleD_wf {r : RIF.Rule} {d : DRule}
    (hok : rifRuleOk r = true) (hd : rifRuleD r = some d) : d.wfB = true := by
  unfold rifRuleOk at hok
  unfold rifRuleD at hd
  cases hb : rifBodyAtoms r with
  | none => rw [hb] at hd; exact absurd hd (by simp)
  | some bs =>
      rw [hb] at hd
      rw [hb] at hok
      simp only [Option.some.injEq] at hd
      subst hd
      simp only [Bool.and_eq_true] at hok
      exact hok.2

theorem rifCoreProgram_rules {rs : RifRuleSet} {p : DatalogProgram}
    (hp : rifCoreProgram? rs = some p) : p.rules = rifDRules rs := by
  unfold rifCoreProgram? at hp
  split at hp
  · injection hp with hp
    exact (congrArg DatalogProgram.rules hp).symm
  · exact absurd hp (by simp)

/-- Every rule set in the fragment IS a program of the class. -/
theorem rifCoreProgram_of_fragment {rs : RifRuleSet}
    (h : rifCoreFragmentB rs = true) :
    ∃ p : DatalogProgram, rifCoreProgram? rs = some p ∧ p.rules = rifDRules rs := by
  have hall : (rifDRules rs).all DRule.wfB = true := by
    refine List.all_eq_true.mpr ?_
    intro d hd
    obtain ⟨r, hr, hrd⟩ := List.mem_filterMap.mp hd
    exact rifRuleD_wf (List.all_eq_true.mp h r hr) hrd
  refine ⟨⟨rifDRules rs, hall⟩, ?_, rfl⟩
  unfold rifCoreProgram?
  rw [dif_pos hall]

/-- The program's schema and the sentence list are the same set. -/
theorem rifCoreToTheory_schema {rs : RifRuleSet} {p : DatalogProgram}
    (hp : p.rules = rifDRules rs) :
    ∀ s, p.toSchema s ↔ s ∈ rifCoreToTheory rs := by
  intro s
  simp only [DatalogProgram.toSchema, rifCoreToTheory, hp]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · intro hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact ⟨r, hr, rfl⟩

/-! ## The data side: graphs as fact bases -/

def subjIriD : RDF.Subject → Option RDF.WfIri
  | .iri i => some i
  | .bnode _ => none

def objIriD : RDF.Term → Option RDF.WfIri
  | .iri i => some i
  | .bnode _ => none
  | .literal _ => none
  | .tripleTerm _ _ _ => none

def rifSubjD : RDF.Subject → DTerm
  | .iri i => .c i.val
  | .bnode b => .c ("urn:rif:b:" ++ b)

def rifObjD : RDF.Term → DTerm
  | .iri i => .c i.val
  | .bnode b => .c ("urn:rif:b:" ++ b)
  | .literal l =>
      .c ("urn:rif:lit:" ++ toString l.val.datatype.val.length ++ ":"
            ++ l.val.datatype.val ++ l.val.lexicalForm)
  | .tripleTerm _ _ _ => .c "urn:rif:tt"

/-- A triple as a binary Datalog fact, the property in operator
position — the same reading `tripleAtom` gives it. -/
def rifTripleFact (t : RDF.Triple) : DAtom :=
  ⟨.c t.p.val, [rifSubjD t.s, rifObjD t.o]⟩

def rifGraphFacts (g : RDF.Graph) : List DAtom := g.map rifTripleFact

theorem rifSubjD_ground (s : RDF.Subject) : (rifSubjD s).groundB = true := by
  cases s <;> rfl

theorem rifObjD_ground (o : RDF.Term) : (rifObjD o).groundB = true := by
  cases o <;> rfl

theorem rifTripleFact_ground (t : RDF.Triple) :
    (rifTripleFact t).groundB = true := by
  cases hs : t.s <;> cases ho : t.o <;>
    simp [DAtom.groundB, rifTripleFact, DTerm.groundB, rifSubjD, rifObjD,
          hs, ho]

theorem rifGraphFacts_ground (g : RDF.Graph) :
    ∀ b ∈ rifGraphFacts g, b.groundB = true := by
  intro b hb
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
  exact rifTripleFact_ground t

/-! ## The data-side fragment guard -/

/-- The subject and object are both IRIs. See the module header for
why blank nodes and literals are outside the class. -/
def TripleIriOnly (t : RDF.Triple) : Prop :=
  ∃ si oi : RDF.WfIri, t.s = .iri si ∧ t.o = .iri oi

def tripleIriOnlyB (t : RDF.Triple) : Bool :=
  (subjIriD t.s).isSome && (objIriD t.o).isSome

def GraphIriOnly (g : RDF.Graph) : Prop := ∀ t ∈ g, TripleIriOnly t

def graphIriOnlyB (g : RDF.Graph) : Bool := g.all tripleIriOnlyB

theorem tripleIriOnly_of_check : ∀ {t : RDF.Triple},
    tripleIriOnlyB t = true → TripleIriOnly t := by
  rintro ⟨s, p, o⟩ h
  cases s with
  | bnode b => simp [tripleIriOnlyB, subjIriD] at h
  | iri si =>
      cases o with
      | iri oi => exact ⟨si, oi, rfl, rfl⟩
      | bnode b => simp [tripleIriOnlyB, subjIriD, objIriD] at h
      | literal l => simp [tripleIriOnlyB, subjIriD, objIriD] at h
      | tripleTerm a b c => simp [tripleIriOnlyB, subjIriD, objIriD] at h

theorem graphIriOnly_of_check {g : RDF.Graph} (h : graphIriOnlyB g = true) :
    GraphIriOnly g :=
  fun t ht => tripleIriOnly_of_check (List.all_eq_true.mp h t ht)

/-! ## The encoded sentences ARE the unified layer's triple
predications -/

theorem rifTripleFact_sentence {t : RDF.Triple} (h : TripleIriOnly t) :
    (rifTripleFact t).sentence = tripleAtom t := by
  obtain ⟨si, oi, hs, ho⟩ := h
  simp [DAtom.sentence, rifTripleFact, tripleAtom, hs, ho, rifSubjD,
        rifObjD, DTerm.toCl, embedSubject, embedTerm]

theorem rifGraphFacts_sentences {g : RDF.Graph} (h : GraphIriOnly g) :
    (rifGraphFacts g).map DAtom.sentence = g.map tripleAtom := by
  simp only [rifGraphFacts, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun t ht => rifTripleFact_sentence (h t ht))

/-! ## Premise and conclusion transport -/

theorem entailsSchema_congr {conds : CL.Interp → Prop} {S S' : Schema}
    {ps qs : List CL.Sentence} {c c' : CL.Sentence}
    (hS : ∀ s, S s ↔ S' s)
    (hp : ∀ i : CL.Interp, CL.SatisfiesAll i ps ↔ CL.SatisfiesAll i qs)
    (hc : ∀ i : CL.Interp, CL.Satisfies i c ↔ CL.Satisfies i c') :
    EntailsSchema conds S ps c ↔ EntailsSchema conds S' qs c' := by
  constructor
  · intro h i hci hsi hsat
    exact (hc i).mp (h i hci (fun s hs => hsi s ((hS s).mp hs)) ((hp i).mpr hsat))
  · intro h i hci hsi hsat
    exact (hc i).mpr (h i hci (fun s hs => hsi s ((hS s).mpr hs)) ((hp i).mp hsat))

/-- The list of a graph's triple predications and the single Skolem
sentence `rdfToTheorySk g` are satisfied by exactly the same
interpretations. -/
theorem satisfiesAll_tripleAtoms_iff (i : CL.Interp) (g : RDF.Graph) :
    CL.SatisfiesAll i (g.map tripleAtom) ↔
      CL.SatisfiesAll i [rdfToTheorySk g] := by
  constructor
  · intro h s hs
    obtain rfl := List.mem_singleton.mp hs
    exact (satisfies_rdfToTheorySk_iff i g).mpr
      (fun t ht => h _ (List.mem_map.mpr ⟨t, ht, rfl⟩))
  · intro h s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact (satisfies_rdfToTheorySk_iff i g).mp
      (h _ (List.mem_singleton.mpr rfl)) t ht

theorem graphBnodeNames_single_nil {t : RDF.Triple} (h : TripleIriOnly t) :
    graphBnodeNames [t] = [] := by
  obtain ⟨si, oi, hs, ho⟩ := h
  simp [graphBnodeNames, RDF.graphBnodeIds, RDF.tripleBnodes,
        RDF.subjectBnodes, RDF.termBnodes, hs, ho]

/-- A single blank-node-free triple's translation is its predication:
the existential closure binds nothing. -/
theorem satisfies_rdfToTheory_single (i : CL.Interp) {t : RDF.Triple}
    (h : TripleIriOnly t) :
    CL.Satisfies i (rdfToTheory [t]) ↔ CL.Satisfies i (tripleAtom t) := by
  have hb := graphBnodeNames_single_nil h
  have hsk : CL.Satisfies i (rdfToTheorySk [t]) ↔ CL.Satisfies i (tripleAtom t) := by
    rw [satisfies_rdfToTheorySk_iff]
    constructor
    · intro hh; exact hh t (by simp)
    · intro hh u hu; simpa [List.mem_singleton.mp hu] using hh
  simpa [rdfToTheory, rdfToTheorySk, hb, CL.Satisfies, CL.Sat, CL.SatExists]
    using hsk

/-! ## The gate theorems -/

/-- **The RIF Core gate theorem, n-ary form.** For a rule set read as
a program of the stage 3 class, over an IRI-only graph, with adequate
fuel: a ground atom is in the least fixpoint EXACTLY WHEN the
rules-as-sentences plus the graph's Skolem reading entail its
predication, over every CL interpretation.

Strength: a FULL IFF. Its hypotheses are `hp` (the program is the
rule set's translation), `hg` (`GraphIriOnly`), `hga` (the queried
atom is ground) and `hfa` (fuel adequacy, `decide`-dischargeable via
`saturatedCheck`). None of them mentions the conclusion. The left-hand
side is the DATALOG least fixpoint, not the native RIF engine — see
the module header. -/
theorem rifCore_lfp_iff_entails_atom (rs : RifRuleSet) (p : DatalogProgram)
    (hp : p.rules = rifDRules rs) (g : RDF.Graph) (hg : GraphIriOnly g)
    (a : DAtom) (hga : a.groundB = true) (fuel : Nat)
    (hfa : p.FuelAdequate (rifGraphFacts g) fuel) :
    a ∈ p.lfp (rifGraphFacts g) fuel ↔
      EntailsSchema condTrue (fun s => s ∈ rifCoreToTheory rs)
        [rdfToTheorySk g] a.sentence := by
  rw [datalog_lfp_iff_entails p (rifGraphFacts_ground g) hga hfa]
  exact entailsSchema_congr (rifCoreToTheory_schema hp)
    (fun i => by
      rw [rifGraphFacts_sentences hg]; exact satisfiesAll_tripleAtoms_iff i g)
    (fun _ => Iff.rfl)

/-- **The RIF Core gate theorem, §4.7's triple form.** Same strength,
same hypotheses, plus `TripleIriOnly` on the queried triple. -/
theorem rifCore_lfp_iff_entails (rs : RifRuleSet) (p : DatalogProgram)
    (hp : p.rules = rifDRules rs) (g : RDF.Graph) (hg : GraphIriOnly g)
    (t : RDF.Triple) (ht : TripleIriOnly t) (fuel : Nat)
    (hfa : p.FuelAdequate (rifGraphFacts g) fuel) :
    rifTripleFact t ∈ p.lfp (rifGraphFacts g) fuel ↔
      EntailsSchema condTrue (fun s => s ∈ rifCoreToTheory rs)
        [rdfToTheorySk g] (rdfToTheory [t]) := by
  rw [rifCore_lfp_iff_entails_atom rs p hp g hg (rifTripleFact t)
        (rifTripleFact_ground t) fuel hfa]
  exact entailsSchema_congr (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun i => by
      rw [rifTripleFact_sentence ht]
      exact (satisfies_rdfToTheory_single i ht).symm)

/-! ## Non-vacuity, part 1: the schema is satisfiable

A theorem whose schema nothing satisfies proves nothing
(anti-pattern #29 / `RDF/SemanticsHypothesisWitness.lean`). -/

theorem rifCoreToTheory_satisfiable (rs : RifRuleSet) (p : DatalogProgram)
    (hp : p.rules = rifDRules rs) :
    ∃ i : CL.Interp, SatisfiesSchema i (fun s => s ∈ rifCoreToTheory rs) := by
  obtain ⟨i, hi⟩ := toSchema_satisfiable p
  exact ⟨i, fun s hs => hi s ((rifCoreToTheory_schema hp s).mpr hs)⟩

/-! ## The boundary, pinned -/

private def bnd (s : String) : RIF.Tm := .const ("http://b.example/" ++ s) RIF.iriSpace

/-- A head variable no body atom binds — the existential-head shape.
Rejected by the class's definiteness gate, so it cannot be written
into a program. -/
def rifExistentialHeadRule : RIF.Rule :=
  { vars := ["x", "w"], head := .member (.var "w") (bnd "D"),
    body := some (.atom (.member (.var "x") (bnd "C"))) }

theorem rifExistentialHeadRule_rejected :
    rifRuleOk rifExistentialHeadRule = false := by decide

/-- An `Equal` body atom: no equality atom in the class. -/
def rifEqualBodyRule : RIF.Rule :=
  { vars := ["x", "y"], head := .member (.var "x") (bnd "D"),
    body := some (.and [.atom (.member (.var "x") (bnd "C")),
                        .atom (.equal (.var "x") (.var "y"))]) }

theorem rifEqualBodyRule_rejected : rifRuleOk rifEqualBodyRule = false := by decide

/-- An `External(pred:…)` body atom: no built-in predicate in the
class. RIF-DTB built-ins are outside. -/
def rifBuiltinBodyRule : RIF.Rule :=
  { vars := ["x"], head := .member (.var "x") (bnd "D"),
    body := some (.and [.atom (.member (.var "x") (bnd "C")),
                        .atom (.externalPred
                          "http://www.w3.org/2007/rif-builtin-predicate#is-literal-integer"
                          [.var "x"])]) }

theorem rifBuiltinBodyRule_rejected :
    rifRuleOk rifBuiltinBodyRule = false := by decide

/-- A disjunctive body: `RIF.collectAtoms` refuses it, so the rule
does not translate at all. -/
def rifOrBodyRule : RIF.Rule :=
  { vars := ["x"], head := .member (.var "x") (bnd "D"),
    body := some (.or [.atom (.member (.var "x") (bnd "C")),
                       .atom (.member (.var "x") (bnd "E"))]) }

theorem rifOrBodyRule_rejected : rifRuleOk rifOrBodyRule = false := by decide
theorem rifOrBodyRule_no_rule : rifRuleD rifOrBodyRule = none := by decide

/-- A function term: the class has no function symbols. -/
def rifFunctionTermRule : RIF.Rule :=
  { vars := ["x"], head := .member (.var "x") (bnd "D"),
    body := some (.atom (.member (.var "x")
      (.fapp "http://b.example/f" RIF.iriSpace [.var "x"]))) }

theorem rifFunctionTermRule_rejected :
    rifRuleOk rifFunctionTermRule = false := by decide

end L4Factoidal.Unified
