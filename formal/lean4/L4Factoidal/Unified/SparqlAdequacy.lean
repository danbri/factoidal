/-
L4Factoidal.Unified.SparqlAdequacy — BGP matching and the entailment
regimes as satisfaction over the unified model theory.

Stage 6 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md`
§4.6. `Unified/SparqlQuery.lean` carries the definitions and the
syntactic bridge; this module carries the theorems.

## The architecture, and why the design document's single iff split

§4.6 proposes ONE theorem,

    μ ∈ evalBgp b g ↔ (μ.domExact b ∧ μ.rangeIn g ∧ Entails …)

Membership in `evalBgp b g` is LIST membership of a `Binding`, which
is a `List (VarName × Term)`. Two facts make the right-hand side
unable to characterise it:

* **Order.** The evaluator conses bindings as it walks subject →
  predicate → object, left to right through the pattern list, so the
  mapping it returns is one particular PERMUTATION of the pairs. A
  semantic condition cannot see the order.
* **Coarseness.** `tryBindTerm`'s already-bound arm keeps the FIRST
  term bound to a variable and only compares the graph's own term to
  it with `Term.eqb`. So a returned mapping's terms need not be
  structurally the terms of `g`, only engine-equal to them
  (`SPARQL/BgpRefinement.lean`'s header records the same point for
  its conclusion).

Landed instead: a PIVOT and two theorems that meet at it.
`Unified.BgpMatches μ b g` says every pattern instantiates under μ into
`g` by engine equality. Then

* `unified_adequate_bgp` — `BgpMatches μ b g ↔ Answers …`, a full iff,
  the model-theoretic gate;
* `bgp_eval_sound` — `μ ∈ evalBgp b g → BgpMatches μ b g`,
  unconditional;
* `bgp_eval_complete` — `BgpMatches μ b g` plus a domain condition
  gives a mapping the evaluator RETURNS which agrees with μ up to
  `Term.eqb`.

`unified_adequate_bgp_engine` and `unified_bgp_answers_returned` chain
them. Recorded as stage 6 correction note 27.

## The term model

The completeness half needs an interpretation in which "true" means
"a triple of `g`" and NOTHING more, while still satisfying
`termEqSchema` (which demands that `Term.eqb`-equal terms denote the
same individual). The Herbrand model of `RDF/Semantics.lean` fails the
second requirement: its domain is `Term` under structural equality, so
`"a"@EN` and `"a"@en` denote differently there.

`herbQ g` is that model with the domain quotiented by `Term.eqb` —
`Quot.mk` for the identification, `Quot.lift` of `Term.eqb x ·` for
the converse, which is available exactly because `Term.eqb` is proved
reflexive, symmetric and transitive in `RDF/Core.lean`. Triple terms
get a constant, so both halves of the completeness direction carry the
triple-term-free guards, for the same reason `RDF.herbrand` does.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlQuery

namespace L4Factoidal.Unified

open L4Factoidal

/-! ## The Skolem reading, transported

`rdfToTheorySk g` is `rdfBody g`: blank nodes as free names, no
closure. Its satisfaction is at the interpretation's own name
valuation, where `FreshVal` is trivial, so the stage 1 transport
lemmas apply with no side condition at all. -/

/-- The blank-node assignment a CL interpretation induces on the
Skolem reading: a blank node denotes what its bound name denotes. -/
def skAssign (i : CL.Interp) : RDF.BnodeAssignment (restrictInterp i).idom :=
  fun b => i.iName (bnodeName b)

theorem satisfies_rdfToTheorySk_iff (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheorySk g) ↔
      ∀ t ∈ g, CL.Satisfies i (tripleAtom t) := by
  simp only [CL.Satisfies, rdfToTheorySk]
  exact sat_rdfBody i i.iName (fun _ => []) g

/-- **Skolem transport**: a CL interpretation satisfies the Skolem
reading of a graph exactly when its restriction holds the graph under
the induced assignment (RDF 1.1 Semantics §6 — no existential
closure, so `HoldsAll` at a FIXED assignment, not `Satisfies`). -/
theorem satisfies_rdfToTheorySk_restrict (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheorySk g) ↔
      RDF.HoldsAll (restrictInterp i) (skAssign i) g := by
  rw [satisfies_rdfToTheorySk_iff]
  constructor
  · intro h t ht
    exact (sat_tripleAtom_restrict i (skAssign i) (freshVal_iName i) t
      (fun _ _ => rfl)).mp (h t ht)
  · intro h t ht
    exact (sat_tripleAtom_restrict i (skAssign i) (freshVal_iName i) t
      (fun _ _ => rfl)).mpr (h t ht)

/-! ## Engine term equality inside satisfaction

Delimitation 3 of `SparqlQuery.lean`: `Graph.mem` is `Term.eqb`, which
is coarser than syntactic identity, so a predication about an
engine-equal triple transfers only under `termEqSchema`. -/

theorem sat_tripleAtom_eqb {i : CL.Interp}
    (hS : SatisfiesSchema i termEqSchema) {t u : RDF.Triple}
    (h : RDF.Triple.eqb t u = true) :
    CL.Satisfies i (tripleAtom t) ↔ CL.Satisfies i (tripleAtom u) := by
  simp only [RDF.Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  have hs' : t.s = u.s := RDF.Subject.eqb_eq hs
  simp only [CL.Satisfies, tripleAtom, CL.Sat, CL.denotSeq, CL.denotTerm,
             hs', hp, denot_embedTerm_congr_of_schema hS ho]

/-- A graph member's predication holds wherever the Skolem reading and
the term-equality schema do. -/
theorem sat_tripleAtom_of_graphMem {i : CL.Interp} {g : RDF.Graph}
    (hS : SatisfiesSchema i termEqSchema)
    (hsat : CL.Satisfies i (rdfToTheorySk g)) {t : RDF.Triple}
    (hmem : RDF.Graph.mem t g = true) : CL.Satisfies i (tripleAtom t) := by
  obtain ⟨u, hu, hue⟩ := RDF.exists_of_graphMem hmem
  exact (sat_tripleAtom_eqb hS hue).mp
    ((satisfies_rdfToTheorySk_iff i g).mp hsat u hu)

/-! ## The evaluator side, soundness

`SPARQL/BgpRefinement.lean` proves that substituting a returned μ back
into the pattern lands inside the graph. `BgpMatches` needs the same
statement PATTERN-WISE — with the witness that each pattern
instantiates at all — which is the shape its `instBgp_into_graph`
proof already establishes internally. -/

open SPARQL in
theorem evalBgpFrom_matches {g : RDF.Graph} : ∀ (b : Bgp) {mu mu' : Binding},
    mu' ∈ evalBgpFrom g b mu → BgpMatches mu' b g := by
  intro b
  induction b with
  | nil => intro mu mu' _ tp htp; exact absurd htp (by simp)
  | cons tp rest ih =>
      intro mu mu' h tp' htp'
      simp only [evalBgpFrom, List.mem_flatMap] at h
      obtain ⟨mu1, hmu1, hrest⟩ := h
      simp only [evalTP, List.mem_filterMap] at hmu1
      obtain ⟨u, hu, hmatch⟩ := hmu1
      rcases List.mem_cons.mp htp' with rfl | hmem
      · obtain ⟨w, hw, hwe⟩ := tpMatch_inst hmatch
        refine ⟨w, instTriple_mono (evalBgpFrom_extends rest hrest) hw, ?_⟩
        exact RDF.graphMem_of_exists ⟨u, hu, by rw [RDF.Triple.eqb_symm]; exact hwe⟩
      · exact ih hrest tp' hmem

/-- **Evaluator soundness at the pivot**: every mapping the algebra
returns instantiates the whole pattern into the graph. Unconditional —
no fragment guard, no schema. -/
theorem bgp_eval_sound {b : SPARQL.Bgp} {g : RDF.Graph} {mu : SPARQL.Binding}
    (h : mu ∈ SPARQL.evalBgp b g) : BgpMatches mu b g :=
  evalBgpFrom_matches b h

/-! ## The model-theoretic side, soundness half -/

/-- Satisfaction of a query body, pattern by pattern. -/
theorem satisfies_bgpBody_iff (i : CL.Interp) (mu : SPARQL.Binding)
    (b : SPARQL.Bgp) :
    CL.Satisfies i (bgpBody mu b) ↔
      ∀ tp ∈ b, CL.Satisfies i (patternAtom mu tp) := by
  simp only [CL.Satisfies, bgpBody, CL.Sat]
  rw [satAll_forall]
  constructor
  · intro h tp htp
    exact h _ (List.mem_map.mpr ⟨tp, htp, rfl⟩)
  · rintro h s hs
    obtain ⟨tp, htp, rfl⟩ := List.mem_map.mp hs
    exact h tp htp

/-- **Soundness of the pivot**: a mapping that instantiates the whole
pattern into the graph answers the query from the graph's Skolem
reading, under the engine-term-equality schema. -/
theorem bgp_matches_answers {b : SPARQL.Bgp} {g : RDF.Graph}
    {mu : SPARQL.Binding} (h : BgpMatches mu b g) :
    Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu := by
  intro i _ hS hsat
  have hg : CL.Satisfies i (rdfToTheorySk g) :=
    hsat _ (List.mem_singleton.mpr rfl)
  refine (satisfies_bgpBody_iff i mu b).mpr (fun tp htp => ?_)
  obtain ⟨t, hinst, hmem⟩ := h tp htp
  rw [patternAtom_eq_tripleAtom hinst]
  exact sat_tripleAtom_of_graphMem hS hg hmem

/-! ## The term model: RDF terms modulo engine equality

`RDF.herbrand` cannot serve the completeness half: its domain is
`Term` under structural equality, so it separates `"a"@EN` from
`"a"@en`, which `termEqSchema` requires to be identified. Quotienting
the domain by `Term.eqb` repairs exactly that, and the quotient
separates nothing else — `Term.eqb` is proved reflexive, symmetric and
transitive in `RDF/Core.lean`, so `Quot.lift` gives the converse of
`Quot.sound`.

Triple terms get a constant, the same quarantine `RDF.herbrand` uses
and for the same reason, which is why every theorem consuming this
model carries the triple-term-free guards. -/

/-- The relation the engine's term equality decides. -/
def EqbRel (x y : RDF.Term) : Prop := RDF.Term.eqb x y = true

/-- RDF terms modulo engine equality. -/
def TermQ : Type := Quot EqbRel

/-- A term's engine-equality class. -/
def tq (t : RDF.Term) : TermQ := Quot.mk EqbRel t

private def eqbFrom (x : RDF.Term) : TermQ → Prop :=
  Quot.lift (fun y => RDF.Term.eqb x y = true) (by
    intro a b hab
    apply propext
    constructor
    · intro hxa; exact RDF.Term.eqb_trans hxa hab
    · intro hxb
      exact RDF.Term.eqb_trans hxb (by rw [RDF.Term.eqb_symm]; exact hab))

/-- The quotient identifies exactly what `Term.eqb` identifies. -/
theorem tq_eq_iff {x y : RDF.Term} : tq x = tq y ↔ RDF.Term.eqb x y = true := by
  constructor
  · intro h
    have h2 : eqbFrom x (tq x) := RDF.Term.eqb_refl x
    rw [h] at h2
    exact h2
  · intro h; exact Quot.sound h

/-- The individual a term denotes in the term model: a tag (the source
string of a name, `none` for a constructed value) paired with the
term's engine-equality class. The tag component is the same device
`Unified.liftInterp` uses (stage 1 correction note 2). -/
def herbDenot : RDF.Term → Option String × TermQ
  | .iri x => (some x.val, tq (.iri x))
  | .bnode b => (some (bnodeName b), tq (.bnode b))
  | .literal l => (none, tq (.literal l))
  | .tripleTerm _ _ _ => (none, tq (.bnode ""))

/-- Rebuild a literal class from the tagged operator arguments — the
decoding half of `literalValueOf`, over the quotient. -/
def qLit (lex dt : String) (tag : Option String)
    (dir : Option RDF.TextDirection) : Option String × TermQ :=
  if h : RDF.isIri dt then
    if hw : RDF.literalWf { lexicalForm := lex, datatype := ⟨dt, h⟩,
                            langTag := tag, direction := dir } then
      (none, tq (.literal ⟨_, hw⟩))
    else (none, tq (.bnode ""))
  else (none, tq (.bnode ""))

def qLitTags : List (Option String) → Option String × TermQ
  | [some lex, some dt] => qLit lex dt none none
  | [some lex, some dt, some tag] => qLit lex dt (some tag) none
  | [some lex, some dt, some tag, some dir] =>
      qLit lex dt (some tag) (some (if dir = "rtl" then .rtl else .ltr))
  | _ => (none, tq (.bnode ""))

/-- The model's name valuation. -/
def herbName (n : String) : Option String × TermQ :=
  (some n,
    if h : RDF.isIri n then tq (.iri ⟨n, h⟩)
    else match bnodeNameDecode n with
      | some b => tq (.bnode b)
      | none => tq (.bnode ("?" ++ n)))

/-- The model's relation: true means "a triple of `g`". -/
def herbRel (g : RDF.Graph) (p : Option String × TermQ)
    (args : List (Option String × TermQ)) : Prop :=
  match args with
  | [x, y] => ∃ t ∈ g, p = herbDenot (.iri t.p) ∧
      x = herbDenot t.s.toTerm ∧ y = herbDenot t.o
  | _ => False

/-- The model's operator interpretation: `literalValueOf` decodes,
everything else (the triple-term operator included) is the quarantine
constant. -/
def herbFn (op : Option String × TermQ) (args : List (Option String × TermQ)) :
    Option String × TermQ :=
  if op.1 = some litOp then qLitTags (args.map Prod.fst)
  else (none, tq (.bnode ""))

/-- **The term model of a graph**: true means "a triple of `g`", and
nothing else is true. -/
def herbQ (g : RDF.Graph) : CL.Interp where
  dom := Option String × TermQ
  domWit := (none, tq (.bnode ""))
  iName := herbName
  iStr := fun s => (some s, tq (.bnode ""))
  rel := herbRel g
  fn := herbFn
  iProp := fun _ _ _ => (none, tq (.bnode ""))

theorem isIri_bnodeName (b : RDF.BNodeId) : RDF.isIri (bnodeName b) = false := by
  cases h : RDF.isIri (bnodeName b) with
  | false => rfl
  | true => exact absurd (isIri_has_colon h) (bnodeName_no_colon b)

theorem isIri_varName (v : SPARQL.VarName) : RDF.isIri (varName v) = false := by
  cases h : RDF.isIri (varName v) with
  | false => rfl
  | true => exact absurd (isIri_has_colon h) (varName_no_colon v)

theorem herbName_iri (x : RDF.WfIri) : herbName x.val = herbDenot (.iri x) := by
  simp only [herbName, herbDenot, dif_pos x.property]

theorem herbName_bnodeName (b : RDF.BNodeId) :
    herbName (bnodeName b) = herbDenot (.bnode b) := by
  simp [herbName, herbDenot, isIri_bnodeName b, bnodeNameDecode_bnodeName]

theorem herbName_varName (v : SPARQL.VarName) :
    herbName (varName v) = (some (varName v), tq (.bnode ("?" ++ varName v))) := by
  have hd : bnodeNameDecode (varName v) = none := by
    simp only [bnodeNameDecode, varName_toList]
    rfl
  simp [herbName, isIri_varName v, hd]

/-- Every tag is the name it came from, or `none`. Used to refute a
match of an unbound variable or of a constructed value against a
name. -/
theorem herbName_fst (n : String) : (herbName n).1 = some n := rfl

/-- The literal operator, over the term model. -/
theorem herbQ_fn_litArgs (g : RDF.Graph) {σ : String → List (herbQ g).dom}
    (l : RDF.WfLiteral) :
    (herbQ g).fn ((herbQ g).iName litOp)
        (CL.denotSeq (herbQ g) (herbQ g).iName σ (embedLiteralArgs l)) =
      herbDenot (.literal l) := by
  obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := l
  have hdt : (herbQ g).iName dt.val = herbDenot (.iri dt) := herbName_iri dt
  have hq : qLit lex dt.val tag dir
      = herbDenot (.literal ⟨{ lexicalForm := lex, datatype := dt,
                               langTag := tag, direction := dir }, hwf⟩) := by
    simp only [qLit, dif_pos dt.property]
    rw [dif_pos (by simpa using hwf)]
    rfl
  rcases tag with _ | tag <;> rcases dir with _ | d
  · simp only [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, herbQ, herbFn,
               herbName_fst, if_pos, List.map_cons, List.map_nil, qLitTags]
    exact hq
  · exact absurd hwf (by simp [RDF.literalWf])
  · simp only [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, herbQ, herbFn,
               herbName_fst, if_pos, List.map_cons, List.map_nil, qLitTags]
    exact hq
  · cases d <;>
    · simp only [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, herbQ, herbFn,
                 herbName_fst, if_pos, List.map_cons, List.map_nil, qLitTags,
                 reduceIte]
      exact hq

/-- Every RDF term denotes its own `herbDenot` value. No fragment
guard here: a triple term denotes the quarantine constant, which is
what makes the guards necessary DOWNSTREAM rather than in this
lemma. -/
theorem denot_embedTerm_herbQ (g : RDF.Graph) {σ : String → List (herbQ g).dom} :
    ∀ t : RDF.Term,
      CL.denotTerm (herbQ g) (herbQ g).iName σ (embedTerm t) = herbDenot t
  | .iri x => by
      simp only [embedTerm, CL.denotTerm, herbQ]
      exact herbName_iri x
  | .bnode b => by
      simp only [embedTerm, CL.denotTerm, herbQ]
      exact herbName_bnodeName b
  | .literal l => by
      simp only [embedTerm, CL.denotTerm]; exact herbQ_fn_litArgs g l
  | .tripleTerm s p o => by
      simp only [embedTerm, CL.denotTerm, herbDenot, herbQ, herbFn, herbName_fst]
      exact if_neg (by decide)

theorem embedSubject_eq_embedTerm (s : RDF.Subject) :
    embedSubject s = embedTerm s.toTerm := by
  cases s <;> rfl

theorem denot_embedSubject_herbQ (g : RDF.Graph)
    {σ : String → List (herbQ g).dom} (s : RDF.Subject) :
    CL.denotTerm (herbQ g) (herbQ g).iName σ (embedSubject s)
      = herbDenot s.toTerm := by
  rw [embedSubject_eq_embedTerm]; exact denot_embedTerm_herbQ g _

/-! ### What the model identifies -/

theorem herbDenot_of_eqb {x y : RDF.Term} (h : RDF.Term.eqb x y = true) :
    herbDenot x = herbDenot y := by
  cases x with
  | iri i =>
      cases y with
      | iri j =>
          have : i = j := Subtype.ext (by simpa [RDF.Term.eqb] using h)
          rw [this]
      | bnode _ => simp [RDF.Term.eqb] at h
      | literal _ => simp [RDF.Term.eqb] at h
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at h
  | bnode b =>
      cases y with
      | iri _ => simp [RDF.Term.eqb] at h
      | bnode c =>
          have : b = c := by simpa [RDF.Term.eqb] using h
          rw [this]
      | literal _ => simp [RDF.Term.eqb] at h
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at h
  | literal l =>
      cases y with
      | iri _ => simp [RDF.Term.eqb] at h
      | bnode _ => simp [RDF.Term.eqb] at h
      | literal m =>
          simp only [herbDenot, Prod.mk.injEq, true_and]
          exact tq_eq_iff.mpr h
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at h
  | tripleTerm a b c =>
      cases y with
      | iri _ => simp [RDF.Term.eqb] at h
      | bnode _ => simp [RDF.Term.eqb] at h
      | literal _ => simp [RDF.Term.eqb] at h
      | tripleTerm _ _ _ => rfl

/-- The converse, on the triple-term-free fragment: equal denotations
mean engine-equal terms. -/
theorem eqb_of_herbDenot {x y : RDF.Term} (hx : RDF.TermTtFree x)
    (hy : RDF.TermTtFree y) (h : herbDenot x = herbDenot y) :
    RDF.Term.eqb x y = true := by
  cases x with
  | tripleTerm _ _ _ => exact absurd hx (by simp [RDF.TermTtFree])
  | iri i =>
      cases y with
      | tripleTerm _ _ _ => exact absurd hy (by simp [RDF.TermTtFree])
      | iri j =>
          have : i.val = j.val := by
            simpa [herbDenot] using congrArg Prod.fst h
          simp [RDF.Term.eqb, Subtype.ext_iff, this]
      | bnode c =>
          have : i.val = bnodeName c := by
            simpa [herbDenot] using congrArg Prod.fst h
          exact absurd this.symm (bnodeName_ne_iri c i)
      | literal m => simp [herbDenot] at h
  | bnode b =>
      cases y with
      | tripleTerm _ _ _ => exact absurd hy (by simp [RDF.TermTtFree])
      | iri j =>
          have : bnodeName b = j.val := by
            simpa [herbDenot] using congrArg Prod.fst h
          exact absurd this (bnodeName_ne_iri b j)
      | bnode c =>
          have : bnodeName b = bnodeName c := by
            simpa [herbDenot] using congrArg Prod.fst h
          simp [RDF.Term.eqb, bnodeName_injective this]
      | literal m => simp [herbDenot] at h
  | literal l =>
      cases y with
      | tripleTerm _ _ _ => exact absurd hy (by simp [RDF.TermTtFree])
      | iri j => simp [herbDenot] at h
      | bnode c => simp [herbDenot] at h
      | literal m =>
          have : tq (.literal l) = tq (.literal m) := by
            simpa [herbDenot] using congrArg Prod.snd h
          simpa [RDF.Term.eqb] using tq_eq_iff.mp this

/-- **The term model satisfies the engine-term-equality schema.** The
tag component is constant on an engine-equality class — only literals
and triple terms are identified non-trivially, and both carry the
`none` tag — so no row of the schema is violated. -/
theorem herbQ_satisfiesSchema (g : RDF.Graph) :
    SatisfiesSchema (herbQ g) termEqSchema := by
  rintro s ⟨x, y, hxy, rfl⟩
  show CL.Sat (herbQ g) (herbQ g).iName (fun _ => []) (.eq _ _)
  simp only [CL.Sat, denot_embedTerm_herbQ g x, denot_embedTerm_herbQ g y]
  exact herbDenot_of_eqb hxy

/-- **The term model satisfies the graph's Skolem reading**, on the
triple-term-free fragment. -/
theorem herbQ_satisfies_sk (g : RDF.Graph) (htt : RDF.GraphTtFree g) :
    CL.Satisfies (herbQ g) (rdfToTheorySk g) := by
  refine (satisfies_rdfToTheorySk_iff (herbQ g) g).mpr (fun t ht => ?_)
  show CL.Sat (herbQ g) (herbQ g).iName (fun _ => []) (.atom _ _)
  simp only [tripleAtom, CL.Sat, CL.denotSeq, CL.denotTerm,
             denot_embedSubject_herbQ g t.s, denot_embedTerm_herbQ g t.o]
  simp only [herbQ, herbName_iri t.p, herbRel]
  exact ⟨t, ht, rfl, rfl, rfl⟩

end L4Factoidal.Unified
