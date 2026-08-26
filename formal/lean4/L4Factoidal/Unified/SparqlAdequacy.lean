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
* `unified_adequate_bgp_spec` — the same iff for the pattern the query
  path matches (`b.map rewriteBnodeTriple`), carrying NO blank-node
  hypothesis: the guard stage 6 assumed is discharged by
  `bgpBnodeFree_rewriteBnodes`;
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

/-! ## Reflection: what a satisfied predication forces

Each pattern position is read back off its denotation. The tag
component does the work: a name denotes with its own string in the
tag, a constructed value (literal, triple term) with `none`, so an
unbound variable, a literal in subject position and a blank node in
predicate position are all REFUTED rather than assumed away. That is
why the pivot iff below needs no domain hypothesis on `mu`. -/

theorem subjectEqb_of_termEqb {a b : RDF.Subject}
    (h : RDF.Term.eqb a.toTerm b.toTerm = true) : RDF.Subject.eqb a b = true := by
  cases a <;> cases b <;> simp_all [RDF.Subject.toTerm, RDF.Term.eqb, RDF.Subject.eqb]

theorem subjToTerm_ttFree (s : RDF.Subject) : RDF.TermTtFree s.toTerm := by
  cases s <;> simp [RDF.Subject.toTerm, RDF.TermTtFree]

theorem herbDenot_fst_subj (s : RDF.Subject) : ∃ n, (herbDenot s.toTerm).1 = some n := by
  cases s with
  | iri i => exact ⟨i.val, rfl⟩
  | bnode b => exact ⟨bnodeName b, rfl⟩

/-- A term whose denotation is a name's denotation is that name's own
kind of term: not a literal, not a triple term. -/
theorem ttFree_of_herbDenot_fst_some {u : RDF.Term} {n : String}
    (h : (herbDenot u).1 = some n) : RDF.TermTtFree u := by
  cases u <;> simp_all [herbDenot, RDF.TermTtFree]

theorem instSubject_of_denot {g : RDF.Graph} {mu : SPARQL.Binding}
    {ps : SPARQL.PatternSubject} {s : RDF.Subject}
    (htt : PatternSubjectTtFree ps)
    (h : CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
           (embedPatternSubject mu ps) = herbDenot s.toTerm) :
    ∃ s', SPARQL.instSubject id mu ps = some s' ∧ RDF.Subject.eqb s' s = true := by
  cases ps with
  | tripleTerm _ _ _ => exact absurd htt (by simp [PatternSubjectTtFree])
  | iri i =>
      rw [show embedPatternSubject mu (.iri i) = embedTerm (.iri i) from rfl,
          denot_embedTerm_herbQ g] at h
      exact ⟨.iri i, rfl,
        subjectEqb_of_termEqb
          (eqb_of_herbDenot (by simp [RDF.TermTtFree, RDF.Subject.toTerm])
            (subjToTerm_ttFree s) h)⟩
  | bnode b =>
      rw [show embedPatternSubject mu (.bnode b) = embedTerm (.bnode b) from rfl,
          denot_embedTerm_herbQ g] at h
      exact ⟨.bnode b, rfl,
        subjectEqb_of_termEqb
          (eqb_of_herbDenot (by simp [RDF.TermTtFree, RDF.Subject.toTerm])
            (subjToTerm_ttFree s) h)⟩
  | var v =>
      cases hl : mu.lookup v with
      | none =>
          exfalso
          rw [show embedPatternSubject mu (.var v) = .name (varName v) by
                simp [embedPatternSubject, hl]] at h
          have h1 : (herbName (varName v)).1 = (herbDenot s.toTerm).1 := by
            simpa [herbQ, CL.denotTerm] using congrArg Prod.fst h
          rw [herbName_fst] at h1
          cases s with
          | iri j =>
              exact varName_ne_iri v j (by simpa [herbDenot, RDF.Subject.toTerm] using h1)
          | bnode c =>
              exact varName_ne_bnodeName v c
                (by simpa [herbDenot, RDF.Subject.toTerm] using h1)
      | some u =>
          rw [show embedPatternSubject mu (.var v) = embedTerm u by
                simp [embedPatternSubject, hl],
              denot_embedTerm_herbQ g] at h
          obtain ⟨nn, hnn⟩ := herbDenot_fst_subj s
          have hu : RDF.TermTtFree u :=
            ttFree_of_herbDenot_fst_some (n := nn) (by rw [h]; exact hnn)
          have heq : RDF.Term.eqb u s.toTerm = true :=
            eqb_of_herbDenot hu (subjToTerm_ttFree s) h
          cases u with
          | iri j =>
              exact ⟨.iri j, by simp [SPARQL.instSubject, hl],
                subjectEqb_of_termEqb (by simpa [RDF.Subject.toTerm] using heq)⟩
          | bnode c =>
              exact ⟨.bnode c, by simp [SPARQL.instSubject, hl],
                subjectEqb_of_termEqb (by simpa [RDF.Subject.toTerm] using heq)⟩
          | literal _ =>
              exact absurd heq
                (by cases s <;> simp [RDF.Subject.toTerm, RDF.Term.eqb])
          | tripleTerm _ _ _ => exact absurd hu (by simp [RDF.TermTtFree])

theorem instObject_of_denot {g : RDF.Graph} {mu : SPARQL.Binding}
    {pt : SPARQL.PatternTerm} {o : RDF.Term}
    (htt : PatternTermTtFree pt) (hott : RDF.TermTtFree o)
    (h : CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
           (embedPatternTerm mu pt) = herbDenot o) :
    ∃ o', SPARQL.instObject id mu pt = some o' ∧ RDF.Term.eqb o' o = true := by
  cases pt with
  | tripleTerm _ _ _ => exact absurd htt (by simp [PatternTermTtFree])
  | iri i =>
      rw [show embedPatternTerm mu (.iri i) = embedTerm (.iri i) from rfl,
          denot_embedTerm_herbQ g] at h
      exact ⟨.iri i, rfl, eqb_of_herbDenot (by simp [RDF.TermTtFree]) hott h⟩
  | bnode b =>
      rw [show embedPatternTerm mu (.bnode b) = embedTerm (.bnode b) from rfl,
          denot_embedTerm_herbQ g] at h
      exact ⟨.bnode b, rfl, eqb_of_herbDenot (by simp [RDF.TermTtFree]) hott h⟩
  | literal l =>
      rw [show embedPatternTerm mu (.literal l) = embedTerm (.literal l) from rfl,
          denot_embedTerm_herbQ g] at h
      exact ⟨.literal l, rfl, eqb_of_herbDenot (by simp [RDF.TermTtFree]) hott h⟩
  | var v =>
      cases hl : mu.lookup v with
      | none =>
          exfalso
          rw [show embedPatternTerm mu (.var v) = .name (varName v) by
                simp [embedPatternTerm, hl]] at h
          have h1 : some (varName v) = (herbDenot o).1 := by
            simpa [herbQ, CL.denotTerm, herbName_fst] using congrArg Prod.fst h
          cases o with
          | iri j => exact varName_ne_iri v j (by simpa [herbDenot] using h1)
          | bnode c => exact varName_ne_bnodeName v c (by simpa [herbDenot] using h1)
          | literal _ => simp [herbDenot] at h1
          | tripleTerm _ _ _ => exact absurd hott (by simp [RDF.TermTtFree])
      | some u =>
          rw [show embedPatternTerm mu (.var v) = embedTerm u by
                simp [embedPatternTerm, hl],
              denot_embedTerm_herbQ g] at h
          have hu : RDF.TermTtFree u := by
            cases u with
            | tripleTerm _ _ _ =>
                exfalso
                cases o with
                | iri j =>
                    exact absurd (congrArg Prod.fst h) (by simp [herbDenot])
                | bnode c =>
                    exact absurd (congrArg Prod.fst h) (by simp [herbDenot])
                | literal m =>
                    have := tq_eq_iff.mp
                      (by simpa [herbDenot] using congrArg Prod.snd h)
                    simp [RDF.Term.eqb] at this
                | tripleTerm _ _ _ => exact absurd hott (by simp [RDF.TermTtFree])
            | iri _ => simp [RDF.TermTtFree]
            | bnode _ => simp [RDF.TermTtFree]
            | literal _ => simp [RDF.TermTtFree]
          exact ⟨u, by simp [SPARQL.instObject, hl], eqb_of_herbDenot hu hott h⟩

theorem constructPredicate_of_denot {g : RDF.Graph} {mu : SPARQL.Binding}
    {pt : SPARQL.PatternTerm} {p : RDF.WfIri} (htt : PatternTermTtFree pt)
    (h : CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
           (embedPatternTerm mu pt) = herbDenot (.iri p)) :
    SPARQL.constructPredicate pt mu = some p := by
  obtain ⟨o', ho', hoe⟩ := instObject_of_denot htt (by simp [RDF.TermTtFree]) h
  cases o' with
  | iri j =>
      have : j = p := Subtype.ext (by simpa [RDF.Term.eqb] using hoe)
      subst this
      cases pt with
      | iri i =>
          simp only [SPARQL.instObject, Option.some.injEq] at ho'
          have hij : i = j := by injection ho'
          simp [SPARQL.constructPredicate, hij]
      | var v =>
          simp only [SPARQL.instObject] at ho'
          simp [SPARQL.constructPredicate, ho']
      | bnode _ => simp [SPARQL.instObject] at ho'
      | literal _ => simp [SPARQL.instObject] at ho'
      | tripleTerm _ _ _ => exact absurd htt (by simp [PatternTermTtFree])
  | bnode _ => simp [RDF.Term.eqb] at hoe
  | literal _ => simp [RDF.Term.eqb] at hoe
  | tripleTerm _ _ _ => simp [RDF.Term.eqb] at hoe

/-- **Reflection at the atom**: a predication true in the term model
comes from a triple of the graph, and the pattern instantiates to an
engine-equal triple. -/
theorem patternAtom_reflect {g : RDF.Graph} {mu : SPARQL.Binding}
    {tp : SPARQL.TriplePattern} (htt : TpTtFree tp) (hg : RDF.GraphTtFree g)
    (h : CL.Satisfies (herbQ g) (patternAtom mu tp)) :
    ∃ t', SPARQL.instTriple id mu tp = some t' ∧ RDF.Graph.mem t' g = true := by
  obtain ⟨hts, htp, hto⟩ := htt
  have h' : herbRel g
      (CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
        (embedPatternTerm mu tp.p))
      [CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
        (embedPatternSubject mu tp.s),
       CL.denotTerm (herbQ g) (herbQ g).iName (fun _ => [])
        (embedPatternTerm mu tp.o)] := by
    simpa [CL.Satisfies, patternAtom, CL.Sat, CL.denotSeq, herbQ] using h
  obtain ⟨t, ht, hp, hs, ho⟩ := h'
  obtain ⟨s', hs', hse⟩ := instSubject_of_denot hts hs
  obtain ⟨o', ho', hoe⟩ := instObject_of_denot hto (hg t ht) ho
  have hpm : SPARQL.constructPredicate tp.p mu = some t.p :=
    constructPredicate_of_denot htp hp
  refine ⟨{ s := s', p := t.p, o := o' }, ?_, ?_⟩
  · simp only [SPARQL.instTriple, hs', hpm, ho']
  · exact RDF.graphMem_of_exists ⟨t, ht, by
      simp [RDF.Triple.eqb, RDF.Subject.eqb_symm, RDF.Term.eqb_symm, hse, hoe]⟩

/-! ## The stage 6 gate theorem -/

/-- **BGP adequacy** (design document §4.6, in the pivot form the
module header explains): a solution mapping instantiates a basic graph
pattern into a graph exactly when it answers the query from the
graph's Skolem reading, under the engine-term-equality schema.

A FULL iff. Hypotheses, and their exact strength:

* `hg : RDF.GraphTtFree g` and `hb : BgpTtFree b` are needed only by
  the ← direction, where the term model gives every triple term the
  same quarantine constant (`RDF.herbrand` carries the identical
  hypothesis for the identical reason). The → direction
  (`bgp_matches_answers`) has no hypotheses at all.
* No domain hypothesis on `mu`: an unbound variable is REFUTED by the
  term model rather than excluded by assumption.

**Delimitation** (SPARQL 1.1 §18.3.1;
https://github.com/danbri/factoidal/issues/607): a blank node in `b`
is read as a CONSTANT on BOTH sides — by `instTriple`/`tryBind*` on
the left, by the Skolem reading on the right. On a pattern containing
a blank node this theorem is therefore adequate TO THE ENGINE at the
`evalBgp` entry point, not to the specification, whose pattern
instance mapping lets that blank node match any RDF term.
`unified_adequate_bgp_spec` below is the specification-level
statement: it applies this theorem to `b.map rewriteBnodeTriple`, the
pattern `Query.evalSelect` actually hands the algebra, and PROVES the
blank-node-freeness that stage 6 assumed. **No multiplicity is
claimed** (design document §5.4). -/
theorem unified_adequate_bgp (b : SPARQL.Bgp) (g : RDF.Graph)
    (mu : SPARQL.Binding) (hg : RDF.GraphTtFree g) (hb : BgpTtFree b) :
    BgpMatches mu b g ↔
      Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu := by
  constructor
  · exact bgp_matches_answers
  · intro hA tp htp
    have hsat : CL.Satisfies (herbQ g) (bgpBody mu b) :=
      hA (herbQ g) trivial (herbQ_satisfiesSchema g) (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs
        exact herbQ_satisfies_sk g hg)
    exact patternAtom_reflect (hb tp htp) hg
      ((satisfies_bgpBody_iff (herbQ g) mu b).mp hsat tp htp)

/-! ## The evaluator side, completeness

The remaining half: a mapping that instantiates the whole pattern into
the graph is one the evaluator RETURNS — up to what the module header
lists as the two things a semantic condition cannot see, binding-list
ORDER and the COARSENESS of `Term.eqb`. So the conclusion is the
existence of a returned mapping that agrees with the given one on the
pattern's variables by engine equality, not membership on the nose.

`BgpTtFree` is carried here for a second, independent reason: the
triple-term arm of `tryBindTerm` recurses through sub-positions with
intermediate mappings, which would need the whole lemma family again
one level down. Recorded as the stage's boundary row. -/

section Complete

open L4Factoidal.SPARQL

/-- Every binding `mu` makes is engine-equal to the target's. -/
def BindingCompat (mu target : Binding) : Prop :=
  ∀ v u, mu.lookup v = some u →
    ∃ u', target.lookup v = some u' ∧ RDF.Term.eqb u u' = true

theorem bindingCompat_empty (target : Binding) :
    BindingCompat Binding.empty target := by
  intro v u h
  simp [Binding.empty, Binding.lookup] at h

theorem bindingCompat_bind {mu target : Binding} {v : VarName} {t t' : RDF.Term}
    (hc : BindingCompat mu target) (ht : target.lookup v = some t')
    (he : RDF.Term.eqb t t' = true) : BindingCompat (mu.bind v t) target := by
  intro w u hw
  simp only [Binding.bind, Binding.lookup] at hw
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl] at hw
    cases hw
    exact ⟨t', ht, he⟩
  · rw [if_neg hvw] at hw
    exact hc w u hw

theorem isSome_of_extends {mu mu' : Binding} {v : VarName}
    (he : Extends mu mu') (h : (mu.lookup v).isSome = true) :
    (mu'.lookup v).isSome = true := by
  cases hl : mu.lookup v with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some u => rw [he v u hl]; rfl

/-- Instantiating a predicate position and instantiating it as an
object agree where the first succeeds. -/
theorem instObject_of_constructPredicate {mu : Binding} {pt : PatternTerm}
    {p : RDF.WfIri} (h : constructPredicate pt mu = some p) :
    instObject id mu pt = some (.iri p) := by
  cases pt with
  | iri i =>
      simp only [constructPredicate, Option.some.injEq] at h
      subst h; rfl
  | bnode _ => simp [constructPredicate] at h
  | literal _ => simp [constructPredicate] at h
  | tripleTerm _ _ _ => simp [constructPredicate] at h
  | var v =>
      simp only [constructPredicate] at h
      simp only [instObject]
      split at h <;> simp_all

theorem tryBindSubject_complete {ps : PatternSubject} {s s' : RDF.Subject}
    {mu target : Binding} (htt : PatternSubjectTtFree ps)
    (hinst : instSubject id target ps = some s')
    (heq : RDF.Subject.eqb s' s = true) (hc : BindingCompat mu target) :
    ∃ mu1, tryBindSubject ps s mu = some mu1 ∧ BindingCompat mu1 target ∧
      Extends mu mu1 ∧ ∀ v ∈ patternSubjectVars ps, (mu1.lookup v).isSome = true := by
  have hss : s' = s := RDF.Subject.eqb_eq heq
  subst hss
  cases ps with
  | tripleTerm _ _ _ => exact absurd htt (by simp [PatternSubjectTtFree])
  | iri i =>
      simp only [instSubject, Option.some.injEq] at hinst
      subst hinst
      exact ⟨mu, by simp [tryBindSubject], hc, Extends.refl mu,
        by simp [patternSubjectVars]⟩
  | bnode b =>
      simp only [instSubject, Option.some.injEq] at hinst
      subst hinst
      exact ⟨mu, by simp [tryBindSubject], hc, Extends.refl mu,
        by simp [patternSubjectVars]⟩
  | var v =>
      have hl : target.lookup v = some s'.toTerm := by
        simp only [instSubject] at hinst
        split at hinst <;>
          first
            | (simp only [Option.some.injEq] at hinst; subst hinst;
               simp_all [RDF.Subject.toTerm])
            | simp at hinst
      cases hm : mu.lookup v with
      | none =>
          refine ⟨mu.bind v s'.toTerm, by simp [tryBindSubject, hm], ?_,
            Extends.bind hm, ?_⟩
          · exact bindingCompat_bind hc hl (RDF.Term.eqb_refl _)
          · intro w hw
            simp only [patternSubjectVars, List.mem_singleton] at hw
            subst hw
            simp [Binding.bind, Binding.lookup]
      | some existing =>
          obtain ⟨u', hu', hue⟩ := hc v existing hm
          rw [hl, Option.some.injEq] at hu'
          subst hu'
          refine ⟨mu, by simp [tryBindSubject, hm, hue], hc, Extends.refl mu, ?_⟩
          intro w hw
          simp only [patternSubjectVars, List.mem_singleton] at hw
          subst hw
          rw [hm]; rfl

theorem tryBindTerm_complete {pt : PatternTerm} {t t' : RDF.Term}
    {mu target : Binding} (htt : PatternTermTtFree pt)
    (hinst : instObject id target pt = some t')
    (heq : RDF.Term.eqb t' t = true) (hc : BindingCompat mu target) :
    ∃ mu1, tryBindTerm pt t mu = some mu1 ∧ BindingCompat mu1 target ∧
      Extends mu mu1 ∧ ∀ v ∈ patternTermVars pt, (mu1.lookup v).isSome = true := by
  cases pt with
  | tripleTerm _ _ _ => exact absurd htt (by simp [PatternTermTtFree])
  | iri i =>
      simp only [instObject, Option.some.injEq] at hinst
      subst hinst
      cases t with
      | iri j =>
          have : i = j := Subtype.ext (by simpa [RDF.Term.eqb] using heq)
          subst this
          exact ⟨mu, by simp [tryBindTerm], hc, Extends.refl mu,
            by simp [patternTermVars]⟩
      | bnode _ => simp [RDF.Term.eqb] at heq
      | literal _ => simp [RDF.Term.eqb] at heq
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at heq
  | bnode b =>
      simp only [instObject, Option.some.injEq] at hinst
      subst hinst
      cases t with
      | bnode c =>
          have : b = c := by simpa [RDF.Term.eqb] using heq
          subst this
          exact ⟨mu, by simp [tryBindTerm], hc, Extends.refl mu,
            by simp [patternTermVars]⟩
      | iri _ => simp [RDF.Term.eqb] at heq
      | literal _ => simp [RDF.Term.eqb] at heq
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at heq
  | literal l =>
      simp only [instObject, Option.some.injEq] at hinst
      subst hinst
      cases t with
      | literal m =>
          have hlm : l.val.eqb m.val = true := by simpa [RDF.Term.eqb] using heq
          exact ⟨mu, by simp [tryBindTerm, hlm], hc, Extends.refl mu,
            by simp [patternTermVars]⟩
      | iri _ => simp [RDF.Term.eqb] at heq
      | bnode _ => simp [RDF.Term.eqb] at heq
      | tripleTerm _ _ _ => simp [RDF.Term.eqb] at heq
  | var v =>
      simp only [instObject] at hinst
      cases hm : mu.lookup v with
      | none =>
          refine ⟨mu.bind v t, by simp [tryBindTerm, hm], ?_,
            Extends.bind hm, ?_⟩
          · exact bindingCompat_bind hc hinst (by rw [RDF.Term.eqb_symm]; exact heq)
          · intro w hw
            simp only [patternTermVars, List.mem_singleton] at hw
            subst hw
            simp [Binding.bind, Binding.lookup]
      | some existing =>
          obtain ⟨u', hu', hue⟩ := hc v existing hm
          rw [hinst, Option.some.injEq] at hu'
          subst hu'
          have hex : existing.eqb t = true := RDF.Term.eqb_trans hue heq
          refine ⟨mu, by simp [tryBindTerm, hm, hex], hc, Extends.refl mu, ?_⟩
          intro w hw
          simp only [patternTermVars, List.mem_singleton] at hw
          subst hw
          rw [hm]; rfl

theorem tpMatch_complete {tp : TriplePattern} {t t' : RDF.Triple}
    {mu target : Binding} (htt : TpTtFree tp)
    (hinst : instTriple id target tp = some t') (heq : RDF.Triple.eqb t' t = true)
    (hc : BindingCompat mu target) :
    ∃ mu1, tpMatch tp t mu = some mu1 ∧ BindingCompat mu1 target ∧
      Extends mu mu1 ∧ ∀ v ∈ tpVars tp, (mu1.lookup v).isSome = true := by
  obtain ⟨hts, htp, hto⟩ := htt
  simp only [RDF.Triple.eqb, Bool.and_eq_true, beq_iff_eq] at heq
  obtain ⟨⟨hes, hep⟩, heo⟩ := heq
  simp only [instTriple] at hinst
  split at hinst
  · exact absurd hinst (by simp)
  · next s0 h1 =>
      split at hinst
      · exact absurd hinst (by simp)
      · next p0 h2 =>
          split at hinst
          · exact absurd hinst (by simp)
          · next o0 h3 =>
              cases hinst
              obtain ⟨mu1, hm1, hc1, he1, hv1⟩ :=
                tryBindSubject_complete hts h1 hes hc
              obtain ⟨mu2, hm2, hc2, he2, hv2⟩ :=
                tryBindTerm_complete htp (instObject_of_constructPredicate h2)
                  (show RDF.Term.eqb (.iri p0) (.iri t.p) = true by
                    rw [show p0 = t.p from hep]; exact RDF.Term.eqb_refl _) hc1
              obtain ⟨mu3, hm3, hc3, he3, hv3⟩ :=
                tryBindTerm_complete hto h3 heo hc2
              refine ⟨mu3, by simp only [tpMatch, hm1, hm2, hm3], hc3,
                (he1.trans he2).trans he3, ?_⟩
              intro w hw
              simp only [tpVars, List.mem_append] at hw
              rcases hw with (hw | hw) | hw
              · exact isSome_of_extends (he2.trans he3) (hv1 w hw)
              · exact isSome_of_extends he3 (hv2 w hw)
              · exact hv3 w hw

theorem evalBgpFrom_complete {g : RDF.Graph} : ∀ (b : Bgp), BgpTtFree b →
    ∀ {mu target : Binding}, BgpMatches target b g → BindingCompat mu target →
      ∃ mu', mu' ∈ evalBgpFrom g b mu ∧ BindingCompat mu' target ∧
        ∀ v ∈ bgpVars b, (mu'.lookup v).isSome = true := by
  intro b
  induction b with
  | nil =>
      intro _ mu target _ hc
      exact ⟨mu, by simp [evalBgpFrom], hc, by simp [bgpVars]⟩
  | cons tp rest ih =>
      intro hb mu target hmatch hc
      obtain ⟨t', hinst, hmem⟩ := hmatch tp (List.mem_cons_self ..)
      obtain ⟨t, ht, hte⟩ := RDF.exists_of_graphMem hmem
      obtain ⟨mu1, hm1, hc1, he1, hv1⟩ :=
        tpMatch_complete (hb tp (List.mem_cons_self ..)) hinst
          (by rw [RDF.Triple.eqb_symm]; exact hte) hc
      obtain ⟨mu', hmem', hc', hv'⟩ :=
        ih (fun u hu => hb u (List.mem_cons_of_mem _ hu))
          (fun u hu => hmatch u (List.mem_cons_of_mem _ hu)) hc1
      refine ⟨mu', ?_, hc', ?_⟩
      · simp only [evalBgpFrom, List.mem_flatMap]
        exact ⟨mu1, List.mem_filterMap.mpr ⟨t, ht, hm1⟩, hmem'⟩
      · intro w hw
        simp only [bgpVars, List.flatMap_cons, List.mem_append] at hw
        rcases hw with hw | hw
        · exact isSome_of_extends (evalBgpFrom_extends rest hmem') (hv1 w hw)
        · exact hv' w hw

/-- **Evaluator completeness at the pivot**: a mapping that
instantiates the whole pattern into the graph has a counterpart the
evaluator RETURNS, agreeing with it on every variable of the pattern
by engine equality.

The conclusion is agreement rather than `target ∈ evalBgp b g` because
binding-list ORDER and the COARSENESS of `Term.eqb` are both invisible
to `BgpMatches` — see the module header. `BgpTtFree` is the fragment
guard; the boundary row records it. -/
theorem bgp_eval_complete {b : Bgp} {g : RDF.Graph} {target : Binding}
    (hb : BgpTtFree b) (h : BgpMatches target b g) :
    ∃ mu', mu' ∈ evalBgp b g ∧
      ∀ v ∈ bgpVars b, ∃ u u', target.lookup v = some u ∧
        mu'.lookup v = some u' ∧ RDF.Term.eqb u' u = true := by
  obtain ⟨mu', hmem, hc, hv⟩ :=
    evalBgpFrom_complete b hb h (bindingCompat_empty target)
  refine ⟨mu', hmem, fun v hvm => ?_⟩
  obtain ⟨u', hl⟩ := Option.isSome_iff_exists.mp (hv v hvm)
  obtain ⟨u, hu, hue⟩ := hc v u' hl
  exact ⟨u, u', hu, hl, hue⟩

end Complete

/-! ## Chaining the two halves to the engine -/

/-- **Engine answers are unified answers.** Unconditional: no fragment
guard, because the soundness half needs none. -/
theorem unified_adequate_bgp_engine {b : SPARQL.Bgp} {g : RDF.Graph}
    {mu : SPARQL.Binding} (h : mu ∈ SPARQL.evalBgp b g) :
    Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu :=
  bgp_matches_answers (bgp_eval_sound h)

/-- **Unified answers are engine answers**, up to the two things the
semantics cannot see (module header): a mapping that answers the query
has a counterpart the evaluator returns, agreeing with it on every
variable of the pattern by engine equality. -/
theorem unified_bgp_answers_returned {b : SPARQL.Bgp} {g : RDF.Graph}
    {mu : SPARQL.Binding} (hg : RDF.GraphTtFree g) (hb : BgpTtFree b)
    (h : Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu) :
    ∃ mu', mu' ∈ SPARQL.evalBgp b g ∧
      ∀ v ∈ bgpVars b, ∃ u u', mu.lookup v = some u ∧
        mu'.lookup v = some u' ∧ RDF.Term.eqb u' u = true :=
  bgp_eval_complete hb ((unified_adequate_bgp b g mu hg hb).mpr h)

/-! ## The §18.3.1 reading, discharged rather than assumed

Stage 6 stated the specification-level corollary as
`unified_adequate_bgp_bnodeFree`, whose extra hypothesis
`bgpBnodeFree b = true` did no work in the proof: it marked which
instances of `unified_adequate_bgp` were claims about SPARQL 1.1
rather than about this engine. That hypothesis is now DROPPED, because
the engine no longer needs it.

`Query.evalSelect` (and `evalAsk`, and `evalConstruct`) runs
`QueryPattern.rewriteBnodes` before evaluation, so the basic graph
pattern the algebra ever sees is `b.map rewriteBnodeTriple`: every
pattern blank node has become the variable `_bnode_<label>`, which is
§18.3.1's non-distinguished variable, and §18.2.4's OutScope strip
(`stripSyntheticBnodeVars`) removes it again from the answer. The
2026-08-26 repair extended that rewrite to EXISTS bodies
(https://github.com/danbri/factoidal/issues/607).

So the fragment guard is not assumed of the user's pattern; it is
PROVED of the pattern the engine matches. `bgpBnodeFree_rewriteBnodes`
below is that proof, and `unified_adequate_bgp_spec` is the gate
theorem with no blank-node hypothesis of any kind. -/

theorem patternTermBnodeFree_rewrite (pt : SPARQL.PatternTerm)
    (h : PatternTermTtFree pt) :
    patternTermBnodeFree (SPARQL.rewriteBnodeTerm pt) = true := by
  cases pt with
  | var _ => rfl
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm _ _ _ => exact absurd h (by simp [PatternTermTtFree])

theorem patternSubjectBnodeFree_rewrite (ps : SPARQL.PatternSubject)
    (h : PatternSubjectTtFree ps) :
    patternSubjectBnodeFree (SPARQL.rewriteBnodeSubject ps) = true := by
  cases ps with
  | var _ => rfl
  | iri _ => rfl
  | bnode _ => rfl
  | tripleTerm _ _ _ => exact absurd h (by simp [PatternSubjectTtFree])

/-- **The rewritten pattern carries no blank node.** The hypothesis is
`BgpTtFree`, which the gate theorem already carries: a triple-term
SUBJECT pattern is the one position `rewriteBnodeSubject` does not
descend into (it matches no concrete data subject, so nothing depends
on it), and `BgpTtFree` excludes exactly that. -/
theorem bgpBnodeFree_rewriteBnodes (b : SPARQL.Bgp) (hb : BgpTtFree b) :
    bgpBnodeFree (b.map SPARQL.rewriteBnodeTriple) = true := by
  simp only [bgpBnodeFree, List.all_eq_true, List.mem_map,
             forall_exists_index, and_imp]
  rintro tp' tp htp rfl
  obtain ⟨hs, hp, ho⟩ := hb tp htp
  simp only [SPARQL.rewriteBnodeTriple, Bool.and_eq_true]
  exact ⟨⟨patternSubjectBnodeFree_rewrite tp.s hs,
          patternTermBnodeFree_rewrite tp.p hp⟩,
         patternTermBnodeFree_rewrite tp.o ho⟩

/-- Rewriting a blank node into a variable preserves triple-term
freeness, position by position. -/
theorem patternTermTtFree_rewrite {pt : SPARQL.PatternTerm}
    (h : PatternTermTtFree pt) :
    PatternTermTtFree (SPARQL.rewriteBnodeTerm pt) := by
  cases pt <;> simp_all [SPARQL.rewriteBnodeTerm, PatternTermTtFree]

theorem patternSubjectTtFree_rewrite {ps : SPARQL.PatternSubject}
    (h : PatternSubjectTtFree ps) :
    PatternSubjectTtFree (SPARQL.rewriteBnodeSubject ps) := by
  cases ps <;> simp_all [SPARQL.rewriteBnodeSubject, PatternSubjectTtFree]

theorem bgpTtFree_rewriteBnodes (b : SPARQL.Bgp) (hb : BgpTtFree b) :
    BgpTtFree (b.map SPARQL.rewriteBnodeTriple) := by
  rintro tp' htp'
  simp only [List.mem_map] at htp'
  obtain ⟨tp, htp, rfl⟩ := htp'
  obtain ⟨hs, hp, ho⟩ := hb tp htp
  exact ⟨patternSubjectTtFree_rewrite hs,
         patternTermTtFree_rewrite hp,
         patternTermTtFree_rewrite ho⟩

/-- **BGP adequacy for the pattern the engine matches** — the gate
theorem with NO blank-node hypothesis.

`b` is the user's basic graph pattern, blank nodes and all;
`b.map SPARQL.rewriteBnodeTriple` is what `Query.evalSelect` hands the
algebra. The two hypotheses are the stage's triple-term guards and
nothing else: `bgpBnodeFree` has been discharged by
`bgpBnodeFree_rewriteBnodes`, not assumed. On this statement the
delimitation of https://github.com/danbri/factoidal/issues/607 is
closed for the query path, and the iff is a claim about SPARQL 1.1
§18.3.1 for EVERY pattern, not only blank-node-free ones.

Still NOT claimed here (registry §9): any multiplicity, and
membership in `evalBgp` on the nose. -/
theorem unified_adequate_bgp_spec (b : SPARQL.Bgp) (g : RDF.Graph)
    (mu : SPARQL.Binding) (hg : RDF.GraphTtFree g) (hb : BgpTtFree b) :
    BgpMatches mu (b.map SPARQL.rewriteBnodeTriple) g ↔
      Answers condTrue termEqSchema [rdfToTheorySk g]
        (sparqlBgpToQuery (b.map SPARQL.rewriteBnodeTriple)) mu :=
  unified_adequate_bgp (b.map SPARQL.rewriteBnodeTriple) g mu hg
    (bgpTtFree_rewriteBnodes b hb)

/-! ## The entailment regimes

The design document's `regime_sound` shape, once: a regime is a
materialisation, so its answers are unified answers over the ORIGINAL
graph whenever the closure it materialises is true in every model of
the graph that satisfies the regime's schema. Each regime instance
supplies that one fact. -/

/-- **The regime theorem shape.** `hclosure` is the regime's own
content: in every interpretation meeting the bundle and the schema
that holds the graph under the Skolem assignment, the materialised
graph holds too. -/
theorem regime_sound_of_closureHolds {S : Schema} {conds : CL.Interp → Prop}
    {g gc : RDF.Graph} {b : SPARQL.Bgp} {mu : SPARQL.Binding}
    (hclosure : ∀ i : CL.Interp, conds i → SatisfiesSchema i S →
      RDF.HoldsAll (restrictInterp i) (skAssign i) g →
      RDF.HoldsAll (restrictInterp i) (skAssign i) gc)
    (h : mu ∈ SPARQL.evalBgp b gc) :
    Answers conds (bgpSchema S) [rdfToTheorySk g] (sparqlBgpToQuery b) mu := by
  intro i hi hS hsat
  rw [bgpSchema, satisfiesSchema_union_iff] at hS
  have hg : RDF.HoldsAll (restrictInterp i) (skAssign i) g :=
    (satisfies_rdfToTheorySk_restrict i g).mp (hsat _ (List.mem_singleton.mpr rfl))
  have hgc : CL.Satisfies i (rdfToTheorySk gc) :=
    (satisfies_rdfToTheorySk_restrict i gc).mpr (hclosure i hi hS.2 hg)
  exact bgp_matches_answers (bgp_eval_sound h) i trivial hS.1
    (fun s hs => by obtain rfl := List.mem_singleton.mp hs; exact hgc)

/-- **`simple`**: the regime materialises nothing
(`RDF.Regime.closure .simple = id`), so its answers are answers over
the empty schema. -/
theorem regime_sound_simple {g : RDF.Graph} {b : SPARQL.Bgp}
    {mu : SPARQL.Binding} (D cmps : List RDF.WfIri)
    (h : mu ∈ SPARQL.evalBgp b (RDF.Regime.closure .simple D cmps g)) :
    Answers condTrue (bgpSchema emptySchema) [rdfToTheorySk g]
      (sparqlBgpToQuery b) mu :=
  regime_sound_of_closureHolds (fun _ _ _ hg => hg) h

/-- **`x-rdfscore`** (`RDFS/RegimeDispatch.lean`'s ρdf closure): every
answer over the closure is an answer over the graph under the ρdf
schema. -/
theorem regime_sound_rhoDf {g : RDF.Graph} {b : SPARQL.Bgp}
    {mu : SPARQL.Binding} (fuel : Nat)
    (h : mu ∈ SPARQL.evalBgp b (RDFS.closure g fuel)) :
    Answers condTrue (bgpSchema rdfsCoreSchema) [rdfToTheorySk g]
      (sparqlBgpToQuery b) mu := by
  refine regime_sound_of_closureHolds (fun i _ hS hg t ht => ?_) h
  exact RDF.rhoDf_derives_holds ((satisfiesSchema_rhoDf_iff i).mp hS) hg
    (RDFS.closure_sound fuel g ht)

/-- **`x-rdfscore`, the materialisation is answer-preserving**: under
the ρdf schema, answering from the closure's Skolem reading and
answering from the graph's are the SAME relation — the Skolem-level
analogue of `RDF.rhoDfEntails_closure_iff`, and the property that
makes a materialisation-based regime well defined. Both directions,
no fragment hypotheses.

This is NOT regime completeness against the running evaluator: that
needs the closure to be SATURATED, which is the hypothesis the stage 2
decided corollary carries (`rhoDfClosedCheck`). Recorded as a gap
row. -/
theorem regime_rhoDf_answers_closure_iff {g : RDF.Graph} {b : SPARQL.Bgp}
    {mu : SPARQL.Binding} (fuel : Nat) :
    Answers condTrue (bgpSchema rdfsCoreSchema)
        [rdfToTheorySk (RDFS.closure g fuel)] (sparqlBgpToQuery b) mu ↔
      Answers condTrue (bgpSchema rdfsCoreSchema) [rdfToTheorySk g]
        (sparqlBgpToQuery b) mu := by
  constructor
  · intro h i hi hS hsat
    rw [bgpSchema, satisfiesSchema_union_iff] at hS
    have hg : RDF.HoldsAll (restrictInterp i) (skAssign i) g :=
      (satisfies_rdfToTheorySk_restrict i g).mp (hsat _ (List.mem_singleton.mpr rfl))
    have hgc : CL.Satisfies i (rdfToTheorySk (RDFS.closure g fuel)) :=
      (satisfies_rdfToTheorySk_restrict i _).mpr (fun t ht =>
        RDF.rhoDf_derives_holds ((satisfiesSchema_rhoDf_iff i).mp hS.2) hg
          (RDFS.closure_sound fuel g ht))
    exact h i hi (by rw [bgpSchema, satisfiesSchema_union_iff]; exact hS)
      (fun s hs => by obtain rfl := List.mem_singleton.mp hs; exact hgc)
  · intro h i hi hS hsat
    refine h i hi hS (fun s hs => ?_)
    obtain rfl := List.mem_singleton.mp hs
    refine (satisfies_rdfToTheorySk_iff i g).mpr (fun t ht => ?_)
    exact (satisfies_rdfToTheorySk_iff i _).mp
      (hsat _ (List.mem_singleton.mpr rfl)) t (RDFS.closure_extensive fuel g ht)

/-- **`RDFS`** (`RDF.Regime.closure .rdfs`, the full closure): every
answer over the closure is an answer over the graph under the RDFS
schema. Carries the two hypotheses `unified_rdfs_closure_sound`
carries — the `rdf:_n` slice condition and `rdf:XMLLiteral ∈ D`
(stage 2 correction note 10b). -/
theorem regime_sound_rdfs {g : RDF.Graph} {b : SPARQL.Bgp}
    {mu : SPARQL.Binding} (D cmps : List RDF.WfIri)
    (hcmps : ∀ c ∈ cmps, RDF.IsRdfMemberIri c)
    (hxml : RDF.rdfXMLLiteral ∈ D)
    (h : mu ∈ SPARQL.evalBgp b (RDF.Regime.closure .rdfs D cmps g)) :
    Answers condTrue (bgpSchema (rdfsSchema (fun x => x ∈ D)))
      [rdfToTheorySk g] (sparqlBgpToQuery b) mu := by
  refine regime_sound_of_closureHolds (fun i _ hS hg t ht => ?_) h
  have hc := (satisfiesSchema_rdfs_iff i (fun x => x ∈ D)).mp hS
  refine RDF.derivesFull_holds hc ?_ hg (RDFS.fullClosure_sound D cmps g ht)
  exact RDF.axiomaticTriples_hold (skAssign i) D cmps hcmps hc.1.2
    (fun a' t' ht' => hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a' t' ht')
    hc.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hxml

/-! ## The assertion-decoration merge: a premise-list transform, not
a closure

The merge does not close a graph under rules; it merges the CONTENT of
every ASSERTED proposition into the default graph (design document
§2.4's assertion decoration). At the unified level that is a transform
of the
PREMISE LIST: the extended default graph is entailed by the dataset's
own graphs, read Skolem-wise.

This module supplies the premise list only. The soundness statements
themselves are in `Unified/ClBridge.lean`, over the unified layer's
own dataset reading (`Unified/DatasetEmbed.lean`'s `datasetToTheory`),
because that reading is what the engine's answers have to be sound
with respect to.

WHY THEY MOVED (https://github.com/danbri/factoidal/issues/609 item 3,
2026-08-26). Until that repair this module carried
these statements over `iklPremises`. Two measurements against them:

* `iklPremises` asserts EVERY named graph, asserted or merely
  mentioned, so it identifies assertion with mention before the
  theorem starts. `ClBridge`'s
  `ikl_reading_diverges_from_decoration_only_embedding` records the
  disagreement that produced.
* `ClBridge`'s `mergeWhere_entailed` proves the same entailment for
  EVERY selection predicate over the named graphs, so the statement
  certified nothing about the choice of the `urn:cl:def:asserts`
  test, and did not see that a link decoration does not assert.

The replacements read the dataset with `datasetToTheory`, which
asserts an ASSERTS-decorated named graph and no other, and are
predicate-sensitive: `ClBridge`'s
`embedding_sees_the_assertion_decoration` refutes the merge-everything
instance. -/

theorem mem_graphAdd {g : RDF.Graph} {t u : RDF.Triple}
    (h : t ∈ RDF.Graph.add u g) : t ∈ g ∨ t = u := by
  simp only [RDF.Graph.add] at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

theorem mem_graphUnion : ∀ (g2 g1 : RDF.Graph) {t : RDF.Triple},
    t ∈ RDF.Graph.union g1 g2 → t ∈ g1 ∨ t ∈ g2
  | [], g1, t, h => Or.inl h
  | u :: rest, g1, t, h => by
      simp only [RDF.Graph.union, List.foldl_cons] at h
      rcases mem_graphUnion rest (g1.add u) h with h | h
      · rcases mem_graphAdd h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The SUPERSEDED premise list a dataset contributes: the default
graph's Skolem reading and every named graph's. It asserts every named
graph, asserted or merely mentioned — kept as the record of what the
issue-609 item-3 repair replaced. -/
def iklPremises (ds : RDF.Dataset) : List CL.Sentence :=
  rdfToTheorySk ds.default :: ds.named.map (fun ng => rdfToTheorySk ng.graph)

/-! ## Non-vacuity

Every guard the design document asks for: a decidable pivot check with
both polarities pinned, a positive answer, a REFUTED answer (so the
gate is not proving everything), and a witness that `termEqSchema`
carries rows no interpretation gets for free. -/

/-- The pivot, decided. -/
def bgpMatchesCheck (mu : SPARQL.Binding) (b : SPARQL.Bgp) (g : RDF.Graph) : Bool :=
  b.all (fun tp =>
    match SPARQL.instTriple id mu tp with
    | some t => RDF.Graph.mem t g
    | none => false)

theorem bgpMatchesCheck_iff {mu : SPARQL.Binding} {b : SPARQL.Bgp}
    {g : RDF.Graph} : bgpMatchesCheck mu b g = true ↔ BgpMatches mu b g := by
  simp only [bgpMatchesCheck, List.all_eq_true]
  constructor
  · intro h tp htp
    have h1 := h tp htp
    split at h1
    · next t ht => exact ⟨t, ht, h1⟩
    · exact absurd h1 (by simp)
  · intro h tp htp
    obtain ⟨t, ht, hm⟩ := h tp htp
    rw [ht]; exact hm

section Witnesses

private theorem exIri (s : String) : RDF.isIri ("http://example/" ++ s) = true := by
  simp [RDF.isIri, String.isEmpty]

private def eIri (s : String) : RDF.WfIri := ⟨"http://example/" ++ s, exIri s⟩

private def wG : RDF.Graph :=
  [{ s := .iri (eIri "a"), p := eIri "p", o := .iri (eIri "b") }]

private def wB : SPARQL.Bgp :=
  [{ s := .var "s", p := .iri (eIri "p"), o := .var "o" }]

private def muGood : SPARQL.Binding :=
  [("s", .iri (eIri "a")), ("o", .iri (eIri "b"))]

private def muBad : SPARQL.Binding :=
  [("s", .iri (eIri "b")), ("o", .iri (eIri "a"))]

#guard bgpMatchesCheck muGood wB wG
#guard ! bgpMatchesCheck muBad wB wG

private theorem wG_ttFree : RDF.GraphTtFree wG := by
  intro t ht
  simp only [wG, List.mem_singleton] at ht
  subst ht
  simp [RDF.TermTtFree]

private theorem wB_ttFree : BgpTtFree wB := by
  intro tp htp
  simp only [wB, List.mem_singleton] at htp
  subst htp
  exact ⟨trivial, trivial, trivial⟩

/-- A real answer: the gate theorem produces an entailment, not a
vacuous one. -/
theorem unified_bgp_answer_witness :
    Answers condTrue termEqSchema [rdfToTheorySk wG] (sparqlBgpToQuery wB) muGood :=
  bgp_matches_answers (bgpMatchesCheck_iff.mp (by rfl))

/-- A REFUTED answer: the reversed mapping is not an answer. Without
this the gate theorem would be compatible with `Answers` holding of
everything. -/
theorem unified_bgp_no_answer :
    ¬ Answers condTrue termEqSchema [rdfToTheorySk wG] (sparqlBgpToQuery wB) muBad := by
  intro h
  have hm := (unified_adequate_bgp wB wG muBad wG_ttFree wB_ttFree).mpr h
  exact absurd (bgpMatchesCheck_iff.mpr hm) (by decide)

/-! ### The §18.3.1 repair has content

Without these three the `bgpBnodeFree` guard could have been dropped
by a theorem that says nothing new. `wBbn` is the user's pattern
`?s <p> _:z`. Against `wG` the RAW pattern matches nothing at all —
`wG` has no blank node, let alone one labelled `z` — while the
rewritten pattern `?s <p> ?_bnode_z` matches, with `_bnode_z` bound to
the object. That difference is exactly what
https://github.com/danbri/factoidal/issues/607 was about, and it is
what `unified_adequate_bgp_spec` now states an iff over. -/

private def wBbn : SPARQL.Bgp :=
  [{ s := .var "s", p := .iri (eIri "p"), o := .bnode "z" }]

private def muBn : SPARQL.Binding :=
  [("s", .iri (eIri "a")), ("_bnode_z", .iri (eIri "b"))]

-- The raw pattern matches NO mapping that the rewritten one matches:
-- the engine reads `_:z` as a constant, and `wG` carries no blank node.
#guard ! bgpMatchesCheck muBn wBbn wG
-- The rewritten pattern does match, with the non-distinguished
-- variable bound to the object §18.3.1's pattern instance mapping
-- sends `_:z` to.
#guard bgpMatchesCheck muBn (wBbn.map SPARQL.rewriteBnodeTriple) wG

private theorem wBbn_ttFree : BgpTtFree wBbn := by
  intro tp htp
  simp only [wBbn, List.mem_singleton] at htp
  subst htp
  exact ⟨trivial, trivial, trivial⟩

/-- The rewritten pattern of a blank-node-carrying BGP satisfies the
guard stage 6 had to ASSUME. -/
theorem wBbn_rewrite_bnodeFree :
    bgpBnodeFree (wBbn.map SPARQL.rewriteBnodeTriple) = true :=
  bgpBnodeFree_rewriteBnodes wBbn wBbn_ttFree

/-- …and the user's own pattern does NOT: the guard was a real
restriction, so dropping it is a real strengthening. -/
theorem wBbn_not_bnodeFree : bgpBnodeFree wBbn = false := by decide

/-- A real answer for a blank-node-carrying pattern, through the
no-blank-node-hypothesis gate. -/
theorem unified_bgp_bnode_answer_witness :
    Answers condTrue termEqSchema [rdfToTheorySk wG]
      (sparqlBgpToQuery (wBbn.map SPARQL.rewriteBnodeTriple)) muBn :=
  (unified_adequate_bgp_spec wBbn wG muBn wG_ttFree wBbn_ttFree).mp
    (bgpMatchesCheck_iff.mp (by rfl))

/-- And not of everything: swapping the two terms is refuted. -/
theorem unified_bgp_bnode_no_answer :
    ¬ Answers condTrue termEqSchema [rdfToTheorySk wG]
        (sparqlBgpToQuery (wBbn.map SPARQL.rewriteBnodeTriple))
        [("s", .iri (eIri "b")), ("_bnode_z", .iri (eIri "a"))] := by
  intro h
  have hm := (unified_adequate_bgp_spec wBbn wG _ wG_ttFree wBbn_ttFree).mpr h
  exact absurd (bgpMatchesCheck_iff.mpr hm) (by decide)

/-- `termEqSchema` carries rows that are NOT instances of
reflexivity: two DISTINCT RDF terms the engine identifies, whose
`eq` row is a real sentence of the schema. Without such a row the
soundness half is false wherever the graph and the pattern spell a
language tag with different case.

Stated with the language-tag fact as a hypothesis for a reason worth
recording: `String.toLower` does not reduce in the Lean kernel, so
neither `decide` nor `rfl` can discharge `langTagEq "EN" "en" = true`.
The `#guard` under this theorem pins that concrete instance at build
time, which is where the tree's other kernel-opaque facts are
pinned. -/
theorem termEqSchema_nontrivial {t1 t2 : String} (hne : t1 ≠ t2)
    (heq : RDF.langTagEq t1 t2 = true) :
    ∃ x y : RDF.Term, x ≠ y ∧ RDF.Term.eqb x y = true ∧
      termEqSchema (.eq (embedTerm x) (embedTerm y)) := by
  refine ⟨.literal ⟨{ lexicalForm := "a", datatype := RDF.rdfLangString,
                      langTag := some t1, direction := none }, by rfl⟩,
          .literal ⟨{ lexicalForm := "a", datatype := RDF.rdfLangString,
                      langTag := some t2, direction := none }, by rfl⟩,
          ?_, ?_, ?_⟩
  · intro h
    simp only [RDF.Term.literal.injEq, Subtype.ext_iff,
               RDF.Literal.mk.injEq, Option.some.injEq] at h
    exact hne h.2.2.1
  · simp only [RDF.Term.eqb, RDF.Literal.eqb, RDF.langTagOptionEq, heq]
    decide +kernel
  · exact ⟨_, _, by
      simp only [RDF.Term.eqb, RDF.Literal.eqb, RDF.langTagOptionEq, heq]
      decide +kernel, rfl⟩

/-! The concrete instance, pinned at build time. -/
#guard RDF.langTagEq "EN" "en"

end Witnesses

/-! ## Axiom audits (in-source, per the stage gate) -/

section Audits

#print axioms satisfies_rdfToTheorySk_restrict
#print axioms bgp_eval_sound
#print axioms bgp_matches_answers
#print axioms tq_eq_iff
#print axioms herbQ_satisfiesSchema
#print axioms herbQ_satisfies_sk
#print axioms unified_adequate_bgp
#print axioms bgpBnodeFree_rewriteBnodes
#print axioms bgpTtFree_rewriteBnodes
#print axioms unified_adequate_bgp_spec
#print axioms bgp_eval_complete
#print axioms unified_adequate_bgp_engine
#print axioms unified_bgp_answers_returned
#print axioms regime_sound_of_closureHolds
#print axioms regime_sound_simple
#print axioms regime_sound_rhoDf
#print axioms regime_rhoDf_answers_closure_iff
#print axioms regime_sound_rdfs
#print axioms unified_bgp_answer_witness
#print axioms unified_bgp_no_answer
#print axioms wBbn_rewrite_bnodeFree
#print axioms wBbn_not_bnodeFree
#print axioms unified_bgp_bnode_answer_witness
#print axioms unified_bgp_bnode_no_answer
#print axioms termEqSchema_nontrivial

end Audits

end L4Factoidal.Unified
