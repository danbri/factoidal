/-
L4Factoidal.Unified.RdfTransport — the transport pair between RDF
simple interpretations and CL interpretations, with the satisfaction
transfer lemmas (stage 1 of
https://github.com/danbri/factoidal/issues/598; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §4.1).

* `restrictInterp : CL.Interp → RDF.Interp` — the RDF interpretation a
  CL interpretation induces: `iext p x y` is `rel p [x, y]`, IRIs
  denote through `iName`, and the `literalValueOf` / `tripleTerm`
  operators realise `iLit` / `iTt`.
* `liftInterp : RDF.Interp → CL.Interp` — the CL interpretation an RDF
  interpretation induces. DEVIATION from the design document, which
  proposed "dom preserved": `CL.fn` receives only the DENOTATIONS of
  the literal operator's arguments, and with `dom = r.idom` there is
  no way to recover the lexical form and datatype IRI that `r.iLit`
  needs (`iStr`/`iName` need not be injective). The domain here is
  `Option String × r.idom`: the second component is the RDF-side
  denotation (what the transfer lemma equates), the first tags a
  domain element with the string it came from when it came from a
  name or a quoted string, which is exactly what the `literalValueOf`
  operator needs to rebuild the literal. The projection to `r.idom`
  is what every transfer statement is about; the tag never influences
  `rel`.

Both transfers rest on the colon-free bound-name spelling of
`Unified.RdfEmbed`: a valuation obtained by overriding `iName` at
bound names still agrees with `iName` on every colon-containing name
(`FreshVal`), so IRI names, datatype names and the operator names are
never captured — unconditionally, for every graph.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfEmbed

namespace L4Factoidal.Unified

/-! ## Valuation plumbing -/

/-- Override a valuation on a name list: names in `names` read from
`f`, all others from `base`. -/
def overrideOn {d : Type} (base : String → d) (names : List String)
    (f : String → d) : String → d :=
  fun n => if n ∈ names then f n else base n

/-- The valuation agrees with the interpretation's own name mapping on
every colon-containing name — the freshness invariant every transfer
lemma consumes (IRI strings and the `urn:cl:def:` operators all
contain a colon; bound names never do). -/
def FreshVal (i : CL.Interp) (ν : String → i.dom) : Prop :=
  ∀ n : String, ':' ∈ n.toList → ν n = i.iName n

theorem freshVal_overrideOn (i : CL.Interp) {names : List String}
    (hnames : ∀ n ∈ names, ':' ∉ n.toList) (f : String → i.dom) :
    FreshVal i (overrideOn i.iName names f) := by
  intro n hn
  have hnm : n ∉ names := fun hmem => hnames n hmem hn
  simp [overrideOn, hnm]

/-- Existential closure over a plain-name list, characterised: some
override of the ambient valuation at exactly those names satisfies the
body. Duplicate names are harmless (the last binding shadows, and the
override reads one value per name). -/
theorem satExists_plains (i : CL.Interp) (σ : String → List i.dom)
    (body : CL.Sentence) :
    ∀ (names : List String) (ν : String → i.dom),
      CL.SatExists i ν σ (names.map .plain) body ↔
        ∃ f : String → i.dom, CL.Sat i (overrideOn ν names f) σ body
  | [], ν => by
      simp only [List.map_nil, CL.SatExists]
      constructor
      · intro hs
        refine ⟨fun _ => i.domWit, ?_⟩
        have hv : overrideOn ν [] (fun _ => i.domWit) = ν := by
          funext m; simp [overrideOn]
        rw [hv]; exact hs
      · rintro ⟨f, hf⟩
        have hv : overrideOn ν [] f = ν := by
          funext m; simp [overrideOn]
        rw [hv] at hf; exact hf
  | n :: rest, ν => by
      simp only [List.map_cons, CL.SatExists]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨f, hf⟩ :=
          (satExists_plains i σ body rest (CL.updateInd ν n x)).mp hx
        refine ⟨fun m => if m ∈ rest then f m else x, ?_⟩
        have hv : overrideOn ν (n :: rest) (fun m => if m ∈ rest then f m else x)
            = overrideOn (CL.updateInd ν n x) rest f := by
          funext m
          by_cases h1 : m ∈ rest <;> by_cases h2 : m = n <;>
            simp [overrideOn, CL.updateInd, h1, h2]
        rw [hv]; exact hf
      · rintro ⟨f, hf⟩
        refine ⟨f n, (satExists_plains i σ body rest (CL.updateInd ν n (f n))).mpr
          ⟨f, ?_⟩⟩
        have hv : overrideOn (CL.updateInd ν n (f n)) rest f
            = overrideOn ν (n :: rest) f := by
          funext m
          by_cases h1 : m ∈ rest <;> by_cases h2 : m = n <;>
            simp [overrideOn, CL.updateInd, h1, h2]
        rw [hv]; exact hf

theorem satAll_forall (i : CL.Interp) (ν : String → i.dom)
    (σ : String → List i.dom) :
    ∀ ss : List CL.Sentence, CL.SatAll i ν σ ss ↔ ∀ s ∈ ss, CL.Sat i ν σ s
  | [] => by simp [CL.SatAll]
  | s :: r => by
      simp only [CL.SatAll, List.mem_cons]
      rw [satAll_forall i ν σ r]
      constructor
      · rintro ⟨h1, h2⟩ u (rfl | hu)
        · exact h1
        · exact h2 u hu
      · intro hh
        exact ⟨hh s (Or.inl rfl), fun u hu => hh u (Or.inr hu)⟩

/-- The graph body is satisfied exactly when every triple's atom is. -/
theorem sat_rdfBody (i : CL.Interp) (ν : String → i.dom)
    (σ : String → List i.dom) (g : RDF.Graph) :
    CL.Sat i ν σ (rdfBody g) ↔ ∀ t ∈ g, CL.Sat i ν σ (tripleAtom t) := by
  unfold rdfBody
  simp only [CL.Sat]
  rw [satAll_forall]
  constructor
  · intro hh t ht
    exact hh _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · rintro hh s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hh t ht

/-- Satisfaction of a translated graph, characterised: some valuation
of the bound names satisfies every triple atom. -/
theorem satisfies_rdfToTheory_iff (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheory g) ↔
      ∃ f : String → i.dom, ∀ t ∈ g,
        CL.Sat i (overrideOn i.iName (graphBnodeNames g) f)
          (fun _ => []) (tripleAtom t) := by
  unfold CL.Satisfies rdfToTheory
  simp only [CL.Sat]
  rw [satExists_plains]
  simp only [sat_rdfBody]

/-! ## `restrictInterp` : CL to RDF -/

/-- The RDF interpretation a CL interpretation induces (design
document §4.1). -/
def restrictInterp (i : CL.Interp) : RDF.Interp where
  idom := i.dom
  idomWit := i.domWit
  iIri := fun x => i.iName x.val
  iLit := fun l => CL.denotTerm i i.iName (fun _ => []) (embedTerm (.literal l))
  iTt := fun s p o => i.fn (i.iName ttOp) [s, p, o]
  iext := fun p x y => i.rel p [x, y]

/-- A literal's argument denotations do not depend on the valuation
pair, given freshness: the arguments are quoted strings and
colon-containing names only. -/
theorem denotSeq_litArgs (i : CL.Interp) {ν : String → i.dom}
    {σ : String → List i.dom} (hν : FreshVal i ν) (l : RDF.WfLiteral) :
    CL.denotSeq i ν σ (embedLiteralArgs l) =
      CL.denotSeq i i.iName (fun _ => []) (embedLiteralArgs l) := by
  obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := l
  have hdt := hν dt.val (isIri_has_colon dt.property)
  rcases tag with _ | tag <;> rcases dir with _ | d <;> try cases d
  all_goals
    simp [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt]

theorem denot_embedSubject_restrict (i : CL.Interp) {ν : String → i.dom}
    {σ : String → List i.dom} (a : RDF.BnodeAssignment i.dom)
    (hν : FreshVal i ν) (s : RDF.Subject)
    (ha : ∀ b ∈ RDF.subjectBnodes s, ν (bnodeName b) = a b) :
    CL.denotTerm i ν σ (embedSubject s) =
      RDF.denotSubject (restrictInterp i) a s := by
  cases s with
  | iri x =>
      simp [embedSubject, CL.denotTerm, RDF.denotSubject, restrictInterp,
            hν x.val (isIri_has_colon x.property)]
  | bnode b =>
      simpa [embedSubject, CL.denotTerm, RDF.denotSubject] using
        ha b (by simp [RDF.subjectBnodes])

theorem denot_embedTerm_restrict (i : CL.Interp) {ν : String → i.dom}
    {σ : String → List i.dom} (a : RDF.BnodeAssignment i.dom)
    (hν : FreshVal i ν) :
    ∀ t : RDF.Term, (∀ b ∈ RDF.termBnodes t, ν (bnodeName b) = a b) →
      CL.denotTerm i ν σ (embedTerm t) = RDF.denotTerm (restrictInterp i) a t
  | .iri x, _ => by
      simp [embedTerm, CL.denotTerm, RDF.denotTerm, restrictInterp,
            hν x.val (isIri_has_colon x.property)]
  | .bnode b, ha => by
      simpa [embedTerm, CL.denotTerm, RDF.denotTerm] using
        ha b (by simp [RDF.termBnodes])
  | .literal l, _ => by
      simp only [embedTerm, CL.denotTerm]
      rw [denotSeq_litArgs i hν l, hν litOp (by decide)]
      rfl
  | .tripleTerm s p o, ha => by
      have hs : ∀ b ∈ RDF.subjectBnodes s, ν (bnodeName b) = a b :=
        fun b hb => ha b (by
          simp only [RDF.termBnodes]; exact List.mem_append_left _ hb)
      have ho : ∀ b ∈ RDF.termBnodes o, ν (bnodeName b) = a b :=
        fun b hb => ha b (by
          simp only [RDF.termBnodes]; exact List.mem_append_right _ hb)
      simp only [embedTerm, CL.denotTerm, CL.denotSeq]
      rw [hν ttOp (by decide), hν p.val (isIri_has_colon p.property),
          denot_embedSubject_restrict i a hν s hs,
          denot_embedTerm_restrict i a hν o ho]
      rfl

/-- Satisfaction of a triple's atom transfers to `TripleHolds` under
the restriction — at any fresh valuation whose bound-name values agree
with the assignment on the triple's blank nodes. -/
theorem sat_tripleAtom_restrict (i : CL.Interp) {ν : String → i.dom}
    {σ : String → List i.dom} (a : RDF.BnodeAssignment i.dom)
    (hν : FreshVal i ν) (t : RDF.Triple)
    (ha : ∀ b ∈ RDF.tripleBnodes t, ν (bnodeName b) = a b) :
    CL.Sat i ν σ (tripleAtom t) ↔ RDF.TripleHolds (restrictInterp i) a t := by
  have hs : ∀ b ∈ RDF.subjectBnodes t.s, ν (bnodeName b) = a b :=
    fun b hb => ha b (by
      simp only [RDF.tripleBnodes]; exact List.mem_append_left _ hb)
  have ho : ∀ b ∈ RDF.termBnodes t.o, ν (bnodeName b) = a b :=
    fun b hb => ha b (by
      simp only [RDF.tripleBnodes]; exact List.mem_append_right _ hb)
  simp only [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq]
  rw [hν t.p.val (isIri_has_colon t.p.property),
      denot_embedSubject_restrict i a hν t.s hs,
      denot_embedTerm_restrict i a hν t.o ho]
  exact Iff.rfl

/-- **Transfer, restriction direction**: a CL interpretation satisfies
a translated graph exactly when its restriction satisfies the graph. -/
theorem satisfies_rdfToTheory_restrict (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheory g) ↔ RDF.Satisfies (restrictInterp i) g := by
  rw [satisfies_rdfToTheory_iff]
  constructor
  · rintro ⟨f, hf⟩
    have hν : FreshVal i (overrideOn i.iName (graphBnodeNames g) f) :=
      freshVal_overrideOn i (graphBnodeNames_no_colon g) f
    refine ⟨fun b => overrideOn i.iName (graphBnodeNames g) f (bnodeName b),
            fun t ht => ?_⟩
    exact (sat_tripleAtom_restrict i _ hν t (fun b _ => rfl)).mp (hf t ht)
  · rintro ⟨a, ha⟩
    let f : String → i.dom := fun n =>
      match bnodeNameDecode n with
      | some b => a b
      | none => i.domWit
    have hν : FreshVal i (overrideOn i.iName (graphBnodeNames g) f) :=
      freshVal_overrideOn i (graphBnodeNames_no_colon g) f
    refine ⟨f, fun t ht => ?_⟩
    refine (sat_tripleAtom_restrict i a hν t ?_).mpr (ha t ht)
    intro b hb
    have hmem : bnodeName b ∈ graphBnodeNames g :=
      List.mem_map.mpr ⟨b, List.mem_flatMap.mpr ⟨t, ht, hb⟩, rfl⟩
    have h1 : overrideOn i.iName (graphBnodeNames g) f (bnodeName b)
        = f (bnodeName b) := if_pos hmem
    rw [h1]
    show (match bnodeNameDecode (bnodeName b) with
          | some b' => a b'
          | none => i.domWit) = a b
    rw [bnodeNameDecode_bnodeName]

/-! ## `liftInterp` : RDF to CL -/

/-- Rebuild the literal denotation from the tagged argument strings:
the decoding half of the `literalValueOf` operator. -/
def liftLitVal (r : RDF.Interp) (lex dt : String) (tag : Option String)
    (dir : Option RDF.TextDirection) : r.idom :=
  if h : RDF.isIri dt then
    if hw : RDF.literalWf { lexicalForm := lex, datatype := ⟨dt, h⟩,
                            langTag := tag, direction := dir } then
      r.iLit ⟨_, hw⟩
    else r.idomWit
  else r.idomWit

/-- Dispatch the `literalValueOf` operator on the argument tags. -/
def liftFnTags (r : RDF.Interp) : List (Option String) → r.idom
  | [some lex, some dt] => liftLitVal r lex dt none none
  | [some lex, some dt, some tag] => liftLitVal r lex dt (some tag) none
  | [some lex, some dt, some tag, some dir] =>
      liftLitVal r lex dt (some tag)
        (some (if dir = "rtl" then .rtl else .ltr))
  | _ => r.idomWit

/-- The CL interpretation an RDF interpretation induces. Domain
`Option String × r.idom` — see the module header for why the tag
component exists (deviation from the design document's "dom
preserved"). -/
def liftInterp (r : RDF.Interp) : CL.Interp where
  dom := Option String × r.idom
  domWit := (none, r.idomWit)
  iName := fun n =>
    (some n, if h : RDF.isIri n then r.iIri ⟨n, h⟩ else r.idomWit)
  iStr := fun s => (some s, r.idomWit)
  rel := fun p args =>
    match args with
    | [x, y] => r.iext p.2 x.2 y.2
    | _ => False
  fn := fun op args =>
    if op.1 = some litOp then (none, liftFnTags r (args.map Prod.fst))
    else if op.1 = some ttOp then
      match args with
      | [s, p, o] => (none, r.iTt s.2 p.2 o.2)
      | _ => (none, r.idomWit)
    else (none, r.idomWit)
  iProp := fun _ _ _ => (none, r.idomWit)

theorem liftInterp_iName_iri (r : RDF.Interp) (x : RDF.WfIri) :
    (liftInterp r).iName x.val = (some x.val, r.iIri x) := by
  simp only [liftInterp]
  rw [dif_pos x.property]

/-- The `literalValueOf` operator applied to a literal's embedded
arguments yields the literal's RDF denotation. -/
theorem liftFn_litArgs (r : RDF.Interp) {ν : String → (liftInterp r).dom}
    {σ : String → List (liftInterp r).dom}
    (hν : FreshVal (liftInterp r) ν) (l : RDF.WfLiteral) :
    (liftInterp r).fn (ν litOp)
        (CL.denotSeq (liftInterp r) ν σ (embedLiteralArgs l)) =
      (none, r.iLit l) := by
  rw [hν litOp (by decide)]
  obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := l
  have hdt := hν dt.val (isIri_has_colon dt.property)
  rcases tag with _ | tag <;> rcases dir with _ | d
  · -- no tag, no direction
    simp [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, liftInterp,
          liftFnTags, liftLitVal, dt.property, hwf]
  · -- direction without tag: ill-formed, unreachable
    exact absurd hwf (by simp [RDF.literalWf])
  · -- tag, no direction
    simp [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, liftInterp,
          liftFnTags, liftLitVal, dt.property, hwf]
  · -- tag and direction
    cases d <;>
      simp [embedLiteralArgs, CL.denotSeq, CL.denotTerm, hdt, liftInterp,
            liftFnTags, liftLitVal, dt.property, hwf]

/-- The `tripleTerm` operator computes `iTt` on the projections. -/
theorem liftFn_tt (r : RDF.Interp) (x y z : (liftInterp r).dom) :
    (liftInterp r).fn ((liftInterp r).iName ttOp) [x, y, z] =
      (none, r.iTt x.2 y.2 z.2) := by
  simp [liftInterp, litOp, ttOp]

theorem denot_embedSubject_lift (r : RDF.Interp)
    {ν : String → (liftInterp r).dom}
    {σ : String → List (liftInterp r).dom}
    (a : RDF.BnodeAssignment r.idom) (hν : FreshVal (liftInterp r) ν)
    (s : RDF.Subject)
    (ha : ∀ b ∈ RDF.subjectBnodes s, (ν (bnodeName b)).2 = a b) :
    (CL.denotTerm (liftInterp r) ν σ (embedSubject s)).2 =
      RDF.denotSubject r a s := by
  cases s with
  | iri x =>
      simp only [embedSubject, CL.denotTerm, RDF.denotSubject]
      rw [hν x.val (isIri_has_colon x.property), liftInterp_iName_iri]
  | bnode b =>
      simpa [embedSubject, CL.denotTerm, RDF.denotSubject] using
        ha b (by simp [RDF.subjectBnodes])

theorem denot_embedTerm_lift (r : RDF.Interp)
    {ν : String → (liftInterp r).dom}
    {σ : String → List (liftInterp r).dom}
    (a : RDF.BnodeAssignment r.idom) (hν : FreshVal (liftInterp r) ν) :
    ∀ t : RDF.Term, (∀ b ∈ RDF.termBnodes t, (ν (bnodeName b)).2 = a b) →
      (CL.denotTerm (liftInterp r) ν σ (embedTerm t)).2 = RDF.denotTerm r a t
  | .iri x, _ => by
      simp only [embedTerm, CL.denotTerm, RDF.denotTerm]
      rw [hν x.val (isIri_has_colon x.property), liftInterp_iName_iri]
  | .bnode b, ha => by
      simpa [embedTerm, CL.denotTerm, RDF.denotTerm] using
        ha b (by simp [RDF.termBnodes])
  | .literal l, _ => by
      simp only [embedTerm, CL.denotTerm]
      rw [liftFn_litArgs r hν l]
      rfl
  | .tripleTerm s p o, ha => by
      have hs : ∀ b ∈ RDF.subjectBnodes s, (ν (bnodeName b)).2 = a b :=
        fun b hb => ha b (by
          simp only [RDF.termBnodes]; exact List.mem_append_left _ hb)
      have ho : ∀ b ∈ RDF.termBnodes o, (ν (bnodeName b)).2 = a b :=
        fun b hb => ha b (by
          simp only [RDF.termBnodes]; exact List.mem_append_right _ hb)
      simp only [embedTerm, CL.denotTerm, CL.denotSeq, RDF.denotTerm]
      rw [hν ttOp (by decide), liftFn_tt r]
      simp only [hν p.val (isIri_has_colon p.property), liftInterp_iName_iri]
      rw [denot_embedSubject_lift r a hν s hs,
          denot_embedTerm_lift r a hν o ho]

theorem sat_tripleAtom_lift (r : RDF.Interp)
    {ν : String → (liftInterp r).dom}
    {σ : String → List (liftInterp r).dom}
    (a : RDF.BnodeAssignment r.idom) (hν : FreshVal (liftInterp r) ν)
    (t : RDF.Triple)
    (ha : ∀ b ∈ RDF.tripleBnodes t, (ν (bnodeName b)).2 = a b) :
    CL.Sat (liftInterp r) ν σ (tripleAtom t) ↔ RDF.TripleHolds r a t := by
  have hs : ∀ b ∈ RDF.subjectBnodes t.s, (ν (bnodeName b)).2 = a b :=
    fun b hb => ha b (by
      simp only [RDF.tripleBnodes]; exact List.mem_append_left _ hb)
  have ho : ∀ b ∈ RDF.termBnodes t.o, (ν (bnodeName b)).2 = a b :=
    fun b hb => ha b (by
      simp only [RDF.tripleBnodes]; exact List.mem_append_right _ hb)
  simp only [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq]
  rw [hν t.p.val (isIri_has_colon t.p.property), liftInterp_iName_iri]
  have hrel : ∀ x y : (liftInterp r).dom,
      (liftInterp r).rel (some t.p.val, r.iIri t.p) [x, y] =
        r.iext (r.iIri t.p) x.2 y.2 := fun x y => rfl
  rw [hrel]
  rw [denot_embedSubject_lift r a hν t.s hs,
      denot_embedTerm_lift r a hν t.o ho]
  exact Iff.rfl

/-- **Transfer, lift direction**: the lifted CL interpretation
satisfies a translated graph exactly when the RDF interpretation
satisfies the graph. -/
theorem satisfies_rdfToTheory_lift (r : RDF.Interp) (g : RDF.Graph) :
    CL.Satisfies (liftInterp r) (rdfToTheory g) ↔ RDF.Satisfies r g := by
  rw [satisfies_rdfToTheory_iff]
  constructor
  · rintro ⟨f, hf⟩
    have hν : FreshVal (liftInterp r)
        (overrideOn (liftInterp r).iName (graphBnodeNames g) f) :=
      freshVal_overrideOn _ (graphBnodeNames_no_colon g) f
    refine ⟨fun b =>
      (overrideOn (liftInterp r).iName (graphBnodeNames g) f (bnodeName b)).2,
      fun t ht => ?_⟩
    exact (sat_tripleAtom_lift r _ hν t (fun b _ => rfl)).mp (hf t ht)
  · rintro ⟨a, ha⟩
    let f : String → (liftInterp r).dom := fun n =>
      (none, match bnodeNameDecode n with
             | some b => a b
             | none => r.idomWit)
    have hν : FreshVal (liftInterp r)
        (overrideOn (liftInterp r).iName (graphBnodeNames g) f) :=
      freshVal_overrideOn _ (graphBnodeNames_no_colon g) f
    refine ⟨f, fun t ht => ?_⟩
    refine (sat_tripleAtom_lift r a hν t ?_).mpr (ha t ht)
    intro b hb
    have hmem : bnodeName b ∈ graphBnodeNames g :=
      List.mem_map.mpr ⟨b, List.mem_flatMap.mpr ⟨t, ht, hb⟩, rfl⟩
    have h1 : overrideOn (liftInterp r).iName (graphBnodeNames g) f (bnodeName b)
        = f (bnodeName b) := if_pos hmem
    rw [h1]
    show ((none, match bnodeNameDecode (bnodeName b) with
                 | some b' => a b'
                 | none => r.idomWit) : (liftInterp r).dom).2 = a b
    rw [bnodeNameDecode_bnodeName]

end L4Factoidal.Unified
