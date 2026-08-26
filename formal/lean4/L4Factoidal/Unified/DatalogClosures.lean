/-
L4Factoidal.Unified.DatalogClosures — stage 3 of
https://github.com/danbri/factoidal/issues/598, second half: the
tree's closure engines EXHIBITED as programs of the Datalog class
(`Unified/Datalog.lean`), with agreement theorems against the native
engines, and the class boundary recorded.

## The exhibits

* `rhoDfProgram` — the six ρdf rows as one Datalog program. The
  agreement theorem `rhoDf_closure_datalog_agree` is GENERAL
  (every graph), stated as MEMBERSHIP equality per the stage 3 brief
  (engine list order/dedup does not match a generic fixpoint), under
  the SAME hypotheses the stage 2 decided corollary carries — engine
  closure ρdf-closed + in the model fragment (both `decide`-dischargeable
  via `rhoDfClosedCheck` / `isRhoDfFrag`) — plus Datalog-side fuel
  adequacy (`saturatedCheck`). The corollary
  `rhoDf_engine_iff_datalog_entails` composes with the stage 3 gate
  theorem: membership in the ρdf ENGINE's closure coincides with CL
  entailment from the program-as-schema — the "closure engines as
  provably-complete fragment deciders" claim of the design document
  §8.2, at its stated claim level (ground-atomic consequences).
* `rdfsPlusProgram` — the RDFS-Plus tier (`RDFS/RDFSPlus.lean`: the
  six ρdf rows plus the 13 OWL rows eq-sym/eq-trans/eq-rep-s/o/p,
  prp-symp, prp-trp, prp-inv1/2, prp-fp, prp-ifp, cax-eqc1/2,
  prp-eqp1/2, and the schema-level inverseOf domain/range flip) as a
  Datalog program — this tier is the RL closure's equality/property
  core. Agreement with the engine (`rdfsPlusClosure`, at fuel its
  length-test loop saturates within — pinned by `#guard`) is
  established on CONCRETE INSTANCES, the demo shapes
  `RDFS/RDFSPlus.lean` pins: membership equality in both directions,
  as a `decide`d THEOREM on the TransitiveProperty demo and as
  native-evaluated build-time `#guard`s on the sameAs and inverseOf
  demos (their substitution closures exceed the kernel `decide`
  budget). A general bridging theorem in the ρdf style is NOT
  claimed for this tier — the
  native tier itself claims no chain-level completeness
  (`RDFS/RDFSPlus.lean` module header), and the engine's per-row
  IRI-subject guards (`subjIri`) restrict some firings the program
  does not.

## The per-rule bridging layer

The stage 2 salvage predicted a bridging layer would be needed
(`rdfs9BnodeConclusions` was stage 2's): here it is the DIAGONAL
specification relations `Rdfs*Derives` (`RDF/EntailmentRdfsSpec.lean`)
— the Datalog rules mirror THOSE, not the engine's step functions.
That choice is what makes the decode direction land on `RhoDfClosed`
(which is stated over the diagonal relations, blank-node classes
included) rather than on the engine step (which skips blank-node
classes; that gap is exactly why `rhoDfClosedCheck` carries
`rdfs9BnodeConclusions`).

## Encoding

RDF terms enter the Datalog fact base through an injective
string-constant encoding: `"i:" ++ iri` / `"b:" ++ label` (distinct
one-character tags; every constant contains `:` at position 1, meeting
the class's colon discipline). Literal and triple-term objects get
placeholder constants — the agreement theorems carry the ρdf model
fragment hypothesis (`RhoDfModelObjectOk`), under which those cases do
not occur; `tripleFact` is proved injective ON that fragment and the
iff carries the same hypothesis on the queried triple's object.

## The boundary — what is OUTSIDE the class, engine by engine

Recorded here because the registry row points at this header.

* rdfD1 / rdfs1-2004 (`RDF.Rdfs1Derives2004`) and the lg/gl literal
  rows: mint a FRESH blank node — an existential head variable.
  Outside BY CONSTRUCTION: `DatalogProgram.wf` includes
  `DRule.definiteB`, so the rule cannot be written into a program
  (`rdfD1Shape` below pins the rejection). Same exclusion the native
  closures make (`RDFS/FullClosure.lean`).
* The OWL RL clash rows (eq-diff1, prp-irp, prp-asyp, prp-pdw,
  cax-dw, cls-nothing2, cls-com, the `owl:NegativePropertyAssertion`
  family — `OWL.RL.detectClash`'s 13 rows): Horn CONSTRAINTS with a
  falsity head. A `DRule` head is an ATOM, so these are outside by
  the shape of the type; the engine treats them as a consistency
  verdict, not as derivation, and so does the unified layer
  (`rangeClashSchema` in `Unified/RdfsSchema.lean` is their
  schema-level home).
* The OWL RL list-valued rows (prp-spo2, prp-key, cls-int1, cls-int2,
  cls-uni, cls-oo, cax-adc, scm-int, scm-uni): each premise walks an
  RDF collection of UNBOUNDED length, so one table row is an infinite
  FAMILY of Horn rules (one per list length), not a finite program's
  rule. The design document §3 stage 4 plans them as sentence
  families at the schema level; they are outside the single-program
  class exhibited here.
* The infinite axiomatic families (`rdf:_n` container membership,
  `RDFS/FullClosure.lean`'s seeded axiom tables): fact SCHEMAS. A
  finite harvested slice is expressible as empty-body ground rules;
  the infinite family is not a finite program. Stage 2's registry
  rows already carry the finite-slice gap.
* rdfs6, rdfs10, eq-ref (reflexivity rows): these ARE definite Horn —
  inside the class — but deliberately excluded by the native engines
  (`RDFS/Closure.lean`, `RDFS/RDFSPlus.lean` module headers), so the
  exhibited programs exclude them too, for agreement.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.Datalog
import L4Factoidal.RDFS.RDFSPlus

namespace L4Factoidal.Unified

open L4Factoidal.RDF (Triple Subject Term WfIri BNodeId Graph)

/-! ## The term encoding -/

/-- An IRI as a Datalog constant: tag `i`, then a colon, then the IRI
string. The colon at position 1 meets the class's constant
discipline for every IRI. -/
def encIri (x : WfIri) : String :=
  String.ofList ('i' :: ':' :: x.val.toList)

/-- A blank-node label as a Datalog constant: tag `b`. -/
def encBnode (b : BNodeId) : String :=
  String.ofList ('b' :: ':' :: b.toList)

def encSubj : Subject → String
  | .iri x => encIri x
  | .bnode b => encBnode b

/-- Total on `Term`; the literal / triple-term branches are
placeholders — the agreement theorems carry the ρdf model-fragment
hypothesis under which they never occur (module header). -/
def encObj : Term → String
  | .iri x => encIri x
  | .bnode b => encBnode b
  | .literal _ => String.ofList ['l', ':']
  | .tripleTerm _ _ _ => String.ofList ['t', ':']

theorem encIri_toList (x : WfIri) :
    (encIri x).toList = 'i' :: ':' :: x.val.toList := by simp [encIri]

theorem encBnode_toList (b : BNodeId) :
    (encBnode b).toList = 'b' :: ':' :: b.toList := by simp [encBnode]

theorem encIri_inj {x y : WfIri} (h : encIri x = encIri y) : x = y := by
  have h2 := congrArg String.toList h
  rw [encIri_toList, encIri_toList] at h2
  injection h2 with _ h2
  injection h2 with _ h2
  exact Subtype.ext (String.toList_inj.mp h2)

theorem encBnode_inj {a b : BNodeId} (h : encBnode a = encBnode b) : a = b := by
  have h2 := congrArg String.toList h
  rw [encBnode_toList, encBnode_toList] at h2
  injection h2 with _ h2
  injection h2 with _ h2
  exact String.toList_inj.mp h2

theorem encIri_ne_encBnode (x : WfIri) (b : BNodeId) :
    encIri x ≠ encBnode b := by
  intro h
  have h2 := congrArg String.toList h
  rw [encIri_toList, encBnode_toList] at h2
  injection h2 with h2 _
  exact absurd h2 (by decide)

theorem encSubj_inj {s t : Subject} (h : encSubj s = encSubj t) : s = t := by
  cases s with
  | iri x =>
      cases t with
      | iri y => exact congrArg Subject.iri (encIri_inj h)
      | bnode b => exact absurd h (encIri_ne_encBnode _ _)
  | bnode a =>
      cases t with
      | iri y => exact absurd h.symm (encIri_ne_encBnode _ _)
      | bnode b => exact congrArg Subject.bnode (encBnode_inj h)

theorem encSubj_eq_encIri {s : Subject} {p : WfIri}
    (h : encSubj s = encIri p) : s = .iri p := by
  cases s with
  | iri x => exact congrArg Subject.iri (encIri_inj h)
  | bnode b => exact absurd h.symm (encIri_ne_encBnode _ _)

theorem encObj_subjTerm (s : Subject) :
    encObj (RDF.subjTerm s) = encSubj s := by
  cases s <;> rfl

theorem encObj_eq_encSubj {t : Term} (ht : RDF.RhoDfModelObjectOk t)
    {s : Subject} (h : encObj t = encSubj s) : t = RDF.subjTerm s := by
  cases t with
  | iri x =>
      cases s with
      | iri y => exact congrArg Term.iri (encIri_inj h)
      | bnode b => exact absurd h (encIri_ne_encBnode _ _)
  | bnode a =>
      cases s with
      | iri y => exact absurd h.symm (encIri_ne_encBnode _ _)
      | bnode b => exact congrArg Term.bnode (encBnode_inj h)
  | literal l => exact absurd ht (by simp [RDF.RhoDfModelObjectOk])
  | tripleTerm a b c => exact absurd ht (by simp [RDF.RhoDfModelObjectOk])

theorem encObj_eq_encIri {t : Term} (ht : RDF.RhoDfModelObjectOk t)
    {p : WfIri} (h : encObj t = encIri p) : t = .iri p := by
  have := encObj_eq_encSubj ht (s := .iri p) h
  simpa [RDF.subjTerm] using this

theorem encObj_inj_ok {t u : Term} (ht : RDF.RhoDfModelObjectOk t)
    (hu : RDF.RhoDfModelObjectOk u) (h : encObj t = encObj u) : t = u := by
  cases u with
  | iri x => exact encObj_eq_encIri ht h
  | bnode b =>
      have := encObj_eq_encSubj ht (s := .bnode b) h
      simpa [RDF.subjTerm] using this
  | literal l => exact absurd hu (by simp [RDF.RhoDfModelObjectOk])
  | tripleTerm a b c => exact absurd hu (by simp [RDF.RhoDfModelObjectOk])

/-! ## Triples as ground atoms -/

/-- One triple as one ground atom: the predicate constant in operator
position, subject and object as arguments — the same operator-position
reading as `tripleAtom` (`Unified/RdfEmbed.lean`), at the Datalog
level. -/
def tripleFact (t : Triple) : DAtom :=
  ⟨.c (encIri t.p), [.c (encSubj t.s), .c (encObj t.o)]⟩

def graphFacts (g : Graph) : List DAtom := g.map tripleFact

theorem tripleFact_ground (t : Triple) : (tripleFact t).groundB = true := rfl

theorem graphFacts_ground (g : Graph) :
    ∀ b ∈ graphFacts g, b.groundB = true := by
  intro b hb
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
  exact tripleFact_ground t

/-- Triple facts carry no `DTerm.lit`: every position of `tripleFact`
is the STRING encoding of an RDF term, so the Herbrand-universe
hypothesis of `datalog_lfp_complete` is discharged by computation. -/
theorem tripleFact_litFree (t : Triple) : (tripleFact t).litFreeB = true := rfl

theorem graphFacts_litFree (g : Graph) :
    ∀ b ∈ graphFacts g, b.litFreeB = true := by
  intro b hb
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
  exact tripleFact_litFree t

theorem tripleFact_inj {t u : Triple} (ht : RDF.RhoDfModelObjectOk t.o)
    (hu : RDF.RhoDfModelObjectOk u.o) (h : tripleFact t = tripleFact u) :
    t = u := by
  cases t with
  | mk ts tp to =>
      cases u with
      | mk us up uo =>
          simp only [tripleFact, DAtom.mk.injEq, DTerm.c.injEq,
                     List.cons.injEq, and_true] at h
          obtain ⟨hp, hs, ho⟩ := h
          rw [Triple.mk.injEq]
          exact ⟨encSubj_inj hs, encIri_inj hp, encObj_inj_ok ht hu ho⟩

/-! ## The ρdf program — the six rows of `RDFS/RdfsCore.lean`, as
Datalog rules mirroring the DIAGONAL specification relations -/

def cRdfType : DTerm := .c (encIri RDFS.rdfType)
def cDomain : DTerm := .c (encIri RDFS.rdfsDomain)
def cRange : DTerm := .c (encIri RDFS.rdfsRange)
def cSco : DTerm := .c (encIri RDFS.rdfsSubClassOf)
def cSpo : DTerm := .c (encIri RDFS.rdfsSubPropertyOf)

/-- A binary atom in the triple reading. -/
def tAtom (p s o : DTerm) : DAtom := ⟨p, [s, o]⟩

def ruleRdfs2 : DRule :=
  ⟨tAtom cRdfType (.v "x") (.v "c"),
   [tAtom cDomain (.v "p") (.v "c"), tAtom (.v "p") (.v "x") (.v "y")]⟩

def ruleRdfs3 : DRule :=
  ⟨tAtom cRdfType (.v "y") (.v "c"),
   [tAtom cRange (.v "p") (.v "c"), tAtom (.v "p") (.v "x") (.v "y")]⟩

def ruleRdfs5 : DRule :=
  ⟨tAtom cSpo (.v "x") (.v "z"),
   [tAtom cSpo (.v "x") (.v "y"), tAtom cSpo (.v "y") (.v "z")]⟩

def ruleRdfs7 : DRule :=
  ⟨tAtom (.v "q") (.v "x") (.v "y"),
   [tAtom cSpo (.v "p") (.v "q"), tAtom (.v "p") (.v "x") (.v "y")]⟩

def ruleRdfs9 : DRule :=
  ⟨tAtom cRdfType (.v "x") (.v "b"),
   [tAtom cSco (.v "a") (.v "b"), tAtom cRdfType (.v "x") (.v "a")]⟩

def ruleRdfs11 : DRule :=
  ⟨tAtom cSco (.v "x") (.v "z"),
   [tAtom cSco (.v "x") (.v "y"), tAtom cSco (.v "y") (.v "z")]⟩

/-- **The ρdf closure as a Datalog program.** Definite Horn by
construction (the `by decide` discharges the class's `wf` gate). -/
def rhoDfProgram : DatalogProgram :=
  ⟨[ruleRdfs2, ruleRdfs3, ruleRdfs5, ruleRdfs7, ruleRdfs9, ruleRdfs11],
   by decide⟩

/-! ## Encode direction: the specification relation maps into the
program's derivations (unconditional — the Datalog rules are at least
as permissive as `RDFS.Derives`) -/

theorem derives_to_datalog {g : Graph} {t : Triple}
    (h : RDFS.Derives g t) :
    rhoDfProgram.Derives (graphFacts g) (tripleFact t) := by
  induction h with
  | base hm =>
      exact DatalogProgram.Derives.fact (List.mem_map.mpr ⟨_, hm, rfl⟩)
  | @rdfs2 p cls s o hdecl hdata ih1 ih2 =>
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs2 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "p" then encIri p else if n = "c" then encObj cls
                  else if n = "x" then encSubj s else encObj o)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cDomain,
                   encSubj] using ih1
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   encSubj] using ih2
          cases hbm)
      simpa [ruleRdfs2, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             cRdfType, encSubj] using hrule
  | @rdfs3 p cls s o osub hdecl hdata hsub ih1 ih2 =>
      have hos : encObj o = encSubj osub := by
        rw [← RDF.subjTerm_of_toSubject? hsub]
        exact encObj_subjTerm osub
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs3 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "p" then encIri p else if n = "c" then encObj cls
                  else if n = "x" then encSubj s else encObj o)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cRange,
                   encSubj] using ih1
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   encSubj] using ih2
          cases hbm)
      simpa [ruleRdfs3, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             cRdfType, hos] using hrule
  | @rdfs5 a b bsub c h1 hsub h2 ih1 ih2 =>
      have hbs : encObj b = encSubj bsub := by
        rw [← RDF.subjTerm_of_toSubject? hsub]
        exact encObj_subjTerm bsub
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs5 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "x" then encSubj a else if n = "y" then encObj b
                  else encObj c)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSpo,
                   encSubj] using ih1
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSpo,
                   hbs] using ih2
          cases hbm)
      simpa [ruleRdfs5, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             cSpo] using hrule
  | @rdfs7 p q s o hdecl hdata ih1 ih2 =>
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs7 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "p" then encIri p else if n = "q" then encIri q
                  else if n = "x" then encSubj s else encObj o)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSpo,
                   encSubj, encObj] using ih1
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   encSubj] using ih2
          cases hbm)
      simpa [ruleRdfs7, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             encSubj] using hrule
  | @rdfs9 s a b hdata hdecl ih1 ih2 =>
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs9 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "a" then encIri a else if n = "b" then encObj b
                  else encSubj s)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSco,
                   encSubj] using ih2
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cRdfType, encSubj, encObj] using ih1
          cases hbm)
      simpa [ruleRdfs9, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             cRdfType] using hrule
  | @rdfs11 a b bsub c h1 hsub h2 ih1 ih2 =>
      have hbs : encObj b = encSubj bsub := by
        rw [← RDF.subjTerm_of_toSubject? hsub]
        exact encObj_subjTerm bsub
      have hrule := DatalogProgram.Derives.rule (p := rhoDfProgram)
        (facts := graphFacts g)
        (show ruleRdfs11 ∈ rhoDfProgram.rules by simp [rhoDfProgram])
        (fun n => if n = "x" then encSubj a else if n = "y" then encObj b
                  else encObj c)
        (by
          intro bAtom hbm
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSco,
                   encSubj] using ih1
          rcases List.mem_cons.mp hbm with rfl | hbm
          · simpa [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSco,
                   hbs] using ih2
          cases hbm)
      simpa [ruleRdfs11, tAtom, DAtom.subst, DTerm.subst, tripleFact,
             cSco] using hrule

/-! ## Decode direction: every program derivation lands inside a
ρdf-CLOSED engine closure (via the diagonal specification relations,
which is what `RhoDfClosed` is stated over) -/

theorem datalog_derives_mem_closure {g : Graph} {m : Nat}
    (hcl : RDF.RhoDfClosed (RDFS.closure g m))
    (hf : RDF.RhoDfModelFragGraph (RDFS.closure g m))
    {a : DAtom} (h : rhoDfProgram.Derives (graphFacts g) a) :
    ∃ t : Triple, a = tripleFact t ∧ t ∈ RDFS.closure g m := by
  induction h with
  | fact ha =>
      obtain ⟨t, htg, rfl⟩ := List.mem_map.mp ha
      exact ⟨t, rfl, RDFS.closure_extensive m g htg⟩
  | @rule r hr θ hb ih =>
      have hr6 : r = ruleRdfs2 ∨ r = ruleRdfs3 ∨ r = ruleRdfs5 ∨
          r = ruleRdfs7 ∨ r = ruleRdfs9 ∨ r = ruleRdfs11 := by
        simpa [rhoDfProgram] using hr
      rcases hr6 with rfl | rfl | rfl | rfl | rfl | rfl
      · -- rdfs2
        obtain ⟨d, hd, hdmem⟩ := ih _ (show tAtom cDomain (.v "p") (.v "c")
          ∈ ruleRdfs2.body by simp [ruleRdfs2])
        obtain ⟨u, hu, humem⟩ := ih _ (show tAtom (.v "p") (.v "x") (.v "y")
          ∈ ruleRdfs2.body by simp [ruleRdfs2])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cDomain,
                   List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at hd hu
        obtain ⟨hdp, hds, hdo⟩ := hd
        obtain ⟨hup, hus, huo⟩ := hu
        have hmem : (⟨u.s, RDFS.rdfType, d.o⟩ : Triple) ∈ RDFS.closure g m :=
          hcl.1 _ ⟨d, hdmem, u, humem, u.p, (encIri_inj hdp).symm,
                   encSubj_eq_encIri (hds.symm.trans hup), rfl, rfl⟩
        refine ⟨⟨u.s, RDFS.rdfType, d.o⟩, ?_, hmem⟩
        simp only [ruleRdfs2, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cRdfType, List.map_cons, List.map_nil]
        rw [hus, hdo]
      · -- rdfs3
        obtain ⟨d, hd, hdmem⟩ := ih _ (show tAtom cRange (.v "p") (.v "c")
          ∈ ruleRdfs3.body by simp [ruleRdfs3])
        obtain ⟨u, hu, humem⟩ := ih _ (show tAtom (.v "p") (.v "x") (.v "y")
          ∈ ruleRdfs3.body by simp [ruleRdfs3])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cRange,
                   List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at hd hu
        obtain ⟨hdp, hds, hdo⟩ := hd
        obtain ⟨hup, hus, huo⟩ := hu
        obtain ⟨osub, hos⟩ := RDF.objectOk_to_subject (hf u humem).1
        have hmem : (⟨osub, RDFS.rdfType, d.o⟩ : Triple) ∈ RDFS.closure g m :=
          hcl.2.1 _ ⟨d, hdmem, u, humem, u.p, osub, (encIri_inj hdp).symm,
                     encSubj_eq_encIri (hds.symm.trans hup), rfl, hos, rfl⟩
        refine ⟨⟨osub, RDFS.rdfType, d.o⟩, ?_, hmem⟩
        simp only [ruleRdfs3, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cRdfType, List.map_cons, List.map_nil]
        rw [huo, hdo, ← hos, encObj_subjTerm]
      · -- rdfs5
        obtain ⟨t1, h1, h1mem⟩ := ih _ (show tAtom cSpo (.v "x") (.v "y")
          ∈ ruleRdfs5.body by simp [ruleRdfs5])
        obtain ⟨t2, h2, h2mem⟩ := ih _ (show tAtom cSpo (.v "y") (.v "z")
          ∈ ruleRdfs5.body by simp [ruleRdfs5])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSpo,
                   List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at h1 h2
        obtain ⟨h1p, h1s, h1o⟩ := h1
        obtain ⟨h2p, h2s, h2o⟩ := h2
        have hlink : t1.o = RDF.subjTerm t2.s :=
          encObj_eq_encSubj (hf t1 h1mem).1 (h1o.symm.trans h2s)
        have hmem : (⟨t1.s, RDFS.rdfsSubPropertyOf, t2.o⟩ : Triple)
            ∈ RDFS.closure g m :=
          hcl.2.2.1 _ ⟨t1, h1mem, t2, h2mem, t2.s, (encIri_inj h1p).symm,
                       (encIri_inj h2p).symm, hlink.symm, rfl, rfl⟩
        refine ⟨⟨t1.s, RDFS.rdfsSubPropertyOf, t2.o⟩, ?_, hmem⟩
        simp only [ruleRdfs5, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cSpo, List.map_cons, List.map_nil]
        rw [h1s, h2o]
      · -- rdfs7
        obtain ⟨d, hd, hdmem⟩ := ih _ (show tAtom cSpo (.v "p") (.v "q")
          ∈ ruleRdfs7.body by simp [ruleRdfs7])
        obtain ⟨u, hu, humem⟩ := ih _ (show tAtom (.v "p") (.v "x") (.v "y")
          ∈ ruleRdfs7.body by simp [ruleRdfs7])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSpo,
                   List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at hd hu
        obtain ⟨hdp, hds, hdo⟩ := hd
        obtain ⟨hup, hus, huo⟩ := hu
        have hdp' : d.p = RDFS.rdfsSubPropertyOf := (encIri_inj hdp).symm
        obtain ⟨b, hb⟩ := (hf d hdmem).2 hdp'
        have hmem : (⟨u.s, b, u.o⟩ : Triple) ∈ RDFS.closure g m :=
          hcl.2.2.2.1 _ ⟨d, hdmem, u, humem, u.p, b, hdp',
                         encSubj_eq_encIri (hds.symm.trans hup), hb, rfl, rfl⟩
        refine ⟨⟨u.s, b, u.o⟩, ?_, hmem⟩
        simp only [ruleRdfs7, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   List.map_cons, List.map_nil]
        rw [hus, huo, hdo, hb]
        simp [encObj]
      · -- rdfs9
        obtain ⟨sub, hsubEq, hsubmem⟩ := ih _
          (show tAtom cSco (.v "a") (.v "b")
            ∈ ruleRdfs9.body by simp [ruleRdfs9])
        obtain ⟨typ, htypEq, htypmem⟩ := ih _
          (show tAtom cRdfType (.v "x") (.v "a")
            ∈ ruleRdfs9.body by simp [ruleRdfs9])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSco,
                   cRdfType, List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at hsubEq htypEq
        obtain ⟨hsp, hss, hso⟩ := hsubEq
        obtain ⟨htp, hts, hto⟩ := htypEq
        have hlink : typ.o = RDF.subjTerm sub.s :=
          encObj_eq_encSubj (hf typ htypmem).1 (hto.symm.trans hss)
        have hmem : (⟨typ.s, RDFS.rdfType, sub.o⟩ : Triple)
            ∈ RDFS.closure g m :=
          hcl.2.2.2.2.1 _ ⟨sub, hsubmem, typ, htypmem, sub.s,
                           (encIri_inj hsp).symm, rfl,
                           (encIri_inj htp).symm, hlink, rfl⟩
        refine ⟨⟨typ.s, RDFS.rdfType, sub.o⟩, ?_, hmem⟩
        simp only [ruleRdfs9, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cRdfType, List.map_cons, List.map_nil]
        rw [hts, hso]
      · -- rdfs11
        obtain ⟨t1, h1, h1mem⟩ := ih _ (show tAtom cSco (.v "x") (.v "y")
          ∈ ruleRdfs11.body by simp [ruleRdfs11])
        obtain ⟨t2, h2, h2mem⟩ := ih _ (show tAtom cSco (.v "y") (.v "z")
          ∈ ruleRdfs11.body by simp [ruleRdfs11])
        simp only [tAtom, DAtom.subst, DTerm.subst, tripleFact, cSco,
                   List.map_cons, List.map_nil, DAtom.mk.injEq,
                   DTerm.c.injEq, List.cons.injEq, and_true] at h1 h2
        obtain ⟨h1p, h1s, h1o⟩ := h1
        obtain ⟨h2p, h2s, h2o⟩ := h2
        have hlink : t1.o = RDF.subjTerm t2.s :=
          encObj_eq_encSubj (hf t1 h1mem).1 (h1o.symm.trans h2s)
        have hmem : (⟨t1.s, RDFS.rdfsSubClassOf, t2.o⟩ : Triple)
            ∈ RDFS.closure g m :=
          hcl.2.2.2.2.2 _ ⟨t1, h1mem, t2, h2mem, t2.s, (encIri_inj h1p).symm,
                           (encIri_inj h2p).symm, hlink.symm, rfl, rfl⟩
        refine ⟨⟨t1.s, RDFS.rdfsSubClassOf, t2.o⟩, ?_, hmem⟩
        simp only [ruleRdfs11, tAtom, DAtom.subst, DTerm.subst, tripleFact,
                   cSco, List.map_cons, List.map_nil]
        rw [h1s, h2o]

/-! ## The agreement theorem and its corollaries -/

/-- **ρdf engine / Datalog agreement**, general graphs, membership
equality (stage 3 brief): under the stage 2 decided-corollary
hypotheses on the ENGINE side (closure ρdf-closed + in the model
fragment) and fuel adequacy on the DATALOG side — each
`decide`-dischargeable — a fragment triple is in the engine's closure
exactly when its atom is in the program's least fixpoint. -/
theorem rhoDf_closure_datalog_agree (g : Graph) (n m : Nat)
    (hcl : RDF.rhoDfClosedCheck (RDFS.closure g m) = true)
    (hf : RDFS.isRhoDfFrag (RDFS.closure g m) = true)
    (hfa : rhoDfProgram.FuelAdequate (graphFacts g) n) :
    ∀ t : Triple, RDF.RhoDfModelObjectOk t.o →
      (tripleFact t ∈ rhoDfProgram.lfp (graphFacts g) n ↔
        t ∈ RDFS.closure g m) := by
  intro t hto
  constructor
  · intro hmem
    obtain ⟨u, hequ, humem⟩ := datalog_derives_mem_closure
      (RDF.rhoDfClosed_of_check hcl) (RDF.rhoDfModelFrag_of_check hf)
      (rhoDfProgram.lfp_sound _ n hmem)
    have huo := ((RDF.rhoDfModelFrag_of_check hf) u humem).1
    rw [tripleFact_inj hto huo hequ]
    exact humem
  · intro hmem
    exact rhoDfProgram.derives_mem_lfp hfa
      (derives_to_datalog (RDFS.closure_sound m g hmem))

/-- Everything in the program's least fixpoint is the atom of an
engine-closure triple — the fixpoint contains no junk outside the
image of the encoding. -/
theorem rhoDf_lfp_image (g : Graph) (n m : Nat)
    (hcl : RDF.rhoDfClosedCheck (RDFS.closure g m) = true)
    (hf : RDFS.isRhoDfFrag (RDFS.closure g m) = true) :
    ∀ a ∈ rhoDfProgram.lfp (graphFacts g) n,
      ∃ t ∈ RDFS.closure g m, a = tripleFact t := by
  intro a ha
  obtain ⟨t, heq, hmem⟩ := datalog_derives_mem_closure
    (RDF.rhoDfClosed_of_check hcl) (RDF.rhoDfModelFrag_of_check hf)
    (rhoDfProgram.lfp_sound _ n ha)
  exact ⟨t, hmem, heq⟩

/-- **The ρdf engine as a fragment decider for the Datalog schema**
(design document §8.2, composed from the agreement theorem and the
stage 3 gate theorem): membership in the ENGINE's closure coincides
with CL entailment of the triple's atom-sentence from the
program-as-schema plus the graph's facts. Claim level: ground-atomic
consequences, on the ρdf model fragment. -/
theorem rhoDf_engine_iff_datalog_entails (g : Graph) (n m : Nat)
    (hcl : RDF.rhoDfClosedCheck (RDFS.closure g m) = true)
    (hf : RDFS.isRhoDfFrag (RDFS.closure g m) = true)
    (hfa : rhoDfProgram.FuelAdequate (graphFacts g) n)
    (t : Triple) (hto : RDF.RhoDfModelObjectOk t.o) :
    t ∈ RDFS.closure g m ↔
      EntailsSchema condTrue rhoDfProgram.toSchema
        ((graphFacts g).map DAtom.sentence) (tripleFact t).sentence := by
  rw [← rhoDf_closure_datalog_agree g n m hcl hf hfa t hto]
  exact datalog_lfp_iff_entails rhoDfProgram (graphFacts_ground g)
    (by decide) (graphFacts_litFree g)
    (tripleFact_ground t) (tripleFact_litFree t) hfa

/-! ### A fully decided ρdf instance -/

private def dmA : WfIri := ⟨"http://rho.example/a", by decide⟩
private def dmC1 : WfIri := ⟨"http://rho.example/C1", by decide⟩
private def dmC2 : WfIri := ⟨"http://rho.example/C2", by decide⟩

def rhoDemoG : Graph :=
  [⟨.iri dmA, RDFS.rdfType, .iri dmC1⟩,
   ⟨.iri dmC1, RDFS.rdfsSubClassOf, .iri dmC2⟩]

/-- The agreement instance, all hypotheses discharged by `decide`. -/
theorem rhoDf_demo_agree :
    ∀ t : Triple, RDF.RhoDfModelObjectOk t.o →
      (tripleFact t ∈ rhoDfProgram.lfp (graphFacts rhoDemoG) 2 ↔
        t ∈ RDFS.closure rhoDemoG 3) :=
  rhoDf_closure_datalog_agree rhoDemoG 2 3 (by decide) (by decide)
    (rhoDfProgram.fuelAdequate_of_check (by decide))

/-- The rdfs9 consequence, through the composed corollary: the engine
result IS a CL-entailment verdict for the Datalog schema. -/
theorem rhoDf_demo_entails :
    EntailsSchema condTrue rhoDfProgram.toSchema
      ((graphFacts rhoDemoG).map DAtom.sentence)
      (tripleFact ⟨.iri dmA, RDFS.rdfType, .iri dmC2⟩).sentence :=
  (rhoDf_engine_iff_datalog_entails rhoDemoG 2 3 (by decide) (by decide)
    (rhoDfProgram.fuelAdequate_of_check (by decide))
    ⟨.iri dmA, RDFS.rdfType, .iri dmC2⟩ trivial).mp (by decide)

/-! ## The RDFS-Plus tier (`RDFS/RDFSPlus.lean`) as a Datalog program
— the RL closure's equality/property core -/

def cSameAs : DTerm := .c (encIri OWL.RL.owlSameAs)
def cInvOf : DTerm := .c (encIri OWL.RL.owlInverseOf)
def cSymP : DTerm := .c (encIri OWL.RL.owlSymmetricProperty)
def cTrP : DTerm := .c (encIri OWL.RL.owlTransitiveProperty)
def cFP : DTerm := .c (encIri OWL.RL.owlFunctionalProperty)
def cIFP : DTerm := .c (encIri OWL.RL.owlInverseFunctionalProperty)
def cEqC : DTerm := .c (encIri OWL.RL.owlEquivalentClass)
def cEqP : DTerm := .c (encIri OWL.RL.owlEquivalentProperty)

/-- The 13 OWL rows of the tier plus the four schema-level inverseOf
domain/range flips, as Datalog rules (row ids in comments follow
`OWL/RLClosure.lean`). -/
def rdfsPlusOwlRules : List DRule :=
  [-- cax-eqc1 / cax-eqc2
   ⟨tAtom cRdfType (.v "x") (.v "d"),
    [tAtom cEqC (.v "c") (.v "d"), tAtom cRdfType (.v "x") (.v "c")]⟩,
   ⟨tAtom cRdfType (.v "x") (.v "c"),
    [tAtom cEqC (.v "c") (.v "d"), tAtom cRdfType (.v "x") (.v "d")]⟩,
   -- prp-eqp1 / prp-eqp2
   ⟨tAtom (.v "q") (.v "x") (.v "y"),
    [tAtom cEqP (.v "p") (.v "q"), tAtom (.v "p") (.v "x") (.v "y")]⟩,
   ⟨tAtom (.v "p") (.v "x") (.v "y"),
    [tAtom cEqP (.v "p") (.v "q"), tAtom (.v "q") (.v "x") (.v "y")]⟩,
   -- prp-symp
   ⟨tAtom (.v "p") (.v "y") (.v "x"),
    [tAtom cRdfType (.v "p") cSymP, tAtom (.v "p") (.v "x") (.v "y")]⟩,
   -- prp-trp
   ⟨tAtom (.v "p") (.v "x") (.v "z"),
    [tAtom cRdfType (.v "p") cTrP, tAtom (.v "p") (.v "x") (.v "y"),
     tAtom (.v "p") (.v "y") (.v "z")]⟩,
   -- prp-inv1 / prp-inv2
   ⟨tAtom (.v "q") (.v "y") (.v "x"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom (.v "p") (.v "x") (.v "y")]⟩,
   ⟨tAtom (.v "p") (.v "y") (.v "x"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom (.v "q") (.v "x") (.v "y")]⟩,
   -- inverseOf domain/range flip (schema-level; `OWL/RLClosure.lean`
   -- `inverseOfDomRngFlipFor`, four directions)
   ⟨tAtom cRange (.v "q") (.v "c"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom cDomain (.v "p") (.v "c")]⟩,
   ⟨tAtom cDomain (.v "q") (.v "c"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom cRange (.v "p") (.v "c")]⟩,
   ⟨tAtom cRange (.v "p") (.v "c"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom cDomain (.v "q") (.v "c")]⟩,
   ⟨tAtom cDomain (.v "p") (.v "c"),
    [tAtom cInvOf (.v "p") (.v "q"), tAtom cRange (.v "q") (.v "c")]⟩,
   -- prp-fp / prp-ifp
   ⟨tAtom cSameAs (.v "y1") (.v "y2"),
    [tAtom cRdfType (.v "p") cFP, tAtom (.v "p") (.v "x") (.v "y1"),
     tAtom (.v "p") (.v "x") (.v "y2")]⟩,
   ⟨tAtom cSameAs (.v "x1") (.v "x2"),
    [tAtom cRdfType (.v "p") cIFP, tAtom (.v "p") (.v "x1") (.v "y"),
     tAtom (.v "p") (.v "x2") (.v "y")]⟩,
   -- eq-sym / eq-trans
   ⟨tAtom cSameAs (.v "y") (.v "x"), [tAtom cSameAs (.v "x") (.v "y")]⟩,
   ⟨tAtom cSameAs (.v "x") (.v "z"),
    [tAtom cSameAs (.v "x") (.v "y"), tAtom cSameAs (.v "y") (.v "z")]⟩,
   -- eq-rep-s / eq-rep-o / eq-rep-p
   ⟨tAtom (.v "p") (.v "s2") (.v "o"),
    [tAtom cSameAs (.v "s") (.v "s2"), tAtom (.v "p") (.v "s") (.v "o")]⟩,
   ⟨tAtom (.v "p") (.v "s") (.v "o2"),
    [tAtom cSameAs (.v "o") (.v "o2"), tAtom (.v "p") (.v "s") (.v "o")]⟩,
   ⟨tAtom (.v "p2") (.v "s") (.v "o"),
    [tAtom cSameAs (.v "p") (.v "p2"), tAtom (.v "p") (.v "s") (.v "o")]⟩]

/-- **The RDFS-Plus closure as a Datalog program**: the six ρdf rows
plus the tier's OWL rows. Definite Horn by construction. -/
def rdfsPlusProgram : DatalogProgram :=
  ⟨[ruleRdfs2, ruleRdfs3, ruleRdfs5, ruleRdfs7, ruleRdfs9, ruleRdfs11]
     ++ rdfsPlusOwlRules,
   by decide⟩

/-! ### Instance-level agreement with `rdfsPlusClosureFix`, on the
demo shapes `RDFS/RDFSPlus.lean` pins (module header records why the
general bridging is not claimed for this tier) -/

private theorem plusIri (s : String) : RDF.isIri ("http://e/" ++ s) = true := by
  simp [RDF.isIri, String.isEmpty]

private def pi (s : String) : WfIri := ⟨"http://e/" ++ s, plusIri s⟩
private def ps (s : String) : Subject := .iri (pi s)
private def pt (s : String) : Term := .iri (pi s)

def plusDemoSameAs : Graph :=
  [⟨ps "a", OWL.RL.owlSameAs, pt "b"⟩, ⟨ps "a", pi "p", pt "v"⟩]

def plusDemoTrp : Graph :=
  [⟨ps "r", RDFS.rdfType, .iri OWL.RL.owlTransitiveProperty⟩,
   ⟨ps "a", pi "r", pt "b"⟩, ⟨ps "b", pi "r", pt "c"⟩]

def plusDemoInv : Graph :=
  [⟨ps "parent", OWL.RL.owlInverseOf, pt "child"⟩,
   ⟨ps "parent", RDFS.rdfsDomain, pt "Person"⟩,
   ⟨ps "x", pi "parent", pt "y"⟩]

set_option maxHeartbeats 2000000 in
/-- Membership equality on the TransitiveProperty demo, both
directions, decided as a THEOREM: every engine-closure triple's atom
is in the program's fixpoint, and every fixpoint atom is an
engine-closure triple's. The engine side is `rdfsPlusClosure _ 6`
rather than `rdfsPlusClosureFix` to keep the kernel evaluation inside
budget; the engine's length-test loop stops AT the fixpoint, so at
saturating fuel the two hold the same triples — the `#guard`s below
pin that one more engine round adds nothing at fuel 6.

The sameAs and inverseOf demos carry the SAME membership equality as
build-time `#guard`s (native evaluation) rather than `decide`d
theorems: their sameAs-substitution closures make the kernel-level
fixpoint evaluation exceed any reasonable heartbeat budget (the
kernel re-evaluates each unshared round), while the compiled check is
immediate. Strength labelled accordingly in the registry. -/
theorem rdfsPlus_demo_trp_agree :
    (∀ t ∈ RDFS.rdfsPlusClosure plusDemoTrp 6,
       tripleFact t ∈ rdfsPlusProgram.lfp (graphFacts plusDemoTrp) 4) ∧
    (∀ a ∈ rdfsPlusProgram.lfp (graphFacts plusDemoTrp) 4,
       ∃ t ∈ RDFS.rdfsPlusClosure plusDemoTrp 6, a = tripleFact t) := by
  decide

/-- The sameAs / inverseOf membership-equality pins (native
evaluation; see `rdfsPlus_demo_trp_agree`'s docstring). -/
def rdfsPlusDemoAgrees (g : Graph) (engineFuel lfpFuel : Nat) : Bool :=
  (RDFS.rdfsPlusClosure g engineFuel).all
    (fun t => decide (tripleFact t ∈ rdfsPlusProgram.lfp (graphFacts g) lfpFuel))
  && (rdfsPlusProgram.lfp (graphFacts g) lfpFuel).all
    (fun a => (RDFS.rdfsPlusClosure g engineFuel).any
      (fun t => decide (tripleFact t = a)))

#guard rdfsPlusDemoAgrees plusDemoSameAs 6 4
#guard rdfsPlusDemoAgrees plusDemoInv 6 4

set_option maxHeartbeats 2000000 in
/-- The generic gate theorem instantiated at the tier: on the
TransitiveProperty demo, the engine-agreed fixpoint decides CL
entailment from the tier's schema — `a r c` follows from prp-trp. -/
theorem rdfsPlus_demo_entails :
    EntailsSchema condTrue rdfsPlusProgram.toSchema
      ((graphFacts plusDemoTrp).map DAtom.sentence)
      (tripleFact ⟨ps "a", pi "r", pt "c"⟩).sentence :=
  (datalog_lfp_iff_entails rdfsPlusProgram (fuel := 4)
    (graphFacts_ground plusDemoTrp) (by decide) (graphFacts_litFree _)
    (tripleFact_ground _) (tripleFact_litFree _)
    (rdfsPlusProgram.fuelAdequate_of_check (by decide))).mp (by decide)

/-! ## The boundary, pinned -/

/-- The rdfD1 SHAPE — a fresh variable in the head (`"w"` stands for
the minted surrogate blank node; it occurs in no body atom). -/
def rdfD1Shape : DRule :=
  ⟨tAtom cRdfType (.v "w") (.v "d"),
   [tAtom (.v "p") (.v "x") (.v "d")]⟩

/-- Witness-minting rules are REJECTED by the class gate: the shape
fails `wfB` (definiteness), so no `DatalogProgram` can contain it —
the design document §5.6 exclusion, machine-checked. -/
theorem rdfD1Shape_not_wf : rdfD1Shape.wfB = false := by decide

section Checks

/- The ρdf demo: engine hypotheses and Datalog saturation all hold
computationally, the derived triple is on both sides, and the two
sides disagree nowhere on the fragment (pinned for the derived
triple and a non-member). -/

#guard RDF.rhoDfClosedCheck (RDFS.closure rhoDemoG 3)
#guard RDFS.isRhoDfFrag (RDFS.closure rhoDemoG 3)
#guard rhoDfProgram.saturatedCheck (graphFacts rhoDemoG) 2
#guard decide (tripleFact ⟨.iri dmA, RDFS.rdfType, .iri dmC2⟩
  ∈ rhoDfProgram.lfp (graphFacts rhoDemoG) 2)
#guard decide ((⟨.iri dmA, RDFS.rdfType, .iri dmC2⟩ : Triple)
  ∈ RDFS.closure rhoDemoG 3)
#guard !decide (tripleFact ⟨.iri dmC2, RDFS.rdfType, .iri dmA⟩
  ∈ rhoDfProgram.lfp (graphFacts rhoDemoG) 2)

/- The RDFS-Plus demos saturate at the chosen fuel. -/

#guard rdfsPlusProgram.saturatedCheck (graphFacts plusDemoSameAs) 4
#guard rdfsPlusProgram.saturatedCheck (graphFacts plusDemoTrp) 4
#guard rdfsPlusProgram.saturatedCheck (graphFacts plusDemoInv) 4

/- The engine closures saturate within the fuel the agreement
theorems use: one more engine round adds nothing at fuel 6, so
`rdfsPlusClosure _ 6` holds the same triples as `rdfsPlusClosureFix`
(the loop stops at the fixpoint). -/

#guard (RDFS.rdfsPlusStep (RDFS.rdfsPlusClosure plusDemoSameAs 6)).length
  == (RDFS.rdfsPlusClosure plusDemoSameAs 6).length
#guard (RDFS.rdfsPlusStep (RDFS.rdfsPlusClosure plusDemoTrp 6)).length
  == (RDFS.rdfsPlusClosure plusDemoTrp 6).length
#guard (RDFS.rdfsPlusStep (RDFS.rdfsPlusClosure plusDemoInv 6)).length
  == (RDFS.rdfsPlusClosure plusDemoInv 6).length

/- eq-ref stays excluded on the Datalog side exactly as the engine
excludes it (`RDFS/RDFSPlus.lean`): a node with NO `owl:sameAs`
statement gets no reflexive sameAs triple. (On sameAs-connected nodes
BOTH sides derive the reflexive triple through eq-sym + eq-trans;
that is rule interplay, not the excluded eq-ref row.) -/

#guard !decide (tripleFact ⟨ps "a", OWL.RL.owlSameAs, RDF.subjTerm (ps "a")⟩
  ∈ rdfsPlusProgram.lfp (graphFacts plusDemoTrp) 4)

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound`. -/

#print axioms encIri_inj
#print axioms tripleFact_inj
#print axioms derives_to_datalog
#print axioms datalog_derives_mem_closure
#print axioms rhoDf_closure_datalog_agree
#print axioms rhoDf_lfp_image
#print axioms rhoDf_engine_iff_datalog_entails
#print axioms rhoDf_demo_agree
#print axioms rhoDf_demo_entails
#print axioms rdfsPlus_demo_trp_agree
#print axioms rdfsPlus_demo_entails
#print axioms rdfD1Shape_not_wf

end Checks

end L4Factoidal.Unified
