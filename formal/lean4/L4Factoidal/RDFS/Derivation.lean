/-
L4Factoidal.RDFS.Derivation — the RDFS closure as a PROOF-CARRYING
answer: `fullClosureWithProof` returns the same graph `fullClosure`
returns, together with a derivation witness that names, for every
triple of the closure, the RDF 1.1 Semantics row that licensed it and
the earlier steps it was licensed from.

  https://www.w3.org/TR/rdf11-mt/#rdf-entailment    (§8)
  https://www.w3.org/TR/rdf11-mt/#rdfs-entailment   (§9)

Why a witness at all: `fullClosure_sound` (FullClosureTheorems.lean)
says every triple of the closure has a `DerivesFull` derivation, but
that derivation lives inside the proof and never reaches a caller. A
caller who does not trust this engine gets nothing it can inspect. A
`Derivation` is data: an array of `Step`s in topological order, each
naming a `RuleId` and the INDICES of the steps it uses as premises.
Every index is strictly less than the step's own index
(`fullClosureWithProof_premises_lt`), so one left-to-right pass
validates the whole array.

## The five theorems

* `fullClosureWithProof_graph` — the emitting entry point returns
  EXACTLY the graph `fullClosure` returns. Without this the witness
  could describe a graph the engine does not serve.
* `fullClosureWithProof_conclusions` — the step conclusions, read in
  order, ARE that graph. So the witness covers every triple, and
  covers nothing else.
* `fullClosureWithProof_sound` — every step's conclusion is
  `DerivesFull (axiomaticTriples D cmps) g`-derivable. Assembled from
  `fullClosure_sound`, through the conclusion equation; the per-row
  soundness lemmas of `FullClosureTheorems.lean` are what
  `fullClosure_sound` is built from and are not re-derived here.
* `fullClosureWithProof_premises_lt` — every premise index of step
  `i` is strictly less than `i`. No forward reference, no cycle, so a
  checker validates the array in one left-to-right pass and cannot be
  fooled by an out-of-range index.
* `fullClosureWithProof_wellTagged` — every step names its component
  (`rdfs`) and cites the Lean statement that backs its row. A step
  with a blank or defaulted assurance reference cannot occur.

## What the witness does NOT claim

`fullClosureWithProof_sound` is SOUNDNESS-ONLY, and it is a statement
about the CONCLUSION of each step, not about the pairing of a
conclusion with the `rule`/`premises` fields. The rule and premise
fields are correct by construction — each row annotator is the row
function of `FullClosure.lean` with the premise positions threaded
through it, and `annStepConclusions_conclusions` proves the annotated
rows emit exactly the conclusions the unannotated rows emit, row for
row — but "step i's rule really licenses step i's conclusion from
steps `premises`" is not itself a landed theorem. `DerivationTests.lean`
exhibits the pairing on concrete chains with `#guard`, four steps deep
on the empty graph and one step deep for every other row.

The other limit is what an `AssuranceRef` can say. `provedBy` cites a
per-row soundness lemma by name; the citation is DATA, not a proof
obligation Lean discharges, so a wrong name is caught by the `#guard`s
in `DerivationTests.lean` and by review, not by the kernel. `base` and
`axiomatic` have no lemma beyond their `DerivesFull` constructor and
say so with `constructorOnly`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.FullClosureTheorems

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

-- The row lemmas below share one rewrite set across every branch of a
-- row's match; not every branch needs every lemma of it.
set_option linter.unusedSimpArgs false

/-! ## Step data -/

/-- Which RDF 1.1 Semantics row licensed a step. One constructor per
`DerivesFull` constructor, so the correspondence is total: a step can
name no rule the relation does not have, and every relation
constructor has a name a step can carry. -/
inductive RuleId where
  /-- `DerivesFull.base` — the triple is in the input graph. -/
  | base
  /-- `DerivesFull.axiomatic` — §8.2 / §9.3 / rdfs1 over D. -/
  | axiomatic
  /-- §8.1 rdfD2. -/
  | rdfD2
  /-- §9.2 rdfs2. -/
  | rdfs2
  /-- §9.2 rdfs3. -/
  | rdfs3
  /-- §9.2 rdfs4a. -/
  | rdfs4a
  /-- §9.2 rdfs4b. -/
  | rdfs4b
  /-- §9.2 rdfs5. -/
  | rdfs5
  /-- §9.2 rdfs6. -/
  | rdfs6
  /-- §9.2 rdfs7. -/
  | rdfs7
  /-- §9.2 rdfs8. -/
  | rdfs8
  /-- §9.2 rdfs9. -/
  | rdfs9
  /-- §9.2 rdfs10. -/
  | rdfs10
  /-- §9.2 rdfs11. -/
  | rdfs11
  /-- §9.2 rdfs12. -/
  | rdfs12
  /-- §9.2 rdfs13. -/
  | rdfs13
  deriving DecidableEq, Repr, Inhabited

/-- Which part of Factoidal licensed a step. Every step this module
emits is `rdfs`; the other members exist so a later stage can put its
own steps into the SAME list rather than replacing the type. Nothing
in this module builds a step with any other tag. -/
inductive Component where
  /-- RDF 1.1 Semantics §8 — the RDF rules and axiomatic triples. -/
  | rdf
  /-- RDF 1.1 Semantics §9 — the RDFS rules and axiomatic triples. -/
  | rdfs
  /-- OWL 2 RL rules. -/
  | owlRl
  /-- SPARQL 1.1 algebra and evaluation. -/
  | sparql
  /-- XML 1.0 / Namespaces. -/
  | xml
  /-- RIF Core. -/
  | rif
  deriving DecidableEq, Repr, Inhabited

/-- WHICH proved Lean statement backs a step's rule row. A reader can
then tell a step backed by a discharged soundness theorem from one
backed only by a constructor of the derivation relation — the two are
different constructors here, never a present-versus-absent field. -/
inductive AssuranceRef where
  /-- A landed theorem licenses this row: its fully-qualified Lean
  name, and the module the theorem is in. -/
  | provedBy (theoremName : String) (module : String)
  /-- No separate soundness theorem: the row IS a constructor of
  `DerivesFull`, and that constructor is the whole licence. -/
  | constructorOnly (constructorName : String) (module : String)
  deriving DecidableEq, Repr, Inhabited

/-- The Lean statement that backs each row.

The eight single-premise rows and the six rdfs-core join rows each
have a per-row soundness lemma, already landed and already used by
`fullClosure_sound`; those are cited with `provedBy`. `base` and
`axiomatic` have no lemma beyond the `DerivesFull` constructor that
states them, and are cited with `constructorOnly` — recorded in the
data, not left blank. -/
def RuleId.assurance : RuleId → AssuranceRef
  | .base => .constructorOnly "L4Factoidal.RDFS.DerivesFull.base"
      "L4Factoidal.RDFS.FullClosure"
  | .axiomatic => .constructorOnly "L4Factoidal.RDFS.DerivesFull.axiomatic"
      "L4Factoidal.RDFS.FullClosure"
  | .rdfD2 => .provedBy "L4Factoidal.RDFS.rdfD2For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs2 => .provedBy "L4Factoidal.RDFS.rdfs2For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs3 => .provedBy "L4Factoidal.RDFS.rdfs3For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs4a => .provedBy "L4Factoidal.RDFS.rdfs4aFor_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs4b => .provedBy "L4Factoidal.RDFS.rdfs4bFor_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs5 => .provedBy "L4Factoidal.RDFS.rdfs5For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs6 => .provedBy "L4Factoidal.RDFS.rdfs6For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs7 => .provedBy "L4Factoidal.RDFS.rdfs7For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs8 => .provedBy "L4Factoidal.RDFS.rdfs8For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs9 => .provedBy "L4Factoidal.RDFS.rdfs9For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs10 => .provedBy "L4Factoidal.RDFS.rdfs10For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs11 => .provedBy "L4Factoidal.RDFS.rdfs11For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"
  | .rdfs12 => .provedBy "L4Factoidal.RDFS.rdfs12For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems"
  | .rdfs13 => .provedBy "L4Factoidal.RDFS.rdfs13For_sound"
      "L4Factoidal.RDFS.ClosureTheorems"

/-- The spec's own row name, for a human reading a witness. -/
def RuleId.name : RuleId → String
  | .base => "base"          | .axiomatic => "axiomatic"
  | .rdfD2 => "rdfD2"        | .rdfs2 => "rdfs2"
  | .rdfs3 => "rdfs3"        | .rdfs4a => "rdfs4a"
  | .rdfs4b => "rdfs4b"      | .rdfs5 => "rdfs5"
  | .rdfs6 => "rdfs6"        | .rdfs7 => "rdfs7"
  | .rdfs8 => "rdfs8"        | .rdfs9 => "rdfs9"
  | .rdfs10 => "rdfs10"      | .rdfs11 => "rdfs11"
  | .rdfs12 => "rdfs12"      | .rdfs13 => "rdfs13"

/-- One derivation step. `premises` are INDICES into the steps that
PRECEDE this one (proved: `fullClosureWithProof_premises_lt`), so the
array is a DAG in topological order and a checker validates it in one
left-to-right pass with no forward references and no cycles. -/
structure Step where
  /-- The §8/§9 row that licensed `conclusion`. -/
  rule : RuleId
  /-- Which part of Factoidal the row belongs to. Always `.rdfs` in
  this module; the field exists so a later stage can add steps from
  another component to the same derivation. -/
  component : Component
  /-- The proved Lean statement that backs `rule`. -/
  assurance : AssuranceRef
  /-- The triple this step derives. -/
  conclusion : Triple
  /-- Indices of the premise steps, in the row's own premise order. -/
  premises : List Nat
  deriving DecidableEq, Repr

/-- Build a step for an RDFS row, tagging it with the component and
with the Lean statement that backs the row. Every step in this module
goes through here, so no step can carry a blank assurance. -/
def mkStep (r : RuleId) (t : Triple) (prem : List Nat) : Step :=
  { rule := r, component := .rdfs, assurance := r.assurance,
    conclusion := t, premises := prem }

@[simp] theorem mkStep_conclusion (r : RuleId) (t : Triple) (prem : List Nat) :
    (mkStep r t prem).conclusion = t := rfl

@[simp] theorem mkStep_premises (r : RuleId) (t : Triple) (prem : List Nat) :
    (mkStep r t prem).premises = prem := rfl

/-- A step is well tagged when it names the component it came from and
cites the Lean statement its row is backed by. Every step this module
emits is well tagged (`fullClosureWithProof_wellTagged`), so no step
can reach a reader with a blank or defaulted assurance reference. -/
def WellTagged (a : Step) : Prop :=
  a.component = Component.rdfs ∧ a.assurance = a.rule.assurance

theorem mkStep_wellTagged (r : RuleId) (t : Triple) (prem : List Nat) :
    WellTagged (mkStep r t prem) := ⟨rfl, rfl⟩

/-- A derivation: steps in topological order. -/
abbrev Derivation := Array Step

/-! ## Indexed graphs

A row annotator needs the POSITION of each premise, not just the
triple. `indexFrom` pairs each triple of a graph with its position;
`indexFrom_map` says the pairing loses nothing. -/

/-- Pair every triple with its position, counting from `i`. -/
def indexFrom : Nat → Graph → List (Nat × Triple)
  | _, []      => []
  | i, t :: ts => (i, t) :: indexFrom (i + 1) ts

/-- Pair every triple with its position in the graph. -/
def indexed (g : Graph) : List (Nat × Triple) := indexFrom 0 g

theorem indexFrom_map (i : Nat) (g : Graph) : (indexFrom i g).map (·.2) = g := by
  induction g generalizing i with
  | nil => rfl
  | cons t ts ih => simp [indexFrom, ih (i + 1)]

@[simp] theorem indexed_map (g : Graph) : (indexed g).map (·.2) = g :=
  indexFrom_map 0 g

theorem indexFrom_idx_lt {i : Nat} {g : Graph} {x : Nat × Triple}
    (h : x ∈ indexFrom i g) : x.1 < i + g.length := by
  induction g generalizing i with
  | nil => cases h
  | cons t ts ih =>
    simp only [indexFrom, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h
      simp only [List.length_cons]
      omega

theorem indexed_idx_lt {g : Graph} {x : Nat × Triple} (h : x ∈ indexed g) :
    x.1 < g.length := by
  have := indexFrom_idx_lt (i := 0) (g := g) h
  omega

/-! ## Two combinators, and the four lemmas that carry every row

Every §8/§9 row is one of two shapes: a SINGLE-premise row reads one
triple and emits conclusions from it (`annOne`), and a JOIN row reads
a first premise and pairs it against a selection of second premises
from the graph (`annJoin`). Writing the fourteen annotators through
these two combinators means the conclusion-preservation lemma and the
index-bound lemma are each proved twice, not fourteen times. -/

/-- A single-premise row, annotated: `f` is the row function of
`FullClosure.lean`, `x` is the premise with its position. -/
def annOne (r : RuleId) (f : Triple → List Triple) (x : Nat × Triple) : List Step :=
  (f x.2).map (fun t => mkStep r t [x.1])

/-- A join row, annotated: select the second premises out of `ig` with
`sel`, then build one step per second premise that `mk` accepts. -/
def annJoin (r : RuleId) (ig : List (Nat × Triple)) (x : Nat × Triple)
    (sel : Triple → Bool) (mk : Triple → Option Triple) : List Step :=
  (ig.filter (fun y => sel y.2)).filterMap (fun y =>
    (mk y.2).map (fun t => mkStep r t [x.1, y.1]))

@[simp] theorem annOne_conclusions (r : RuleId) (f : Triple → List Triple)
    (x : Nat × Triple) : (annOne r f x).map (·.conclusion) = f x.2 := by
  simp [annOne, List.map_map, Function.comp_def]

theorem annOne_idx {r : RuleId} {f : Triple → List Triple} {x : Nat × Triple}
    {n : Nat} (hx : x.1 < n) {a : Step} (ha : a ∈ annOne r f x) :
    WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  simp only [annOne, List.mem_map] at ha
  obtain ⟨t, _, rfl⟩ := ha
  refine ⟨mkStep_wellTagged .., ?_⟩
  intro p hp
  simp only [mkStep_premises, List.mem_singleton] at hp
  omega

theorem annJoin_conclusions (r : RuleId) (ig : List (Nat × Triple))
    (x : Nat × Triple) (sel : Triple → Bool) (mk : Triple → Option Triple) :
    (annJoin r ig x sel mk).map (·.conclusion)
      = ((ig.map (·.2)).filter sel).filterMap mk := by
  induction ig with
  | nil => rfl
  | cons y ys ih =>
    by_cases hs : sel y.2
    · cases hm : mk y.2 with
      | none => simp [annJoin, hs, hm] at ih ⊢; exact ih
      | some t => simp [annJoin, hs, hm] at ih ⊢; exact ih
    · simp [annJoin, hs] at ih ⊢; exact ih

theorem annJoin_idx {r : RuleId} {ig : List (Nat × Triple)} {x : Nat × Triple}
    {sel : Triple → Bool} {mk : Triple → Option Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ annJoin r ig x sel mk) :
    WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  simp only [annJoin, List.mem_filterMap, List.mem_filter] at ha
  obtain ⟨y, ⟨hy, _⟩, hmk⟩ := ha
  cases hm : mk y.2 with
  | none => rw [hm] at hmk; simp at hmk
  | some t =>
    rw [hm] at hmk
    simp only [Option.map_some, Option.some.injEq] at hmk
    subst hmk
    refine ⟨mkStep_wellTagged .., ?_⟩
    intro p hp
    simp only [mkStep_premises, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hx
    · exact hig _ hy


theorem filterMap_some_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.filterMap (fun a => some (f a)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-! ## The fourteen rows, annotated

Each `…Ann` is the row function of `Closure.lean` / `FullClosure.lean`
with the premise positions threaded through it. The `…_conclusions`
lemma next to it proves the annotated row emits EXACTLY the
conclusions the unannotated row emits — this is what makes the witness
describe the closure the engine computes, rather than a second
computation that happens to look similar. -/

/-- **rdfs7**, annotated (`Closure.rdfs7For`). -/
def rdfs7Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  match x.2.s, x.2.o with
  | .iri p, .iri q =>
      if x.2.p == rdfsSubPropertyOf then
        annJoin .rdfs7 ig x (fun y => y.p == p) (fun y => some ⟨y.s, q, y.o⟩)
      else []
  | _, _ => []

theorem rdfs7Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs7Ann ig x).map (·.conclusion) = rdfs7For (ig.map (·.2)) x.2 := by
  unfold rdfs7Ann rdfs7For
  cases hs : x.2.s <;> cases ho : x.2.o <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, triplesWithPredicate, filterMap_some_eq_map]

/-- **rdfs2**, annotated (`Closure.rdfs2For`). -/
def rdfs2Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  match x.2.s with
  | .iri p =>
      if x.2.p == rdfsDomain then
        annJoin .rdfs2 ig x (fun y => y.p == p) (fun y => some ⟨y.s, rdfType, x.2.o⟩)
      else []
  | _ => []

theorem rdfs2Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs2Ann ig x).map (·.conclusion) = rdfs2For (ig.map (·.2)) x.2 := by
  unfold rdfs2Ann rdfs2For
  cases hs : x.2.s <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, triplesWithPredicate, filterMap_some_eq_map]

/-- **rdfs3**, annotated (`Closure.rdfs3For`). -/
def rdfs3Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  match x.2.s with
  | .iri p =>
      if x.2.p == rdfsRange then
        annJoin .rdfs3 ig x (fun y => y.p == p)
          (fun y => match y.o.toSubject? with
                    | some osub => some ⟨osub, rdfType, x.2.o⟩
                    | none      => none)
      else []
  | _ => []

theorem rdfs3Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs3Ann ig x).map (·.conclusion) = rdfs3For (ig.map (·.2)) x.2 := by
  unfold rdfs3Ann rdfs3For
  cases hs : x.2.s <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, triplesWithPredicate] <;> rfl

/-- **rdfs9**, annotated (`Closure.rdfs9For`). -/
def rdfs9Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  match x.2.o with
  | .iri a =>
      if x.2.p == rdfType then
        annJoin .rdfs9 ig x
          (fun y => y.s == Subject.iri a && y.p == rdfsSubClassOf)
          (fun y => some ⟨x.2.s, rdfType, y.o⟩)
      else []
  | _ => []

theorem rdfs9Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs9Ann ig x).map (·.conclusion) = rdfs9For (ig.map (·.2)) x.2 := by
  unfold rdfs9Ann rdfs9For
  cases ho : x.2.o <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, objectsOf, filterMap_some_eq_map, List.map_map,
          Function.comp_def]

/-- **rdfs11**, annotated (`Closure.rdfs11For`). -/
def rdfs11Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  if x.2.p == rdfsSubClassOf then
    match x.2.o.toSubject? with
    | some bsub =>
        annJoin .rdfs11 ig x
          (fun y => y.s == bsub && y.p == rdfsSubClassOf)
          (fun y => some ⟨x.2.s, rdfsSubClassOf, y.o⟩)
    | none => []
  else []

theorem rdfs11Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs11Ann ig x).map (·.conclusion) = rdfs11For (ig.map (·.2)) x.2 := by
  unfold rdfs11Ann rdfs11For
  cases ho : x.2.o.toSubject? <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, objectsOf, filterMap_some_eq_map, List.map_map,
          Function.comp_def]

/-- **rdfs5**, annotated (`Closure.rdfs5For`). -/
def rdfs5Ann (ig : List (Nat × Triple)) (x : Nat × Triple) : List Step :=
  if x.2.p == rdfsSubPropertyOf then
    match x.2.o.toSubject? with
    | some bsub =>
        annJoin .rdfs5 ig x
          (fun y => y.s == bsub && y.p == rdfsSubPropertyOf)
          (fun y => some ⟨x.2.s, rdfsSubPropertyOf, y.o⟩)
    | none => []
  else []

theorem rdfs5Ann_conclusions (ig : List (Nat × Triple)) (x : Nat × Triple) :
    (rdfs5Ann ig x).map (·.conclusion) = rdfs5For (ig.map (·.2)) x.2 := by
  unfold rdfs5Ann rdfs5For
  cases ho : x.2.o.toSubject? <;> dsimp only <;> (try split) <;>
    simp [annJoin_conclusions, objectsOf, filterMap_some_eq_map, List.map_map,
          Function.comp_def]


/-! ### Index bounds, row by row

Every premise index a row emits comes from `ig`, so it is bounded by
whatever bounds `ig`'s positions. -/

theorem rdfs7Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs7Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs7Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

theorem rdfs2Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs2Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs2Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

theorem rdfs3Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs3Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs3Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

theorem rdfs9Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs9Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs9Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

theorem rdfs11Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs11Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs11Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

theorem rdfs5Ann_idx {ig : List (Nat × Triple)} {x : Nat × Triple} {n : Nat}
    (hig : ∀ y ∈ ig, y.1 < n) (hx : x.1 < n) {a : Step}
    (ha : a ∈ rdfs5Ann ig x) : WellTagged a ∧ ∀ p ∈ a.premises, p < n := by
  unfold rdfs5Ann at ha
  split at ha <;> (try split at ha) <;>
    first
      | exact annJoin_idx hig hx ha
      | simp at ha

/-! ## One round, annotated -/

theorem map_flatMap_ann (l : List (Nat × Triple)) (F : (Nat × Triple) → List Step)
    (f : Triple → List Triple) (h : ∀ x, (F x).map (·.conclusion) = f x.2) :
    (l.flatMap F).map (·.conclusion) = (l.map (·.2)).flatMap f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [h a, ih]

/-- Everything the full rule set concludes from `g` in one round, each
conclusion annotated with the row that licensed it and the POSITIONS
in `g` of the premises it was licensed from. Row order is exactly
`fullStepConclusions`'s: the six rdfs-core rows (rdfs7, rdfs2, rdfs3,
rdfs9, rdfs11, rdfs5), then the eight single-premise rows. -/
def annStepConclusions (g : Graph) : List Step :=
  let ig := indexed g
  ig.flatMap (rdfs7Ann ig) ++
  ig.flatMap (rdfs2Ann ig) ++
  ig.flatMap (rdfs3Ann ig) ++
  ig.flatMap (rdfs9Ann ig) ++
  ig.flatMap (rdfs11Ann ig) ++
  ig.flatMap (rdfs5Ann ig) ++
  ig.flatMap (annOne .rdfD2 rdfD2For) ++
  ig.flatMap (annOne .rdfs4a rdfs4aFor) ++
  ig.flatMap (annOne .rdfs4b rdfs4bFor) ++
  ig.flatMap (annOne .rdfs6 rdfs6For) ++
  ig.flatMap (annOne .rdfs8 rdfs8For) ++
  ig.flatMap (annOne .rdfs10 rdfs10For) ++
  ig.flatMap (annOne .rdfs12 rdfs12For) ++
  ig.flatMap (annOne .rdfs13 rdfs13For)

/-- **The annotated round emits exactly the round's conclusions.** Row
for row, in order — so the witness describes the closure the engine
computes and not a second computation beside it. -/
theorem annStepConclusions_conclusions (g : Graph) :
    (annStepConclusions g).map (·.conclusion) = fullStepConclusions g := by
  have h7 := map_flatMap_ann (indexed g) (rdfs7Ann (indexed g))
      (rdfs7For ((indexed g).map (·.2))) (rdfs7Ann_conclusions (indexed g))
  have h2 := map_flatMap_ann (indexed g) (rdfs2Ann (indexed g))
      (rdfs2For ((indexed g).map (·.2))) (rdfs2Ann_conclusions (indexed g))
  have h3 := map_flatMap_ann (indexed g) (rdfs3Ann (indexed g))
      (rdfs3For ((indexed g).map (·.2))) (rdfs3Ann_conclusions (indexed g))
  have h9 := map_flatMap_ann (indexed g) (rdfs9Ann (indexed g))
      (rdfs9For ((indexed g).map (·.2))) (rdfs9Ann_conclusions (indexed g))
  have h11 := map_flatMap_ann (indexed g) (rdfs11Ann (indexed g))
      (rdfs11For ((indexed g).map (·.2))) (rdfs11Ann_conclusions (indexed g))
  have h5 := map_flatMap_ann (indexed g) (rdfs5Ann (indexed g))
      (rdfs5For ((indexed g).map (·.2))) (rdfs5Ann_conclusions (indexed g))
  have hD2 := map_flatMap_ann (indexed g) (annOne .rdfD2 rdfD2For) rdfD2For
      (annOne_conclusions .rdfD2 rdfD2For)
  have h4a := map_flatMap_ann (indexed g) (annOne .rdfs4a rdfs4aFor) rdfs4aFor
      (annOne_conclusions .rdfs4a rdfs4aFor)
  have h4b := map_flatMap_ann (indexed g) (annOne .rdfs4b rdfs4bFor) rdfs4bFor
      (annOne_conclusions .rdfs4b rdfs4bFor)
  have h6 := map_flatMap_ann (indexed g) (annOne .rdfs6 rdfs6For) rdfs6For
      (annOne_conclusions .rdfs6 rdfs6For)
  have h8 := map_flatMap_ann (indexed g) (annOne .rdfs8 rdfs8For) rdfs8For
      (annOne_conclusions .rdfs8 rdfs8For)
  have h10 := map_flatMap_ann (indexed g) (annOne .rdfs10 rdfs10For) rdfs10For
      (annOne_conclusions .rdfs10 rdfs10For)
  have h12 := map_flatMap_ann (indexed g) (annOne .rdfs12 rdfs12For) rdfs12For
      (annOne_conclusions .rdfs12 rdfs12For)
  have h13 := map_flatMap_ann (indexed g) (annOne .rdfs13 rdfs13For) rdfs13For
      (annOne_conclusions .rdfs13 rdfs13For)
  simp only [annStepConclusions, fullStepConclusions, stepConclusions,
    List.map_append, h7, h2, h3, h9, h11, h5, hD2, h4a, h4b, h6, h8, h10, h12,
    h13, indexed_map, List.append_assoc]

/-- Every premise index of an annotated round is a position in `g`. -/
theorem annStepConclusions_ok {g : Graph} {a : Step}
    (ha : a ∈ annStepConclusions g) :
    WellTagged a ∧ ∀ p ∈ a.premises, p < g.length := by
  have hig : ∀ y ∈ indexed g, y.1 < g.length := fun _ hy => indexed_idx_lt hy
  simp only [annStepConclusions, List.mem_append, List.mem_flatMap] at ha
  rcases ha with
    ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
    obtain ⟨x, hx, hax⟩ := h
  · exact rdfs7Ann_idx hig (hig _ hx) hax
  · exact rdfs2Ann_idx hig (hig _ hx) hax
  · exact rdfs3Ann_idx hig (hig _ hx) hax
  · exact rdfs9Ann_idx hig (hig _ hx) hax
  · exact rdfs11Ann_idx hig (hig _ hx) hax
  · exact rdfs5Ann_idx hig (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax
  · exact annOne_idx (hig _ hx) hax


/-! ## Deduplicating with the annotation attached

`addAll` (Closure.lean) appends a conclusion exactly when the graph
does not already hold it. `addAllAnn` runs the same test and appends
the STEP exactly when `addAll` appends its conclusion — which is what
keeps "the steps, read in order, are the graph" true at every point. -/

/-- `addAll` with the step annotation carried alongside. -/
def addAllAnn : Graph → List Step → List Step → Graph × List Step
  | g, ss, []      => (g, ss)
  | g, ss, a :: as =>
      if g.mem a.conclusion then addAllAnn g ss as
      else addAllAnn (g ++ [a.conclusion]) (ss ++ [a]) as

/-- The graph `addAllAnn` computes is the graph `addAll` computes. -/
theorem addAllAnn_fst (as : List Step) : ∀ (g : Graph) (ss : List Step),
    (addAllAnn g ss as).1 = addAll g (as.map (·.conclusion)) := by
  induction as with
  | nil => intro g ss; rfl
  | cons a as ih =>
    intro g ss
    simp only [addAllAnn, List.map_cons, addAll, Graph.add]
    by_cases h : g.mem a.conclusion
    · simp only [h, if_pos]; exact ih g ss
    · simp only [h, if_neg, Bool.false_eq_true]; exact ih _ _

/-- The steps, read in order, stay the graph. -/
theorem addAllAnn_snd (as : List Step) : ∀ (g : Graph) (ss : List Step),
    ss.map (·.conclusion) = g →
    (addAllAnn g ss as).2.map (·.conclusion) = (addAllAnn g ss as).1 := by
  induction as with
  | nil => intro g ss h; exact h
  | cons a as ih =>
    intro g ss h
    simp only [addAllAnn]
    by_cases hm : g.mem a.conclusion
    · simp only [hm, if_pos]; exact ih g ss h
    · simp only [hm, if_neg, Bool.false_eq_true]
      refine ih _ _ ?_
      simp [h]

/-! ## The premise-index bound

`PremisesBounded ss` is the property a left-to-right checker needs:
step `i` names only steps before `i`. No forward reference, no cycle,
one pass. -/

/-- Every premise index of step `i` is strictly less than `i`. -/
def PremisesBounded (ss : List Step) : Prop :=
  ∀ (i : Nat) (h : i < ss.length), ∀ p ∈ ss[i].premises, p < i

theorem premisesBounded_nil : PremisesBounded [] := by
  intro i h; exact absurd h (by simp)

theorem premisesBounded_snoc {ss : List Step} {a : Step} (h : PremisesBounded ss)
    (ha : ∀ p ∈ a.premises, p < ss.length) : PremisesBounded (ss ++ [a]) := by
  intro i hi p hp
  by_cases hlt : i < ss.length
  · rw [List.getElem_append_left hlt] at hp
    exact h i hlt p hp
  · have hge : ss.length ≤ i := Nat.le_of_not_lt hlt
    have hlen : i < ss.length + 1 := by simpa using hi
    have : i = ss.length := by omega
    subst this
    rw [List.getElem_append_right (by omega)] at hp
    simp only [Nat.sub_self] at hp
    exact ha p (by simpa using hp)

theorem premisesBounded_of_map {ss : List Step} (h : ∀ a ∈ ss, a.premises = []) :
    PremisesBounded ss := by
  intro i hi p hp
  rw [h _ (List.getElem_mem hi)] at hp
  exact absurd hp (by simp)

theorem addAllAnn_bounded (as : List Step) : ∀ (g : Graph) (ss : List Step),
    PremisesBounded ss → (∀ a ∈ as, ∀ p ∈ a.premises, p < ss.length) →
    PremisesBounded (addAllAnn g ss as).2 := by
  induction as with
  | nil => intro g ss h _; exact h
  | cons a as ih =>
    intro g ss h hb
    simp only [addAllAnn]
    by_cases hm : g.mem a.conclusion
    · simp only [hm, if_pos]
      exact ih g ss h (fun b hbm => hb b (List.mem_cons_of_mem _ hbm))
    · simp only [hm, if_neg, Bool.false_eq_true]
      refine ih _ _ (premisesBounded_snoc h (hb a (List.mem_cons_self ..))) ?_
      intro b hbm p hp
      have := hb b (List.mem_cons_of_mem _ hbm) p hp
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-! ## The loop, annotated -/

/-- `fullClosureLoop` with the annotation carried alongside. -/
def fullClosureLoopAnn (g : Graph) (ss : List Step) : Nat → Graph × List Step
  | 0     => (g, ss)
  | n + 1 =>
      let r := addAllAnn g ss (annStepConclusions g)
      if r.1.length = g.length then (g, ss) else fullClosureLoopAnn r.1 r.2 n

/-- One annotated round computes the round `fullStep` computes. -/
theorem addAllAnn_step (g : Graph) (ss : List Step) :
    (addAllAnn g ss (annStepConclusions g)).1 = fullStep g := by
  rw [addAllAnn_fst, annStepConclusions_conclusions]; rfl

/-- The annotated loop computes the graph `fullClosureLoop` computes. -/
theorem fullClosureLoopAnn_fst (fuel : Nat) : ∀ (g : Graph) (ss : List Step),
    (fullClosureLoopAnn g ss fuel).1 = fullClosureLoop g fuel := by
  induction fuel with
  | zero => intro g ss; rfl
  | succ n ih =>
    intro g ss
    simp only [fullClosureLoopAnn, fullClosureLoop, addAllAnn_step]
    by_cases h : (fullStep g).length = g.length
    · simp [h]
    · simp only [h, if_neg]
      exact ih _ _

/-- The two invariants the loop preserves: the steps read in order are
the graph, and every premise index points strictly backwards. -/
theorem fullClosureLoopAnn_ok (fuel : Nat) : ∀ (g : Graph) (ss : List Step),
    ss.map (·.conclusion) = g → PremisesBounded ss →
    (fullClosureLoopAnn g ss fuel).2.map (·.conclusion)
        = (fullClosureLoopAnn g ss fuel).1
      ∧ PremisesBounded (fullClosureLoopAnn g ss fuel).2 := by
  induction fuel with
  | zero => intro g ss h hb; exact ⟨h, hb⟩
  | succ n ih =>
    intro g ss h hb
    simp only [fullClosureLoopAnn]
    by_cases hstop : (addAllAnn g ss (annStepConclusions g)).1.length = g.length
    · simp [hstop, h, hb]
    · simp only [hstop, if_neg]
      have hlen : ss.length = g.length := by
        have := congrArg List.length h; simpa using this
      refine ih _ _ (addAllAnn_snd _ _ _ h) (addAllAnn_bounded _ _ _ hb ?_)
      intro a ha p hp
      rw [hlen]
      exact (annStepConclusions_ok ha).2 p hp

/-- `addAllAnn` appends only steps it was given, so a tag property
that holds of both lists holds of the result. -/
theorem addAllAnn_tagged (as : List Step) : ∀ (g : Graph) (ss : List Step),
    (∀ a ∈ ss, WellTagged a) → (∀ a ∈ as, WellTagged a) →
    ∀ a ∈ (addAllAnn g ss as).2, WellTagged a := by
  induction as with
  | nil => intro g ss h _; exact h
  | cons a as ih =>
    intro g ss h hb
    simp only [addAllAnn]
    by_cases hm : g.mem a.conclusion
    · simp only [hm, if_pos]
      exact ih g ss h (fun b hbm => hb b (List.mem_cons_of_mem _ hbm))
    · simp only [hm, if_neg, Bool.false_eq_true]
      refine ih _ _ ?_ (fun b hbm => hb b (List.mem_cons_of_mem _ hbm))
      intro b hbm
      rcases List.mem_append.1 hbm with hbm | hbm
      · exact h b hbm
      · rw [List.mem_singleton.1 hbm]; exact hb a (List.mem_cons_self ..)

theorem fullClosureLoopAnn_tagged (fuel : Nat) : ∀ (g : Graph) (ss : List Step),
    (∀ a ∈ ss, WellTagged a) →
    ∀ a ∈ (fullClosureLoopAnn g ss fuel).2, WellTagged a := by
  induction fuel with
  | zero => intro g ss h; exact h
  | succ n ih =>
    intro g ss h
    simp only [fullClosureLoopAnn]
    by_cases hstop : (addAllAnn g ss (annStepConclusions g)).1.length = g.length
    · simp only [hstop, if_pos]; exact h
    · simp only [hstop, if_neg]
      exact ih _ _ (addAllAnn_tagged _ _ _ h (fun a ha => (annStepConclusions_ok ha).1))

/-! ## The seed -/

/-- One `base` step per triple of the input graph. -/
def baseSteps (g : Graph) : List Step := g.map (fun t => mkStep .base t [])

/-- One `axiomatic` step per axiomatic triple. -/
def axiomSteps (ax : Graph) : List Step := ax.map (fun t => mkStep .axiomatic t [])

@[simp] theorem baseSteps_conclusions (g : Graph) :
    (baseSteps g).map (·.conclusion) = g := by
  simp [baseSteps, List.map_map, Function.comp_def]

@[simp] theorem axiomSteps_conclusions (ax : Graph) :
    (axiomSteps ax).map (·.conclusion) = ax := by
  simp [axiomSteps, List.map_map, Function.comp_def]

theorem baseSteps_bounded (g : Graph) : PremisesBounded (baseSteps g) := by
  refine premisesBounded_of_map ?_
  intro a ha
  simp only [baseSteps, List.mem_map] at ha
  obtain ⟨t, _, rfl⟩ := ha
  rfl

theorem baseSteps_tagged (g : Graph) : ∀ a ∈ baseSteps g, WellTagged a := by
  intro a ha
  simp only [baseSteps, List.mem_map] at ha
  obtain ⟨t, _, rfl⟩ := ha
  exact mkStep_wellTagged ..

theorem axiomSteps_tagged (ax : Graph) : ∀ a ∈ axiomSteps ax, WellTagged a := by
  intro a ha
  simp only [axiomSteps, List.mem_map] at ha
  obtain ⟨t, _, rfl⟩ := ha
  exact mkStep_wellTagged ..

theorem axiomSteps_premises (ax : Graph) (n : Nat) :
    ∀ a ∈ axiomSteps ax, ∀ p ∈ a.premises, p < n := by
  intro a ha
  simp only [axiomSteps, List.mem_map] at ha
  obtain ⟨t, _, rfl⟩ := ha
  intro p hp
  exact absurd hp (by simp)

/-! ## The proof-carrying closure -/

/-- The seeded graph with its `base` / `axiomatic` steps. -/
def seedAnn (D cmps : List WfIri) (g : Graph) : Graph × List Step :=
  addAllAnn g (baseSteps g) (axiomSteps (axiomaticTriples D cmps))

theorem seedAnn_fst (D cmps : List WfIri) (g : Graph) :
    (seedAnn D cmps g).1 = addAll g (axiomaticTriples D cmps) := by
  simp only [seedAnn, addAllAnn_fst, axiomSteps_conclusions]

theorem seedAnn_snd (D cmps : List WfIri) (g : Graph) :
    (seedAnn D cmps g).2.map (·.conclusion) = (seedAnn D cmps g).1 :=
  addAllAnn_snd _ _ _ (baseSteps_conclusions g)

theorem seedAnn_bounded (D cmps : List WfIri) (g : Graph) :
    PremisesBounded (seedAnn D cmps g).2 :=
  addAllAnn_bounded _ _ _ (baseSteps_bounded g) (axiomSteps_premises _ _)

theorem seedAnn_tagged (D cmps : List WfIri) (g : Graph) :
    ∀ a ∈ (seedAnn D cmps g).2, WellTagged a :=
  addAllAnn_tagged _ _ _ (baseSteps_tagged g) (axiomSteps_tagged _)

/-- The RDFS-regime closure and its derivation, as a list. -/
def fullClosureAnn (D cmps : List WfIri) (g : Graph) : Graph × List Step :=
  fullClosureLoopAnn (seedAnn D cmps g).1 (seedAnn D cmps g).2
    (fullClosureFuelBound (seedAnn D cmps g).1)

theorem fullClosureAnn_fst (D cmps : List WfIri) (g : Graph) :
    (fullClosureAnn D cmps g).1 = fullClosure D cmps g := by
  simp only [fullClosureAnn, fullClosureLoopAnn_fst, fullClosure, seedAnn_fst]

theorem fullClosureAnn_ok (D cmps : List WfIri) (g : Graph) :
    (fullClosureAnn D cmps g).2.map (·.conclusion) = (fullClosureAnn D cmps g).1
      ∧ PremisesBounded (fullClosureAnn D cmps g).2 :=
  fullClosureLoopAnn_ok (fullClosureFuelBound (seedAnn D cmps g).1) _ _
    (seedAnn_snd D cmps g) (seedAnn_bounded D cmps g)

theorem fullClosureAnn_tagged (D cmps : List WfIri) (g : Graph) :
    ∀ a ∈ (fullClosureAnn D cmps g).2, WellTagged a :=
  fullClosureLoopAnn_tagged (fullClosureFuelBound (seedAnn D cmps g).1) _ _
    (seedAnn_tagged D cmps g)

/-- **The RDFS-regime closure, with its derivation.** The graph is
exactly `fullClosure D cmps g` (`fullClosureWithProof_graph`); the
`Derivation` names, for every triple of it, the §8/§9 row that
licensed the triple, the Lean statement that backs that row, and the
indices of the steps it was licensed from. -/
def fullClosureWithProof (D cmps : List WfIri) (g : Graph) : Graph × Derivation :=
  ((fullClosureAnn D cmps g).1, (fullClosureAnn D cmps g).2.toArray)

/-- **Requirement: the emitting entry point returns the graph the
plain entry point returns.** Without this the witness would describe
something `fullClosure` does not serve. -/
theorem fullClosureWithProof_graph (D cmps : List WfIri) (g : Graph) :
    (fullClosureWithProof D cmps g).1 = fullClosure D cmps g := by
  simp only [fullClosureWithProof]
  exact fullClosureAnn_fst D cmps g

/-- **The step conclusions, read in order, ARE the closure.** So the
witness covers every triple of the answer and nothing else. -/
theorem fullClosureWithProof_conclusions (D cmps : List WfIri) (g : Graph) :
    (fullClosureWithProof D cmps g).2.toList.map (·.conclusion)
      = fullClosure D cmps g := by
  simp only [fullClosureWithProof, List.toList_toArray]
  rw [(fullClosureAnn_ok D cmps g).1, fullClosureAnn_fst]

/-- **Requirement: premise indices point strictly backwards.** Step
`i` names only steps before `i`, so a checker validates the array in
one left-to-right pass and cannot be fooled by a forward reference or
a cycle. -/
theorem fullClosureWithProof_premises_lt (D cmps : List WfIri) (g : Graph)
    (i : Nat) (hi : i < (fullClosureWithProof D cmps g).2.size)
    (p : Nat) (hp : p ∈ ((fullClosureWithProof D cmps g).2[i]).premises) : p < i := by
  have hlist : (fullClosureWithProof D cmps g).2.toList = (fullClosureAnn D cmps g).2 := by
    simp only [fullClosureWithProof, List.toList_toArray]
  have hb := (fullClosureAnn_ok D cmps g).2
  rw [← hlist] at hb
  have hi'' : i < (fullClosureWithProof D cmps g).2.toList.length := by simpa using hi
  refine hb i hi'' p ?_
  rw [Array.getElem_toList hi]
  exact hp

/-- **Soundness of the witness.** Every step the emitter produces has
a conclusion that really is derivable from `g` and the axiomatic
triples by the §8.1 / §9.2 rows — assembled from `fullClosure_sound`
through the conclusion equation, so the per-row soundness lemmas of
`FullClosureTheorems.lean` are used, not re-derived. -/
theorem fullClosureWithProof_sound (D cmps : List WfIri) (g : Graph)
    (i : Nat) (hi : i < (fullClosureWithProof D cmps g).2.size) :
    DerivesFull (axiomaticTriples D cmps) g
      ((fullClosureWithProof D cmps g).2[i]).conclusion := by
  refine fullClosure_sound D cmps g ?_
  rw [← fullClosureWithProof_conclusions D cmps g]
  exact List.mem_map_of_mem (Array.getElem_mem_toList hi)

/-- **Every step carries a real assurance reference.** Its component
is `rdfs` and its `assurance` is the one `RuleId.assurance` gives for
its row — so a reader can always tell which proved statement backs a
step, and no step reaches a reader with a blank or defaulted
reference. -/
theorem fullClosureWithProof_wellTagged (D cmps : List WfIri) (g : Graph)
    (i : Nat) (hi : i < (fullClosureWithProof D cmps g).2.size) :
    WellTagged ((fullClosureWithProof D cmps g).2[i]) := by
  have hlist : (fullClosureWithProof D cmps g).2.toList = (fullClosureAnn D cmps g).2 := by
    simp only [fullClosureWithProof, List.toList_toArray]
  have hmem : ((fullClosureWithProof D cmps g).2[i])
      ∈ (fullClosureWithProof D cmps g).2.toList := Array.getElem_mem_toList hi
  rw [hlist] at hmem
  exact fullClosureAnn_tagged D cmps g _ hmem

end L4Factoidal.RDFS
