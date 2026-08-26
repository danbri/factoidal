/-
L4Factoidal.RDFS.DerivationCheck — the DERIVATION CHECKER: an
independent, total decision procedure that reads a `Derivation`
(`Derivation.lean`) and decides whether every step really is licensed
by the RDF 1.1 Semantics row it names, over the premise steps it
names.

  https://www.w3.org/TR/rdf11-mt/#rdf-entailment    (§8)
  https://www.w3.org/TR/rdf11-mt/#rdfs-entailment   (§9)

Design: `docs/designissues/2026-08-26-proof-certificate-v1.md`
§2 (trust model), §5 (what the checker rejects), §6 (the two
obligations).

## Why this exists

`fullClosureWithProof` (Derivation.lean) emits a witness. Design §2
states the property the witness exists for: a party who does NOT
trust this engine can still check the answer. `checkDerivation`
below reads the graph, the axiom set and the witness, and needs
nothing from the closure algorithm — no fixpoint, no fuel, no index
structures. It is one left-to-right pass over a finite array. A
reader who distrusts us can reimplement it from §8 and §9 of RDF 1.1
Semantics and get the same verdict.

## What `checkDerivation_sound` says

`checkDerivation ax g d = true` implies that EVERY step's conclusion
is `DerivesFull ax g`-derivable. The theorem is unconditional: no
hypothesis on `d`, `g` or `ax`, and in particular no hypothesis that
`d` came from this engine. A `Derivation` from any source that passes
the check carries a real derivation.

⚠️ A checker that returned `false` on everything would satisfy that
theorem vacuously. The gate is therefore a MATCHED PAIR:

* ACCEPTANCE is `checkDerivation_roundTrip` below — the checker
  accepts `fullClosureWithProof`'s output for every datatype map,
  `rdf:_n` slice and graph. Three concrete witnesses (141, 190 and
  147 steps) are pinned by `#guard` in `DerivationCheckTests.lean`.
* REJECTION is pinned by `#guard` only, in the same file: one
  mutation per row of design §5, each built by changing ONE field of
  ONE step of a witness the checker accepts. No theorem here states
  that a defective derivation is rejected.

## What the checker does NOT do

* It does not check that the derivation is COMPLETE — that every
  triple of the closure has a step. `fullClosureWithProof_conclusions`
  is where that lives, and design §6 records completeness as out of
  scope for v1.
* It does not verify the `assurance` field. That field is DATA. The
  Lean kernel does not check that the named theorem exists or that it
  says what the name suggests. `checkDerivation_ignores_tags` proves
  the verdict does not depend on `assurance` or `component` at all,
  so a step can never pass BECAUSE its assurance claims a theorem.
  `weakestAssurance` reports the weakest link as information
  alongside the verdict (design §6b), never in place of the check.
* It does not check graph identity, artifact hashes or the wire
  format (design §3, §4). Those are the serialisation layer and are
  not in this module.

## Assurance tiers at this layer, stated so the field is not read as
## more than it is

`AssuranceRef` has two constructors, so `weakestAssurance` returns one
of two values. Every whole-closure witness contains `base` and
`axiomatic` steps, and those carry `constructorOnly`; so the reported
weakest link is `constructorOnly` for every witness this engine emits
today, and the three `#guard`s in the test file pin exactly that.
The field becomes informative only once the Lean tree has its own
generated assurance inventory — design §8 records that as a
PREREQUISITE for §6b, not as a nice-to-have. Nothing here copies an
F* module's tier onto a Lean step of the same name (anti-pattern #31).

No `sorry`, no `axiom`, no `native_decide`, no `partial`. The checker
is structurally recursive over the step list: one pass, no fuel.
-/
import L4Factoidal.RDFS.Derivation

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-- A default `Step`, so the `d[i]!` form of `checkDerivation_sound`
elaborates. `Step` itself is not `Inhabited` (its `Triple` field has
no canonical value — `WfIri` is a subtype), so the default is spelled
out here rather than derived. It never reaches a reader: every use
below is guarded by an in-range proof (`getElem!_pos`). -/
instance : Inhabited Step :=
  ⟨mkStep .base ⟨.iri rdfType, rdfType, .iri rdfType⟩ []⟩

/-! ## Reading a premise

A premise is an INDEX into the steps that precede the step citing it.
`prefixConclusion` reads one, and returns `none` when the index is out
of range — which is what makes an out-of-range premise a rejection
rather than a crash or a defaulted triple. -/

/-- The conclusion of the step at position `j` of a prefix, if there
is one. -/
def prefixConclusion (pre : List Step) (j : Nat) : Option Triple :=
  (pre[j]?).map (·.conclusion)

/-! ## The two row shapes

Every §8/§9 row the emitter uses is one of two shapes, and the
checker mirrors that split. A SINGLE-premise row is checked against
the row function applied to the one premise. A JOIN row is checked
against the row function applied to the TWO-ELEMENT graph holding
exactly the two premises, with the first premise as the row's driving
triple — which is what makes the existing per-row soundness lemmas
(`rdfs7For_sound` and friends, which want `decl ∈ g`) apply directly.

A row cited with the wrong number of premises is rejected: there is
no fall-through that ignores extra premises. -/

/-- Check a single-premise row: `st.conclusion` must be one of the
conclusions `f` licenses from the one premise's conclusion. -/
def oneRow (f : Triple → List Triple) (pre : List Step) (st : Step) : Bool :=
  match st.premises with
  | [j] =>
      match prefixConclusion pre j with
      | some u => decide (st.conclusion ∈ f u)
      | none   => false
  | _   => false

/-- Check a join row: `st.conclusion` must be one of the conclusions
`f` licenses from the FIRST premise read against the two-element
graph holding both premises. -/
def joinRow (f : Graph → Triple → List Triple) (pre : List Step) (st : Step) : Bool :=
  match st.premises with
  | [j, k] =>
      match prefixConclusion pre j, prefixConclusion pre k with
      | some u, some v => decide (st.conclusion ∈ f [u, v] u)
      | _, _           => false
  | _      => false

/-! ## One step

`rowCheck` is total over `RuleId`: all sixteen rows have a case, and
each case names the row function of `Closure.lean` / `FullClosure.lean`
that the RDF 1.1 Semantics table assigns to it. There is no default
branch, so a row added to `RuleId` without a case here fails to
compile rather than being silently accepted. -/

/-- The row-specific half of the step check. -/
def rowCheck (ax g : Graph) (pre : List Step) (st : Step) : Bool :=
  match st.rule with
  | .base      => match st.premises with
                  | [] => decide (st.conclusion ∈ g)
                  | _  => false
  | .axiomatic => match st.premises with
                  | [] => decide (st.conclusion ∈ ax)
                  | _  => false
  | .rdfD2  => oneRow rdfD2For  pre st
  | .rdfs4a => oneRow rdfs4aFor pre st
  | .rdfs4b => oneRow rdfs4bFor pre st
  | .rdfs6  => oneRow rdfs6For  pre st
  | .rdfs8  => oneRow rdfs8For  pre st
  | .rdfs10 => oneRow rdfs10For pre st
  | .rdfs12 => oneRow rdfs12For pre st
  | .rdfs13 => oneRow rdfs13For pre st
  | .rdfs7  => joinRow rdfs7For  pre st
  | .rdfs2  => joinRow rdfs2For  pre st
  | .rdfs3  => joinRow rdfs3For  pre st
  | .rdfs9  => joinRow rdfs9For  pre st
  | .rdfs11 => joinRow rdfs11For pre st
  | .rdfs5  => joinRow rdfs5For  pre st

/-- One step passes when every premise index points STRICTLY
BACKWARDS into the prefix, and the row licenses the conclusion from
those premises.

The range test is stated even though `prefixConclusion` already
returns `none` out of range: design §5's first two rejection rows —
a premise index equal to the step's own index (self-justification)
and one greater than it (forward reference) — are the reason the
checker takes a PREFIX rather than the whole array, and the test
makes that explicit at the point a reader looks for it. -/
def stepOk (ax g : Graph) (pre : List Step) (st : Step) : Bool :=
  st.premises.all (fun p => decide (p < pre.length)) && rowCheck ax g pre st

/-! ## The pass

`checkSteps` carries the already-checked prefix and consumes the rest.
It is structurally recursive on the remaining steps: it terminates on
every input, takes no fuel parameter, and has equation lemmas the
soundness proof below uses (issue #617: a `partial def` would compile
to an opaque constant and `checkDerivation_sound` would be
unprovable about it). -/

/-- One left-to-right pass: `pre` is the checked prefix, the second
argument is what is left. -/
def checkSteps (ax g : Graph) : List Step → List Step → Bool
  | _,   []      => true
  | pre, a :: as => stepOk ax g pre a && checkSteps ax g (pre ++ [a]) as

/-- **The checker.** `true` exactly when every step of `d` is
licensed by the row it names over the premises it names, reading `g`
as the input graph and `ax` as the axiom set. -/
def checkDerivation (ax g : Graph) (d : Derivation) : Bool :=
  checkSteps ax g [] d.toList

/-! ## Soundness

The chain is: a row check discharges into the per-row soundness lemma
over a one- or two-element graph, and `DerivesFull.cut` moves that
back to `g` using the derivations already established for the premise
steps. -/

/-- A prefix entry read by index is an entry of the prefix. -/
theorem mem_of_prefixConclusion {pre : List Step} {j : Nat} {u : Triple}
    (h : prefixConclusion pre j = some u) :
    ∃ b ∈ pre, b.conclusion = u := by
  unfold prefixConclusion at h
  cases hj : pre[j]? with
  | none => rw [hj] at h; simp at h
  | some b =>
    rw [hj] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨b, List.mem_of_getElem? hj, h⟩

/-- A single-premise row check discharges into that row's soundness
lemma. `hf` is the lemma's shape: the driving triple is in the graph
and the conclusion is emitted, so the conclusion is derivable. -/
theorem oneRow_sound {ax g : Graph} {pre : List Step} {st : Step}
    {f : Triple → List Triple}
    (hf : ∀ (h : Graph) (u t : Triple), u ∈ h → t ∈ f u → DerivesFull ax h t)
    (hpre : ∀ b ∈ pre, DerivesFull ax g b.conclusion)
    (h : oneRow f pre st = true) : DerivesFull ax g st.conclusion := by
  unfold oneRow at h
  split at h
  · rename_i j hprem
    cases hj : prefixConclusion pre j with
    | none => rw [hj] at h; simp at h
    | some u =>
      rw [hj] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨b, hb, hbu⟩ := mem_of_prefixConclusion hj
      have hsmall : DerivesFull ax [u] st.conclusion :=
        hf [u] u st.conclusion (List.mem_singleton_self u) h
      refine DerivesFull.cut ?_ hsmall
      intro x hx
      rw [List.mem_singleton.1 hx, ← hbu]
      exact hpre b hb
  · simp at h

/-- A join row check discharges into that row's soundness lemma over
the two-element graph holding the two premises. -/
theorem joinRow_sound {ax g : Graph} {pre : List Step} {st : Step}
    {f : Graph → Triple → List Triple}
    (hf : ∀ (h : Graph) (u t : Triple), u ∈ h → t ∈ f h u → Derives h t)
    (hpre : ∀ b ∈ pre, DerivesFull ax g b.conclusion)
    (h : joinRow f pre st = true) : DerivesFull ax g st.conclusion := by
  unfold joinRow at h
  split at h
  · rename_i j k hprem
    cases hj : prefixConclusion pre j with
    | none => rw [hj] at h; simp at h
    | some u =>
      cases hk : prefixConclusion pre k with
      | none => rw [hj, hk] at h; simp at h
      | some v =>
        rw [hj, hk] at h
        simp only [decide_eq_true_eq] at h
        obtain ⟨bu, hbu, hbuc⟩ := mem_of_prefixConclusion hj
        obtain ⟨bv, hbv, hbvc⟩ := mem_of_prefixConclusion hk
        have hsmall : Derives [u, v] st.conclusion :=
          hf [u, v] u st.conclusion (by simp) h
        refine DerivesFull.cut ?_ (Derives.toFull hsmall)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [← hbuc]; exact hpre bu hbu
        · rw [← hbvc]; exact hpre bv hbv
  · simp at h

/-- **One step that passes is derivable.** Sixteen cases, one per row
of the rule set; each names the per-row soundness lemma that
discharges it. -/
theorem stepOk_sound {ax g : Graph} {pre : List Step} {a : Step}
    (hpre : ∀ b ∈ pre, DerivesFull ax g b.conclusion)
    (h : stepOk ax g pre a = true) : DerivesFull ax g a.conclusion := by
  simp only [stepOk, Bool.and_eq_true] at h
  obtain ⟨_, hrow⟩ := h
  unfold rowCheck at hrow
  split at hrow
  · -- base
    split at hrow
    · simp only [decide_eq_true_eq] at hrow
      exact DerivesFull.base hrow
    · simp at hrow
  · -- axiomatic
    split at hrow
    · simp only [decide_eq_true_eq] at hrow
      exact DerivesFull.axiomatic hrow
    · simp at hrow
  -- the fourteen rule rows; each `exact` typechecks for exactly one row,
  -- because `hrow` pins the row function and the lemma's hypothesis names it
  all_goals first
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfD2For_sound  hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs4aFor_sound hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs4bFor_sound hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs6For_sound  hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs8For_sound  hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs10For_sound hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs12For_sound hu ht) hpre hrow
    | exact oneRow_sound  (fun _ _ _ hu ht => rdfs13For_sound hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs7For_sound  hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs2For_sound  hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs3For_sound  hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs9For_sound  hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs11For_sound hu ht) hpre hrow
    | exact joinRow_sound (fun _ _ _ hu ht => rdfs5For_sound  hu ht) hpre hrow

/-- The pass, as an induction: everything the checker accepts —
prefix and remainder together — is derivable. -/
theorem checkSteps_sound {ax g : Graph} : ∀ (post pre : List Step),
    (∀ b ∈ pre, DerivesFull ax g b.conclusion) →
    checkSteps ax g pre post = true →
    ∀ a ∈ pre ++ post, DerivesFull ax g a.conclusion := by
  intro post
  induction post with
  | nil => intro pre hpre _ a ha; exact hpre a (by simpa using ha)
  | cons a as ih =>
    intro pre hpre h x hx
    simp only [checkSteps, Bool.and_eq_true] at h
    obtain ⟨ha, has⟩ := h
    have hader : DerivesFull ax g a.conclusion := stepOk_sound hpre ha
    have hpre' : ∀ b ∈ pre ++ [a], DerivesFull ax g b.conclusion := by
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hpre b hb
      · rw [List.mem_singleton.1 hb]; exact hader
    have := ih (pre ++ [a]) hpre' has x
    rw [List.append_assoc] at this
    exact this (by simpa using hx)

/-- **Soundness of the checker.** If `checkDerivation ax g d = true`
then every step of `d` concludes a triple that really is derivable
from `g` and `ax` by the RDF 1.1 Semantics §8.1 / §9.2 rows.

UNCONDITIONAL: no hypothesis on `d`, `g` or `ax`, and no hypothesis
that `d` was produced by this engine. This is the property design §2
exists for — a party who does not trust the engine runs the checker
and, if it accepts, holds a derivation. -/
theorem checkDerivation_sound {ax g : Graph} {d : Derivation}
    (h : checkDerivation ax g d = true) (i : Nat) (hi : i < d.size) :
    DerivesFull ax g (d[i]!).conclusion := by
  have hall := checkSteps_sound d.toList [] (by intro b hb; simp at hb) h
  rw [List.nil_append] at hall
  have hidx : d[i]! = d[i] := getElem!_pos d i hi
  rw [hidx]
  exact hall _ (Array.getElem_mem_toList hi)

/-! ## The assurance field is DATA, and the verdict does not read it

Design §6b: a step must never be treated as valid because its
`assurance` says a theorem exists. The strongest form of that
statement is that the verdict does not depend on the field at all —
proved below by rewriting every step's `assurance` and `component` to
fixed values and showing the verdict is unchanged. -/

/-- Replace a step's `assurance` and `component` with fixed values,
keeping the rule, the premises and the conclusion. -/
def scrubTags (st : Step) : Step :=
  { st with assurance := .constructorOnly "" "", component := .rdf }

@[simp] theorem scrubTags_rule (st : Step) : (scrubTags st).rule = st.rule := rfl
@[simp] theorem scrubTags_premises (st : Step) :
    (scrubTags st).premises = st.premises := rfl
@[simp] theorem scrubTags_conclusion (st : Step) :
    (scrubTags st).conclusion = st.conclusion := rfl

@[simp] theorem prefixConclusion_scrub (pre : List Step) (j : Nat) :
    prefixConclusion (pre.map scrubTags) j = prefixConclusion pre j := by
  simp [prefixConclusion, List.getElem?_map, Option.map_map, Function.comp_def]

@[simp] theorem oneRow_scrub (f : Triple → List Triple) (pre : List Step)
    (st : Step) : oneRow f (pre.map scrubTags) (scrubTags st) = oneRow f pre st := by
  simp only [oneRow, scrubTags_premises, scrubTags_conclusion, prefixConclusion_scrub]
  rfl

@[simp] theorem joinRow_scrub (f : Graph → Triple → List Triple) (pre : List Step)
    (st : Step) : joinRow f (pre.map scrubTags) (scrubTags st) = joinRow f pre st := by
  simp only [joinRow, scrubTags_premises, scrubTags_conclusion, prefixConclusion_scrub]
  rfl

@[simp] theorem rowCheck_scrub (ax g : Graph) (pre : List Step) (st : Step) :
    rowCheck ax g (pre.map scrubTags) (scrubTags st) = rowCheck ax g pre st := by
  unfold rowCheck
  cases hr : st.rule <;>
    simp only [scrubTags_rule, hr, scrubTags_premises, scrubTags_conclusion,
      oneRow_scrub, joinRow_scrub] <;> try rfl

@[simp] theorem stepOk_scrub (ax g : Graph) (pre : List Step) (st : Step) :
    stepOk ax g (pre.map scrubTags) (scrubTags st) = stepOk ax g pre st := by
  simp [stepOk]

theorem checkSteps_scrub (ax g : Graph) : ∀ (post pre : List Step),
    checkSteps ax g (pre.map scrubTags) (post.map scrubTags)
      = checkSteps ax g pre post := by
  intro post
  induction post with
  | nil => intro pre; rfl
  | cons a as ih =>
    intro pre
    simp only [List.map_cons, checkSteps, stepOk_scrub]
    rw [show (pre.map scrubTags) ++ [scrubTags a] = (pre ++ [a]).map scrubTags by simp]
    rw [ih (pre ++ [a])]

/-- **The verdict does not read the assurance or component tags.**
Rewriting every step's `assurance` and `component` leaves the verdict
unchanged, so no step can pass BECAUSE its assurance claims a theorem
exists — design §6b, and requirement 5 of the checker's brief. -/
theorem checkDerivation_ignores_tags (ax g : Graph) (d : Derivation) :
    checkDerivation ax g (d.map scrubTags) = checkDerivation ax g d := by
  simp only [checkDerivation, Array.toList_map]
  exact checkSteps_scrub ax g d.toList []

/-! ## Reporting the weakest link (design §6b)

Reported alongside the verdict. It has no effect on the verdict, and
`checkDerivation_ignores_tags` above is the proof of that. -/

/-- The strength of the licence a step cites. Two values, because
`AssuranceRef` has two constructors: a discharged Lean soundness
theorem, or the `DerivesFull` constructor that states the row.

⚠️ `constructorOnly` is ordered WEAKER here in one specific sense
only — no separate discharged theorem is cited. It is not a claim
that such a step is less well founded: `base` and `axiomatic` need no
lemma beyond their constructor, and `checkDerivation_sound` covers
them. The ordering is what design §6b's "report the weakest link"
needs to be computable; it becomes informative about IMPLEMENTATION
assurance only once the Lean tree has its own generated inventory
(design §8). -/
inductive AssuranceTier where
  /-- The row is a constructor of `DerivesFull`; no separate theorem. -/
  | constructorOnly
  /-- A landed, discharged Lean soundness theorem backs the row. -/
  | provedBy
  deriving DecidableEq, Repr, Inhabited

def AssuranceRef.tier : AssuranceRef → AssuranceTier
  | .provedBy _ _        => .provedBy
  | .constructorOnly _ _ => .constructorOnly

/-- The weaker of two tiers. -/
def AssuranceTier.weaker : AssuranceTier → AssuranceTier → AssuranceTier
  | .constructorOnly, _ => .constructorOnly
  | _, .constructorOnly => .constructorOnly
  | .provedBy, .provedBy => .provedBy

/-- The weakest assurance tier any step of the derivation cites, or
`none` for an empty derivation. -/
def weakestAssurance (d : Derivation) : Option AssuranceTier :=
  d.toList.foldl
    (fun acc st =>
      match acc with
      | none   => some st.assurance.tier
      | some a => some (AssuranceTier.weaker a st.assurance.tier))
    none

/-- What a caller gets back: the verdict, and the weakest link
alongside it. Design §6b leaves the POLICY to the caller — v1 reports
the tier and does not downgrade a valid chain because of it. -/
structure CheckResult where
  /-- `checkDerivation`'s verdict. -/
  valid : Bool
  /-- The weakest assurance tier in the chain. Information only. -/
  weakest : Option AssuranceTier
  deriving DecidableEq, Repr

/-- Check a derivation and report the weakest link with the verdict. -/
def checkDerivationReport (ax g : Graph) (d : Derivation) : CheckResult :=
  { valid := checkDerivation ax g d, weakest := weakestAssurance d }

@[simp] theorem checkDerivationReport_valid (ax g : Graph) (d : Derivation) :
    (checkDerivationReport ax g d).valid = checkDerivation ax g d := rfl

/-- **The report's verdict is the checker's verdict.** So a caller
reading `CheckResult.valid` is reading `checkDerivation`, and
`checkDerivation_sound` applies to it unchanged — the tier does not
enter the verdict. -/
theorem checkDerivationReport_sound {ax g : Graph} {d : Derivation}
    (h : (checkDerivationReport ax g d).valid = true) (i : Nat) (hi : i < d.size) :
    DerivesFull ax g (d[i]!).conclusion :=
  checkDerivation_sound h i hi

/-! ## The round trip: everything the emitter emits, the checker accepts

`checkDerivation_sound` says the checker accepts nothing false. The
theorem below says the checker accepts what this engine produces, for
EVERY datatype map, `rdf:_n` slice and graph — the three witnesses
`DerivationCheckTests.lean` pins are instances of it.

The proof follows the same three-layer shape as `Derivation.lean`'s
own invariants: a row-level statement, carried through `addAllAnn`,
carried through `fullClosureLoopAnn`, applied at the seed. -/

/-- The pass splits at any point of the remaining steps. -/
theorem checkSteps_append (ax g : Graph) : ∀ (post1 post2 pre : List Step),
    checkSteps ax g pre (post1 ++ post2)
      = (checkSteps ax g pre post1 && checkSteps ax g (pre ++ post1) post2) := by
  intro post1
  induction post1 with
  | nil => intro post2 pre; simp [checkSteps]
  | cons a as ih =>
    intro post2 pre
    simp only [List.cons_append, checkSteps, ih, Bool.and_assoc, List.append_assoc,
      List.cons_append, List.nil_append]

/-- Appending one step: the whole array passes when the prefix passes
and the new step passes against that prefix. -/
theorem checkSteps_snoc (ax g : Graph) (ss : List Step) (a : Step) :
    checkSteps ax g [] (ss ++ [a])
      = (checkSteps ax g [] ss && stepOk ax g ss a) := by
  rw [checkSteps_append]
  simp [checkSteps]

/-! ### The row check reads only the premises' conclusions

Two prefixes that agree on the step's premise indices give the same
row verdict. This is the one fact behind both the extension lemma
below and `checkDerivation_ignores_tags` above: nothing else about
the prefix enters the check. -/

theorem oneRow_congr (f : Triple → List Triple) (pre pre' : List Step) (a : Step)
    (hpc : ∀ p ∈ a.premises, prefixConclusion pre' p = prefixConclusion pre p) :
    oneRow f pre' a = oneRow f pre a := by
  unfold oneRow
  split
  · rename_i j hprem
    rw [hpc j (by rw [hprem]; simp)]
  · rfl

theorem joinRow_congr (f : Graph → Triple → List Triple) (pre pre' : List Step)
    (a : Step)
    (hpc : ∀ p ∈ a.premises, prefixConclusion pre' p = prefixConclusion pre p) :
    joinRow f pre' a = joinRow f pre a := by
  unfold joinRow
  split
  · rename_i j k hprem
    rw [hpc j (by rw [hprem]; simp), hpc k (by rw [hprem]; simp)]
  · rfl

theorem rowCheck_congr (ax g : Graph) (pre pre' : List Step) (a : Step)
    (hpc : ∀ p ∈ a.premises, prefixConclusion pre' p = prefixConclusion pre p) :
    rowCheck ax g pre' a = rowCheck ax g pre a := by
  unfold rowCheck
  cases hr : a.rule <;>
    simp only [oneRow_congr _ pre pre' a hpc, joinRow_congr _ pre pre' a hpc]

/-- A step that passes against a prefix passes against any EXTENSION
of that prefix. The premise bound needed for this is part of
`stepOk` itself, so there is no side condition. -/
theorem stepOk_mono (ax g : Graph) (pre ext : List Step) (a : Step)
    (h : stepOk ax g pre a = true) : stepOk ax g (pre ++ ext) a = true := by
  simp only [stepOk, Bool.and_eq_true] at h ⊢
  obtain ⟨hb, hrow⟩ := h
  have hb' : ∀ p ∈ a.premises, p < pre.length := by
    intro p hp
    have := List.all_eq_true.1 hb p hp
    simpa using this
  refine ⟨?_, ?_⟩
  · refine List.all_eq_true.2 ?_
    intro p hp
    have := hb' p hp
    simp only [decide_eq_true_eq, List.length_append]
    omega
  · rw [rowCheck_congr ax g pre (pre ++ ext) a ?_]
    · exact hrow
    · intro p hp
      simp only [prefixConclusion, List.getElem?_append_left (hb' p hp)]

/-! ### Reading a position of the round's graph

`indexed g` pairs each triple with its position; the emitter's premise
indices are those positions. `mem_indexed_getElem?` is what turns a
premise index back into the triple the row was applied to. -/

theorem mem_indexFrom_getElem? {i : Nat} {gg : Graph} {x : Nat × Triple}
    (h : x ∈ indexFrom i gg) : i ≤ x.1 ∧ gg[x.1 - i]? = some x.2 := by
  induction gg generalizing i with
  | nil => cases h
  | cons t ts ih =>
    simp only [indexFrom, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨hle, hget⟩ := ih h
      refine ⟨by omega, ?_⟩
      have hpos : x.1 - i = (x.1 - (i + 1)) + 1 := by omega
      rw [hpos, List.getElem?_cons_succ]
      exact hget

theorem mem_indexed_getElem? {gg : Graph} {x : Nat × Triple} (h : x ∈ indexed gg) :
    gg[x.1]? = some x.2 := by
  have := (mem_indexFrom_getElem? (i := 0) (gg := gg) h).2
  simpa using this

/-- With `ss` the round's step list, reading premise index `p` gives
the triple at position `p` of the round's graph. -/
theorem prefixConclusion_of_steps {ss : List Step} {gg : Graph}
    (hss : ss.map (·.conclusion) = gg) (p : Nat) :
    prefixConclusion ss p = gg[p]? := by
  rw [← hss]
  simp [prefixConclusion, List.getElem?_map]

theorem length_of_steps {ss : List Step} {gg : Graph}
    (hss : ss.map (·.conclusion) = gg) : ss.length = gg.length := by
  rw [← hss]; simp

/-! ### One emitted step passes

Two lemmas, one per row shape, mirroring `annOne` / `annJoin` in
`Derivation.lean`. The row-specific content is isolated in `hrow`:
what a join row has to establish is a statement about TRIPLES —
the row applied to the two-element graph holding its two premises
yields the conclusion — with no step machinery in it. -/

/-- A step an `annOne` row emitted passes the check. -/
theorem annOne_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg)
    {r : RuleId} {f : Triple → List Triple}
    (hdisp : ∀ st : Step, st.rule = r → rowCheck ax g ss st = oneRow f ss st)
    {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ annOne r f x) : stepOk ax g ss a = true := by
  simp only [annOne, List.mem_map] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  have hlen : ss.length = gg.length := length_of_steps hss
  have hxlt : x.1 < gg.length := indexed_idx_lt hx
  simp only [stepOk, mkStep_premises, Bool.and_eq_true]
  refine ⟨by simp [hlen, hxlt], ?_⟩
  rw [hdisp _ rfl]
  simp only [oneRow, mkStep_conclusion, mkStep_premises,
    prefixConclusion_of_steps hss, mem_indexed_getElem? hx]
  exact decide_eq_true ht

/-- A step an `annJoin` row emitted passes the check, given that the
row really does license the conclusion from the two premises alone. -/
theorem annJoin_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg)
    {r : RuleId} {F : Graph → Triple → List Triple}
    (hdisp : ∀ st : Step, st.rule = r → rowCheck ax g ss st = joinRow F ss st)
    {x : Nat × Triple} (hx : x ∈ indexed gg)
    {sel : Triple → Bool} {mk : Triple → Option Triple}
    (hrow : ∀ (u t : Triple), sel u = true → mk u = some t → t ∈ F [x.2, u] x.2)
    {a : Step} (ha : a ∈ annJoin r (indexed gg) x sel mk) :
    stepOk ax g ss a = true := by
  simp only [annJoin, List.mem_filterMap, List.mem_filter] at ha
  obtain ⟨y, ⟨hy, hsel⟩, hmk⟩ := ha
  cases hm : mk y.2 with
  | none => rw [hm] at hmk; simp at hmk
  | some t =>
    rw [hm] at hmk
    simp only [Option.map_some, Option.some.injEq] at hmk
    subst hmk
    have hlen : ss.length = gg.length := length_of_steps hss
    have hxlt : x.1 < gg.length := indexed_idx_lt hx
    have hylt : y.1 < gg.length := indexed_idx_lt hy
    simp only [stepOk, mkStep_premises, Bool.and_eq_true]
    refine ⟨by simp [hlen, hxlt, hylt], ?_⟩
    rw [hdisp _ rfl]
    simp only [joinRow, mkStep_conclusion, mkStep_premises,
      prefixConclusion_of_steps hss, mem_indexed_getElem? hx,
      mem_indexed_getElem? hy]
    exact decide_eq_true (hrow y.2 t hsel hm)

/-! ### The fourteen rows

One lemma per annotated row: every step the row emits passes the
check. The join rows carry the row-specific content — that the row,
applied to the two-element graph holding just its two premises,
yields the conclusion. That is what makes the checker independent of
the graph the emitter ran over. -/

theorem rdfs7Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs7Ann (indexed gg) x) : stepOk ax g ss a = true := by
  cases hs : x.2.s with
  | bnode b => simp [rdfs7Ann, hs] at ha
  | iri p =>
    cases ho : x.2.o with
    | bnode _ => simp [rdfs7Ann, hs, ho] at ha
    | literal _ => simp [rdfs7Ann, hs, ho] at ha
    | tripleTerm _ _ _ => simp [rdfs7Ann, hs, ho] at ha
    | iri q =>
      by_cases hp : x.2.p = rdfsSubPropertyOf
      · simp only [rdfs7Ann, hs, ho, hp, beq_self_eq_true, if_true] at ha
        refine annJoin_stepOk (F := rdfs7For) hss
          (fun st h => by simp only [rowCheck, h]) hx ?_ ha
        intro u t hsel hmk
        simp only [Option.some.injEq] at hmk
        subst hmk
        simp only [rdfs7For, hs, ho, hp, beq_self_eq_true, if_true,
          triplesWithPredicate, List.mem_map, List.mem_filter]
        exact ⟨u, ⟨by simp, by simpa using hsel⟩, rfl⟩
      · have hp' : (x.2.p == rdfsSubPropertyOf) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
        simp [rdfs7Ann, hs, ho, hp'] at ha

theorem rdfs2Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs2Ann (indexed gg) x) : stepOk ax g ss a = true := by
  cases hs : x.2.s with
  | bnode b => simp [rdfs2Ann, hs] at ha
  | iri p =>
    by_cases hp : x.2.p = rdfsDomain
    · simp only [rdfs2Ann, hs, hp, beq_self_eq_true, if_true] at ha
      refine annJoin_stepOk (F := rdfs2For) hss
        (fun st h => by simp only [rowCheck, h]) hx ?_ ha
      intro u t hsel hmk
      simp only [Option.some.injEq] at hmk
      subst hmk
      simp only [rdfs2For, hs, hp, beq_self_eq_true, if_true,
        triplesWithPredicate, List.mem_map, List.mem_filter]
      exact ⟨u, ⟨by simp, by simpa using hsel⟩, rfl⟩
    · have hp' : (x.2.p == rdfsDomain) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
      simp [rdfs2Ann, hs, hp'] at ha

theorem rdfs3Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs3Ann (indexed gg) x) : stepOk ax g ss a = true := by
  cases hs : x.2.s with
  | bnode b => simp [rdfs3Ann, hs] at ha
  | iri p =>
    by_cases hp : x.2.p = rdfsRange
    · simp only [rdfs3Ann, hs, hp, beq_self_eq_true, if_true] at ha
      refine annJoin_stepOk (F := rdfs3For) hss
        (fun st h => by simp only [rowCheck, h]) hx ?_ ha
      intro u t hsel hmk
      simp only [rdfs3For, hs, hp, beq_self_eq_true, if_true,
        triplesWithPredicate, List.mem_filterMap, List.mem_filter]
      exact ⟨u, ⟨by simp, by simpa using hsel⟩, hmk⟩
    · have hp' : (x.2.p == rdfsRange) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
      simp [rdfs3Ann, hs, hp'] at ha

theorem rdfs9Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs9Ann (indexed gg) x) : stepOk ax g ss a = true := by
  cases ho : x.2.o with
  | bnode _ => simp [rdfs9Ann, ho] at ha
  | literal _ => simp [rdfs9Ann, ho] at ha
  | tripleTerm _ _ _ => simp [rdfs9Ann, ho] at ha
  | iri c =>
    by_cases hp : x.2.p = rdfType
    · simp only [rdfs9Ann, ho, hp, beq_self_eq_true, if_true] at ha
      refine annJoin_stepOk (F := rdfs9For) hss
        (fun st h => by simp only [rowCheck, h]) hx ?_ ha
      intro u t hsel hmk
      simp only [Option.some.injEq] at hmk
      subst hmk
      simp only [rdfs9For, ho, hp, beq_self_eq_true, if_true,
        objectsOf, List.mem_map, List.mem_filter]
      exact ⟨u.o, ⟨u, ⟨by simp, by simpa using hsel⟩, rfl⟩, rfl⟩
    · have hp' : (x.2.p == rdfType) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
      simp [rdfs9Ann, ho, hp'] at ha

theorem rdfs11Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs11Ann (indexed gg) x) : stepOk ax g ss a = true := by
  by_cases hp : x.2.p = rdfsSubClassOf
  · cases hsub : x.2.o.toSubject? with
    | none => simp [rdfs11Ann, hp, hsub] at ha
    | some bsub =>
      simp only [rdfs11Ann, hp, hsub, beq_self_eq_true, if_true] at ha
      refine annJoin_stepOk (F := rdfs11For) hss
        (fun st h => by simp only [rowCheck, h]) hx ?_ ha
      intro u t hsel hmk
      simp only [Option.some.injEq] at hmk
      subst hmk
      simp only [rdfs11For, hp, hsub, beq_self_eq_true, if_true,
        objectsOf, List.mem_map, List.mem_filter]
      exact ⟨u.o, ⟨u, ⟨by simp, by simpa using hsel⟩, rfl⟩, rfl⟩
  · have hp' : (x.2.p == rdfsSubClassOf) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
    simp [rdfs11Ann, hp'] at ha

theorem rdfs5Ann_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {x : Nat × Triple} (hx : x ∈ indexed gg)
    {a : Step} (ha : a ∈ rdfs5Ann (indexed gg) x) : stepOk ax g ss a = true := by
  by_cases hp : x.2.p = rdfsSubPropertyOf
  · cases hsub : x.2.o.toSubject? with
    | none => simp [rdfs5Ann, hp, hsub] at ha
    | some bsub =>
      simp only [rdfs5Ann, hp, hsub, beq_self_eq_true, if_true] at ha
      refine annJoin_stepOk (F := rdfs5For) hss
        (fun st h => by simp only [rowCheck, h]) hx ?_ ha
      intro u t hsel hmk
      simp only [Option.some.injEq] at hmk
      subst hmk
      simp only [rdfs5For, hp, hsub, beq_self_eq_true, if_true,
        objectsOf, List.mem_map, List.mem_filter]
      exact ⟨u.o, ⟨u, ⟨by simp, by simpa using hsel⟩, rfl⟩, rfl⟩
  · have hp' : (x.2.p == rdfsSubPropertyOf) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hp
    simp [rdfs5Ann, hp'] at ha

/-- **Every step one annotated round emits passes the check.** The
fourteen rows, in `annStepConclusions`'s order. -/
theorem annStepConclusions_stepOk {ax g gg : Graph} {ss : List Step}
    (hss : ss.map (·.conclusion) = gg) {a : Step} (ha : a ∈ annStepConclusions gg) :
    stepOk ax g ss a = true := by
  simp only [annStepConclusions, List.mem_append, List.mem_flatMap] at ha
  rcases ha with
    ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
    obtain ⟨x, hx, hax⟩ := h
  · exact rdfs7Ann_stepOk hss hx hax
  · exact rdfs2Ann_stepOk hss hx hax
  · exact rdfs3Ann_stepOk hss hx hax
  · exact rdfs9Ann_stepOk hss hx hax
  · exact rdfs11Ann_stepOk hss hx hax
  · exact rdfs5Ann_stepOk hss hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax
  · exact annOne_stepOk hss (fun st h => by simp only [rowCheck, h]) hx hax

/-! ### Carrying the invariant through the loop and the seed -/

/-- A premise-free step reads nothing from the prefix, so a list of
them passes against any prefix. This is what covers `base` and
`axiomatic`. -/
theorem checkSteps_of_premiseFree (ax g : Graph) : ∀ (post pre : List Step),
    (∀ b ∈ post, b.premises = [] ∧ rowCheck ax g [] b = true) →
    checkSteps ax g pre post = true := by
  intro post
  induction post with
  | nil => intro pre _; rfl
  | cons b bs ih =>
    intro pre hall
    obtain ⟨hpe, hrc⟩ := hall b (List.mem_cons_self ..)
    simp only [checkSteps, Bool.and_eq_true]
    refine ⟨?_, ih _ (fun c hc => hall c (List.mem_cons_of_mem _ hc))⟩
    simp only [stepOk, hpe, List.all_nil, Bool.true_and]
    rw [rowCheck_congr ax g [] pre b (by simp [hpe])]
    exact hrc

theorem premiseFree_stepOk (ax g : Graph) (pre : List Step) (b : Step)
    (h : b.premises = [] ∧ rowCheck ax g [] b = true) : stepOk ax g pre b = true := by
  obtain ⟨hpe, hrc⟩ := h
  simp only [stepOk, hpe, List.all_nil, Bool.true_and]
  rw [rowCheck_congr ax g [] pre b (by simp [hpe])]
  exact hrc

theorem baseSteps_premiseFree (ax g : Graph) :
    ∀ b ∈ baseSteps g, b.premises = [] ∧ rowCheck ax g [] b = true := by
  intro b hb
  simp only [baseSteps, List.mem_map] at hb
  obtain ⟨t, ht, rfl⟩ := hb
  refine ⟨rfl, ?_⟩
  simp only [rowCheck, mkStep]
  exact decide_eq_true ht

theorem axiomSteps_premiseFree (ax g : Graph) :
    ∀ b ∈ axiomSteps ax, b.premises = [] ∧ rowCheck ax g [] b = true := by
  intro b hb
  simp only [axiomSteps, List.mem_map] at hb
  obtain ⟨t, ht, rfl⟩ := hb
  refine ⟨rfl, ?_⟩
  simp only [rowCheck, mkStep]
  exact decide_eq_true ht

/-- Deduplication preserves the invariant: `addAllAnn` appends only
steps it was given, and a step that passed against the shorter
prefix passes against the longer one (`stepOk_mono`). -/
theorem addAllAnn_checked (ax g : Graph) (as : List Step) :
    ∀ (gg : Graph) (ss : List Step),
      checkSteps ax g [] ss = true →
      (∀ b ∈ as, stepOk ax g ss b = true) →
      checkSteps ax g [] (addAllAnn gg ss as).2 = true := by
  induction as with
  | nil => intro gg ss h _; exact h
  | cons b bs ih =>
    intro gg ss h hb
    simp only [addAllAnn]
    by_cases hm : gg.mem b.conclusion
    · simp only [hm, if_pos]
      exact ih gg ss h (fun c hc => hb c (List.mem_cons_of_mem _ hc))
    · simp only [hm, Bool.false_eq_true, if_false]
      refine ih _ _ ?_ ?_
      · rw [checkSteps_snoc, h, hb b (List.mem_cons_self ..)]
        rfl
      · intro c hc
        exact stepOk_mono ax g ss [b] c (hb c (List.mem_cons_of_mem _ hc))

/-- The fixpoint loop preserves the invariant. -/
theorem fullClosureLoopAnn_checked (ax g : Graph) (fuel : Nat) :
    ∀ (gg : Graph) (ss : List Step),
      ss.map (·.conclusion) = gg →
      checkSteps ax g [] ss = true →
      checkSteps ax g [] (fullClosureLoopAnn gg ss fuel).2 = true := by
  induction fuel with
  | zero => intro gg ss _ h; exact h
  | succ n ih =>
    intro gg ss hss h
    simp only [fullClosureLoopAnn]
    by_cases hstop : (addAllAnn gg ss (annStepConclusions gg)).1.length = gg.length
    · simp only [hstop, if_pos]; exact h
    · simp only [hstop, if_false]
      refine ih _ _ (addAllAnn_snd _ _ _ hss) (addAllAnn_checked ax g _ _ _ h ?_)
      intro b hb
      exact annStepConclusions_stepOk hss hb

/-- The seed passes: `base` steps quote `g`, `axiomatic` steps quote
the axiom set, and neither reads the prefix. -/
theorem seedAnn_checked (D cmps : List WfIri) (g : Graph) :
    checkSteps (axiomaticTriples D cmps) g [] (seedAnn D cmps g).2 = true := by
  unfold seedAnn
  refine addAllAnn_checked _ _ _ _ _ ?_ ?_
  · exact checkSteps_of_premiseFree _ _ _ _ (baseSteps_premiseFree _ g)
  · intro b hb
    exact premiseFree_stepOk _ _ _ b (axiomSteps_premiseFree _ g b hb)

/-- **The round trip.** Everything the emitter emits, the checker
accepts — for EVERY datatype map `D`, `rdf:_n` slice `cmps` and graph
`g`. Unconditional: no hypothesis on any of them.

With `checkDerivation_sound` the two directions are both theorems:
the checker accepts nothing underivable, and rejects nothing this
engine derives. The `#guard`s in `DerivationCheckTests.lean` are the
gate for the third direction, which no theorem here states — that a
defective derivation is rejected. -/
theorem checkDerivation_roundTrip (D cmps : List WfIri) (g : Graph) :
    checkDerivation (axiomaticTriples D cmps) g (fullClosureWithProof D cmps g).2
      = true := by
  simp only [checkDerivation, fullClosureWithProof, List.toList_toArray, fullClosureAnn]
  exact fullClosureLoopAnn_checked _ _ _ _ _ (seedAnn_snd D cmps g) (seedAnn_checked D cmps g)

/-- The consequence a caller wants stated in one place: the graph the
engine serves and the derivation it emits go together — the checker
accepts the derivation, and every step of it is derivable. -/
theorem fullClosureWithProof_checked (D cmps : List WfIri) (g : Graph)
    (i : Nat) (hi : i < (fullClosureWithProof D cmps g).2.size) :
    DerivesFull (axiomaticTriples D cmps) g
      ((fullClosureWithProof D cmps g).2[i]!).conclusion :=
  checkDerivation_sound (checkDerivation_roundTrip D cmps g) i hi

end L4Factoidal.RDFS
