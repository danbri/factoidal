/-
L4Factoidal.Unified.Datalog — stage 3 of
https://github.com/danbri/factoidal/issues/598: Datalog as the NAMED
COMPUTABLE-FRAGMENT CLASS of the unified model theory (design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §3 stage 3,
§4.3, §5.6).

## The class

A `DatalogProgram` is a finite set of DEFINITE HORN rules over n-ary
predications: every head is an ATOM (no falsity heads — the OWL RL
clash rows are outside), every head variable occurs in the body (no
existential heads — rdfD1-style surrogate-blank-node minting is outside
BY CONSTRUCTION: the `wf` field of `DatalogProgram` is a proof, so a
program with an existential head cannot be built), and there are no
function symbols (a `DTerm` is a variable or a constant). The variable
discipline is the same colon-free spelling every Unified schema row
uses (`Unified/RdfEmbed.lean`): rule variables are colon-free, rule
constants contain a colon, so the universal closure in `DRule.sentence`
can never capture a constant.

## The three layers, and the two generic theorems

1. OPERATIONAL — `DatalogProgram.step` (one naive materialisation
   round: every rule fired at every matching substitution) and
   `DatalogProgram.lfp` (the fuel-bounded least fixpoint, the shape
   `RDFS/FixedPoint.lean` and the closure engines use).
   `FuelAdequate` is saturation — one more step derives nothing new —
   with the executable check `saturatedCheck` dischargeable by
   `decide` on concrete inputs (the `rhoDfClosedCheck` pattern).
2. PROOF-THEORETIC — `DatalogProgram.Derives`, the rule relation
   (base facts + one constructor for a rule instance). `lfp_sound`
   and `derives_mem_lfp` tie it to the operational layer in both
   directions (the second under `FuelAdequate`).
3. MODEL-THEORETIC — `DRule.sentence` (the universally closed
   implication), `DatalogProgram.toSchema` (design doc §3), and the
   TWO GENERIC THEOREMS proved ONCE for every program:

   * `datalog_lfp_sound` — every atom of the least fixpoint is
     entailed by the program-as-schema plus the facts, over EVERY CL
     interpretation (`step`-shaped induction, the
     `rhoDf_derives_holds` shape the stage 2 salvage prescribed);
   * `datalog_lfp_complete` — every GROUND ATOM the schema plus facts
     entail is in the fuel-adequate least fixpoint. The countermodel
     is the Herbrand interpretation of the fixpoint itself
     (`herbInterp`: `dom = String`, names denote themselves, a
     relation holds exactly when the corresponding ground atom is in
     the fixpoint) — the generic form of the construction
     `RDFS/RhoDfCompleteness.lean` performs for ρdf.

   `datalog_lfp_iff_entails` is the two directions as one iff — the
   design document §4.3 gate theorem. Completeness is claimed for
   GROUND-ATOMIC consequences only (§5.6): that is the whole claim
   level of the class, stated, not a proof gap.

`Unified/DatalogClosures.lean` exhibits the tree's closure engines as
programs of this class and records what falls outside it.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RhoDfSchema

namespace L4Factoidal.Unified

/-! ## Terms, atoms, rules, programs -/

/-- A Datalog term: a variable or a constant. No function symbols
(design document §3 — "no function symbols in derived positions";
here in NO position, which only shrinks the class). -/
inductive DTerm where
  | v (n : String)
  | c (s : String)
  | lit (l : RDF.WfLiteral)
  deriving DecidableEq, Repr

/-- An n-ary predication with the predicate itself a term — the
operator-position reading of the design document §2.3 generalised
from the binary `HAtom` to any arity, per the stage 2 salvage's
build order. A VARIABLE predicate is legal (CL is unsegregated);
rdfs7's head uses exactly that. -/
structure DAtom where
  pred : DTerm
  args : List DTerm
  deriving DecidableEq, Repr

/-- A definite Horn rule: head atom, body atoms. Definiteness (every
head variable occurs in the body) is enforced at the PROGRAM level by
`DatalogProgram.wf`. -/
structure DRule where
  head : DAtom
  body : List DAtom
  deriving DecidableEq, Repr

/-! ### Groundness, variables, well-formedness -/

def DTerm.groundB : DTerm → Bool
  | .v _ => false
  | .c _ => true
  | .lit _ => true

def DAtom.groundB (a : DAtom) : Bool :=
  a.pred.groundB && a.args.all DTerm.groundB

def DTerm.varList : DTerm → List String
  | .v n => [n]
  | .c _ => []
  | .lit _ => []

def DAtom.varList (a : DAtom) : List String :=
  a.pred.varList ++ a.args.flatMap DTerm.varList

def DRule.bodyVars (r : DRule) : List String :=
  r.body.flatMap DAtom.varList

/-- The rule's binder list: body variables then head variables
(duplicates harmless under `Sentence.all`). -/
def DRule.vars (r : DRule) : List String :=
  r.bodyVars ++ r.head.varList

/-- The colon discipline of `Unified/RdfEmbed.lean`, at the rule
level: a variable name is colon-free, a constant contains a colon.
This is what makes the universal closure capture-free with ONE
side-condition-free satisfaction lemma. -/
def DTerm.wfB : DTerm → Bool
  | .v n => !(n.toList.contains ':')
  | .c s => s.toList.contains ':'
  | .lit _ => true

/-- **Literal-freeness**: no `DTerm.lit` occurs. The colon discipline
(`wfB`) is about capture under the universal closure and a literal
term captures nothing, so `wfB` holds of every literal. What a literal
DOES break is the STRING Herbrand universe of `herbInterp`, whose
domain is the constant names: a literal term is rigid and denotes
outside that universe. Every theorem that builds or reads `herbInterp`
carries this predicate as a hypothesis; the model-theoretic layer
(`DRule.sentence`, `satisfies_ruleSentence_iff`) does not need it. -/
def DTerm.litFreeB : DTerm → Bool
  | .v _ => true
  | .c _ => true
  | .lit _ => false

def DAtom.litFreeB (a : DAtom) : Bool :=
  a.pred.litFreeB && a.args.all DTerm.litFreeB

def DRule.litFreeB (r : DRule) : Bool :=
  r.head.litFreeB && r.body.all DAtom.litFreeB

@[simp] theorem DTerm.litFreeB_v (n : String) :
    (DTerm.v n).litFreeB = true := rfl

@[simp] theorem DTerm.litFreeB_c (s : String) :
    (DTerm.c s).litFreeB = true := rfl

@[simp] theorem DTerm.litFreeB_lit (l : RDF.WfLiteral) :
    (DTerm.lit l).litFreeB = false := rfl

def DAtom.wfB (a : DAtom) : Bool :=
  a.pred.wfB && a.args.all DTerm.wfB

/-- Definiteness: every head variable occurs in the body. The rules
this EXCLUDES are exactly the witness-minting ones — rdfD1's
surrogate blank nodes, `owl:someValuesFrom` generation (design
document §5.6). -/
def DRule.definiteB (r : DRule) : Bool :=
  r.head.varList.all (fun n => r.bodyVars.contains n)

def DRule.wfB (r : DRule) : Bool :=
  r.head.wfB && r.body.all DAtom.wfB && r.definiteB

/-- A Datalog program: finitely many rules, well-formed BY
CONSTRUCTION — the `wf` proof field means no value of this type
contains an existential head, a falsity head, or a
discipline-breaking name. -/
structure DatalogProgram where
  rules : List DRule
  wf : rules.all DRule.wfB = true

theorem DatalogProgram.rule_wf (p : DatalogProgram) :
    ∀ r ∈ p.rules, r.wfB = true :=
  fun r hr => List.all_eq_true.mp p.wf r hr

theorem DRule.wf_head {r : DRule} (h : r.wfB = true) : r.head.wfB = true := by
  simp only [DRule.wfB, Bool.and_eq_true] at h
  exact h.1.1

theorem DRule.wf_body {r : DRule} (h : r.wfB = true) :
    ∀ a ∈ r.body, a.wfB = true := by
  simp only [DRule.wfB, Bool.and_eq_true] at h
  exact fun a ha => List.all_eq_true.mp h.1.2 a ha

theorem DRule.wf_definite {r : DRule} (h : r.wfB = true) :
    r.definiteB = true := by
  simp only [DRule.wfB, Bool.and_eq_true] at h
  exact h.2

theorem DAtom.wf_pred {a : DAtom} (h : a.wfB = true) : a.pred.wfB = true := by
  simp only [DAtom.wfB, Bool.and_eq_true] at h
  exact h.1

theorem DAtom.wf_args {a : DAtom} (h : a.wfB = true) :
    ∀ t ∈ a.args, t.wfB = true := by
  simp only [DAtom.wfB, Bool.and_eq_true] at h
  exact fun t ht => List.all_eq_true.mp h.2 t ht

theorem DTerm.varList_no_colon {t : DTerm} (h : t.wfB = true) :
    ∀ n ∈ t.varList, ':' ∉ n.toList := by
  cases t with
  | v m =>
      intro n hn
      simp only [DTerm.varList, List.mem_singleton] at hn
      subst hn
      simp only [DTerm.wfB, Bool.not_eq_true'] at h
      intro hc
      have hcon : n.toList.contains ':' = true := List.contains_iff_mem.mpr hc
      rw [h] at hcon
      cases hcon
  | c s => intro n hn; simp [DTerm.varList] at hn
  | lit l => intro n hn; simp [DTerm.varList] at hn

theorem DAtom.varList_no_colon {a : DAtom} (h : a.wfB = true) :
    ∀ n ∈ a.varList, ':' ∉ n.toList := by
  intro n hn
  rcases List.mem_append.mp hn with hp | hargs
  · exact DTerm.varList_no_colon (DAtom.wf_pred h) n hp
  · obtain ⟨t, ht, hnt⟩ := List.mem_flatMap.mp hargs
    exact DTerm.varList_no_colon (DAtom.wf_args h t ht) n hnt

theorem DRule.vars_no_colon {r : DRule} (h : r.wfB = true) :
    ∀ n ∈ r.vars, ':' ∉ n.toList := by
  intro n hn
  rcases List.mem_append.mp hn with hb | hh
  · obtain ⟨a, ha, hna⟩ := List.mem_flatMap.mp hb
    exact DAtom.varList_no_colon (DRule.wf_body h a ha) n hna
  · exact DAtom.varList_no_colon (DRule.wf_head h) n hh

theorem DRule.head_scoped (r : DRule) : ∀ n ∈ r.head.varList, n ∈ r.vars :=
  fun _ hn => List.mem_append_right _ hn

theorem DRule.body_scoped (r : DRule) :
    ∀ a ∈ r.body, ∀ n ∈ a.varList, n ∈ r.vars :=
  fun a ha _ hn =>
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, ha, hn⟩)

/-! ### Substitution -/

/-- The constant a term becomes under a (total, ground) substitution. -/
def DTerm.substVal (θ : String → String) : DTerm → String
  | .v n => θ n
  | .c s => s
  | .lit _ => ""

/-- Grounding substitution: every variable to a constant. -/
def DTerm.subst (θ : String → String) : DTerm → DTerm
  | .v n => .c (θ n)
  | .c s => .c s
  | .lit l => .lit l

theorem DTerm.subst_eq_substVal (θ : String → String) :
    ∀ t : DTerm, t.litFreeB = true → t.subst θ = .c (t.substVal θ)
  | .v _, _ => rfl
  | .c _, _ => rfl
  | .lit _, h => by simp [DTerm.litFreeB] at h

def DAtom.subst (θ : String → String) (a : DAtom) : DAtom :=
  ⟨a.pred.subst θ, a.args.map (DTerm.subst θ)⟩

theorem DTerm.subst_ground (θ : String → String) (t : DTerm) :
    (t.subst θ).groundB = true := by
  cases t <;> rfl

theorem DAtom.subst_ground (θ : String → String) (a : DAtom) :
    (a.subst θ).groundB = true := by
  simp only [DAtom.subst, DAtom.groundB, Bool.and_eq_true, List.all_eq_true]
  exact ⟨DTerm.subst_ground θ a.pred,
         fun t ht => by
           obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
           exact DTerm.subst_ground θ u⟩

theorem DTerm.subst_congr {θ1 θ2 : String → String} :
    ∀ {t : DTerm}, (∀ n ∈ t.varList, θ1 n = θ2 n) → t.subst θ1 = t.subst θ2
  | .v n, h => by
      simp only [DTerm.subst, DTerm.c.injEq]
      exact h n (by simp [DTerm.varList])
  | .c _, _ => rfl
  | .lit _, _ => rfl

theorem DAtom.subst_congr {θ1 θ2 : String → String} {a : DAtom}
    (h : ∀ n ∈ a.varList, θ1 n = θ2 n) : a.subst θ1 = a.subst θ2 := by
  unfold DAtom.subst
  rw [DTerm.subst_congr (fun n hn => h n (List.mem_append_left _ hn)),
      List.map_congr_left (fun t ht =>
        DTerm.subst_congr (fun n hn =>
          h n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hn⟩))))]

theorem DTerm.subst_of_ground {t : DTerm} (h : t.groundB = true)
    (θ : String → String) : t.subst θ = t := by
  cases t with
  | v n => simp [DTerm.groundB] at h
  | c s => rfl
  | lit l => rfl

theorem DAtom.subst_of_ground {a : DAtom} (h : a.groundB = true)
    (θ : String → String) : a.subst θ = a := by
  simp only [DAtom.groundB, Bool.and_eq_true, List.all_eq_true] at h
  unfold DAtom.subst
  rw [DTerm.subst_of_ground h.1,
      List.map_congr_left (fun t ht => DTerm.subst_of_ground (h.2 t ht) θ)]
  simp

/-! ## Matching

The executable substitution search of `DRule.conclusions`: match the
body atoms against the fact set left to right, threading a binding
list. `matchTerm/matchArgs/matchAtom/matchBody` carry a soundness
triple (the found binding extends the input, binds every pattern
variable, and instantiates each pattern to a fact) and a completeness
triple (any substitution that grounds the body into the fact set is
found, with agreeing bindings). -/

abbrev Bindings := List (String × String)

def blookup : Bindings → String → Option String
  | [], _ => none
  | (m, v) :: r, n => if n = m then some v else blookup r n

/-- The substitution a binding list denotes (unbound names map to
themselves; definiteness makes that branch irrelevant for heads). -/
def bsubst (b : Bindings) : String → String :=
  fun n => (blookup b n).getD n

/-- `b'` preserves every binding of `b`. -/
def BindExtends (b b' : Bindings) : Prop :=
  ∀ n v, blookup b n = some v → blookup b' n = some v

theorem BindExtends.refl (b : Bindings) : BindExtends b b := fun _ _ h => h

theorem BindExtends.trans {a b c : Bindings} (h1 : BindExtends a b)
    (h2 : BindExtends b c) : BindExtends a c :=
  fun n v h => h2 n v (h1 n v h)

/-- Every variable of the term is bound. -/
def DTerm.boundIn (b : Bindings) : DTerm → Prop
  | .v n => (blookup b n).isSome
  | .c _ => True
  | .lit _ => True

theorem DTerm.boundIn_mono {b b' : Bindings} (h : BindExtends b b') :
    ∀ {t : DTerm}, t.boundIn b → t.boundIn b'
  | .v n, hb => by
      simp only [DTerm.boundIn, Option.isSome_iff_exists] at hb ⊢
      obtain ⟨v, hv⟩ := hb
      exact ⟨v, h n v hv⟩
  | .c _, _ => trivial
  | .lit _, _ => trivial

theorem DTerm.subst_bsubst_mono {b b' : Bindings} (h : BindExtends b b') :
    ∀ {t : DTerm}, t.boundIn b → t.subst (bsubst b) = t.subst (bsubst b')
  | .v n, hb => by
      simp only [DTerm.boundIn, Option.isSome_iff_exists] at hb
      obtain ⟨v, hv⟩ := hb
      simp [DTerm.subst, bsubst, hv, h n v hv]
  | .c _, _ => rfl
  | .lit _, _ => rfl

def matchTerm (b : Bindings) : DTerm → DTerm → Option Bindings
  | .c s, .c g => if s = g then some b else none
  | .c _, .v _ => none
  | .c _, .lit _ => none
  | .v n, .c g =>
      match blookup b n with
      | some v => if v = g then some b else none
      | none => some ((n, g) :: b)
  | .v _, .v _ => none
  | .v _, .lit _ => none
  | .lit _, .c _ => none
  | .lit _, .v _ => none
  | .lit l, .lit g => if l = g then some b else none

def matchArgs : Bindings → List DTerm → List DTerm → Option Bindings
  | b, [], [] => some b
  | b, p :: pr, g :: gr =>
      match matchTerm b p g with
      | some b1 => matchArgs b1 pr gr
      | none => none
  | _, _, _ => none

def matchAtom (b : Bindings) (pat fact : DAtom) : Option Bindings :=
  match matchTerm b pat.pred fact.pred with
  | some b1 => matchArgs b1 pat.args fact.args
  | none => none

def matchBody (facts : List DAtom) : Bindings → List DAtom → List Bindings
  | b, [] => [b]
  | b, pat :: rest =>
      facts.flatMap (fun fact =>
        match matchAtom b pat fact with
        | some b1 => matchBody facts b1 rest
        | none => [])

/-! ### Matching soundness -/

theorem matchTerm_sound {pat gt : DTerm} {b b' : Bindings}
    (h : matchTerm b pat gt = some b') :
    BindExtends b b' ∧ pat.boundIn b' ∧ pat.subst (bsubst b') = gt := by
  cases pat with
  | c s =>
      cases gt with
      | c g =>
          simp only [matchTerm] at h
          split at h
          · next heq =>
              cases h
              exact ⟨BindExtends.refl _, trivial, by simp [DTerm.subst, heq]⟩
          · cases h
      | v m => simp [matchTerm] at h
      | lit g => simp [matchTerm] at h
  | lit l =>
      cases gt with
      | c g => simp [matchTerm] at h
      | v m => simp [matchTerm] at h
      | lit g =>
          simp only [matchTerm] at h
          split at h
          · next heq =>
              cases h
              exact ⟨BindExtends.refl _, trivial, by simp [DTerm.subst, heq]⟩
          · cases h
  | v n =>
      cases gt with
      | c g =>
          simp only [matchTerm] at h
          split at h
          · next v hv =>
              split at h
              · next hveq =>
                  cases h
                  refine ⟨BindExtends.refl _, by simp [DTerm.boundIn, hv], ?_⟩
                  simp [DTerm.subst, bsubst, hv, hveq]
              · cases h
          · next hnone =>
              cases h
              refine ⟨?_, ?_, ?_⟩
              · intro m v hmv
                by_cases hm : m = n
                · rw [hm] at hmv; rw [hmv] at hnone; cases hnone
                · simp [blookup, hm, hmv]
              · simp [DTerm.boundIn, blookup]
              · simp [DTerm.subst, bsubst, blookup]
      | v m => simp [matchTerm] at h
      | lit g => simp [matchTerm] at h

theorem matchArgs_sound :
    ∀ {pats gts : List DTerm} {b b' : Bindings},
      matchArgs b pats gts = some b' →
      BindExtends b b' ∧ (∀ t ∈ pats, t.boundIn b') ∧
        pats.map (DTerm.subst (bsubst b')) = gts
  | [], [], b, b' => by
      intro h
      cases h
      exact ⟨BindExtends.refl _, by simp, by simp⟩
  | [], _ :: _, b, b' => by intro h; simp [matchArgs] at h
  | _ :: _, [], b, b' => by intro h; simp [matchArgs] at h
  | p :: pr, g :: gr, b, b' => by
      intro h
      simp only [matchArgs] at h
      split at h
      · next b1 hb1 =>
          obtain ⟨hx1, hbd1, hs1⟩ := matchTerm_sound hb1
          obtain ⟨hx2, hbd2, hs2⟩ := matchArgs_sound h
          refine ⟨hx1.trans hx2, ?_, ?_⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact DTerm.boundIn_mono hx2 hbd1
            · exact hbd2 t ht
          · simp only [List.map_cons, hs2]
            rw [← DTerm.subst_bsubst_mono hx2 hbd1, hs1]
      · cases h

theorem matchAtom_sound {b b' : Bindings} {pat fact : DAtom}
    (h : matchAtom b pat fact = some b') :
    BindExtends b b' ∧ (pat.pred.boundIn b' ∧ ∀ t ∈ pat.args, t.boundIn b') ∧
      pat.subst (bsubst b') = fact := by
  unfold matchAtom at h
  split at h
  · next b1 hb1 =>
      obtain ⟨hx1, hbd1, hs1⟩ := matchTerm_sound hb1
      obtain ⟨hx2, hbd2, hs2⟩ := matchArgs_sound h
      refine ⟨hx1.trans hx2, ⟨DTerm.boundIn_mono hx2 hbd1, hbd2⟩, ?_⟩
      cases fact with
      | mk fp fargs =>
          unfold DAtom.subst
          simp only [DAtom.mk.injEq]
          exact ⟨by rw [← DTerm.subst_bsubst_mono hx2 hbd1, hs1], hs2⟩
  · cases h

theorem matchBody_sound (facts : List DAtom) :
    ∀ {pats : List DAtom} {b b' : Bindings},
      b' ∈ matchBody facts b pats →
      BindExtends b b' ∧
        ∀ pat ∈ pats,
          (pat.pred.boundIn b' ∧ ∀ t ∈ pat.args, t.boundIn b') ∧
            pat.subst (bsubst b') ∈ facts
  | [], b, b' => by
      intro h
      simp only [matchBody, List.mem_singleton] at h
      subst h
      exact ⟨BindExtends.refl _, by simp⟩
  | pat :: rest, b, b' => by
      intro h
      simp only [matchBody] at h
      obtain ⟨fact, hfact, hmem⟩ := List.mem_flatMap.mp h
      split at hmem
      · next b1 hb1 =>
          obtain ⟨hx1, hbd1, hs1⟩ := matchAtom_sound hb1
          obtain ⟨hx2, hrest⟩ := matchBody_sound facts hmem
          refine ⟨hx1.trans hx2, ?_⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · refine ⟨⟨DTerm.boundIn_mono hx2 hbd1.1,
                     fun t ht => DTerm.boundIn_mono hx2 (hbd1.2 t ht)⟩, ?_⟩
            have heq : q.subst (bsubst b') = q.subst (bsubst b1) := by
              unfold DAtom.subst
              rw [DTerm.subst_bsubst_mono hx2 hbd1.1,
                  List.map_congr_left (fun t ht =>
                    (DTerm.subst_bsubst_mono hx2 (hbd1.2 t ht)).symm)]
            rw [heq, hs1]
            exact hfact
          · exact hrest q hq
      · simp at hmem

/-! ### Matching completeness -/

/-- Every binding agrees with the target substitution. -/
def BindAgrees (θ : String → String) (b : Bindings) : Prop :=
  ∀ n v, blookup b n = some v → v = θ n

theorem bindAgrees_nil (θ : String → String) : BindAgrees θ [] := by
  intro n v h; simp [blookup] at h

theorem matchTerm_complete {θ : String → String} {b : Bindings}
    (ha : BindAgrees θ b) (pat : DTerm) :
    ∃ b', matchTerm b pat (pat.subst θ) = some b' ∧ BindAgrees θ b' ∧
      BindExtends b b' ∧ ∀ n ∈ pat.varList, blookup b' n = some (θ n) := by
  cases pat with
  | c s =>
      exact ⟨b, by simp [DTerm.subst, matchTerm], ha, BindExtends.refl _,
             by simp [DTerm.varList]⟩
  | lit l =>
      exact ⟨b, by simp [DTerm.subst, matchTerm], ha, BindExtends.refl _,
             by simp [DTerm.varList]⟩
  | v n =>
      cases hl : blookup b n with
      | some v =>
          have hv : v = θ n := ha n v hl
          refine ⟨b, ?_, ha, BindExtends.refl _, ?_⟩
          · simp [DTerm.subst, matchTerm, hl, hv]
          · intro m hm
            simp only [DTerm.varList, List.mem_singleton] at hm
            subst hm
            rw [hl, hv]
      | none =>
          refine ⟨(n, θ n) :: b, by simp [DTerm.subst, matchTerm, hl], ?_, ?_, ?_⟩
          · intro m v hmv
            by_cases hm : m = n
            · subst hm
              simp [blookup] at hmv
              exact hmv.symm
            · simp only [blookup, if_neg hm] at hmv
              exact ha m v hmv
          · intro m v hmv
            by_cases hm : m = n
            · subst hm; rw [hmv] at hl; cases hl
            · simp [blookup, hm, hmv]
          · intro m hm
            simp only [DTerm.varList, List.mem_singleton] at hm
            subst hm
            simp [blookup]

theorem matchArgs_complete {θ : String → String} :
    ∀ (pats : List DTerm) {b : Bindings}, BindAgrees θ b →
      ∃ b', matchArgs b pats (pats.map (DTerm.subst θ)) = some b' ∧
        BindAgrees θ b' ∧ BindExtends b b' ∧
        ∀ n ∈ pats.flatMap DTerm.varList, blookup b' n = some (θ n)
  | [], b, ha => ⟨b, rfl, ha, BindExtends.refl _, by simp⟩
  | p :: pr, b, ha => by
      obtain ⟨b1, hm1, ha1, hx1, hbind1⟩ := matchTerm_complete ha p
      obtain ⟨b', hm2, ha2, hx2, hbind2⟩ := matchArgs_complete pr ha1
      refine ⟨b', ?_, ha2, hx1.trans hx2, ?_⟩
      · simp only [List.map_cons, matchArgs, hm1]
        exact hm2
      · intro n hn
        simp only [List.flatMap_cons, List.mem_append] at hn
        rcases hn with hp | hrest
        · exact hx2 n (θ n) (hbind1 n hp)
        · exact hbind2 n hrest

theorem matchAtom_complete {θ : String → String} {b : Bindings}
    (ha : BindAgrees θ b) (pat : DAtom) :
    ∃ b', matchAtom b pat (pat.subst θ) = some b' ∧ BindAgrees θ b' ∧
      BindExtends b b' ∧ ∀ n ∈ pat.varList, blookup b' n = some (θ n) := by
  obtain ⟨b1, hm1, ha1, hx1, hbind1⟩ := matchTerm_complete ha pat.pred
  obtain ⟨b', hm2, ha2, hx2, hbind2⟩ := matchArgs_complete pat.args ha1
  refine ⟨b', ?_, ha2, hx1.trans hx2, ?_⟩
  · unfold matchAtom DAtom.subst
    simp only [hm1]
    exact hm2
  · intro n hn
    rcases List.mem_append.mp hn with hp | hargs
    · exact hx2 n (θ n) (hbind1 n hp)
    · exact hbind2 n hargs

theorem matchBody_complete (facts : List DAtom) {θ : String → String} :
    ∀ (pats : List DAtom) {b : Bindings}, BindAgrees θ b →
      (∀ pat ∈ pats, pat.subst θ ∈ facts) →
      ∃ b' ∈ matchBody facts b pats, BindAgrees θ b' ∧ BindExtends b b' ∧
        ∀ n ∈ pats.flatMap DAtom.varList, blookup b' n = some (θ n)
  | [], b, ha, _ => ⟨b, by simp [matchBody], ha, BindExtends.refl _, by simp⟩
  | pat :: rest, b, ha, hin => by
      obtain ⟨b1, hm1, ha1, hx1, hbind1⟩ := matchAtom_complete ha pat
      obtain ⟨b', hmem, ha2, hx2, hbind2⟩ :=
        matchBody_complete facts rest ha1 (fun q hq => hin q (by simp [hq]))
      refine ⟨b', ?_, ha2, hx1.trans hx2, ?_⟩
      · simp only [matchBody]
        refine List.mem_flatMap.mpr ⟨pat.subst θ, hin pat (by simp), ?_⟩
        simp only [hm1]
        exact hmem
      · intro n hn
        simp only [List.flatMap_cons, List.mem_append] at hn
        rcases hn with hp | hrest
        · exact hx2 n (θ n) (hbind1 n hp)
        · exact hbind2 n hrest

/-! ## One round, the least fixpoint, saturation -/

/-- Every conclusion one rule licenses from the fact set. -/
def DRule.conclusions (r : DRule) (facts : List DAtom) : List DAtom :=
  (matchBody facts [] r.body).map (fun b => r.head.subst (bsubst b))

/-- One naive materialisation round: the conclusions only (design
document §3; the fixpoint accumulates). -/
def DatalogProgram.step (p : DatalogProgram) (facts : List DAtom) :
    List DAtom :=
  p.rules.flatMap (fun r => r.conclusions facts)

/-- The fuel-bounded least fixpoint: the facts, then each round's NEW
conclusions appended (the `RDFS/FixedPoint.lean` shape). -/
def DatalogProgram.lfp (p : DatalogProgram) (facts : List DAtom) :
    Nat → List DAtom
  | 0 => facts
  | n + 1 =>
      let cur := p.lfp facts n
      cur ++ (p.step cur).filter (fun a => !decide (a ∈ cur))

/-- Fuel adequacy = saturation: one more round derives nothing new.
The design document §4.3's `FuelAdequate` hypothesis. -/
def DatalogProgram.FuelAdequate (p : DatalogProgram) (facts : List DAtom)
    (fuel : Nat) : Prop :=
  ∀ a ∈ p.step (p.lfp facts fuel), a ∈ p.lfp facts fuel

/-- The executable saturation check (the `rhoDfClosedCheck` pattern:
`decide`-dischargeable on concrete inputs). -/
def DatalogProgram.saturatedCheck (p : DatalogProgram) (facts : List DAtom)
    (fuel : Nat) : Bool :=
  (p.step (p.lfp facts fuel)).all (fun a => decide (a ∈ p.lfp facts fuel))

theorem DatalogProgram.fuelAdequate_of_check {p : DatalogProgram}
    {facts : List DAtom} {fuel : Nat}
    (h : p.saturatedCheck facts fuel = true) : p.FuelAdequate facts fuel :=
  fun a ha => of_decide_eq_true (List.all_eq_true.mp h a ha)

theorem DatalogProgram.lfp_extensive (p : DatalogProgram)
    (facts : List DAtom) : ∀ (n : Nat), ∀ a ∈ facts, a ∈ p.lfp facts n
  | 0, _, ha => ha
  | n + 1, a, ha =>
      List.mem_append_left _ (p.lfp_extensive facts n a ha)

/-! ## The rule relation (proof-theoretic layer) -/

/-- `p.Derives facts a` — the atom is a fact, or the head of a rule
instance whose body atoms are all derivable. The generic counterpart
of `RDFS.Derives`. -/
inductive DatalogProgram.Derives (p : DatalogProgram) (facts : List DAtom) :
    DAtom → Prop where
  | fact {a : DAtom} (h : a ∈ facts) : Derives p facts a
  | rule {r : DRule} (hr : r ∈ p.rules) (θ : String → String)
      (hb : ∀ b ∈ r.body, Derives p facts (b.subst θ)) :
      Derives p facts (r.head.subst θ)

/-- Everything the least fixpoint holds is derivable — soundness of
the operational layer against the rule relation, at every fuel. -/
theorem DatalogProgram.lfp_sound (p : DatalogProgram) (facts : List DAtom) :
    ∀ (n : Nat) {a : DAtom}, a ∈ p.lfp facts n → p.Derives facts a := by
  intro n
  induction n with
  | zero => exact fun ha => Derives.fact ha
  | succ n ih =>
      intro a ha
      rcases List.mem_append.mp ha with hcur | hnew
      · exact ih hcur
      · have hstep : a ∈ p.step (p.lfp facts n) := (List.mem_filter.mp hnew).1
        obtain ⟨r, hr, hconc⟩ := List.mem_flatMap.mp hstep
        obtain ⟨bnd, hbnd, rfl⟩ := List.mem_map.mp hconc
        refine Derives.rule hr (bsubst bnd) ?_
        intro q hq
        exact ih ((matchBody_sound _ hbnd).2 q hq).2

/-- A rule instance whose body is already in the fact set has its
head among the rule's conclusions — matching completeness, packaged.
Needs definiteness: an existential-head instance is NOT found (its
head variable is bound by nothing). -/
theorem DRule.mem_conclusions_of_instance {r : DRule}
    (hdef : r.definiteB = true) {facts : List DAtom} {θ : String → String}
    (hb : ∀ a ∈ r.body, a.subst θ ∈ facts) :
    r.head.subst θ ∈ r.conclusions facts := by
  obtain ⟨b', hmem, hag, _, hcov⟩ :=
    matchBody_complete facts r.body (bindAgrees_nil θ) hb
  refine List.mem_map.mpr ⟨b', hmem, ?_⟩
  refine (DAtom.subst_congr ?_).symm
  intro n hn
  have hnb : n ∈ r.bodyVars :=
    List.contains_iff_mem.mp (List.all_eq_true.mp hdef n hn)
  have := hcov n hnb
  simp [bsubst, this]

/-- Everything derivable is in a fuel-adequate least fixpoint —
completeness of the operational layer against the rule relation. -/
theorem DatalogProgram.derives_mem_lfp {p : DatalogProgram}
    {facts : List DAtom} {fuel : Nat} (hfa : p.FuelAdequate facts fuel)
    {a : DAtom} (h : p.Derives facts a) : a ∈ p.lfp facts fuel := by
  induction h with
  | fact ha => exact p.lfp_extensive facts fuel _ ha
  | rule hr θ hb ih =>
      refine hfa _ (List.mem_flatMap.mpr ⟨_, hr, ?_⟩)
      exact DRule.mem_conclusions_of_instance
        (DRule.wf_definite (p.rule_wf _ hr)) ih

/-! ## The model-theoretic layer: rules as sentences -/

def DTerm.toCl : DTerm → CL.Term
  | .v n => .name n
  | .c s => .name s
  | .lit l => embedTerm (.literal l)

/-- An atom as a CL predication (the same operator-position reading
as `HAtom.sentence`, at any arity). -/
def DAtom.sentence (a : DAtom) : CL.Sentence :=
  .atom a.pred.toCl (a.args.map (fun t => .term t.toCl))

/-- A rule as its universally closed implication (design document §3:
"rules read as universally closed implications"). -/
def DRule.sentence (r : DRule) : CL.Sentence :=
  .all (r.vars.map .plain)
    (.impl (.conj (r.body.map DAtom.sentence)) r.head.sentence)

/-- The program's schema: one sentence per rule. -/
def DatalogProgram.toSchema (p : DatalogProgram) : Schema :=
  fun s => ∃ r ∈ p.rules, s = r.sentence

/-! ### The native reading of atoms over a CL interpretation -/

def DTerm.val (i : CL.Interp) (f : String → i.dom) : DTerm → i.dom
  | .v n => f n
  | .c s => i.iName s
  | .lit l => CL.denotTerm i i.iName (fun _ => []) (embedTerm (.literal l))

/-- The n-ary generalisation of `HAtom.HoldsN`, stated directly over
the CL interpretation (no `restrictInterp` — arity is not 2). -/
def DAtom.Holds (i : CL.Interp) (f : String → i.dom) (a : DAtom) : Prop :=
  i.rel (a.pred.val i f) (a.args.map (DTerm.val i f))

theorem denot_dterm (i : CL.Interp) {vars : List String}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList) (f : String → i.dom)
    (σ : String → List i.dom) :
    ∀ {t : DTerm}, t.wfB = true → (∀ n ∈ t.varList, n ∈ vars) →
      CL.denotTerm i (overrideOn i.iName vars f) σ t.toCl = t.val i f
  | .v n, _, hs => by
      have hn : n ∈ vars := hs n (by simp [DTerm.varList])
      simp [DTerm.toCl, CL.denotTerm, DTerm.val, overrideOn, hn]
  | .c s, hwf, _ => by
      have hcolon : ':' ∈ s.toList := by
        simpa [DTerm.wfB, List.contains_iff_mem] using hwf
      have hnm : s ∉ vars := fun hmem => hvars s hmem hcolon
      simp [DTerm.toCl, CL.denotTerm, DTerm.val, overrideOn, hnm]
  | .lit l, _, _ => by
      have hfresh : FreshVal i (overrideOn i.iName vars f) :=
        freshVal_overrideOn i hvars f
      simp only [DTerm.toCl, DTerm.val, embedTerm, CL.denotTerm]
      rw [denotSeq_litArgs i hfresh l, hfresh litOp (by decide)]

theorem denotSeq_dargs (i : CL.Interp) {vars : List String}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList) (f : String → i.dom)
    (σ : String → List i.dom) :
    ∀ (args : List DTerm), (∀ t ∈ args, t.wfB = true) →
      (∀ t ∈ args, ∀ n ∈ t.varList, n ∈ vars) →
      CL.denotSeq i (overrideOn i.iName vars f) σ
          (args.map (fun t => .term t.toCl))
        = args.map (DTerm.val i f)
  | [], _, _ => rfl
  | t :: r, hw, hs => by
      simp only [List.map_cons, CL.denotSeq]
      rw [denot_dterm i hvars f σ (hw t (by simp)) (hs t (by simp)),
          denotSeq_dargs i hvars f σ r (fun u hu => hw u (by simp [hu]))
            (fun u hu => hs u (by simp [hu]))]

/-- The n-ary generalisation of `sat_hatom`. -/
theorem sat_datom (i : CL.Interp) {vars : List String}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList) (f : String → i.dom)
    (σ : String → List i.dom) {a : DAtom} (hwf : a.wfB = true)
    (hscope : ∀ n ∈ a.varList, n ∈ vars) :
    CL.Sat i (overrideOn i.iName vars f) σ a.sentence ↔ a.Holds i f := by
  have hpw := DAtom.wf_pred hwf
  have hps : ∀ n ∈ a.pred.varList, n ∈ vars :=
    fun n hn => hscope n (List.mem_append_left _ hn)
  have haw := DAtom.wf_args hwf
  have has : ∀ t ∈ a.args, ∀ n ∈ t.varList, n ∈ vars :=
    fun t ht n hn =>
      hscope n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hn⟩))
  simp only [DAtom.sentence, CL.Sat,
             denot_dterm i hvars f σ hpw hps,
             denotSeq_dargs i hvars f σ a.args haw has]
  exact Iff.rfl

/-- **The one satisfaction lemma** of the n-ary Horn machinery — the
`satisfies_hornRow_iff` shape at any arity: a rule sentence is
satisfied exactly when the rule's native reading holds at every
valuation. -/
theorem satisfies_ruleSentence_iff (i : CL.Interp) {r : DRule}
    (hwf : r.wfB = true) :
    CL.Satisfies i r.sentence ↔
      ∀ f : String → i.dom,
        (∀ a ∈ r.body, a.Holds i f) → r.head.Holds i f := by
  have hvars := DRule.vars_no_colon hwf
  unfold CL.Satisfies DRule.sentence
  simp only [CL.Sat]
  rw [satForall_plains]
  constructor
  · intro h f hb
    have hh := h f
    simp only [CL.Sat] at hh
    rw [satAll_forall] at hh
    refine (sat_datom i hvars f _ (DRule.wf_head hwf) (r.head_scoped)).mp
      (hh ?_)
    intro s hsmem
    obtain ⟨a, hamem, rfl⟩ := List.mem_map.mp hsmem
    exact (sat_datom i hvars f _ (DRule.wf_body hwf a hamem)
      (r.body_scoped a hamem)).mpr (hb a hamem)
  · intro h f
    simp only [CL.Sat]
    rw [satAll_forall]
    intro hb
    refine (sat_datom i hvars f _ (DRule.wf_head hwf) (r.head_scoped)).mpr
      (h f ?_)
    intro a hamem
    exact (sat_datom i hvars f _ (DRule.wf_body hwf a hamem)
      (r.body_scoped a hamem)).mp
      (hb _ (List.mem_map.mpr ⟨a, hamem, rfl⟩))

/-! ### Ground atoms -/

theorem denot_ground_dterm (i : CL.Interp) (σ : String → List i.dom)
    (f : String → i.dom) :
    ∀ {t : DTerm}, t.groundB = true →
      CL.denotTerm i i.iName σ t.toCl = t.val i f
  | .v n, hg => by simp [DTerm.groundB] at hg
  | .c s, _ => by simp [DTerm.toCl, CL.denotTerm, DTerm.val]
  | .lit l, _ => by
      simp only [DTerm.toCl, DTerm.val, embedTerm, CL.denotTerm]
      rw [denotSeq_litArgs i (fun _ _ => rfl) l]

theorem denotSeq_ground_dargs (i : CL.Interp) (σ : String → List i.dom)
    (f : String → i.dom) :
    ∀ (args : List DTerm), (∀ t ∈ args, t.groundB = true) →
      CL.denotSeq i i.iName σ (args.map (fun t => .term t.toCl))
        = args.map (DTerm.val i f)
  | [], _ => rfl
  | t :: r, hg => by
      simp only [List.map_cons, CL.denotSeq]
      rw [denot_ground_dterm i σ f (hg t (by simp)),
          denotSeq_ground_dargs i σ f r (fun u hu => hg u (by simp [hu]))]

/-- A ground atom's sentence is satisfied exactly when the atom holds
— at ANY valuation, since no variable occurs. -/
theorem satisfies_groundAtom (i : CL.Interp) (f : String → i.dom)
    {a : DAtom} (hg : a.groundB = true) :
    CL.Satisfies i a.sentence ↔ a.Holds i f := by
  simp only [DAtom.groundB, Bool.and_eq_true, List.all_eq_true] at hg
  unfold CL.Satisfies
  simp only [DAtom.sentence, CL.Sat,
             denot_ground_dterm i _ f hg.1,
             denotSeq_ground_dargs i _ f a.args hg.2]
  exact Iff.rfl

/-- Instantiated-atom satisfaction is the native reading at the
substitution's denotation. -/
theorem holds_subst (i : CL.Interp) (f : String → i.dom)
    (θ : String → String) (a : DAtom) :
    (a.subst θ).Holds i f ↔ a.Holds i (fun n => i.iName (θ n)) := by
  have hterm : ∀ t : DTerm,
      (t.subst θ).val i f = t.val i (fun n => i.iName (θ n)) := by
    intro t; cases t <;> rfl
  unfold DAtom.Holds DAtom.subst
  rw [hterm, List.map_map,
      List.map_congr_left (fun t _ => by
        show (t.subst θ).val i f = t.val i (fun n => i.iName (θ n))
        exact hterm t)]

/-! ## Generic theorem 1: least-fixpoint soundness -/

/-- Every DERIVABLE atom is entailed by the program-as-schema plus the
facts, over every CL interpretation — the `rhoDf_derives_holds` shape,
proved once for the whole class. -/
theorem datalog_derives_sound (p : DatalogProgram) (facts : List DAtom)
    {a : DAtom} (h : p.Derives facts a) :
    EntailsSchema condTrue p.toSchema (facts.map DAtom.sentence)
      a.sentence := by
  induction h with
  | fact ha =>
      intro i _ _ hprem
      exact hprem _ (List.mem_map.mpr ⟨_, ha, rfl⟩)
  | rule hr θ hb ih =>
      intro i hc hsch hprem
      have hrule := (satisfies_ruleSentence_iff i (p.rule_wf _ hr)).mp
        (hsch _ ⟨_, hr, rfl⟩)
      have hhead := hrule (fun n => i.iName (θ n)) (fun b hbm => by
        rw [← holds_subst i (fun _ => i.domWit) θ b]
        exact (satisfies_groundAtom i _ (b.subst_ground θ)).mp
          (ih b hbm i hc hsch hprem))
      rw [← holds_subst i (fun _ => i.domWit) θ _] at hhead
      exact (satisfies_groundAtom i _ (DAtom.subst_ground θ _)).mpr hhead

/-- **Generic least-fixpoint SOUNDNESS** (design document §4.3, →
direction): every atom of the least fixpoint — at any fuel — is
entailed. No groundness or saturation hypothesis. -/
theorem datalog_lfp_sound (p : DatalogProgram) (facts : List DAtom)
    (fuel : Nat) {a : DAtom} (h : a ∈ p.lfp facts fuel) :
    EntailsSchema condTrue p.toSchema (facts.map DAtom.sentence)
      a.sentence :=
  datalog_derives_sound p facts (p.lfp_sound facts fuel h)

/-! ## Generic theorem 2: Herbrand completeness for ground atoms -/

/-- The Herbrand interpretation of a fact base: the domain is the
constants themselves (`String`), every name denotes itself, and a
relation holds of a sequence exactly when the corresponding ground
atom is in the base. The generic form of `RDF.Semantics.herbrand`,
over the unified theory. -/
def herbInterp (base : List DAtom) : CL.Interp where
  dom := String
  domWit := ""
  iName := id
  iStr := id
  rel := fun d ds => (⟨.c d, ds.map .c⟩ : DAtom) ∈ base
  fn := fun _ _ => ""
  iProp := fun _ _ _ => ""

/-- In the Herbrand interpretation, an atom holds at a valuation
exactly when its instance under that valuation (read as a
substitution) is in the base. -/
theorem herb_holds_iff (base : List DAtom)
    (f : String → (herbInterp base).dom) {a : DAtom}
    (hlf : a.litFreeB = true) :
    a.Holds (herbInterp base) f ↔ a.subst f ∈ base := by
  simp only [DAtom.litFreeB, Bool.and_eq_true, List.all_eq_true] at hlf
  have hval : ∀ t : DTerm, t.litFreeB = true →
      DTerm.val (herbInterp base) f t = DTerm.substVal f t := by
    intro t ht
    cases t with
    | v n => rfl
    | c s => rfl
    | lit l => simp [DTerm.litFreeB] at ht
  have hsubst : ∀ t : DTerm, t.litFreeB = true →
      DTerm.subst f t = DTerm.c (DTerm.substVal f t) := by
    intro t ht
    cases t with
    | v n => rfl
    | c s => rfl
    | lit l => simp [DTerm.litFreeB] at ht
  simp only [DAtom.Holds, DAtom.subst,
             hval _ hlf.1, hsubst _ hlf.1,
             List.map_congr_left (fun t ht => hval t (hlf.2 t ht)),
             List.map_congr_left (fun t ht => hsubst t (hlf.2 t ht))]
  simp only [herbInterp, List.map_map, Function.comp_def]

/-- A GROUND atom's sentence is satisfied by the Herbrand
interpretation exactly when the atom is in the base. -/
theorem herb_ground_mem_iff (base : List DAtom) {a : DAtom}
    (hg : a.groundB = true) (hlf : a.litFreeB = true) :
    CL.Satisfies (herbInterp base) a.sentence ↔ a ∈ base := by
  rw [satisfies_groundAtom _ (herbInterp base).iName hg, herb_holds_iff _ _ hlf]
  exact iff_of_eq (congrArg (· ∈ base) (DAtom.subst_of_ground hg _))

/-- The Herbrand interpretation of a SATURATED least fixpoint
satisfies the program's schema: a rule's native reading at any
valuation is one `step` firing, and saturation keeps the head inside
the fixpoint. -/
theorem herb_satisfiesSchema {p : DatalogProgram} {facts : List DAtom}
    {fuel : Nat} (hfa : p.FuelAdequate facts fuel)
    (hlf : ∀ r ∈ p.rules, r.litFreeB = true) :
    SatisfiesSchema (herbInterp (p.lfp facts fuel)) p.toSchema := by
  rintro s ⟨r, hr, rfl⟩
  have hrl := hlf r hr
  simp only [DRule.litFreeB, Bool.and_eq_true, List.all_eq_true] at hrl
  rw [satisfies_ruleSentence_iff _ (p.rule_wf _ hr)]
  intro f hb
  rw [herb_holds_iff _ _ hrl.1]
  refine hfa _ (List.mem_flatMap.mpr ⟨_, hr, ?_⟩)
  refine DRule.mem_conclusions_of_instance
    (DRule.wf_definite (p.rule_wf _ hr)) ?_
  intro b hbm
  rw [← herb_holds_iff _ _ (hrl.2 b hbm)]
  exact hb b hbm

/-- **Generic least-fixpoint COMPLETENESS for ground-atomic
consequences** (design document §4.3, ← direction; §5.6 fixes the
claim level): a GROUND atom entailed by the schema plus ground facts
is in the fuel-adequate least fixpoint. The Herbrand interpretation of
the fixpoint is the minimal model. -/
theorem datalog_lfp_complete (p : DatalogProgram) {facts : List DAtom}
    {fuel : Nat} (hgf : ∀ b ∈ facts, b.groundB = true)
    (hlfp : ∀ r ∈ p.rules, r.litFreeB = true)
    (hlff : ∀ b ∈ facts, b.litFreeB = true)
    (hfa : p.FuelAdequate facts fuel) {a : DAtom} (hg : a.groundB = true)
    (hla : a.litFreeB = true)
    (h : EntailsSchema condTrue p.toSchema (facts.map DAtom.sentence)
      a.sentence) :
    a ∈ p.lfp facts fuel := by
  have hsat : CL.Satisfies (herbInterp (p.lfp facts fuel)) a.sentence := by
    refine h _ trivial (herb_satisfiesSchema hfa hlfp) ?_
    intro s hs
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hs
    exact (herb_ground_mem_iff _ (hgf b hbm) (hlff b hbm)).mpr
      (p.lfp_extensive facts fuel b hbm)
  exact (herb_ground_mem_iff _ hg hla).mp hsat

/-- **The stage 3 gate theorem** (design document §4.3,
`datalog_lfp_iff_entails`): for a well-formed program (definite Horn
by construction), ground facts, a ground atom, and adequate fuel, the
least fixpoint contains the atom EXACTLY WHEN the program-as-schema
plus the facts entail its sentence over every CL interpretation. -/
theorem datalog_lfp_iff_entails (p : DatalogProgram) {facts : List DAtom}
    {fuel : Nat} {a : DAtom} (hgf : ∀ b ∈ facts, b.groundB = true)
    (hlfp : ∀ r ∈ p.rules, r.litFreeB = true)
    (hlff : ∀ b ∈ facts, b.litFreeB = true)
    (hg : a.groundB = true) (hla : a.litFreeB = true)
    (hfa : p.FuelAdequate facts fuel) :
    a ∈ p.lfp facts fuel ↔
      EntailsSchema condTrue p.toSchema (facts.map DAtom.sentence)
        a.sentence :=
  ⟨fun h => datalog_lfp_sound p facts fuel h,
   fun h => datalog_lfp_complete p hgf hlfp hlff hfa hg hla h⟩

/-! ## Non-vacuity witnesses (the `SemanticsHypothesisWitness`
discipline: a schema nothing satisfies would make every entailment
claim above vacuous, and an entailment relation that holds everywhere
would make the completeness direction empty) -/

/-- The all-true interpretation satisfies EVERY program's schema —
`toSchema` is satisfiable for every program, so `EntailsSchema` over
it is never vacuous. -/
def allTrueInterp : CL.Interp where
  dom := Unit
  domWit := ()
  iName := fun _ => ()
  iStr := fun _ => ()
  rel := fun _ _ => True
  fn := fun _ _ => ()
  iProp := fun _ _ _ => ()

theorem toSchema_satisfiable (p : DatalogProgram) :
    ∃ i : CL.Interp, SatisfiesSchema i p.toSchema := by
  refine ⟨allTrueInterp, ?_⟩
  rintro s ⟨r, hr, rfl⟩
  rw [satisfies_ruleSentence_iff _ (p.rule_wf _ hr)]
  intro f _
  exact trivial

/-! ### A concrete program: transitive closure, plus one ternary rule
to pin the n-ary machinery beyond arity 2 -/

private def pEdge : DTerm := .c "d:edge"
private def pPath : DTerm := .c "d:path"
private def pTri  : DTerm := .c "d:tri"
private def cMark : DTerm := .c "d:mark"

/-- `path(x,y) ⇐ edge(x,y)`; `path(x,z) ⇐ edge(x,y), path(y,z)`;
`tri(x,y,d:mark) ⇐ edge(x,y)` (arity 3, constant in head). -/
def demoProgram : DatalogProgram :=
  ⟨[⟨⟨pPath, [.v "x", .v "y"]⟩, [⟨pEdge, [.v "x", .v "y"]⟩]⟩,
    ⟨⟨pPath, [.v "x", .v "z"]⟩,
     [⟨pEdge, [.v "x", .v "y"]⟩, ⟨pPath, [.v "y", .v "z"]⟩]⟩,
    ⟨⟨pTri, [.v "x", .v "y", cMark]⟩, [⟨pEdge, [.v "x", .v "y"]⟩]⟩],
   by decide⟩

private def dA : DTerm := .c "d:a"
private def dB : DTerm := .c "d:b"
private def dC : DTerm := .c "d:c"

def demoFacts : List DAtom :=
  [⟨pEdge, [dA, dB]⟩, ⟨pEdge, [dB, dC]⟩]

theorem demoFacts_ground : ∀ b ∈ demoFacts, b.groundB = true := by decide

/-- The positive instance: `path(a,c)` — a two-step consequence — is
entailed, established END TO END through the executable fixpoint and
the gate theorem. -/
theorem demo_path_entailed :
    EntailsSchema condTrue demoProgram.toSchema
      (demoFacts.map DAtom.sentence)
      (DAtom.sentence ⟨pPath, [dA, dC]⟩) :=
  (datalog_lfp_iff_entails demoProgram (fuel := 3) demoFacts_ground
    (by decide) (by decide) (by decide) (by decide)
    (demoProgram.fuelAdequate_of_check (by decide))).mp
    (by decide)

/-- The ternary instance: `tri(a,b,d:mark)` is entailed — the n-ary
machinery does real work beyond arity 2. -/
theorem demo_tri_entailed :
    EntailsSchema condTrue demoProgram.toSchema
      (demoFacts.map DAtom.sentence)
      (DAtom.sentence ⟨pTri, [dA, dB, cMark]⟩) :=
  (datalog_lfp_iff_entails demoProgram (fuel := 3) demoFacts_ground
    (by decide) (by decide) (by decide) (by decide)
    (demoProgram.fuelAdequate_of_check (by decide))).mp
    (by decide)

/-- The negative instance — the not-everything guard: `path(c,a)` is
NOT entailed. The refutation flows through the completeness half: were
it entailed, it would be in the saturated fixpoint, and by `decide` it
is not. -/
theorem demo_not_entailed_reverse :
    ¬ EntailsSchema condTrue demoProgram.toSchema
        (demoFacts.map DAtom.sentence)
        (DAtom.sentence ⟨pPath, [dC, dA]⟩) := by
  intro h
  have hmem := (datalog_lfp_iff_entails demoProgram (fuel := 3)
    demoFacts_ground (by decide) (by decide) (by decide) (by decide)
    (demoProgram.fuelAdequate_of_check (by decide))).mpr h
  exact absurd hmem (by decide)

/-! ## Build-time checks -/

section Checks

/- The fixpoint computes what the theorems say: the base facts, the
one-step and two-step paths, the ternary marks — and saturates at
fuel 3. -/

#guard demoProgram.saturatedCheck demoFacts 3
#guard decide ((⟨pPath, [dA, dC]⟩ : DAtom) ∈ demoProgram.lfp demoFacts 3)
#guard decide ((⟨pPath, [dA, dB]⟩ : DAtom) ∈ demoProgram.lfp demoFacts 3)
#guard decide ((⟨pTri, [dA, dB, cMark]⟩ : DAtom) ∈ demoProgram.lfp demoFacts 3)
#guard !decide ((⟨pPath, [dC, dA]⟩ : DAtom) ∈ demoProgram.lfp demoFacts 3)

/- The saturation check is not vacuously true: at fuel 0 the demo is
NOT saturated. -/

#guard !demoProgram.saturatedCheck demoFacts 0

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations). No `sorryAx`, nothing
user-declared. -/

#print axioms matchBody_sound
#print axioms matchBody_complete
#print axioms DatalogProgram.lfp_sound
#print axioms DatalogProgram.derives_mem_lfp
#print axioms satisfies_ruleSentence_iff
#print axioms datalog_derives_sound
#print axioms datalog_lfp_sound
#print axioms herb_satisfiesSchema
#print axioms datalog_lfp_complete
#print axioms datalog_lfp_iff_entails
#print axioms toSchema_satisfiable
#print axioms demo_path_entailed
#print axioms demo_not_entailed_reverse

end Checks

end L4Factoidal.Unified
