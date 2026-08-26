/-
L4Factoidal.CL.FiniteSatTheorems — the satisfaction half of the
`CL.FiniteSat` / `CL.Semantics` agreement.

`CL/FiniteSat.lean` proves the TERM half unconditionally
(`denotTermFin_eq` / `denotSeqFin_eq`) and states the satisfaction
half as three conditions in its header, with the four `tiny_sat_*`
theorems of `CL.Examples` restated as `#guard`s. This module proves
the satisfaction half.
Tracking: https://github.com/danbri/factoidal/issues/609 item 1.

## The theorem

`satFin_eq` — for every finite interpretation `fi` and valuation `v`,

    sat fi v s = true  ↔  Sat fi.toInterp v.ind v.seq s

under exactly three hypotheses:

1. `[LawfulBEq α]` — `==` on the domain type is `=`. Used in ONE
   place: the `.eq` clause compares `denotTermFin` results with `==`
   where `Sat` compares them with `=`. Nothing else in the checker
   depends on `BEq α` being lawful (`relB` and `fnD` use `==` on both
   sides of the agreement, so a wrong `==` is wrong the same way on
   each side). `beqAlwaysTrue_disagrees` below exhibits a non-lawful
   `BEq` and a sentence the two sides decide differently, so the
   hypothesis is not removable.

2. `hdom : ∀ x : α, x ∈ fi.domain` — DOMAIN COMPLETENESS. `satFA` /
   `satEX` fold plain and restricted bindings over `fi.domain` where
   `SatForall` / `SatExists` quantify over all of `α`.
   `partialDomain_disagrees` below exhibits a `FiniteInterp` whose
   `domain` omits an individual and a sentence the two sides decide
   differently.

3. `hns : noSeqQuant s = true` — NO SEQUENCE-MARKER QUANTIFIER binding
   anywhere in the sentence. §6.3 quantifies a bound marker over ALL
   finite sequences of individuals; `satFA` / `satEX` fold over
   `seqsUpTo fi.domain fi.maxSeq`, which is an under-approximation for
   `exists` and an over-approximation for `forall`.
   `seqQuant_disagrees` below exhibits the disagreement.

FREE sequence markers are NOT excluded: `denotSeqFin` and `denotSeq`
both splice `v.seq m`, and the term half already covers that.

## The condition that turned out NOT to be a hypothesis

`FiniteSat.lean`'s header lists, alongside lawful `BEq`, that "the
interpretation of an IKL `that`-term does not depend on the
valuation". That is not a hypothesis of `satFin_eq` and cannot be:
`FiniteInterp.toInterp` DEFINES `iProp := fun s _ _ => fi.propD
s.toClif`, so on the interpretation the theorem is about, `iProp` is
valuation-independent by construction, and `denotTermFin_eq` already
proves the two `that`-readings equal unconditionally.

What the header condition is really about is a DIFFERENT question,
which `satFin_eq` does not answer and does not claim: whether
`fi.toInterp` is an adequate reading of IKL. It generally is not.
`FiniteInterp.toInterp` never satisfies `IklRespectsThat` unless the
`props` and `rels` tables happen to agree, and a `that`-term under a
quantifier binding one of its free names denotes the SAME individual
at every binding, because the key is the canonical CLIF text of the
sentence and nothing else. `iProp_valuation_independent` states that
fact, and `toInterp_quantifying_in_collapses` exhibits a coherent
interpretation the finite reading cannot express. Both are recorded
as boundary rows, not as hypotheses.

## Totality

No `sorry`, no `axiom`, no `partial`, no `native_decide`. Axiom audit
by in-source `#print axioms` at the end of the file.
-/

import L4Factoidal.CL.FiniteSat

namespace L4Factoidal.CL

/-! ## The sequence-marker-quantifier-free fragment -/

mutual

/-- `true` iff no quantifier of the sentence binds a SEQUENCE MARKER.
Terms are not descended into: a `that`-term's sentence is never
satisfaction-recursed (the `that` case of both denotations consults a
table), and a restricted binding's guard is a term. -/
def noSeqQuant : Sentence → Bool
  | .atom _ _ => true
  | .eq _ _ => true
  | .conj ss => noSeqQuantList ss
  | .disj ss => noSeqQuantList ss
  | .neg s => noSeqQuant s
  | .impl a b => noSeqQuant a && noSeqQuant b
  | .iff a b => noSeqQuant a && noSeqQuant b
  | .all bs body => noSeqBinds bs && noSeqQuant body
  | .ex bs body => noSeqBinds bs && noSeqQuant body

/-- Every sentence of the list is sequence-marker-quantifier-free. -/
def noSeqQuantList : List Sentence → Bool
  | [] => true
  | s :: r => noSeqQuant s && noSeqQuantList r

/-- No entry of the boundlist is a sequence marker. -/
def noSeqBinds : List Binding → Bool
  | [] => true
  | .plain _ :: r => noSeqBinds r
  | .seqmark _ :: _ => false
  | .restricted _ _ :: r => noSeqBinds r

end

/-! ## Reading the finite tables through `toInterp` -/

/-- The relation extension of `toInterp` is `relB`, definitionally. -/
theorem toInterp_rel {α : Type} [BEq α] (fi : FiniteInterp α) (x : α) (args : List α) :
    fi.toInterp.rel x args ↔ fi.relB x args = true := Iff.rfl

/-! ## Clause lemmas for `CL.Sat`

`CL.Semantics`' satisfaction group is compiled by well-founded
recursion, so its clauses are not definitional equalities and `simp`
cannot use them at `fi.toInterp`: the valuation `v.ind : String → α`
type-checks against `String → fi.toInterp.dom` only at DEFAULT
transparency, and `simp` matches at `implicit`. One `rw [Sat]`-proved
clause lemma per constructor, stated over an arbitrary `Interp`, fixes
that once; the `f`-prefixed specialisations below instantiate them at
`fi.toInterp` with `α`-typed valuations. -/

section Clauses

variable (i : Interp) (nu : String → i.dom) (sg : String → List i.dom)

theorem sat_atom_iff (p : Term) (args : List SeqItem) :
    Sat i nu sg (.atom p args) ↔ i.rel (denotTerm i nu sg p) (denotSeq i nu sg args) := by
  rw [Sat]

theorem sat_eq_iff (a b : Term) :
    Sat i nu sg (.eq a b) ↔ denotTerm i nu sg a = denotTerm i nu sg b := by rw [Sat]

theorem sat_conj_iff (ss : List Sentence) :
    Sat i nu sg (.conj ss) ↔ SatAll i nu sg ss := by rw [Sat]

theorem sat_disj_iff (ss : List Sentence) :
    Sat i nu sg (.disj ss) ↔ SatAny i nu sg ss := by rw [Sat]

theorem sat_neg_iff (s : Sentence) :
    Sat i nu sg (.neg s) ↔ ¬ Sat i nu sg s := by rw [Sat]

theorem sat_impl_iff (a b : Sentence) :
    Sat i nu sg (.impl a b) ↔ (Sat i nu sg a → Sat i nu sg b) := by rw [Sat]

theorem sat_iff_iff (a b : Sentence) :
    Sat i nu sg (.iff a b) ↔ (Sat i nu sg a ↔ Sat i nu sg b) := by rw [Sat]

theorem sat_all_iff (bs : List Binding) (body : Sentence) :
    Sat i nu sg (.all bs body) ↔ SatForall i nu sg bs body := by rw [Sat]

theorem sat_ex_iff (bs : List Binding) (body : Sentence) :
    Sat i nu sg (.ex bs body) ↔ SatExists i nu sg bs body := by rw [Sat]

theorem satAll_nil_iff : SatAll i nu sg [] ↔ True := by rw [SatAll]

theorem satAll_cons_iff (s : Sentence) (r : List Sentence) :
    SatAll i nu sg (s :: r) ↔ (Sat i nu sg s ∧ SatAll i nu sg r) := by rw [SatAll]

theorem satAny_nil_iff : SatAny i nu sg [] ↔ False := by rw [SatAny]

theorem satAny_cons_iff (s : Sentence) (r : List Sentence) :
    SatAny i nu sg (s :: r) ↔ (Sat i nu sg s ∨ SatAny i nu sg r) := by rw [SatAny]

theorem satForall_nil_iff (body : Sentence) :
    SatForall i nu sg [] body ↔ Sat i nu sg body := by rw [SatForall]

theorem satForall_plain_iff (nm : String) (r : List Binding) (body : Sentence) :
    SatForall i nu sg (.plain nm :: r) body ↔
      ∀ x : i.dom, SatForall i (updateInd nu nm x) sg r body := by rw [SatForall]

theorem satForall_restricted_iff (nm : String) (g : Term) (r : List Binding)
    (body : Sentence) :
    SatForall i nu sg (.restricted nm g :: r) body ↔
      ∀ x : i.dom, i.rel (denotTerm i nu sg g) [x] →
        SatForall i (updateInd nu nm x) sg r body := by rw [SatForall]

theorem satForall_seqmark_iff (m : String) (r : List Binding) (body : Sentence) :
    SatForall i nu sg (.seqmark m :: r) body ↔
      ∀ xs : List i.dom, SatForall i nu (updateSeq sg m xs) r body := by rw [SatForall]

theorem satExists_nil_iff (body : Sentence) :
    SatExists i nu sg [] body ↔ Sat i nu sg body := by rw [SatExists]

theorem satExists_plain_iff (nm : String) (r : List Binding) (body : Sentence) :
    SatExists i nu sg (.plain nm :: r) body ↔
      ∃ x : i.dom, SatExists i (updateInd nu nm x) sg r body := by rw [SatExists]

theorem satExists_seqmark_iff (m : String) (r : List Binding) (body : Sentence) :
    SatExists i nu sg (.seqmark m :: r) body ↔
      ∃ xs : List i.dom, SatExists i nu (updateSeq sg m xs) r body := by rw [SatExists]

theorem satExists_restricted_iff (nm : String) (g : Term) (r : List Binding)
    (body : Sentence) :
    SatExists i nu sg (.restricted nm g :: r) body ↔
      ∃ x : i.dom, i.rel (denotTerm i nu sg g) [x] ∧
        SatExists i (updateInd nu nm x) sg r body := by rw [SatExists]

end Clauses

/-! ## The same clauses at a finite interpretation

Every statement below is the clause lemma above instantiated at
`fi.toInterp`, which turns `i.dom` into `α` and `i.rel x args` into
`fi.relB x args = true`. -/

section FiniteClauses

variable {α : Type} [BEq α] (fi : FiniteInterp α) (nu : String → α) (sg : String → List α)

private theorem fsat_atom (p : Term) (args : List SeqItem) :
    Sat fi.toInterp nu sg (.atom p args) ↔
      fi.relB (denotTerm fi.toInterp nu sg p) (denotSeq fi.toInterp nu sg args) = true :=
  sat_atom_iff fi.toInterp nu sg p args

private theorem fsat_eq (a b : Term) :
    Sat fi.toInterp nu sg (.eq a b) ↔
      denotTerm fi.toInterp nu sg a = denotTerm fi.toInterp nu sg b :=
  sat_eq_iff fi.toInterp nu sg a b

private theorem fsatFA_plain (nm : String) (r : List Binding) (body : Sentence) :
    SatForall fi.toInterp nu sg (.plain nm :: r) body ↔
      ∀ x : α, SatForall fi.toInterp (updateInd nu nm x) sg r body :=
  satForall_plain_iff fi.toInterp nu sg nm r body

private theorem fsatFA_restricted (nm : String) (g : Term) (r : List Binding)
    (body : Sentence) :
    SatForall fi.toInterp nu sg (.restricted nm g :: r) body ↔
      ∀ x : α, fi.relB (denotTerm fi.toInterp nu sg g) [x] = true →
        SatForall fi.toInterp (updateInd nu nm x) sg r body :=
  satForall_restricted_iff fi.toInterp nu sg nm g r body

private theorem fsatEX_plain (nm : String) (r : List Binding) (body : Sentence) :
    SatExists fi.toInterp nu sg (.plain nm :: r) body ↔
      ∃ x : α, SatExists fi.toInterp (updateInd nu nm x) sg r body :=
  satExists_plain_iff fi.toInterp nu sg nm r body

private theorem fsatEX_restricted (nm : String) (g : Term) (r : List Binding)
    (body : Sentence) :
    SatExists fi.toInterp nu sg (.restricted nm g :: r) body ↔
      ∃ x : α, fi.relB (denotTerm fi.toInterp nu sg g) [x] = true ∧
        SatExists fi.toInterp (updateInd nu nm x) sg r body :=
  satExists_restricted_iff fi.toInterp nu sg nm g r body

end FiniteClauses

/-! ## Bool-to-Prop plumbing

Five one-line lemmas transporting an `= true` characterisation
through the Boolean connectives the checker uses. -/

private theorem bnot_iff {b : Bool} {P : Prop} (h : b = true ↔ P) :
    (!b) = true ↔ ¬ P := by
  cases b <;> simp_all

private theorem band_iff {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) : (a && b) = true ↔ (P ∧ Q) := by
  cases a <;> cases b <;> simp_all

private theorem bor_iff {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) : (a || b) = true ↔ (P ∨ Q) := by
  cases a <;> cases b <;> simp_all

private theorem bimp_iff {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (!a || b) = true ↔ (P → Q) := by
  cases a <;> cases b <;> simp_all

private theorem bbeq_iff {a b : Bool} {P Q : Prop}
    (ha : a = true ↔ P) (hb : b = true ↔ Q) :
    (a == b) = true ↔ (P ↔ Q) := by
  cases a <;> cases b <;> simp_all

/-! ## The agreement, by induction on fuel

Every recursive call of the satisfaction group decrements fuel by
exactly 1, so ONE induction on the fuel argument carries all five
functions. The size side conditions are the `Sentence.size` bound
`FiniteSat.lean`'s header argues informally; here they are the
induction's hypotheses, discharged by `omega` at every step. -/

variable {α : Type}

private theorem satFuel_eq_aux [BEq α] [LawfulBEq α] (fi : FiniteInterp α)
    (hdom : ∀ x : α, x ∈ fi.domain) (fuel : Nat) :
    (∀ (v : FinVal α) (s : Sentence), noSeqQuant s = true → s.size < fuel →
        (satFuel fi fuel v s = true ↔ Sat fi.toInterp v.ind v.seq s))
    ∧ (∀ (v : FinVal α) (ss : List Sentence), noSeqQuantList ss = true →
        sentencesSize ss < fuel →
        (satAllFuel fi fuel v ss = true ↔ SatAll fi.toInterp v.ind v.seq ss))
    ∧ (∀ (v : FinVal α) (ss : List Sentence), noSeqQuantList ss = true →
        sentencesSize ss < fuel →
        (satAnyFuel fi fuel v ss = true ↔ SatAny fi.toInterp v.ind v.seq ss))
    ∧ (∀ (v : FinVal α) (bs : List Binding) (body : Sentence),
        noSeqBinds bs = true → noSeqQuant body = true →
        bindingsSize bs + body.size < fuel →
        (satFA fi fuel v bs body = true ↔
          SatForall fi.toInterp v.ind v.seq bs body))
    ∧ (∀ (v : FinVal α) (bs : List Binding) (body : Sentence),
        noSeqBinds bs = true → noSeqQuant body = true →
        bindingsSize bs + body.size < fuel →
        (satEX fi fuel v bs body = true ↔
          SatExists fi.toInterp v.ind v.seq bs body)) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ h; omega
      · intro _ _ _ h; omega
      · intro _ _ _ h; omega
      · intro _ _ _ _ _ h; omega
      · intro _ _ _ _ _ h; omega
  | succ n ih =>
      refine ⟨?sat, ?all, ?any, ?fa, ?ex⟩
      case sat =>
        intro v s hns hsz
        cases s with
        | atom p args =>
            rw [fsat_atom fi v.ind v.seq p args]
            simp only [satFuel, denotTermFin_eq, denotSeqFin_eq]
        | eq a b =>
            rw [fsat_eq fi v.ind v.seq a b]
            simp only [satFuel, denotTermFin_eq]
            exact beq_iff_eq
        | conj ss =>
            simp only [noSeqQuant] at hns
            simp only [Sentence.size] at hsz
            rw [sat_conj_iff fi.toInterp v.ind v.seq ss]
            exact ih.2.1 v ss hns (by omega)
        | disj ss =>
            simp only [noSeqQuant] at hns
            simp only [Sentence.size] at hsz
            rw [sat_disj_iff fi.toInterp v.ind v.seq ss]
            exact ih.2.2.1 v ss hns (by omega)
        | neg s1 =>
            simp only [noSeqQuant] at hns
            simp only [Sentence.size] at hsz
            rw [sat_neg_iff fi.toInterp v.ind v.seq s1]
            exact bnot_iff (ih.1 v s1 hns (by omega))
        | impl a b =>
            simp only [noSeqQuant, Bool.and_eq_true] at hns
            simp only [Sentence.size] at hsz
            rw [sat_impl_iff fi.toInterp v.ind v.seq a b]
            exact bimp_iff (ih.1 v a hns.1 (by omega)) (ih.1 v b hns.2 (by omega))
        | iff a b =>
            simp only [noSeqQuant, Bool.and_eq_true] at hns
            simp only [Sentence.size] at hsz
            rw [sat_iff_iff fi.toInterp v.ind v.seq a b]
            exact bbeq_iff (ih.1 v a hns.1 (by omega)) (ih.1 v b hns.2 (by omega))
        | all bs body =>
            simp only [noSeqQuant, Bool.and_eq_true] at hns
            simp only [Sentence.size] at hsz
            rw [sat_all_iff fi.toInterp v.ind v.seq bs body]
            exact ih.2.2.2.1 v bs body hns.1 hns.2 (by omega)
        | ex bs body =>
            simp only [noSeqQuant, Bool.and_eq_true] at hns
            simp only [Sentence.size] at hsz
            rw [sat_ex_iff fi.toInterp v.ind v.seq bs body]
            exact ih.2.2.2.2 v bs body hns.1 hns.2 (by omega)
      case all =>
        intro v ss hns hsz
        cases ss with
        | nil =>
            rw [satAll_nil_iff fi.toInterp v.ind v.seq]
            simp [satAllFuel]
        | cons s r =>
            simp only [noSeqQuantList, Bool.and_eq_true] at hns
            simp only [sentencesSize] at hsz
            rw [satAll_cons_iff fi.toInterp v.ind v.seq s r]
            simp only [satAllFuel]
            exact band_iff (ih.1 v s hns.1 (by omega)) (ih.2.1 v r hns.2 (by omega))
      case any =>
        intro v ss hns hsz
        cases ss with
        | nil =>
            rw [satAny_nil_iff fi.toInterp v.ind v.seq]
            simp [satAnyFuel]
        | cons s r =>
            simp only [noSeqQuantList, Bool.and_eq_true] at hns
            simp only [sentencesSize] at hsz
            rw [satAny_cons_iff fi.toInterp v.ind v.seq s r]
            simp only [satAnyFuel]
            exact bor_iff (ih.1 v s hns.1 (by omega)) (ih.2.2.1 v r hns.2 (by omega))
      case fa =>
        intro v bs body hbs hbody hsz
        cases bs with
        | nil =>
            simp only [bindingsSize] at hsz
            rw [satForall_nil_iff fi.toInterp v.ind v.seq body]
            simp only [satFA]
            exact ih.1 v body hbody (by omega)
        | cons b r =>
            cases b with
            | plain nm =>
                simp only [noSeqBinds] at hbs
                simp only [bindingsSize] at hsz
                rw [fsatFA_plain fi v.ind v.seq nm r body]
                simp only [satFA, List.all_eq_true]
                constructor
                · intro hall x
                  exact (ih.2.2.2.1 (v.updInd nm x) r body hbs hbody (by omega)).mp
                    (hall x (hdom x))
                · intro hall x _
                  exact (ih.2.2.2.1 (v.updInd nm x) r body hbs hbody (by omega)).mpr
                    (hall x)
            | seqmark m =>
                simp [noSeqBinds] at hbs
            | restricted nm g =>
                simp only [noSeqBinds] at hbs
                simp only [bindingsSize] at hsz
                rw [fsatFA_restricted fi v.ind v.seq nm g r body]
                simp only [satFA, List.all_eq_true, denotTermFin_eq, Bool.or_eq_true,
                  Bool.not_eq_true']
                constructor
                · intro hall x hrel
                  rcases hall x (hdom x) with h | h
                  · rw [h] at hrel; exact absurd hrel (by simp)
                  · exact (ih.2.2.2.1 (v.updInd nm x) r body hbs hbody (by omega)).mp h
                · intro hall x _
                  by_cases hr :
                      fi.relB (denotTerm fi.toInterp v.ind v.seq g) [x] = true
                  · exact Or.inr
                      ((ih.2.2.2.1 (v.updInd nm x) r body hbs hbody (by omega)).mpr
                        (hall x hr))
                  · exact Or.inl (by simpa using hr)
      case ex =>
        intro v bs body hbs hbody hsz
        cases bs with
        | nil =>
            simp only [bindingsSize] at hsz
            rw [satExists_nil_iff fi.toInterp v.ind v.seq body]
            simp only [satEX]
            exact ih.1 v body hbody (by omega)
        | cons b r =>
            cases b with
            | plain nm =>
                simp only [noSeqBinds] at hbs
                simp only [bindingsSize] at hsz
                rw [fsatEX_plain fi v.ind v.seq nm r body]
                simp only [satEX, List.any_eq_true]
                constructor
                · rintro ⟨x, _, hx⟩
                  exact ⟨x, (ih.2.2.2.2 (v.updInd nm x) r body hbs hbody
                    (by omega)).mp hx⟩
                · rintro ⟨x, hx⟩
                  exact ⟨x, hdom x, (ih.2.2.2.2 (v.updInd nm x) r body hbs hbody
                    (by omega)).mpr hx⟩
            | seqmark m =>
                simp [noSeqBinds] at hbs
            | restricted nm g =>
                simp only [noSeqBinds] at hbs
                simp only [bindingsSize] at hsz
                rw [fsatEX_restricted fi v.ind v.seq nm g r body]
                simp only [satEX, List.any_eq_true, denotTermFin_eq, Bool.and_eq_true]
                constructor
                · rintro ⟨x, _, hrel, hx⟩
                  exact ⟨x, hrel, (ih.2.2.2.2 (v.updInd nm x) r body hbs hbody
                    (by omega)).mp hx⟩
                · rintro ⟨x, hrel, hx⟩
                  exact ⟨x, hdom x, hrel, (ih.2.2.2.2 (v.updInd nm x) r body hbs
                    hbody (by omega)).mpr hx⟩

/-! ## The gate theorems -/

/-- **The satisfaction half of the `FiniteSat` / `Semantics`
agreement.** The executable checker decides `CL.Sat` on `toInterp`,
under exactly the three hypotheses named in this module's header:
lawful `BEq` on the domain type, domain completeness, and no
sequence-marker quantifier. -/
theorem satFin_eq [BEq α] [LawfulBEq α] (fi : FiniteInterp α)
    (hdom : ∀ x : α, x ∈ fi.domain) (v : FinVal α) (s : Sentence)
    (hns : noSeqQuant s = true) :
    sat fi v s = true ↔ Sat fi.toInterp v.ind v.seq s :=
  (satFuel_eq_aux fi hdom (s.size + 1)).1 v s hns (Nat.lt_succ_self _)

/-- `satFin_eq` at sentence level: the executable `satisfies` decides
`CL.Satisfies`. -/
theorem satisfiesFin_eq [BEq α] [LawfulBEq α] (fi : FiniteInterp α)
    (hdom : ∀ x : α, x ∈ fi.domain) (s : Sentence)
    (hns : noSeqQuant s = true) :
    fi.satisfies s = true ↔ Satisfies fi.toInterp s :=
  satFin_eq fi hdom ⟨fi.nameD, fun _ => []⟩ s hns

/-! ## Non-vacuity: the hypotheses are satisfiable and the conclusion
is not trivial

`Unified/Witnesses.lean`'s discipline. `witFin` is `CL.Examples`'
`tiny` interpretation re-based on a FINITE domain type, so
`hdom` is dischargeable by `decide`; the four `tiny_sat_*` shapes come
back through `satisfiesFin_eq` as `Satisfies` theorems, and the
refuted shapes come back as refutations, so the agreement is not
compatible with `Sat` holding of everything. -/

/-- `CL.Examples`' `tiny` over a finite domain: `Boy` and `Sue` denote
`true`, `Bill` denotes `false`, and `Boy` holds of `Bill` alone. -/
def witFin : FiniteInterp Bool where
  domain := [false, true]
  deflt := false
  names := [("Boy", true), ("Bill", false), ("Sue", true)]
  strs := []
  fns := []
  rels := [(true, [false])]
  props := []

/-- Domain completeness for `witFin`, by decision. -/
theorem witFin_dom : ∀ x : Bool, x ∈ witFin.domain := by decide

/-- `(Boy Sue)`. -/
def wBoySue : Sentence := .atom (.name "Boy") [.term (.name "Sue")]

/-- `(exists (x) (Boy x))`. -/
def wExBoy : Sentence := .ex [.plain "x"] (.atom (.name "Boy") [.term (.name "x")])

/-- `(forall (x) (Boy x))`. -/
def wAllBoy : Sentence := .all [.plain "x"] (.atom (.name "Boy") [.term (.name "x")])

/-- `(forall ((x Boy)) (= x Bill))`. -/
def wRestricted : Sentence :=
  .all [.restricted "x" (.name "Boy")] (.eq (.name "x") (.name "Bill"))

-- The checker's verdicts, pinned.
#guard witFin.satisfies boyBill
#guard witFin.satisfies wBoySue == false
#guard witFin.satisfies wExBoy
#guard witFin.satisfies wAllBoy == false
#guard witFin.satisfies wRestricted
#guard noSeqQuant wRestricted
#guard noSeqQuant (.ex [.seqmark "m"] (.atom (.name "P") [.seqmark "m"])) == false

/-- `tiny_sat_conj`'s first conjunct, through the proved agreement. -/
theorem wit_sat_boyBill : Satisfies witFin.toInterp boyBill :=
  (satisfiesFin_eq witFin witFin_dom boyBill (by decide)).mp (by decide)

/-- `tiny_sat_ex`, through the proved agreement. -/
theorem wit_sat_ex : Satisfies witFin.toInterp wExBoy :=
  (satisfiesFin_eq witFin witFin_dom wExBoy (by decide)).mp (by decide)

/-- `tiny_sat_neg`, through the proved agreement. -/
theorem wit_sat_neg : Satisfies witFin.toInterp (.neg wBoySue) :=
  (satisfiesFin_eq witFin witFin_dom (.neg wBoySue) (by decide)).mp (by decide)

/-- `tiny_sat_restricted`, through the proved agreement. -/
theorem wit_sat_restricted : Satisfies witFin.toInterp wRestricted :=
  (satisfiesFin_eq witFin witFin_dom wRestricted (by decide)).mp (by decide)

/-- The conclusion is not trivial: `Sat` is refuted where the tables
have no row. -/
theorem wit_not_sat_boySue : ¬ Satisfies witFin.toInterp wBoySue := by
  intro h
  exact absurd ((satisfiesFin_eq witFin witFin_dom wBoySue (by decide)).mpr h) (by decide)

/-- And refuted for a plain universal the domain refutes. -/
theorem wit_not_sat_allBoy : ¬ Satisfies witFin.toInterp wAllBoy := by
  intro h
  exact absurd ((satisfiesFin_eq witFin witFin_dom wAllBoy (by decide)).mpr h) (by decide)

/-! ## Each hypothesis is necessary

`FiniteInterp.toInterp` reads NEITHER `domain` NOR `maxSeq`, so two
finite interpretations differing only in one of those fields have the
SAME `Interp` — while the checker can decide the same sentence
differently over them. That is the whole necessity argument for
hypotheses 2 and 3, and it needs no unfolding of `Sat`. -/

/-- `witFin` with an INCOMPLETE domain: `true` is missing. -/
def partialFin : FiniteInterp Bool := { witFin with domain := [false] }

/-- The two interpretations are the same `Interp`. -/
theorem partialFin_toInterp : partialFin.toInterp = witFin.toInterp := rfl

-- The same universal, decided both ways by the two domains.
#guard partialFin.satisfies wAllBoy
#guard witFin.satisfies wAllBoy == false

/-- **Hypothesis 2 (domain completeness) is not removable.** Dropping
it makes the agreement claim contradictory: `partialFin` and `witFin`
have the same `Interp` and decide `wAllBoy` differently. -/
theorem domain_hypothesis_necessary :
    ¬ ∀ (fi : FiniteInterp Bool) (v : FinVal Bool) (s : Sentence),
        noSeqQuant s = true → (sat fi v s = true ↔ Sat fi.toInterp v.ind v.seq s) := by
  intro h
  have h0 := h partialFin ⟨witFin.nameD, fun _ => []⟩ wAllBoy (by decide)
  have h1 := h witFin ⟨witFin.nameD, fun _ => []⟩ wAllBoy (by decide)
  -- `partialFin.toInterp` and `witFin.toInterp` are the SAME term
  -- (`partialFin_toInterp` is `rfl`), so the two right-hand sides are
  -- interchangeable without a rewrite.
  exact absurd (h1.mpr (h0.mp (by decide))) (by decide)

/-- `(exists (...m) (P ...m))`: `P` holds of the length-2 sequence
`[false, false]` and of nothing else. -/
def sExMark : Sentence := .ex [.seqmark "m"] (.atom (.name "P") [.seqmark "m"])

/-- A bound sequence marker with `maxSeq = 0`: only the empty sequence
is folded over. -/
def seqFin0 : FiniteInterp Bool where
  domain := [false, true]
  deflt := false
  names := [("P", true)]
  strs := []
  fns := []
  rels := [(true, [false, false])]
  props := []
  maxSeq := 0

/-- The same interpretation with `maxSeq = 2`. -/
def seqFin1 : FiniteInterp Bool := { seqFin0 with maxSeq := 2 }

/-- `maxSeq` is invisible to `toInterp`. -/
theorem seqFin_toInterp : seqFin0.toInterp = seqFin1.toInterp := rfl

#guard seqFin0.satisfies sExMark == false
#guard seqFin1.satisfies sExMark == true

/-- **Hypothesis 3 (no sequence-marker quantifier) is not removable.**
`seqFin0` and `seqFin1` have the same `Interp` and decide `sExMark`
differently, so no agreement statement can cover it. -/
theorem seqQuant_hypothesis_necessary :
    ¬ ∀ (fi : FiniteInterp Bool) (v : FinVal Bool) (s : Sentence),
        (∀ x : Bool, x ∈ fi.domain) →
        (sat fi v s = true ↔ Sat fi.toInterp v.ind v.seq s) := by
  intro h
  have h0 := h seqFin0 ⟨seqFin0.nameD, fun _ => []⟩ sExMark (by decide)
  have h1 := h seqFin1 ⟨seqFin0.nameD, fun _ => []⟩ sExMark (by decide)
  -- `seqFin_toInterp` is `rfl`, so the two right-hand sides are the
  -- same proposition.
  exact absurd (h0.mpr (h1.mp (by decide))) (by decide)

/-! ### Hypothesis 1: lawful `BEq`

A two-element domain type whose `==` is constantly `true`. The
interpretation's tables never consult it (`rels`, `fns`, `props` are
empty and `nameD` compares STRINGS), so `nlFin.toInterp` is an
ordinary interpretation; only the checker's `.eq` clause reads the
unlawful `==`. -/

/-- A domain type with an unlawful `BEq`. -/
inductive NL where
  | a
  | b
  deriving Repr

instance : BEq NL := ⟨fun _ _ => true⟩

/-- An interpretation over `NL`: `p` denotes `a`, `q` denotes `b`. -/
def nlFin : FiniteInterp NL where
  domain := [NL.a, NL.b]
  deflt := NL.a
  names := [("p", NL.a), ("q", NL.b)]
  strs := []
  fns := []
  rels := []
  props := []

/-- The initial valuation. -/
def nlV : FinVal NL := ⟨nlFin.nameD, fun _ => []⟩

/-- `(= p q)`. -/
def eqPQ : Sentence := .eq (.name "p") (.name "q")

#guard sat nlFin nlV eqPQ

/-- **Hypothesis 1 (lawful `BEq`) is not removable.** The checker
decides `(= p q)` true because `==` is constantly true; `CL.Sat` reads
the clause as an equation between two distinct individuals and is
false. -/
theorem lawfulBEq_hypothesis_necessary :
    sat nlFin nlV eqPQ = true ∧ ¬ Sat nlFin.toInterp nlV.ind nlV.seq eqPQ := by
  refine ⟨by decide, ?_⟩
  show ¬ Sat nlFin.toInterp nlV.ind nlV.seq (.eq (.name "p") (.name "q"))
  rw [fsat_eq nlFin nlV.ind nlV.seq (.name "p") (.name "q"),
      ← denotTermFin_eq nlFin nlV (.name "p"),
      ← denotTermFin_eq nlFin nlV (.name "q")]
  have hne : ¬ (NL.a = NL.b) := by intro hh; cases hh
  exact hne

/-! ## What `satFin_eq` does NOT say about IKL

`toInterp.iProp` keys a proposition by the canonical CLIF text of its
sentence and ignores both valuations. Two facts follow, and neither is
a hypothesis of `satFin_eq`: they are properties of the reading it is
stated over. -/

/-- The `that`-reading is valuation-independent BY CONSTRUCTION — the
`FiniteSat.lean` header's third condition is a property of
`toInterp`, not a side condition on the agreement. -/
theorem iProp_valuation_independent {α : Type} [BEq α] (fi : FiniteInterp α)
    (s : Sentence) (nu1 nu2 : String → α) (sg1 sg2 : String → List α) :
    fi.toInterp.iProp s nu1 sg1 = fi.toInterp.iProp s nu2 sg2 := rfl

/-- Quantifying in collapses: a `that`-term denotes the same
individual at every valuation, so `(that (... x ...))` under a
quantifier binding `x` names ONE proposition. -/
theorem denotTermFin_that_constant {α : Type} [BEq α] (fi : FiniteInterp α)
    (s : Sentence) (v1 v2 : FinVal α) :
    denotTermFin fi v1 (.that s) = denotTermFin fi v2 (.that s) := rfl

/-- The finite reading is NOT IKL-coherent in general: `witFin` has an
empty `props` table, so every `that`-term denotes `false`, whose
relation extension is empty, while `(and)` is satisfied. `satFin_eq`
is agreement with `fi.toInterp`, not with IKL entailment. -/
theorem witFin_not_ikl_coherent : ¬ IklRespectsThat witFin.toInterp := by
  intro h
  have hsat : Sat witFin.toInterp witFin.toInterp.iName (fun _ => []) (.conj []) := by
    rw [sat_conj_iff witFin.toInterp witFin.toInterp.iName (fun _ => []) [],
        satAll_nil_iff witFin.toInterp witFin.toInterp.iName (fun _ => [])]
    trivial
  have hrel := (h (.conj []) witFin.toInterp.iName (fun _ => [])).mpr hsat
  have hb := (toInterp_rel witFin _ []).mp hrel
  -- `witFin.rels` has no row with an empty argument sequence, so the
  -- proposition's zero-ary extension is empty whatever it denotes.
  have hnil : ∀ y : Bool, witFin.relB y [] = false := by decide
  exact Bool.false_ne_true ((hnil _).symm.trans hb)

/-! ## Axiom audit -/

#print axioms satFin_eq
#print axioms satisfiesFin_eq
#print axioms wit_sat_boyBill
#print axioms wit_sat_ex
#print axioms wit_sat_neg
#print axioms wit_sat_restricted
#print axioms wit_not_sat_boySue
#print axioms wit_not_sat_allBoy
#print axioms domain_hypothesis_necessary
#print axioms seqQuant_hypothesis_necessary
#print axioms lawfulBEq_hypothesis_necessary
#print axioms iProp_valuation_independent
#print axioms witFin_not_ikl_coherent

end L4Factoidal.CL
