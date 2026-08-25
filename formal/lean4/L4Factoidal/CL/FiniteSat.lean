/-
L4Factoidal.CL.FiniteSat — an EXECUTABLE satisfaction checker over
finite interpretations.

`CL.Semantics` transcribes ISO/IEC 24707 §6.2/§6.3 as `Prop`-level
satisfaction over an arbitrary domain type — nothing there computes.
This module is the executable counterpart: a `FiniteInterp α` carries a
finite `domain` list and association-list lookups for the name /
string / function / relation / proposition maps, and `sat` decides
satisfaction by folding quantifiers over `domain`.
Tracking: https://github.com/danbri/factoidal/issues/580

## Relation to `CL.Semantics`

`FiniteInterp.toInterp` reads a finite interpretation as a
`Semantics.Interp` (same lookups, `Prop`-lifted relation). `sat` agrees
with `Sat` on `toInterp` under three conditions:

  1. every element of `α` occurs in `domain` (plain-name and restricted
     quantifiers fold over `domain`, `Sat` quantifies over `α`);
  2. the sentence has no SEQUENCE-MARKER quantifier binding: §6.3
     quantifies a bound marker over ALL finite sequences, which no fold
     can enumerate — `sat` folds over the sequences of length at most
     `maxSeq` (an under-approximation for `exists`, an
     over-approximation for `forall`);
  3. `BEq α` is lawful (`==` is `=`), and the interpretation of an IKL
     `that`-term does not depend on the valuation: `toInterp.iProp`
     keys propositions by the CANONICAL CLIF SERIALISATION of the
     enclosed sentence (`Sentence.toClif`), so two `that`-terms denote
     the same proposition exactly when their sentences serialise
     identically — quantifying-in (`(that (... x ...))` under a
     quantifier binding `x`) is therefore outside the agreement.

Term denotation agrees UNCONDITIONALLY (`denotTermFin_eq` /
`denotSeqFin_eq` below, proved by structural induction). For
satisfaction the full agreement proof (a mutual induction relating a
Bool fold to `Prop` quantifiers under conditions 1–3) is
disproportionate for this bootstrap; instead the four satisfaction
theorems of `CL.Examples` (`tiny_sat_conj`, `tiny_sat_ex`,
`tiny_sat_neg`, `tiny_sat_restricted`) are restated as `#guard`s
through the executable checker over the same interpretation, with
negative cases alongside so the checker is seen deciding both ways.

## Totality

No `sorry`, no `axiom`, no `partial`. The satisfaction group recurses
on an explicit fuel (the style of `CL.Clif`'s reader): every recursive
call decrements fuel by exactly 1 and moves to a strictly smaller
`Sentence.size` measure, so `size + 1` fuel never exhausts — the
`fuel = 0` arm returns `false` and is unreachable from the `sat`
entry point.
-/

import L4Factoidal.CL.Clif
import L4Factoidal.CL.Semantics
import L4Factoidal.CL.Examples

namespace L4Factoidal.CL

/-! ## Sentence size — the fuel bound -/

mutual

/-- Node count of a term (every constructor counts 1). -/
def Term.size : Term → Nat
  | .name _ => 1
  | .str _ => 1
  | .funapp op args => 1 + op.size + seqItemsSize args
  | .that s => 1 + s.size

/-- Node count of an argument sequence. -/
def seqItemsSize : List SeqItem → Nat
  | [] => 1
  | .term t :: r => 1 + t.size + seqItemsSize r
  | .seqmark _ :: r => 1 + seqItemsSize r

/-- Node count of a boundlist. -/
def bindingsSize : List Binding → Nat
  | [] => 1
  | .plain _ :: r => 1 + bindingsSize r
  | .seqmark _ :: r => 1 + bindingsSize r
  | .restricted _ g :: r => 1 + g.size + bindingsSize r

/-- Node count of a sentence. Bounds the recursion depth of the
satisfaction group: every arm of `satFuel`/`satAllFuel`/`satAnyFuel`/
`satFA`/`satEX` decrements fuel by 1 while its size measure (the
sentence's size; a boundlist's size plus its body's; a sentence list's
size) strictly decreases, so `size + 1` fuel suffices. -/
def Sentence.size : Sentence → Nat
  | .atom p args => 1 + p.size + seqItemsSize args
  | .eq a b => 1 + a.size + b.size
  | .conj ss => 1 + sentencesSize ss
  | .disj ss => 1 + sentencesSize ss
  | .neg s => 1 + s.size
  | .impl a b => 1 + a.size + b.size
  | .iff a b => 1 + a.size + b.size
  | .all bs body => 1 + bindingsSize bs + body.size
  | .ex bs body => 1 + bindingsSize bs + body.size

/-- Node count of a sentence list. -/
def sentencesSize : List Sentence → Nat
  | [] => 1
  | s :: r => 1 + s.size + sentencesSize r

end

/-! ## Finite interpretations -/

/-- A finite CL interpretation: the executable counterpart of
`Semantics.Interp`, every map an association-list lookup.

* `domain` — the individuals the quantifier folds range over. For
  agreement with the `Prop` semantics it must enumerate all of `α`;
  nothing checks that (a smaller list is a bounded model check).
* `deflt` — the individual every lookup misses to (also §6.2's
  non-emptiness witness).
* `names` / `strs` — name and quoted-string denotations.
* `fns` — the functional extension: `((op, args), value)` rows.
* `rels` — the relation extension: the FINITE SET of `(op, args)`
  pairs that hold (§6.2 `rel(x) ⊆ UD*` as an explicit list).
* `props` — IKL proposition denotations, keyed by the canonical CLIF
  serialisation of the `that`-sentence (see the module header on what
  that identification costs).
* `maxSeq` — sequence-marker quantifiers fold over the sequences over
  `domain` of length at most `maxSeq` (default 0: only the empty
  sequence). A BOUND, not §6.3's all-finite-sequences quantification. -/
structure FiniteInterp (α : Type) where
  domain : List α
  deflt : α
  names : List (String × α)
  strs : List (String × α)
  fns : List ((α × List α) × α)
  rels : List (α × List α)
  props : List (String × α)
  maxSeq : Nat := 0

variable {α : Type}

/-- Name denotation: first `names` row, else `deflt`. -/
def FiniteInterp.nameD [BEq α] (fi : FiniteInterp α) (n : String) : α :=
  ((fi.names.find? (·.1 == n)).map (·.2)).getD fi.deflt

/-- Quoted-string denotation: first `strs` row, else `deflt`. -/
def FiniteInterp.strD [BEq α] (fi : FiniteInterp α) (s : String) : α :=
  ((fi.strs.find? (·.1 == s)).map (·.2)).getD fi.deflt

/-- Functional extension: first `fns` row matching `(op, args)`, else
`deflt` (the totalisation `Semantics.Interp.fn` also applies). -/
def FiniteInterp.fnD [BEq α] (fi : FiniteInterp α) (op : α) (args : List α) : α :=
  ((fi.fns.find? (fun p => p.1.1 == op && p.1.2 == args)).map (·.2)).getD fi.deflt

/-- Relation extension: whether `(op, args)` is a `rels` row. -/
def FiniteInterp.relB [BEq α] (fi : FiniteInterp α) (op : α) (args : List α) : Bool :=
  fi.rels.any (fun p => p.1 == op && p.2 == args)

/-- IKL proposition denotation, keyed by canonical CLIF text. -/
def FiniteInterp.propD [BEq α] (fi : FiniteInterp α) (key : String) : α :=
  ((fi.props.find? (·.1 == key)).map (·.2)).getD fi.deflt

/-- Read a finite interpretation as a `Semantics.Interp` — the
structure the agreement statements are about. -/
def FiniteInterp.toInterp [BEq α] (fi : FiniteInterp α) : Interp where
  dom := α
  domWit := fi.deflt
  iName := fi.nameD
  iStr := fi.strD
  rel := fun x args => fi.relB x args = true
  fn := fi.fnD
  iProp := fun s _ _ => fi.propD s.toClif

/-! ## Valuations -/

/-- An executable valuation pair: names to individuals, sequence
markers to finite sequences — `Semantics`' `ν` and `σ` in one record. -/
structure FinVal (α : Type) where
  ind : String → α
  seq : String → List α

/-- Point-wise name update — `Semantics.updateInd` on the record. -/
def FinVal.updInd (v : FinVal α) (n : String) (x : α) : FinVal α :=
  { v with ind := updateInd v.ind n x }

/-- Point-wise sequence-marker update — `Semantics.updateSeq`. -/
def FinVal.updSeq (v : FinVal α) (m : String) (xs : List α) : FinVal α :=
  { v with seq := updateSeq v.seq m xs }

/-! ## Denotation — executable, and proved equal to `Semantics` -/

mutual

/-- The individual a term denotes (executable `denotTerm`). -/
def denotTermFin [BEq α] (fi : FiniteInterp α) (v : FinVal α) : Term → α
  | .name n => v.ind n
  | .str s => fi.strD s
  | .funapp op args => fi.fnD (denotTermFin fi v op) (denotSeqFin fi v args)
  | .that s => fi.propD s.toClif

/-- The sequence of individuals an argument sequence denotes
(executable `denotSeq`; a bound marker's sequence splices in). -/
def denotSeqFin [BEq α] (fi : FiniteInterp α) (v : FinVal α) : List SeqItem → List α
  | [] => []
  | .term t :: r => denotTermFin fi v t :: denotSeqFin fi v r
  | .seqmark m :: r => v.seq m ++ denotSeqFin fi v r

end

mutual

/-- Term denotation agrees with `Semantics.denotTerm` on `toInterp` —
unconditionally (denotation never quantifies). -/
theorem denotTermFin_eq [BEq α] (fi : FiniteInterp α) (v : FinVal α) :
    (t : Term) → denotTermFin fi v t = denotTerm fi.toInterp v.ind v.seq t
  | .name _ => rfl
  | .str _ => rfl
  | .funapp op args => by
      rw [denotTermFin, denotTermFin_eq fi v op, denotSeqFin_eq fi v args]
      rfl
  | .that _ => rfl

/-- Sequence denotation agrees with `Semantics.denotSeq` on
`toInterp`. -/
theorem denotSeqFin_eq [BEq α] (fi : FiniteInterp α) (v : FinVal α) :
    (items : List SeqItem) →
      denotSeqFin fi v items = denotSeq fi.toInterp v.ind v.seq items
  | [] => rfl
  | .term t :: r => by
      rw [denotSeqFin, denotTermFin_eq fi v t, denotSeqFin_eq fi v r]
      rfl
  | .seqmark _ :: r => by
      rw [denotSeqFin, denotSeqFin_eq fi v r]
      rfl

end

/-! ## Sequence enumeration -/

/-- All sequences over `dom` of length at most `k`, in fold order:
the empty sequence first, then one element prepended to each shorter
sequence. `(dom.length + 1) ^ k` entries at most. -/
def seqsUpTo (dom : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => [] :: dom.flatMap (fun x => (seqsUpTo dom k).map (x :: ·))

/-! ## Satisfaction — the executable checker

Clause for clause the mutual `Sat` family of `CL.Semantics`, with
`Prop` quantifiers replaced by folds: `∀ x : dom` becomes
`domain.all`, `∃` becomes `domain.any`, sequence-marker quantifiers
fold over `seqsUpTo domain maxSeq` (bounded — see the header). Fuel
per the `Sentence.size` bound. -/

mutual

/-- Satisfaction of a sentence (executable `Sat`). -/
def satFuel [BEq α] (fi : FiniteInterp α) : Nat → FinVal α → Sentence → Bool
  | 0, _, _ => false
  | fuel + 1, v, s =>
    match s with
    | .atom p args => fi.relB (denotTermFin fi v p) (denotSeqFin fi v args)
    | .eq a b => denotTermFin fi v a == denotTermFin fi v b
    | .conj ss => satAllFuel fi fuel v ss
    | .disj ss => satAnyFuel fi fuel v ss
    | .neg s1 => !satFuel fi fuel v s1
    | .impl a b => !satFuel fi fuel v a || satFuel fi fuel v b
    | .iff a b => satFuel fi fuel v a == satFuel fi fuel v b
    | .all bs body => satFA fi fuel v bs body
    | .ex bs body => satEX fi fuel v bs body

/-- Every sentence of the list is satisfied (executable `SatAll`). -/
def satAllFuel [BEq α] (fi : FiniteInterp α) : Nat → FinVal α → List Sentence → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, v, s :: r => satFuel fi fuel v s && satAllFuel fi fuel v r

/-- Some sentence of the list is satisfied (executable `SatAny`). -/
def satAnyFuel [BEq α] (fi : FiniteInterp α) : Nat → FinVal α → List Sentence → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => false
  | fuel + 1, v, s :: r => satFuel fi fuel v s || satAnyFuel fi fuel v r

/-- Universal quantification down a boundlist (executable
`SatForall`): plain names fold over `domain`, markers over
`seqsUpTo domain maxSeq`, restricted names over the guard's unary
extension. -/
def satFA [BEq α] (fi : FiniteInterp α) :
    Nat → FinVal α → List Binding → Sentence → Bool
  | 0, _, _, _ => false
  | fuel + 1, v, [], body => satFuel fi fuel v body
  | fuel + 1, v, .plain n :: r, body =>
      fi.domain.all (fun x => satFA fi fuel (v.updInd n x) r body)
  | fuel + 1, v, .seqmark m :: r, body =>
      (seqsUpTo fi.domain fi.maxSeq).all
        (fun xs => satFA fi fuel (v.updSeq m xs) r body)
  | fuel + 1, v, .restricted n g :: r, body =>
      fi.domain.all (fun x =>
        !fi.relB (denotTermFin fi v g) [x] || satFA fi fuel (v.updInd n x) r body)

/-- Existential quantification down a boundlist (executable
`SatExists`); a restriction conjoins. -/
def satEX [BEq α] (fi : FiniteInterp α) :
    Nat → FinVal α → List Binding → Sentence → Bool
  | 0, _, _, _ => false
  | fuel + 1, v, [], body => satFuel fi fuel v body
  | fuel + 1, v, .plain n :: r, body =>
      fi.domain.any (fun x => satEX fi fuel (v.updInd n x) r body)
  | fuel + 1, v, .seqmark m :: r, body =>
      (seqsUpTo fi.domain fi.maxSeq).any
        (fun xs => satEX fi fuel (v.updSeq m xs) r body)
  | fuel + 1, v, .restricted n g :: r, body =>
      fi.domain.any (fun x =>
        fi.relB (denotTermFin fi v g) [x] && satEX fi fuel (v.updInd n x) r body)

end

/-- Decide satisfaction under a valuation. Fuel `size + 1` per the
argument at `Sentence.size`: the `fuel = 0` arm is unreachable from
here. -/
def sat [BEq α] (fi : FiniteInterp α) (v : FinVal α) (s : Sentence) : Bool :=
  satFuel fi (s.size + 1) v s

/-- Sentence-level satisfaction: names denote what the interpretation
says, free sequence markers default to the empty sequence — the
executable `Satisfies`. -/
def FiniteInterp.satisfies [BEq α] (fi : FiniteInterp α) (s : Sentence) : Bool :=
  sat fi ⟨fi.nameD, fun _ => []⟩ s

/-! ## The `CL.Examples` interpretation, executably

`tinyFin` is `Examples.tiny` as a `FiniteInterp`: the same name
denotations (`tinyName`) and the same relation rows (`tinyRel`'s two
`true` cases), with `domain` enumerating every individual any of them
mentions plus the default 99. The four `tiny_sat_*` theorems of
`CL.Examples` are restated below as `#guard`s through `sat`; the
negative guards check the same tables decide `false` where the
`Prop`-level tables have no row. -/

/-- `Examples.tiny` as a finite interpretation. -/
def tinyFin : FiniteInterp Nat where
  domain := [0, 1, 10, 11, 99]
  deflt := 99
  names := [("Boy", 10), ("Girl", 11), ("Bill", 0), ("Sue", 1)]
  strs := []
  fns := []
  rels := [(10, [0]), (11, [1])]
  props := []

-- `tiny_sat_conj`: (and (Boy Bill) (Girl Sue)).
#guard tinyFin.satisfies exConj
-- `tiny_sat_ex`: (exists (x) (Boy x)).
#guard tinyFin.satisfies (.ex [.plain "x"] (.atom (.name "Boy") [.term (.name "x")]))
-- `tiny_sat_neg`: (not (Boy Sue)).
#guard tinyFin.satisfies (.neg (.atom (.name "Boy") [.term (.name "Sue")]))
-- `tiny_sat_restricted`: (forall ((x Boy)) (= x Bill)).
#guard tinyFin.satisfies (.all [.restricted "x" (.name "Boy")]
  (.eq (.name "x") (.name "Bill")))

-- The checker decides both ways: no table row, no satisfaction.
#guard tinyFin.satisfies (.atom (.name "Boy") [.term (.name "Sue")]) == false
#guard tinyFin.satisfies (.all [.plain "x"] (.atom (.name "Boy") [.term (.name "x")]))
  == false
-- Reader-to-checker round trip: the same conjunction, from CLIF text.
#guard (parseClifSentence "(and (Boy Bill) (Girl Sue))").toOption.map
  tinyFin.satisfies == some true
#guard (parseClifSentence "(or (Boy Sue) (Girl Bill))").toOption.map
  tinyFin.satisfies == some false

-- A bounded sequence-marker quantifier: with maxSeq 1 the sequences
-- [], [0], [1], [10], [11], [99] are enumerated, and [0] witnesses
-- (exists (...m) (Boy ...m)).
#guard { tinyFin with maxSeq := 1 : FiniteInterp Nat }.satisfies
  (.ex [.seqmark "m"] (.atom (.name "Boy") [.seqmark "m"])) == true
#guard tinyFin.satisfies
  (.ex [.seqmark "m"] (.atom (.name "Boy") [.seqmark "m"])) == false

/-- An IKL row: `ist` 5, context `c` 6, the proposition named by
`(that (P a))` is 7 (keyed by the sentence's canonical CLIF), and the
`ist` relation holds of (6, 7). -/
def tinyIkl : FiniteInterp Nat where
  domain := [5, 6, 7, 99]
  deflt := 99
  names := [("ist", 5), ("c", 6)]
  strs := []
  fns := []
  rels := [(5, [6, 7]), (7, [])]
  props := [("(P a)", 7)]

-- (ist c (that (P a))): the that-term denotes 7, the ist row fires.
#guard (parseClifSentence "(ist c (that (P a)))").toOption.map
  tinyIkl.satisfies == some true
-- ((that (P a))): zero-ary predication of the proposition — the (7, [])
-- row is exactly `IklRespectsThat`'s consequent for it.
#guard (parseClifSentence "((that (P a)))").toOption.map
  tinyIkl.satisfies == some true
#guard (parseClifSentence "(ist c (that (Q b)))").toOption.map
  tinyIkl.satisfies == some false

end L4Factoidal.CL
