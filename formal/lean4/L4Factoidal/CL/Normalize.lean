/-
L4Factoidal.CL.Normalize — IKL normalization: eliminate every
`that`-term from an IKL sentence, producing a Common Logic text.

Source: Pat Hayes, "A Satisfiability-Preserving Reduction of IKL to
Common Logic", Florida IHMC, 2009 (https://jfsowa.com/ikl/PHnsfs09.pdf,
fetched 2026-08-26). Section "Eliminating Proposition names" gives the
base case, "Quantifier intrusions" the parameterised case, and
"Multiple proposition names" the iteration; the paper's pseudocode is
quoted in the design note
`docs/designissues/2026-08-26-ikl-normalization.md`.
Tracking: https://github.com/danbri/factoidal/issues/580

## What the transformation does

An occurrence of the proposition term `(that S)` inside a sentence E
is replaced by a term built from a fresh name K and the INTRUSIONS of
that occurrence — the names (and sequence markers) that occur free in
S and are bound by a quantifier of E whose scope contains the
occurrence. With intrusions `U1 ... Un` the replacement term is
`(K U1 ... Un)` and the transformation emits one tail sentence

    (forall (U1 ... Un) (iff ((K U1 ... Un)) S'))

where `S'` is S with its own `that`-terms already eliminated. With no
intrusions the replacement term is the bare name `K` and the tail is
`(iff ((K)) S')`, which is the paper's base case. `((K ...))` is
predication of the K-term on the EMPTY argument sequence — the
cancelling-parentheses form whose IKL reading is
`CL.Semantics.sat_assert_that`.

## Shape of the recursion, and where Hayes's termination argument goes

The paper states the algorithm as a loop over a text ("UNTIL E
contains no proposition names DO ... substitute (K U1 ... Un) for P in
E"), with a recursive call `NORMAL` on each tail, and says only that
"an obvious inductive argument shows that this process of
normalization must terminate with a CL text". The loop form needs a
measure, because a step that eliminates an OUTERMOST `that` moves the
proposition names nested inside it out into a tail sentence, so the
count of proposition names in the text does not fall: eliminating
`(that (K (that (not (D)))))` leaves `(that (not (D)))` in the tail.
`Sentence.thatWeight` below is such a measure — each occurrence
weighted by 2 raised to the number of `that`s enclosing it — and
`thatWeight_that` records the strict drop the loop step realises.

This module does not need it. `normSent` is a single traversal that
recurses only into strict subterms (the body of a `that` is a
subsentence), so Lean accepts it by STRUCTURAL recursion, with no
measure, no `decreasing_by`, and no `partial`. The traversal visits
outermost `that`s first and recurses into the body immediately, which
reproduces the paper's `gensym` numbering exactly — see the Knower pin
below, where the outer proposition name is `prop4` and the one nested
inside it is `prop5`.

The traversal also gives each OCCURRENCE its own fresh name, where the
paper's loop substitutes one name for every occurrence of one
proposition name at once. Two syntactically equal `that`-terms under
different quantifiers have different intrusion sets, so the paper's
"substitute (K U1 ... Un) for P in E" is not well defined at that
level of generality; per-occurrence naming is. No paradox in the paper
has a repeated proposition name, so the pins are unaffected.

## Skolemization

The paper Skolemizes E first, so that every intrusion is universal,
and re-Skolemizes each tail because the biconditional exposes a
quantifier. This module does NOT Skolemize. The tail
`(forall (U) (iff ((K U)) S'))` is satisfied in the constructed model
whatever quantifier bound U, because the functional extension given to
K is total: it sends EVERY argument tuple to the proposition the body
denotes at that tuple. The Skolemization step is therefore not part of
the satisfiability-preservation argument; see
`CL.NormalizeSemantics` and the design note.
-/

import L4Factoidal.CL.Syntax
import L4Factoidal.CL.Clif

namespace L4Factoidal.CL

/-! ## Free names and free sequence markers

Free occurrences per ISO/IEC 24707 §6.3's binding discipline, as
`CL.Semantics.SatForall` / `SatExists` implement it: a boundlist binds
its names down the rest of the list AND in the body, and the guard of
a restricted binding is read in the scope OUTSIDE that binding (so a
guard sees the names bound to its left, not its own name). -/

/-- Drop every occurrence of `n`. -/
def removeName (n : String) (l : List String) : List String :=
  l.filter (fun m => m != n)

/-- Add `n` at the END, keeping the list duplicate-free. Intrusion
lists are built with this, so they come out in outermost-first order
and a shadowed name is listed once. -/
def addName (l : List String) (n : String) : List String :=
  if l.contains n then l else l ++ [n]

/-- Names a boundlist binds. -/
def bindNames : List Binding → List String
  | [] => []
  | .plain n :: r => n :: bindNames r
  | .seqmark _ :: r => bindNames r
  | .restricted n _ :: r => n :: bindNames r

/-- Sequence markers a boundlist binds. -/
def bindMarks : List Binding → List String
  | [] => []
  | .plain _ :: r => bindMarks r
  | .seqmark m :: r => m :: bindMarks r
  | .restricted _ _ :: r => bindMarks r

/-- Drop every occurrence of any name of `ns`. -/
def removeNames : List String → List String → List String
  | [], l => l
  | n :: r, l => removeNames r (removeName n l)

mutual

/-- Names occurring free in a term. The body of a `that` counts:
`(that (P x))` has `x` free, which is what makes `x` an intrusion when
a quantifier outside the `that` binds it. -/
def freeNamesT : Term → List String
  | .name n => [n]
  | .str _ => []
  | .funapp op args => freeNamesT op ++ freeNamesSeq args
  | .that s => freeNamesS s

/-- Names occurring free in an argument sequence. -/
def freeNamesSeq : List SeqItem → List String
  | [] => []
  | .term t :: r => freeNamesT t ++ freeNamesSeq r
  | .seqmark _ :: r => freeNamesSeq r

/-- Names occurring free in the GUARDS of a boundlist. The guard of a
restricted binding is read outside that binding, so it sees the names
bound to its left only. -/
def freeNamesGuards : List Binding → List String
  | [] => []
  | .plain n :: r => removeName n (freeNamesGuards r)
  | .seqmark _ :: r => freeNamesGuards r
  | .restricted n g :: r => freeNamesT g ++ removeName n (freeNamesGuards r)

/-- Names occurring free in a sentence. -/
def freeNamesS : Sentence → List String
  | .atom p args => freeNamesT p ++ freeNamesSeq args
  | .eq a b => freeNamesT a ++ freeNamesT b
  | .conj ss => freeNamesSs ss
  | .disj ss => freeNamesSs ss
  | .neg s => freeNamesS s
  | .impl a b => freeNamesS a ++ freeNamesS b
  | .iff a b => freeNamesS a ++ freeNamesS b
  | .all bs body => freeNamesGuards bs ++ removeNames (bindNames bs) (freeNamesS body)
  | .ex bs body => freeNamesGuards bs ++ removeNames (bindNames bs) (freeNamesS body)

/-- Names occurring free in a sentence list. -/
def freeNamesSs : List Sentence → List String
  | [] => []
  | s :: r => freeNamesS s ++ freeNamesSs r

end

mutual

/-- Sequence markers occurring free in a term. -/
def freeMarksT : Term → List String
  | .name _ => []
  | .str _ => []
  | .funapp op args => freeMarksT op ++ freeMarksSeq args
  | .that s => freeMarksS s

/-- Sequence markers occurring free in an argument sequence. -/
def freeMarksSeq : List SeqItem → List String
  | [] => []
  | .term t :: r => freeMarksT t ++ freeMarksSeq r
  | .seqmark m :: r => m :: freeMarksSeq r

/-- Sequence markers occurring free in the GUARDS of a boundlist. -/
def freeMarksGuards : List Binding → List String
  | [] => []
  | .plain _ :: r => freeMarksGuards r
  | .seqmark m :: r => removeName m (freeMarksGuards r)
  | .restricted _ g :: r => freeMarksT g ++ freeMarksGuards r

/-- Sequence markers occurring free in a sentence. -/
def freeMarksS : Sentence → List String
  | .atom p args => freeMarksT p ++ freeMarksSeq args
  | .eq a b => freeMarksT a ++ freeMarksT b
  | .conj ss => freeMarksSs ss
  | .disj ss => freeMarksSs ss
  | .neg s => freeMarksS s
  | .impl a b => freeMarksS a ++ freeMarksS b
  | .iff a b => freeMarksS a ++ freeMarksS b
  | .all bs body => freeMarksGuards bs ++ removeNames (bindMarks bs) (freeMarksS body)
  | .ex bs body => freeMarksGuards bs ++ removeNames (bindMarks bs) (freeMarksS body)

/-- Sequence markers occurring free in a sentence list. -/
def freeMarksSs : List Sentence → List String
  | [] => []
  | s :: r => freeMarksS s ++ freeMarksSs r

end

/-! ## The `that`-weight measure

The measure Hayes's loop form needs. Each `that` occurrence counts
`2 ^ d` where `d` is the number of `that`s enclosing it, written here
as the recurrence `w (that S) = 1 + 2 * w S`. `thatWeight_that` below
is the inequality a loop step turns on: the tail sentence the step
emits weighs `w S`, and the replacement term weighs 0, so a step that
eliminates one occurrence of `(that S)` drops the weight of the text
by at least `1 + w S`. -/

mutual

/-- `that`-weight of a term. -/
def Term.thatWeight : Term → Nat
  | .name _ => 0
  | .str _ => 0
  | .funapp op args => op.thatWeight + seqThatWeight args
  | .that s => 1 + 2 * s.thatWeight

/-- `that`-weight of an argument sequence. -/
def seqThatWeight : List SeqItem → Nat
  | [] => 0
  | .term t :: r => t.thatWeight + seqThatWeight r
  | .seqmark _ :: r => seqThatWeight r

/-- `that`-weight of a boundlist (guards can carry `that`s). -/
def bindsThatWeight : List Binding → Nat
  | [] => 0
  | .plain _ :: r => bindsThatWeight r
  | .seqmark _ :: r => bindsThatWeight r
  | .restricted _ g :: r => g.thatWeight + bindsThatWeight r

/-- `that`-weight of a sentence. -/
def Sentence.thatWeight : Sentence → Nat
  | .atom p args => p.thatWeight + seqThatWeight args
  | .eq a b => a.thatWeight + b.thatWeight
  | .conj ss => sentsThatWeight ss
  | .disj ss => sentsThatWeight ss
  | .neg s => s.thatWeight
  | .impl a b => a.thatWeight + b.thatWeight
  | .iff a b => a.thatWeight + b.thatWeight
  | .all bs body => bindsThatWeight bs + body.thatWeight
  | .ex bs body => bindsThatWeight bs + body.thatWeight

/-- `that`-weight of a sentence list. -/
def sentsThatWeight : List Sentence → Nat
  | [] => 0
  | s :: r => s.thatWeight + sentsThatWeight r

end

/-- The loop step's strict drop: eliminating one occurrence of
`(that S)` replaces a term of weight `1 + 2 * w S` by a term of weight
0 and emits a tail of weight `w S`. -/
theorem thatWeight_that (s : Sentence) :
    Sentence.thatWeight s < (Term.that s).thatWeight := by
  simp [Term.thatWeight]
  omega

/-! ## Counting proposition names

The number of `that` occurrences — the number of iterations of the
paper's main loop, and the number of tail sentences this module's
traversal emits. -/

mutual

/-- Number of `that` occurrences in a term. -/
def Term.thatCount : Term → Nat
  | .name _ => 0
  | .str _ => 0
  | .funapp op args => op.thatCount + seqThatCount args
  | .that s => 1 + s.thatCount

/-- Number of `that` occurrences in an argument sequence. -/
def seqThatCount : List SeqItem → Nat
  | [] => 0
  | .term t :: r => t.thatCount + seqThatCount r
  | .seqmark _ :: r => seqThatCount r

/-- Number of `that` occurrences in a boundlist. -/
def bindsThatCount : List Binding → Nat
  | [] => 0
  | .plain _ :: r => bindsThatCount r
  | .seqmark _ :: r => bindsThatCount r
  | .restricted _ g :: r => g.thatCount + bindsThatCount r

/-- Number of `that` occurrences in a sentence. -/
def Sentence.thatCount : Sentence → Nat
  | .atom p args => p.thatCount + seqThatCount args
  | .eq a b => a.thatCount + b.thatCount
  | .conj ss => sentsThatCount ss
  | .disj ss => sentsThatCount ss
  | .neg s => s.thatCount
  | .impl a b => a.thatCount + b.thatCount
  | .iff a b => a.thatCount + b.thatCount
  | .all bs body => bindsThatCount bs + body.thatCount
  | .ex bs body => bindsThatCount bs + body.thatCount

/-- Number of `that` occurrences in a sentence list. -/
def sentsThatCount : List Sentence → Nat
  | [] => 0
  | s :: r => s.thatCount + sentsThatCount r

end

/-! ## Fresh names

The paper's `gensym()`. Names are allocated from one counter that runs
across the whole normalization, including the recursive treatment of
tails, which is what makes the Knower's nested proposition name
`prop5` rather than a restart at `prop1`. -/

/-- The `k`-th proposition name. -/
def propName (k : Nat) : String := "prop" ++ toString k

/-! ## Scope tracking

`bnd` is the list of names bound by quantifiers whose scope contains
the position being visited, outermost first; `bm` the same for
sequence markers. -/

/-- Extend a scope list with everything a boundlist binds. -/
def addNames (l : List String) : List String → List String
  | [] => l
  | n :: r => addNames (addName l n) r

/-! ## The transformation

`normSent bnd bm c s` returns the transformed sentence, the tail
sentences it emitted (the K-defining biconditionals), and the next
free counter value. Every recursive call is on a strict subterm, so
the group is structurally recursive. -/

/-- The replacement term for a proposition name: the bare name when
there are no intrusions (the paper's base case, `prop1`), otherwise
the skolem-like term `(K U1 ... Un)`. -/
def kTerm (k : String) (u : List String) (um : List String) : Term :=
  if u.isEmpty && um.isEmpty then .name k
  else .funapp (.name k)
    (u.map (fun n => SeqItem.term (.name n)) ++ um.map SeqItem.seqmark)

/-- The tail sentence defining a proposition name:
`(forall (U1 ... Un) (iff ((K U1 ... Un)) S))`, dropping the empty
quantifier in the base case. -/
def kTail (k : String) (u um : List String) (body : Sentence) : Sentence :=
  let core := Sentence.iff (.atom (kTerm k u um) []) body
  if u.isEmpty && um.isEmpty then core
  else .all (u.map Binding.plain ++ um.map Binding.seqmark) core

mutual

/-- Transform a term. -/
def normTerm (bnd bm : List String) (c : Nat) : Term → Term × List Sentence × Nat
  | .name n => (.name n, [], c)
  | .str s => (.str s, [], c)
  | .funapp op args =>
      let r1 := normTerm bnd bm c op
      let r2 := normSeq bnd bm r1.2.2 args
      (.funapp r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .that s =>
      let u := bnd.filter (fun n => (freeNamesS s).contains n)
      let um := bm.filter (fun m => (freeMarksS s).contains m)
      let k := propName c
      let r := normSent u um (c + 1) s
      (kTerm k u um, kTail k u um r.1 :: r.2.1, r.2.2)

/-- Transform an argument sequence. -/
def normSeq (bnd bm : List String) (c : Nat) :
    List SeqItem → List SeqItem × List Sentence × Nat
  | [] => ([], [], c)
  | .term t :: r =>
      let r1 := normTerm bnd bm c t
      let r2 := normSeq bnd bm r1.2.2 r
      (.term r1.1 :: r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .seqmark m :: r =>
      let r2 := normSeq bnd bm c r
      (.seqmark m :: r2.1, r2.2.1, r2.2.2)

/-- Transform a boundlist's guards, threading the scope: the guard of
a restricted binding sees the names bound to its left. -/
def normBinds (bnd bm : List String) (c : Nat) :
    List Binding → List Binding × List Sentence × Nat
  | [] => ([], [], c)
  | .plain n :: r =>
      let r2 := normBinds (addName bnd n) bm c r
      (.plain n :: r2.1, r2.2.1, r2.2.2)
  | .seqmark m :: r =>
      let r2 := normBinds bnd (addName bm m) c r
      (.seqmark m :: r2.1, r2.2.1, r2.2.2)
  | .restricted n g :: r =>
      let r1 := normTerm bnd bm c g
      let r2 := normBinds (addName bnd n) bm r1.2.2 r
      (.restricted n r1.1 :: r2.1, r1.2.1 ++ r2.2.1, r2.2.2)

/-- Transform a sentence. -/
def normSent (bnd bm : List String) (c : Nat) :
    Sentence → Sentence × List Sentence × Nat
  | .atom p args =>
      let r1 := normTerm bnd bm c p
      let r2 := normSeq bnd bm r1.2.2 args
      (.atom r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .eq a b =>
      let r1 := normTerm bnd bm c a
      let r2 := normTerm bnd bm r1.2.2 b
      (.eq r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .conj ss =>
      let r := normSents bnd bm c ss
      (.conj r.1, r.2.1, r.2.2)
  | .disj ss =>
      let r := normSents bnd bm c ss
      (.disj r.1, r.2.1, r.2.2)
  | .neg s =>
      let r := normSent bnd bm c s
      (.neg r.1, r.2.1, r.2.2)
  | .impl a b =>
      let r1 := normSent bnd bm c a
      let r2 := normSent bnd bm r1.2.2 b
      (.impl r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .iff a b =>
      let r1 := normSent bnd bm c a
      let r2 := normSent bnd bm r1.2.2 b
      (.iff r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .all bs body =>
      let r1 := normBinds bnd bm c bs
      let r2 := normSent (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
                  r1.2.2 body
      (.all r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)
  | .ex bs body =>
      let r1 := normBinds bnd bm c bs
      let r2 := normSent (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
                  r1.2.2 body
      (.ex r1.1 r2.1, r1.2.1 ++ r2.2.1, r2.2.2)

/-- Transform a sentence list. -/
def normSents (bnd bm : List String) (c : Nat) :
    List Sentence → List Sentence × List Sentence × Nat
  | [] => ([], [], c)
  | s :: r =>
      let r1 := normSent bnd bm c s
      let r2 := normSents bnd bm r1.2.2 r
      (r1.1 :: r2.1, r1.2.1 ++ r2.2.1, r2.2.2)

end

/-! ## Entry points -/

/-- Normalize one sentence, allocating proposition names from `start`.
Returns the head and the tail sentences; the paper's returned text is
`head :: tail`. -/
def normalizeFrom (start : Nat) (s : Sentence) : Sentence × List Sentence :=
  let r := normSent [] [] start s
  (r.1, r.2.1)

/-- Normalize one sentence with names from `prop1`. -/
def normalizeSentence (s : Sentence) : Sentence × List Sentence :=
  normalizeFrom 1 s

/-- Normalize a text: one head sentence list, one shared tail, one
counter running across the whole text. -/
def normalizeText (ss : List Sentence) : List Sentence × List Sentence :=
  let r := normSents [] [] 1 ss
  (r.1, r.2.1)

/-- Normalize CLIF source, returning the head text followed by the
tail sentences, each rendered back to CLIF. `none` on a parse error. -/
def normalizeClifFrom (start : Nat) (input : String) : Option (List String) :=
  match parseClifSentence input with
  | .ok s =>
      let r := normalizeFrom start s
      some (r.1.toClif :: r.2.map Sentence.toClif)
  | .error _ => none

/-- Number of iterations of the paper's main loop the input needs:
one per `that` occurrence. `none` on a parse error. -/
def clifThatCount (input : String) : Option Nat :=
  match parseClifSentence input with
  | .ok s => some s.thatCount
  | .error _ => none

/-! ## The four paradoxes

The paper's illustrative exercise ("Normalizing the paradoxes"), which
applies the transformation to the sentences reviewed in Hayes 2009,
"First-order logic can describe its own propositions". Each input is
the paper's own CLIF text; each expected output is the paper's own
result, in this module's canonical spacing. The proposition-name
counter is started where the paper's running `gensym` had reached, so
the names match the paper verbatim.

Every `#guard` runs during elaboration, so `lake build` is the test
run (`skills/factoidal-lean-basics`, Build/test/demo). -/

/-- 1. That Nothing Is True. -/
def paradoxTNIT : String := "((that (forall (p)(not (p)))))"

/-- 2. The Liar. -/
def paradoxLiar : String := "(= p (that (not (p))))"

/-- 3. Kripke's semantic paradox. -/
def paradoxKripke : String :=
  "(forall (x)(iff (S x)(= x (that (forall (y)(if (S y) (not (y)) )) )) ))"

/-- 4. The Knower (Kaplan and Montague 1950) — the fourth sentence of
the paper's text, the one carrying proposition names. The paper's
first three Knower sentences contain none and pass through unchanged.
-/
def paradoxKnower : String := "(= D (that (K (that (not (D))))))"

-- 1. That Nothing Is True: one iteration, no intrusions, so the base
-- case applies and the replacement term is the bare name.
#guard clifThatCount paradoxTNIT == some 1
#guard normalizeClifFrom 1 paradoxTNIT ==
  some ["(prop1)",
        "(iff (prop1) (forall (p) (not (p))))"]

-- 2. The Liar. `p` is free in the body and free in the sentence, so it
-- is not an intrusion and the tail keeps it free.
#guard clifThatCount paradoxLiar == some 1
#guard normalizeClifFrom 2 paradoxLiar ==
  some ["(= p prop2)",
        "(iff (prop2) (not (p)))"]

-- 3. Kripke's semantic paradox. The `that` is inside the scope of
-- `(forall (x))`, and `x` does NOT occur free in the body, so the
-- intrusion set is empty and the replacement term stays a bare name.
-- This is the case that fixes the definition of intrusion as
-- enclosing-bound INTERSECT free-in-body.
#guard clifThatCount paradoxKripke == some 1
#guard normalizeClifFrom 3 paradoxKripke ==
  some ["(forall (x) (iff (S x) (= x prop3)))",
        "(iff (prop3) (forall (y) (if (S y) (not (y)))))"]

-- 4. The Knower — the paper's only example needing more than one
-- iteration of the main loop. Two `that` occurrences, one nested
-- inside the other; two iterations; two tail sentences. The outer
-- proposition name is allocated first (`prop4`) and the nested one
-- second (`prop5`), which is the numbering the paper prints.
#guard clifThatCount paradoxKnower == some 2
#guard normalizeClifFrom 4 paradoxKnower ==
  some ["(= D prop4)",
        "(iff (prop4) (K prop5))",
        "(iff (prop5) (not (D)))"]

-- One tail sentence per iteration, in every case.
#guard (normalizeClifFrom 1 paradoxTNIT).map List.length == some 2
#guard (normalizeClifFrom 2 paradoxLiar).map List.length == some 2
#guard (normalizeClifFrom 3 paradoxKripke).map List.length == some 2
#guard (normalizeClifFrom 4 paradoxKnower).map List.length == some 3

-- Every sentence of every output text is ISO/IEC 24707 CL: no
-- proposition name survives. This is the "terminates with a CL text"
-- claim, checked on the paper's own examples; `normalize_pureCL` in
-- `CL.NormalizeSemantics` proves it for every input.
#guard (normalizeClifFrom 1 paradoxTNIT).map
  (fun l => l.all (fun t => pureOf t == some true)) == some true
#guard (normalizeClifFrom 2 paradoxLiar).map
  (fun l => l.all (fun t => pureOf t == some true)) == some true
#guard (normalizeClifFrom 3 paradoxKripke).map
  (fun l => l.all (fun t => pureOf t == some true)) == some true
#guard (normalizeClifFrom 4 paradoxKnower).map
  (fun l => l.all (fun t => pureOf t == some true)) == some true

/-! ## The quantifier-intrusion examples

The three sentences of the paper's "Quantifier intrusions" section.
The first and third reproduce the paper's printed output exactly (up
to the paper's own counter, which had reached `prop2` by the third).
The second differs, and the difference is Skolemization: the paper
Skolemizes before the mapping, so `(exists (y) ...)` becomes the term
`(sk1 x)` and only `x` intrudes, giving `(prop1 x)`. This module does
not Skolemize, so `y` intrudes as well and the replacement term is
`(prop1 x y)`. See the module header and the design note for why the
tail still holds in the constructed model when the intruding
quantifier is existential. -/

#guard normalizeClifFrom 1
    "(FredBelieves (that (forall ((x Human))(exists (y)(hasFather x y)))) )" ==
  some ["(FredBelieves prop1)",
        "(iff (prop1) (forall ((x Human)) (exists (y) (hasFather x y))))"]

#guard normalizeClifFrom 1
    "(forall ((x Human))(exists (y)(FredBelieves (that (hasFather x y)) )))" ==
  some ["(forall ((x Human)) (exists (y) (FredBelieves (prop1 x y))))",
        "(forall (x y) (iff ((prop1 x y)) (hasFather x y)))"]

#guard normalizeClifFrom 1
    "(forall ((x Human))(FredBelieves (that (exists (y)(hasFather x y))) ))" ==
  some ["(forall ((x Human)) (FredBelieves (prop1 x)))",
        "(forall (x) (iff ((prop1 x)) (exists (y) (hasFather x y))))"]

/-! ## Side conditions for the semantic theorems

Three decidable conditions that `CL.NormalizeSemantics` needs, plus
the record of which fresh name names which proposition. All of them
mirror the traversal above, so each recursive case of a soundness
proof gets its sub-condition by unfolding. -/

mutual

/-- Every name occurring in a term, binder positions included. -/
def allNamesT : Term → List String
  | .name n => [n]
  | .str _ => []
  | .funapp op args => allNamesT op ++ allNamesSeq args
  | .that s => allNamesS s

/-- Every name occurring in an argument sequence. -/
def allNamesSeq : List SeqItem → List String
  | [] => []
  | .term t :: r => allNamesT t ++ allNamesSeq r
  | .seqmark _ :: r => allNamesSeq r

/-- Every name occurring in a boundlist, the bound names included. -/
def allNamesBinds : List Binding → List String
  | [] => []
  | .plain n :: r => n :: allNamesBinds r
  | .seqmark _ :: r => allNamesBinds r
  | .restricted n g :: r => n :: (allNamesT g ++ allNamesBinds r)

/-- Every name occurring in a sentence. -/
def allNamesS : Sentence → List String
  | .atom p args => allNamesT p ++ allNamesSeq args
  | .eq a b => allNamesT a ++ allNamesT b
  | .conj ss => allNamesSs ss
  | .disj ss => allNamesSs ss
  | .neg s => allNamesS s
  | .impl a b => allNamesS a ++ allNamesS b
  | .iff a b => allNamesS a ++ allNamesS b
  | .all bs body => allNamesBinds bs ++ allNamesS body
  | .ex bs body => allNamesBinds bs ++ allNamesS body

/-- Every name occurring in a sentence list. -/
def allNamesSs : List Sentence → List String
  | [] => []
  | s :: r => allNamesS s ++ allNamesSs r

end

/-- The fresh names this module allocates all begin `prop`. -/
def isFreshName (n : String) : Bool := "prop".isPrefixOf n

/-- No name of the sentence collides with the fresh-name space, so
`propName` is fresh for it at every counter value. -/
def freshFor (s : Sentence) : Bool := (allNamesS s).all (fun n => !isFreshName n)

/-- Every allocated name is in the fresh-name space. -/
theorem isFreshName_propName (k : Nat) : isFreshName (propName k) = true := by
  simp [isFreshName, propName, String.isPrefixOf]

mutual

/-- No quantifier intrudes into a proposition name: at every `that`
node the intrusion lists the traversal computes are empty. -/
def noIntrT (bnd bm : List String) : Term → Bool
  | .name _ => true
  | .str _ => true
  | .funapp op args => noIntrT bnd bm op && noIntrSeq bnd bm args
  | .that s =>
      (bnd.filter (fun n => (freeNamesS s).contains n)).isEmpty
        && (bm.filter (fun m => (freeMarksS s).contains m)).isEmpty
        && noIntrS [] [] s

/-- No intrusion anywhere in an argument sequence. -/
def noIntrSeq (bnd bm : List String) : List SeqItem → Bool
  | [] => true
  | .term t :: r => noIntrT bnd bm t && noIntrSeq bnd bm r
  | .seqmark _ :: r => noIntrSeq bnd bm r

/-- No intrusion anywhere in a boundlist's guards. -/
def noIntrBinds (bnd bm : List String) : List Binding → Bool
  | [] => true
  | .plain n :: r => noIntrBinds (addName bnd n) bm r
  | .seqmark m :: r => noIntrBinds bnd (addName bm m) r
  | .restricted n g :: r => noIntrT bnd bm g && noIntrBinds (addName bnd n) bm r

/-- No intrusion anywhere in a sentence. -/
def noIntrS (bnd bm : List String) : Sentence → Bool
  | .atom p args => noIntrT bnd bm p && noIntrSeq bnd bm args
  | .eq a b => noIntrT bnd bm a && noIntrT bnd bm b
  | .conj ss => noIntrSs bnd bm ss
  | .disj ss => noIntrSs bnd bm ss
  | .neg s => noIntrS bnd bm s
  | .impl a b => noIntrS bnd bm a && noIntrS bnd bm b
  | .iff a b => noIntrS bnd bm a && noIntrS bnd bm b
  | .all bs body =>
      noIntrBinds bnd bm bs
        && noIntrS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs)) body
  | .ex bs body =>
      noIntrBinds bnd bm bs
        && noIntrS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs)) body

/-- No intrusion anywhere in a sentence list. -/
def noIntrSs (bnd bm : List String) : List Sentence → Bool
  | [] => true
  | s :: r => noIntrS bnd bm s && noIntrSs bnd bm r

end

/-- No quantifier of the sentence intrudes into any proposition name
it contains. All four of the paper's paradoxes satisfy this. -/
def noIntrusion (s : Sentence) : Bool := noIntrS [] [] s

mutual

/-- Which proposition each allocated name names: the fresh name
paired with the ORIGINAL `that`-body, in the order the traversal
allocates them and with the traversal's own counter threading. -/
def assignT (bnd bm : List String) (c : Nat) : Term → List (String × Sentence)
  | .name _ => []
  | .str _ => []
  | .funapp op args =>
      assignT bnd bm c op ++ assignSeq bnd bm (normTerm bnd bm c op).2.2 args
  | .that s =>
      (propName c, s) ::
        assignS (bnd.filter (fun n => (freeNamesS s).contains n))
          (bm.filter (fun m => (freeMarksS s).contains m)) (c + 1) s

/-- Allocations down an argument sequence. -/
def assignSeq (bnd bm : List String) (c : Nat) :
    List SeqItem → List (String × Sentence)
  | [] => []
  | .term t :: r =>
      assignT bnd bm c t ++ assignSeq bnd bm (normTerm bnd bm c t).2.2 r
  | .seqmark _ :: r => assignSeq bnd bm c r

/-- Allocations down a boundlist. -/
def assignBinds (bnd bm : List String) (c : Nat) :
    List Binding → List (String × Sentence)
  | [] => []
  | .plain n :: r => assignBinds (addName bnd n) bm c r
  | .seqmark m :: r => assignBinds bnd (addName bm m) c r
  | .restricted n g :: r =>
      assignT bnd bm c g
        ++ assignBinds (addName bnd n) bm (normTerm bnd bm c g).2.2 r

/-- Allocations down a sentence. -/
def assignS (bnd bm : List String) (c : Nat) :
    Sentence → List (String × Sentence)
  | .atom p args =>
      assignT bnd bm c p ++ assignSeq bnd bm (normTerm bnd bm c p).2.2 args
  | .eq a b => assignT bnd bm c a ++ assignT bnd bm (normTerm bnd bm c a).2.2 b
  | .conj ss => assignSs bnd bm c ss
  | .disj ss => assignSs bnd bm c ss
  | .neg s => assignS bnd bm c s
  | .impl a b => assignS bnd bm c a ++ assignS bnd bm (normSent bnd bm c a).2.2 b
  | .iff a b => assignS bnd bm c a ++ assignS bnd bm (normSent bnd bm c a).2.2 b
  | .all bs body =>
      assignBinds bnd bm c bs
        ++ assignS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
             (normBinds bnd bm c bs).2.2 body
  | .ex bs body =>
      assignBinds bnd bm c bs
        ++ assignS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
             (normBinds bnd bm c bs).2.2 body

/-- Allocations down a sentence list. -/
def assignSs (bnd bm : List String) (c : Nat) :
    List Sentence → List (String × Sentence)
  | [] => []
  | s :: r => assignS bnd bm c s ++ assignSs bnd bm (normSent bnd bm c s).2.2 r

end

/-! ## Scope-list membership -/

/-- `addName` adds exactly its argument. -/
theorem mem_addName {m n : String} {l : List String} :
    m ∈ addName l n ↔ m ∈ l ∨ m = n := by
  unfold addName
  by_cases h : n ∈ l
  · simp only [h, decide_true, List.contains_eq_mem, if_pos]
    constructor
    · exact Or.inl
    · rintro (hm | rfl)
      · exact hm
      · exact h
  · simp [h]

/-- `addNames` adds exactly the names of its second argument. -/
theorem mem_addNames {m : String} {ns : List String} :
    ∀ {l : List String}, m ∈ addNames l ns ↔ m ∈ l ∨ m ∈ ns := by
  induction ns with
  | nil => intro l; simp [addNames]
  | cons n r ih =>
      intro l
      rw [addNames, ih, mem_addName]
      constructor
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inr (by simp)
        · exact Or.inr (by simp [h])
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr h

end L4Factoidal.CL
