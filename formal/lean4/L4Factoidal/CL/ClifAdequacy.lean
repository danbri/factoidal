/-
L4Factoidal.CL.ClifAdequacy — what a CLIF reader-adequacy claim can
honestly be here, the fragment it holds on, the counterexample that
bounds it, and why the general statement is not proved.
Tracking: https://github.com/danbri/factoidal/issues/609 item 2.

## What "the reader denotes per ISO/IEC 24707 Annex A" can mean

Annex A specifies CLIF's CONCRETE syntax. It carries no meaning
function of its own: the meaning of a CLIF text is the meaning of the
abstract sentence it denotes, and that is clause 6, which
`CL/Semantics.lean` transcribes over `CL/Syntax.lean`'s abstract
syntax. This tree holds no second, independent formalisation of Annex
A, so "the reader is adequate to Annex A" cannot be an agreement
between two formal objects the way `satFin_eq` is one between the
checker and `CL.Sat`.

What CAN be stated is the ROUND TRIP against the serialiser — the only
other object in the tree spanning concrete and abstract syntax:

    parseClifSentence s.toClif = .ok s

## The general round trip is FALSE, and the fragment is exact

`Sentence.toClif` renders a NAME through `renderName`, which encloses
it in `"..."` whenever the bare spelling would not re-lex, so reserved
words, the empty name, names carrying delimiters and names beginning
`...` all survive. It renders a SEQUENCE MARKER as the raw
concatenation `"..." ++ m`, with no such guard —
`seqItemsToClif_seqmark` and `bindingToClif_seqmark` below are that
absence, machine-checked as `rfl`. A marker name carrying a non-name
character therefore does not come back:

    .atom (.name "P") [.seqmark "a b"]
      serialises to  (P ...a b)
      and reads back as
    .atom (.name "P") [.seqmark "a", .term (.name "b")]

ONE argument item became TWO. Note what the existing string-level
`#guard`s cannot see: the misparse re-serialises to the SAME text, so
`stable "(P ...a b)"` is `true`. Round-trip claims about this reader
have to be stated over the abstract syntax.

`marksLexable` is the exact fragment boundary found by measurement,
not by reading the code: 38 shapes covering every constructor and
every spelling hazard round-trip, and the only failures are marker
names outside `markerLexable`. A marker name carrying a delimiter does
not even parse (`markParenSentence`).

    OPEN LEMMA (`clif_roundTrip`, NOT proved):
      ∀ s, marksLexable s = true → parseClifSentence s.toClif = .ok s

## Why there is no theorem here, not even an instance-level one

Two separate obstacles, both recorded rather than worked around.

1. The GENERAL statement needs the lexer taken apart: `lex` runs over
   the whole character list with fuel `length + 1`, so an induction
   over `toClif`'s string concatenations needs fuel-monotonicity of
   `lexAcc`, a decomposition lemma for `lexAcc` over `++` with the
   position counter threaded, then the same for `parseSExpr` over
   token-list concatenation, before `readSentence` can be inverted.
   That is a proof programme of its own.

2. INSTANCE-level theorems (`parseClifSentence s.toClif = .ok s` by
   `rfl` for a concrete `s`) are also unavailable: the kernel cannot
   reduce this parser at useful sizes. Measured 2026-08-26 on a 16 GB
   container: `(P a)` and `(P a b)` reduce in 4-6 s, while
   `(P ...a b)` and `(forall (x) (P x))` exhaust memory and are killed
   after ~150-200 s. The cliff is in the string primitives the lexer
   goes through (`String.toList`, `String.startsWith`, `String.ofList`
   over character lists rebuilt from literals), not in the grammar.
   `native_decide` would evaluate them, and is banned by this
   programme's discipline.

So the corpus below is pinned by `#guard`, which uses COMPILED
evaluation. Those are tests, not proofs, and are labelled as such. The
comparator they use, `Sentence.structEq`, is written constructor for
constructor; `DecidableEq` is not derivable for this mutual family
(checked: no deriving handler applies) and `structEq`'s lawfulness is
NOT proved — it is test harness, and the boundary row says so.

## Totality

No `sorry`, no `axiom`, no `partial`, no `native_decide`. Axiom audit
by in-source `#print axioms` at the end of the file.
-/

import L4Factoidal.CL.Clif
import L4Factoidal.CL.FiniteSatTheorems

namespace L4Factoidal.CL

/-! ## The fragment -/

/-- A sequence-marker name re-lexes exactly when it is a run of name
characters: the serialiser writes `"..." ++ m`, and the lexer reads
back the maximal name-character run after the three dots. -/
def markerLexable (m : String) : Bool := m.toList.all isNameChar

mutual

/-- Every sequence-marker name inside the term re-lexes. -/
def termMarksLexable : Term → Bool
  | .name _ => true
  | .str _ => true
  | .funapp op args => termMarksLexable op && seqMarksLexable args
  | .that s => sentMarksLexable s

/-- Every sequence-marker name in the argument sequence re-lexes. -/
def seqMarksLexable : List SeqItem → Bool
  | [] => true
  | .term t :: r => termMarksLexable t && seqMarksLexable r
  | .seqmark m :: r => markerLexable m && seqMarksLexable r

/-- Every sequence-marker name in the boundlist re-lexes. -/
def bindMarksLexable : List Binding → Bool
  | [] => true
  | .plain _ :: r => bindMarksLexable r
  | .seqmark m :: r => markerLexable m && bindMarksLexable r
  | .restricted _ g :: r => termMarksLexable g && bindMarksLexable r

/-- Every sequence-marker name in the sentence re-lexes. This is the
fragment `clif_roundTrip` is stated over. -/
def sentMarksLexable : Sentence → Bool
  | .atom p args => termMarksLexable p && seqMarksLexable args
  | .eq a b => termMarksLexable a && termMarksLexable b
  | .conj ss => sentsMarksLexable ss
  | .disj ss => sentsMarksLexable ss
  | .neg s => sentMarksLexable s
  | .impl a b => sentMarksLexable a && sentMarksLexable b
  | .iff a b => sentMarksLexable a && sentMarksLexable b
  | .all bs body => bindMarksLexable bs && sentMarksLexable body
  | .ex bs body => bindMarksLexable bs && sentMarksLexable body

/-- Every sentence of the list is in the fragment. -/
def sentsMarksLexable : List Sentence → Bool
  | [] => true
  | s :: r => sentMarksLexable s && sentsMarksLexable r

end

/-! ## Where the serialiser guards, and where it does not

`renderName` re-encloses a name whenever the bare spelling would not
re-lex. The two marker clauses carry no such guard: they are the raw
concatenation. Both are `rfl` — what is machine-checked is the ABSENCE
of a case split, which is what the counterexample exploits. -/

theorem seqItemsToClif_seqmark (m : String) (r : List SeqItem) :
    seqItemsToClif (.seqmark m :: r) = " ..." ++ m ++ seqItemsToClif r := rfl

theorem bindingToClif_seqmark (m : String) :
    bindingToClif (.seqmark m) = "..." ++ m := rfl

/-! ## A structural comparator for the tests

`DecidableEq` does not derive for this mutual family (no deriving
handler applies, checked 2026-08-26), so the round-trip tests below
compare with a hand-written Bool equality. It is test harness: no
lawfulness theorem relates `structEq a b = true` to `a = b`. -/

mutual

/-- Structural equality of terms. -/
def Term.structEq : Term → Term → Bool
  | .name a, .name b => a == b
  | .str a, .str b => a == b
  | .funapp o1 a1, .funapp o2 a2 => Term.structEq o1 o2 && seqStructEq a1 a2
  | .that s1, .that s2 => Sentence.structEq s1 s2
  | _, _ => false

/-- Structural equality of argument sequences. -/
def seqStructEq : List SeqItem → List SeqItem → Bool
  | [], [] => true
  | .term t1 :: r1, .term t2 :: r2 => Term.structEq t1 t2 && seqStructEq r1 r2
  | .seqmark m1 :: r1, .seqmark m2 :: r2 => (m1 == m2) && seqStructEq r1 r2
  | _, _ => false

/-- Structural equality of boundlists. -/
def bindStructEq : List Binding → List Binding → Bool
  | [], [] => true
  | .plain a :: r1, .plain b :: r2 => (a == b) && bindStructEq r1 r2
  | .seqmark a :: r1, .seqmark b :: r2 => (a == b) && bindStructEq r1 r2
  | .restricted a g1 :: r1, .restricted b g2 :: r2 =>
      (a == b) && Term.structEq g1 g2 && bindStructEq r1 r2
  | _, _ => false

/-- Structural equality of sentences. -/
def Sentence.structEq : Sentence → Sentence → Bool
  | .atom p1 a1, .atom p2 a2 => Term.structEq p1 p2 && seqStructEq a1 a2
  | .eq a1 b1, .eq a2 b2 => Term.structEq a1 a2 && Term.structEq b1 b2
  | .conj s1, .conj s2 => sentsStructEq s1 s2
  | .disj s1, .disj s2 => sentsStructEq s1 s2
  | .neg s1, .neg s2 => Sentence.structEq s1 s2
  | .impl a1 b1, .impl a2 b2 => Sentence.structEq a1 a2 && Sentence.structEq b1 b2
  | .iff a1 b1, .iff a2 b2 => Sentence.structEq a1 a2 && Sentence.structEq b1 b2
  | .all b1 y1, .all b2 y2 => bindStructEq b1 b2 && Sentence.structEq y1 y2
  | .ex b1 y1, .ex b2 y2 => bindStructEq b1 b2 && Sentence.structEq y1 y2
  | _, _ => false

/-- Structural equality of sentence lists. -/
def sentsStructEq : List Sentence → List Sentence → Bool
  | [], [] => true
  | s1 :: r1, s2 :: r2 => Sentence.structEq s1 s2 && sentsStructEq r1 r2
  | _, _ => false

end

/-- The round-trip test: serialise, read back, compare abstract
syntax. -/
def roundTripsClif (s : Sentence) : Bool :=
  match parseClifSentence s.toClif with
  | .ok s' => s'.structEq s
  | .error _ => false

/-! ## The counterexample

Stated twice: once through the comparator, and once through argument
COUNTS, which need no comparator at all (`Nat` has `DecidableEq`), so
the sharpest form of the finding does not rest on test harness. -/

/-- `(P ...a b)` written from a marker whose name carries a space. -/
def markSpaceSentence : Sentence := .atom (.name "P") [.seqmark "a b"]

/-- What the reader gives back: TWO argument items. -/
def markSpaceMisparse : Sentence :=
  .atom (.name "P") [.seqmark "a", .term (.name "b")]

/-- Argument-sequence length of a predication, `0` elsewhere. -/
def argCount : Sentence → Nat
  | .atom _ args => args.length
  | _ => 0

-- Outside the fragment.
#guard sentMarksLexable markSpaceSentence == false
-- One argument item in; two argument items out. No comparator used.
#guard argCount markSpaceSentence == 1
#guard (parseClifSentence markSpaceSentence.toClif).toOption.map argCount == some 2
-- The same fact through the comparator.
#guard roundTripsClif markSpaceSentence == false
#guard (parseClifSentence markSpaceSentence.toClif).toOption.map
  (Sentence.structEq markSpaceMisparse) == some true
-- Invisible to the string-level check: the misparse re-serialises to
-- the same text.
#guard stable markSpaceSentence.toClif
#guard markSpaceMisparse.toClif == markSpaceSentence.toClif

/-- A marker name carrying a delimiter does not even parse. -/
def markParenSentence : Sentence := .atom (.name "P") [.seqmark "a)b"]

#guard sentMarksLexable markParenSentence == false
#guard parses markParenSentence.toClif == false
#guard roundTripsClif markParenSentence == false

/-! ## The round trip on the fragment: 38 shapes

Every entry is `(in the fragment, round-trips)`. Compiled evaluation
through `#guard`: a test corpus, not a theorem. It covers every
constructor of `CL.Syntax` and every spelling hazard `renderName`
guards against. -/

/-- The corpus, with a label for each shape. -/
def rtCorpus : List (String × Sentence) :=
  [ ("zero-ary predication", .atom (.name "P") []),
    ("predication with arguments", .atom (.name "P") [.term (.name "a"), .term (.name "b")]),
    ("equation over a functional term",
      .eq (.funapp (.name "fatherOf") [.term (.name "Bill")]) (.name "John")),
    ("empty and", .conj []),
    ("empty or", .disj []),
    ("nested and/or", .conj [.conj [], .disj [.atom (.name "P") []]]),
    ("negation", .neg (.atom (.name "P") [])),
    ("implication", .impl (.atom (.name "P") []) (.atom (.name "Q") [])),
    ("biconditional", .iff (.atom (.name "P") []) (.atom (.name "Q") [])),
    ("empty boundlist, forall", .all [] (.atom (.name "P") [.term (.name "a")])),
    ("empty boundlist, exists", .ex [] (.atom (.name "P") [.term (.name "a")])),
    ("plain binding", .all [.plain "x"] (.atom (.name "P") [.term (.name "x")])),
    ("marker binding", .ex [.seqmark "r"] (.atom (.name "P") [.seqmark "r"])),
    ("restricted binding",
      .all [.restricted "x" (.name "G")] (.eq (.name "x") (.name "a"))),
    ("all three binding forms",
      .all [.plain "x", .seqmark "r", .restricted "y" (.name "G")]
        (.atom (.name "P") [.term (.name "x"), .seqmark "r", .term (.name "y")])),
    ("reserved word bound plain",
      .all [.plain "and"] (.atom (.name "P") [.term (.name "and")])),
    ("reserved words in a restricted binding",
      .all [.restricted "and" (.name "or")] (.atom (.name "P") [])),
    ("that-term as a guard",
      .all [.restricted "x" (.that (.atom (.name "P") []))] (.atom (.name "P") [])),
    ("empty marker name", .ex [.seqmark ""] (.atom (.name "P") [.seqmark ""])),
    ("marker name beginning with dots", .atom (.name "P") [.seqmark "...x"]),
    ("empty name", .atom (.name "") [.term (.name "a")]),
    ("reserved word as predicate", .atom (.name "and") [.term (.name "a")]),
    ("IKL that as an ordinary name", .atom (.name "that") [.term (.name "a")]),
    ("cl: phrase keyword as a name", .atom (.name "cl:text") [.term (.name "a")]),
    ("equality operator as a name", .atom (.name "=") [.term (.name "a")]),
    ("name beginning with dots", .atom (.name "...x") [.term (.name "a")]),
    ("name carrying a backslash", .atom (.name "a\\b") [.term (.name "c")]),
    ("name carrying a double quote", .atom (.name "a\"b") [.term (.name "c")]),
    ("name carrying a space", .atom (.name "a b") [.term (.name "c")]),
    ("quoted string with a newline", .atom (.name "P") [.term (.str "a\nb")]),
    ("quoted string with its own quote", .atom (.name "P") [.term (.str "a'b")]),
    ("quoted string with a backslash", .atom (.name "P") [.term (.str "a\\b")]),
    ("empty quoted string", .atom (.name "P") [.term (.str "")]),
    ("quoted string as predicate", .atom (.str "s") [.term (.name "a")]),
    ("argument-less functional term in operator position",
      .atom (.funapp (.name "f") []) []),
    ("functional term as operator",
      .atom (.funapp (.funapp (.name "f") [.term (.name "a")]) [.term (.name "b")]) []),
    ("IKL assertion ((that S))",
      .atom (.that (.atom (.name "P") [.term (.name "a")])) []),
    ("IKL that in argument position",
      .atom (.name "ist") [.term (.name "c"), .term (.that (.atom (.name "P") []))])
  ]

/-- Labels of the corpus entries that are NOT in the fragment. -/
def rtOutOfFragment : List String :=
  (rtCorpus.filter (fun p => !(sentMarksLexable p.2))).map (·.1)

/-- Labels of the corpus entries that do NOT round-trip. -/
def rtFailures : List String :=
  (rtCorpus.filter (fun p => !(roundTripsClif p.2))).map (·.1)

-- The whole corpus is in the fragment, and the whole corpus
-- round-trips. Denominator stated: 38 shapes.
#guard rtCorpus.length == 38
#guard rtOutOfFragment == []
#guard rtFailures == []

/-! ## Reader and checker, end to end

The satisfaction half is a theorem (`satFin_eq`, issue 609 item 1);
the reading half is a `#guard`, for the kernel-reduction reason in the
header. The join is stated as what it is. -/

-- Reading half: tests.
#guard (parseClifSentence "(Boy Bill)").toOption.map (Sentence.structEq boyBill) == some true
#guard (parseClifSentence "(Boy Sue)").toOption.map (Sentence.structEq wBoySue) == some true

/-- Satisfaction half, proved: `witFin` satisfies `(Boy Bill)` and
refutes `(Boy Sue)`. -/
theorem clif_checked_pair :
    Satisfies witFin.toInterp boyBill ∧ ¬ Satisfies witFin.toInterp wBoySue :=
  ⟨wit_sat_boyBill, wit_not_sat_boySue⟩

/-! ## Axiom audit -/

#print axioms seqItemsToClif_seqmark
#print axioms bindingToClif_seqmark
#print axioms clif_checked_pair

end L4Factoidal.CL
