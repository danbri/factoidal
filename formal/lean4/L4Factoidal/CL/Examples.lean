/-
L4Factoidal.CL.Examples — worked examples: IKL guide sentences parsed
at build time, and satisfaction facts over a small interpretation.

Sources: the IKL guide (Hayes/Menzel),
https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html — fetched
2026-08-25; the sentences marked "guide" below are transcribed from
it, those marked "adapted" recombine guide material (the guide's own
quantifying-in example uses the numeric quantifier `(exists 3 ...)`,
which this bootstrap does not cover — issue 580). Plain-CLIF sentences
follow ISO/IEC 24707 Annex A shapes.
Tracking: https://github.com/danbri/factoidal/issues/580

Every `#guard` runs during elaboration, so `lake build` is the test
run (`skills/factoidal-lean-basics`, Build/test/demo).
-/

import L4Factoidal.CL.Clif
import L4Factoidal.CL.Alpha
import L4Factoidal.CL.Semantics

namespace L4Factoidal.CL

/-! ## Plain CLIF sentences (ISO/IEC 24707 Annex A shapes) -/

#guard stable "(married Jack Jill)"
#guard stable "(= (fatherOf Bill) John)"
#guard stable "(forall (x) (if (Boy x) (Human x)))"
#guard stable "(exists (x) (and (Dog x) (owns Jack x)))"
#guard stable "(or (Robot Sue) (not (Robot Sue)))"
-- A free sequence marker in argument position is grammatical.
#guard stable "(P a b ...rest)"
-- All of the above are ISO/IEC 24707 CL proper: no IKL construct.
#guard pureOf "(forall (x) (if (Boy x) (Human x)))" == some true

/-! ## IKL guide sentences

Each comment quotes the guide's own reading. -/

-- guide: a proposition asserted by "cancelling" parentheses — the
-- proposition name applied as a relation with no arguments.
#guard stable "((that (isHuman \"Brant Cheikes\")))"
#guard pureOf "((that (isHuman \"Brant Cheikes\")))" == some false

-- guide ("Contexts and Modalities in IKL"): `ist` relates a context
-- to a proposition; the proposition is an ordinary term.
#guard stable "(ist TemporalContextDay06-16-2006 (that (Dead Osama-Bin-Laden)))"
#guard pureOf "(ist TemporalContextDay06-16-2006 (that (Dead Osama-Bin-Laden)))"
  == some false

-- guide ("Forms of quantifiers"): restricted quantification —
-- `(forall ((x isHuman)) S)` abbreviates `(forall (x) (if (isHuman x) S))`.
#guard stable "(forall ((x isHuman))(exists ((y charseq))(= y (nameOf x))))"
#guard pureOf "(forall ((x isHuman))(exists ((y charseq))(= y (nameOf x))))"
  == some true

-- guide ("Contexts and Modalities in IKL"): a temporal context bound
-- by a restricted quantifier, with a that-term under it.
#guard stable "(exists ((t time))(and (before t now) (ist t (that (exists ((x isHuman)) (and (Democrat x)(PresidentOfUSA x)))))))"

-- adapted from the guide's belief examples: a that-term with a
-- closed quantified sentence inside — belief about the general
-- proposition, not about any particular individual.
#guard stable "(believes Bill_Andersen (that (forall ((x isHuman))(isMammal x))))"

-- guide (Appendix B): bound-variable renaming does not change the
-- proposition — the guide's alpha-variant pair has ONE alpha-normal
-- form (`CL/Alpha.lean`, issue 589).
#guard alphaCanon "(exists (x)(loves Jim x))"
       == alphaCanon "(exists (y)(loves Jim y))"

-- guide (Appendix B): propositions as zero-ary relations — a bound
-- sequence marker, zero-ary predication `(p)`, and a proposition-
-- building function `OR`, verbatim.
#guard stable "(forall (p ... )(iff ((OR p ...))(or (p)((OR ...)))))"
#guard canon "(forall (p ... )(iff ((OR p ...))(or (p)((OR ...)))))"
  == some "(forall (p ...) (iff ((OR p ...)) (or (p) ((OR ...)))))"

/-! ## The parser meets the abstract syntax

`exConj` is built by hand; the parsed text canonicalises to exactly
its serialisation, tying the reader to the AST the satisfaction facts
below are about. -/

/-- `(Boy Bill)`. -/
def boyBill : Sentence := .atom (.name "Boy") [.term (.name "Bill")]

/-- `(Girl Sue)`. -/
def girlSue : Sentence := .atom (.name "Girl") [.term (.name "Sue")]

/-- `(and (Boy Bill) (Girl Sue))`. -/
def exConj : Sentence := .conj [boyBill, girlSue]

#guard canon "(and (Boy Bill) (Girl Sue))" == some exConj.toClif
#guard exConj.isPureCL

/-! ## A small concrete interpretation

Universe `Nat`; `Boy` denotes 10, `Girl` 11, `Bill` 0, `Sue` 1,
everything else 99. The relation extension is given by a decidable
table, lifted to `Prop` in the `Interp` record — the pattern
`RDF.Semantics` uses, at toy scale. -/

/-- The relation-extension table: `(Boy Bill)` and `(Girl Sue)` hold,
nothing else does. -/
def tinyRel : Nat → List Nat → Bool
  | 10, [0] => true
  | 11, [1] => true
  | _, _ => false

/-- Name denotations. -/
def tinyName : String → Nat
  | "Boy" => 10
  | "Girl" => 11
  | "Bill" => 0
  | "Sue" => 1
  | _ => 99

/-- The interpretation. `iProp` is a constant — `tiny` is NOT an
IKL-coherent interpretation (`IklRespectsThat` fails for it), which is
fine: it is used only on pure-CL sentences, whose satisfaction never
consults `iProp`. -/
def tiny : Interp where
  dom := Nat
  domWit := 0
  iName := tinyName
  iStr := fun _ => 99
  rel := fun r args => tinyRel r args = true
  fn := fun _ _ => 99
  iProp := fun _ _ _ => 99

/-- `tiny` satisfies `(and (Boy Bill) (Girl Sue))` — ISO/IEC 24707
§6.3 satisfaction computed clause by clause. -/
theorem tiny_sat_conj : Satisfies tiny exConj := by
  simp [Satisfies, Sat, SatAll, exConj, boyBill, girlSue,
        denotTerm, denotSeq, tiny, tinyName, tinyRel]

/-- `tiny` satisfies `(exists (x) (Boy x))`, witnessed by Bill's
individual. -/
theorem tiny_sat_ex :
    Satisfies tiny (.ex [.plain "x"] (.atom (.name "Boy") [.term (.name "x")])) := by
  simp only [Satisfies, Sat, SatExists, denotTerm, denotSeq, tiny, updateInd]
  exact ⟨0, by simp [tinyName, tinyRel]⟩

/-- `tiny` satisfies `(not (Boy Sue))`: the table has no row for
`(10, [1])`. -/
theorem tiny_sat_neg :
    Satisfies tiny (.neg (.atom (.name "Boy") [.term (.name "Sue")])) := by
  simp [Satisfies, Sat, denotTerm, denotSeq, tiny, tinyName, tinyRel]

/-- `tiny` satisfies the restricted universal
`(forall ((x Boy)) (= x Bill))`: the only individual in `Boy`'s unary
extension is 0, which is `Bill`'s denotation. -/
theorem tiny_sat_restricted :
    Satisfies tiny (.all [.restricted "x" (.name "Boy")]
      (.eq (.name "x") (.name "Bill"))) := by
  simp only [Satisfies, Sat, SatForall, denotTerm, tiny, updateInd]
  intro x hx
  -- The table row forces x = 0.
  match x, hx with
  | 0, _ => simp [tinyName]

end L4Factoidal.CL
