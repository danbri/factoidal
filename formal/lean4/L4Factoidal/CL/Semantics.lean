/-
L4Factoidal.CL.Semantics — CL interpretations and satisfaction, with
the IKL proposition extension.

Common Logic semantics per ISO/IEC 24707 §6.2 (interpretations) and
§6.3 (satisfaction), in the style `L4Factoidal.RDF.Semantics` uses for
RDF: an abstract structure over an arbitrary domain type, satisfaction
as a `Prop`, nothing decided or enumerated. IKL: the IKL guide
(https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html), sections
"IKL Overview" and Appendix B (propositions).
Tracking: https://github.com/danbri/factoidal/issues/580

## The CL positions this transcribes

* ONE universe of discourse, and every name denotes an individual in
  it (ISO/IEC 24707 §6.2: `int` maps each name into the universe; the
  unsegregated dialects make every name a discourse name). There is no
  predicate/function/individual segregation: the SAME term denotes the
  SAME individual in operator position and argument position, and
  `rel`/`fn` below give each INDIVIDUAL a relation extension and a
  functional extension.
* Relation extensions are sets of FINITE SEQUENCES of individuals
  (§6.2: `rel(x)` a subset of `UD*`) — arity is not fixed anywhere.
* Sequence markers denote finite sequences of individuals, and
  quantifiers may bind them (§6.3); a bound marker's sequence splices
  into the argument list at its position.
* Quantifiers bind NAMES (there is no separate variable category):
  satisfaction of a quantified sentence quantifies over point-wise
  modifications of the name valuation (§6.3's `I[x/d]`).

## Deliberate enlargements (the `RDF.Semantics` pattern)

* `rel` and `fn` are totalised over the whole domain — the standard
  reaches them through `relname`/`funname` side conditions that the
  unsegregated dialect makes vacuous.
* Free sequence markers are read against a valuation that defaults to
  the empty sequence; the standard's texts always bind their markers,
  so this only ENLARGES the readable sentence set.
* `iStr` interprets a quoted string as an arbitrary individual, not
  necessarily a character sequence: the string-theory axioms of
  ISO/IEC 24707 are not transcribed here (issue 580's not-covered
  list). Every enlargement widens the interpretation class, which
  STRENGTHENS any soundness statement quantified over it.

## The IKL extension

`iProp` maps a sentence AND a valuation pair to an individual — the
proposition the sentence expresses under that valuation. Making the
valuations arguments is what gives quantifying-in (the guide's
`(exists (x) (believes p (that (... x ...))))`) its meaning: the
proposition denoted depends on what the free names currently denote.
Truth OF a proposition is zero-ary predication — `((that S))` asserts
the empty sequence is in the proposition's relation extension — and
`IklRespectsThat` states the guide's coherence requirement: that
zero-ary extension agrees with satisfaction of the enclosed sentence.
It is a CONDITION on interpretations (the `EntailsUnder` parameter),
not a definitional equation, exactly so that pure-CL reasoning can
ignore it.

## NOT covered here (issue 580)

* Text/module/importation semantics (ISO/IEC 24707 §6.4).
* Datatypes, the string and number theories, `cl:comment` opacity.
* IKL's propositional identity relation `=p` and the structural
  axioms of guide Appendix A/B.
* Completeness in any direction; this file defines structures and
  satisfaction and proves the assertion/`that` agreement law only.
-/

import L4Factoidal.CL.Syntax

namespace L4Factoidal.CL

/-! ## Interpretations -/

/-- A CL interpretation over one unsegregated universe
(ISO/IEC 24707 §6.2), extended with IKL's proposition denotation.

* `dom` — the universe of discourse UD; `domWit` its required
  inhabitant (§6.2: UD is non-empty).
* `iName` — `int` restricted to names: every name denotes an
  individual.
* `iStr` — denotation of quoted-string terms (see the module header's
  enlargement note).
* `rel` — relation extension: `rel x args` holds when the finite
  sequence `args` is in the extension of the individual `x`
  (§6.2 `rel(x) ⊆ UD*`).
* `fn` — functional extension: the individual a functional term
  denotes, given the operator's individual and the argument sequence
  (§6.2 `fun(x) : UD* → UD`, totalised).
* `iProp` — IKL: the proposition (an individual) a sentence expresses
  under a name valuation and a sequence-marker valuation. Pure-CL
  sentences never reach it. -/
structure Interp where
  dom : Type
  domWit : dom
  iName : String → dom
  iStr : String → dom
  rel : dom → List dom → Prop
  fn : dom → List dom → dom
  iProp : Sentence → (String → dom) → (String → List dom) → dom

/-- Point-wise update of a name valuation — ISO/IEC 24707 §6.3's
`I[x/d]`, kept on the valuation rather than the interpretation so the
interpretation stays fixed through a satisfaction derivation. -/
def updateInd {d : Type} (ν : String → d) (n : String) (x : d) : String → d :=
  fun m => if m = n then x else ν m

/-- Point-wise update of a sequence-marker valuation. -/
def updateSeq {d : Type} (σ : String → List d) (m : String) (xs : List d) :
    String → List d :=
  fun k => if k = m then xs else σ k

/-! ## Denotation

Terms denote individuals; argument sequences denote finite sequences
of individuals, a bound sequence marker splicing its whole sequence in
at its position (ISO/IEC 24707 §6.3). The `that` case consults `iProp`
and does NOT recurse into satisfaction — the tie between the two is
`IklRespectsThat` below — so this group is structural on the term. -/

mutual

/-- The individual a term denotes under valuations `ν` (names) and `σ`
(sequence markers). -/
def denotTerm (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    Term → i.dom
  | .name n => ν n
  | .str s => i.iStr s
  | .funapp op args => i.fn (denotTerm i ν σ op) (denotSeq i ν σ args)
  | .that s => i.iProp s ν σ

/-- The finite sequence of individuals an argument sequence denotes. -/
def denotSeq (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    List SeqItem → List i.dom
  | [] => []
  | .term t :: r => denotTerm i ν σ t :: denotSeq i ν σ r
  | .seqmark m :: r => σ m ++ denotSeq i ν σ r

end

/-! ## Satisfaction

ISO/IEC 24707 §6.3, clause by clause. Restricted bindings expand per
the guard reading (IKL guide, "Forms of quantifiers"): a `forall`
guard conditions, an `exists` guard conjoins; successive guards see
the names bound to their left because the recursion threads the
updated valuation. -/

mutual

/-- Satisfaction of a sentence under fixed valuations. -/
def Sat (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    Sentence → Prop
  | .atom p args => i.rel (denotTerm i ν σ p) (denotSeq i ν σ args)
  | .eq a b => denotTerm i ν σ a = denotTerm i ν σ b
  | .conj ss => SatAll i ν σ ss
  | .disj ss => SatAny i ν σ ss
  | .neg s => ¬ Sat i ν σ s
  | .impl a b => Sat i ν σ a → Sat i ν σ b
  | .iff a b => Sat i ν σ a ↔ Sat i ν σ b
  | .all bs body => SatForall i ν σ bs body
  | .ex bs body => SatExists i ν σ bs body

/-- Every sentence of the list is satisfied (`and`; empty = true). -/
def SatAll (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    List Sentence → Prop
  | [] => True
  | s :: r => Sat i ν σ s ∧ SatAll i ν σ r

/-- Some sentence of the list is satisfied (`or`; empty = false). -/
def SatAny (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    List Sentence → Prop
  | [] => False
  | s :: r => Sat i ν σ s ∨ SatAny i ν σ r

/-- Universal quantification down a boundlist: plain names range over
the universe, sequence markers over finite sequences, restricted names
over the guard's unary extension. -/
def SatForall (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    List Binding → Sentence → Prop
  | [], body => Sat i ν σ body
  | .plain n :: r, body =>
      ∀ x : i.dom, SatForall i (updateInd ν n x) σ r body
  | .seqmark m :: r, body =>
      ∀ xs : List i.dom, SatForall i ν (updateSeq σ m xs) r body
  | .restricted n g :: r, body =>
      ∀ x : i.dom, i.rel (denotTerm i ν σ g) [x] →
        SatForall i (updateInd ν n x) σ r body

/-- Existential quantification down a boundlist; a restriction
conjoins. -/
def SatExists (i : Interp) (ν : String → i.dom) (σ : String → List i.dom) :
    List Binding → Sentence → Prop
  | [], body => Sat i ν σ body
  | .plain n :: r, body =>
      ∃ x : i.dom, SatExists i (updateInd ν n x) σ r body
  | .seqmark m :: r, body =>
      ∃ xs : List i.dom, SatExists i ν (updateSeq σ m xs) r body
  | .restricted n g :: r, body =>
      ∃ x : i.dom, i.rel (denotTerm i ν σ g) [x] ∧
        SatExists i (updateInd ν n x) σ r body

end

/-! ## Sentence-level satisfaction and entailment -/

/-- The initial valuations: names denote what the interpretation says,
free sequence markers default to the empty sequence (an enlargement —
see the module header). -/
def Satisfies (i : Interp) (s : Sentence) : Prop :=
  Sat i i.iName (fun _ => []) s

/-- Every sentence of a list is satisfied outright. -/
def SatisfiesAll (i : Interp) (ss : List Sentence) : Prop :=
  ∀ s, s ∈ ss → Satisfies i s

/-- Entailment relative to a class of interpretations — the
`RDF.Semantics.EntailsUnder` pattern, so later rungs (string axioms,
IKL structural axioms) grow the condition bundle without restating
theorems. -/
def EntailsUnder (conds : Interp → Prop) (premises : List Sentence)
    (conclusion : Sentence) : Prop :=
  ∀ i : Interp, conds i → SatisfiesAll i premises → Satisfies i conclusion

/-- Plain CL entailment: every interpretation counts. -/
def Entails : List Sentence → Sentence → Prop :=
  EntailsUnder (fun _ => True)

/-! ## The IKL condition -/

/-- The IKL coherence requirement: the zero-ary extension of the
proposition a sentence expresses agrees with satisfaction of that
sentence, at every valuation (IKL guide, "IKL Overview": asserting a
proposition is applying it "as a relation with no arguments"). -/
def IklRespectsThat (i : Interp) : Prop :=
  ∀ (s : Sentence) (ν : String → i.dom) (σ : String → List i.dom),
    i.rel (i.iProp s ν σ) [] ↔ Sat i ν σ s

/-- IKL entailment: entailment over the coherent interpretations. -/
def IklEntails : List Sentence → Sentence → Prop :=
  EntailsUnder IklRespectsThat

/-- The cancelling-parentheses law (IKL guide, "IKL Overview"):
in a coherent interpretation, asserting `((that S))` is exactly
satisfying `S` — at any valuation, so it also holds under quantifiers.
The proof is the coherence condition itself once predication of a
`that`-term on the empty sequence is unfolded. -/
theorem sat_assert_that (i : Interp) (h : IklRespectsThat i)
    (ν : String → i.dom) (σ : String → List i.dom) (s : Sentence) :
    Sat i ν σ (.atom (.that s) []) ↔ Sat i ν σ s := by
  simpa [Sat, denotTerm, denotSeq] using h s ν σ

/-- `sat_assert_that` at the top level. -/
theorem satisfies_assert_that (i : Interp) (h : IklRespectsThat i)
    (s : Sentence) :
    Satisfies i (.atom (.that s) []) ↔ Satisfies i s :=
  sat_assert_that i h i.iName (fun _ => []) s

end L4Factoidal.CL
