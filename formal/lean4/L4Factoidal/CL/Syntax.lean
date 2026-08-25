/-
L4Factoidal.CL.Syntax — abstract syntax of Common Logic text, with the
IKL proposition-term extension.

Common Logic: ISO/IEC 24707 (Common Logic — a framework for a family
of logic-based languages), abstract syntax per clause 6.1 and the CLIF
dialect grammar of Annex A. IKL: the IKRIS Knowledge Language
(Hayes/Menzel), primary reference the IKL guide,
https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html (fetched
2026-08-25), section "IKL Overview".

This is the LEAN-FIRST half of the two-tree plan (owner, 2026-08-25:
implement IKL and Common Logic "in parallel expressions for both F*
and Lean 4. It is ok to do Lean first."). Every definition here is
written for mechanical transcription into F*: inductive datatypes,
structural recursion through explicit list helpers, no typeclass
machinery on the spec surface. Tracking issue:
https://github.com/danbri/factoidal/issues/580

## What IS covered

* Terms: names (plain and enclosed — one constructor, quoting is a
  lexical matter), quoted strings (ISO/IEC 24707 A.2.2: a quoted
  string is a term denoting itself, distinct from an enclosed name),
  functional terms (operator term applied to a term sequence), and
  IKL's `(that <sentence>)` proposition term.
* Term sequences whose items are terms or sequence markers
  (ISO/IEC 24707 6.1.2: an argument sequence may interleave both).
* Atomic sentences: predication of a TERM (not a segregated predicate
  symbol — CL has a single universe, ISO/IEC 24707 6.2) on a term
  sequence, and equations.
* Boolean sentences: `and` / `or` (n-ary), `not`, `if`, `iff`
  (CLIF `boolsent`, ISO/IEC 24707 A.2.2.2.4).
* Quantified sentences: `forall` / `exists` over a binding sequence
  whose entries are plain names, sequence markers, or restricted
  `(name term)` pairs (CLIF `quantsent`, A.2.2.2.5; the restricted
  form is the guard abbreviation the IKL guide's "Forms of
  quantifiers" section uses, e.g. `(forall ((x isHuman)) ...)`).

## What is NOT covered (deliberate; see issue 580)

* Text structure above single sentences: `cl:text`, `cl:module` with
  exclusion lists, `cl:imports`, and importation semantics
  (ISO/IEC 24707 6.1.3).
* `cl:comment` annotations on terms and sentences.
* IKL numeric quantifiers (`(exists 3 ...)`) and the other special
  IKL name forms ("Special IKL name forms" in the guide).
* Role sets / role-pair syntax and other irregular CLIF sugar.
* Datatyped names and any built-in string/number theory.
-/

namespace L4Factoidal.CL

/-! ## Terms, term sequences, sentences

One mutual family: IKL's `that` makes `Term` and `Sentence` mutually
recursive, which is exactly why IKL is bootstrapped together with CL
rather than bolted on later. CL-without-IKL is the syntactic subset
characterised by `Sentence.isPureCL` below. -/

mutual

/-- A CL term (ISO/IEC 24707 6.1.2), extended with IKL's proposition
term.

* `name` — an interpreted name. Whether the CLIF surface spells it
  bare (`Bill`) or enclosed (`"Bank Melli Iran"`) is lexical only; both
  arrive here as `name`.
* `str` — a quoted string `'like this'`, a term denoting the character
  sequence itself (ISO/IEC 24707 A.2.2 quoted strings).
* `funapp` — a functional term: an operator TERM applied to a term
  sequence. The operator position is a full term because CL does not
  segregate function symbols from individuals.
* `that` — IKL: `(that S)` names the proposition expressed by `S`
  (IKL guide, "IKL Overview": enclosing a sentence in
  `(that ...)` "makes a sentence into the name of the corresponding
  proposition"). Not ISO/IEC 24707; `isPureCL` is false on it. -/
inductive Term where
  | name (n : String)
  | str (s : String)
  | funapp (op : Term) (args : List SeqItem)
  | that (s : Sentence)
  deriving Repr

/-- One item of a term sequence (ISO/IEC 24707 6.1.2): a term, or a
sequence marker standing for a finite sequence of terms. The marker
name EXCLUDES the leading `...` of the CLIF spelling. -/
inductive SeqItem where
  | term (t : Term)
  | seqmark (m : String)
  deriving Repr

/-- One entry of a quantifier's binding sequence (CLIF `boundlist`,
ISO/IEC 24707 A.2.2.2.5): a plain name, a sequence marker, or the
restricted form `(name term)` — the guard abbreviation
(`(forall ((x P)) S)` abbreviates `(forall (x) (if (P x) S))`;
for `exists` the expansion conjoins, per the IKL guide's "Forms of
quantifiers"). -/
inductive Binding where
  | plain (n : String)
  | seqmark (m : String)
  | restricted (n : String) (guard : Term)
  deriving Repr

/-- A CL sentence (ISO/IEC 24707 6.1.2; CLIF `sentence`, A.2.2.2).

`atom` applies a term to a term sequence — this includes the IKL
assertion form `((that S))`, which is predication of the proposition
term on the EMPTY sequence (IKL guide: a proposition asserted "as a
relation with no arguments"). -/
inductive Sentence where
  | atom (pred : Term) (args : List SeqItem)
  | eq (t1 t2 : Term)
  | conj (ss : List Sentence)
  | disj (ss : List Sentence)
  | neg (s : Sentence)
  | impl (s1 s2 : Sentence)
  | iff (s1 s2 : Sentence)
  | all (bs : List Binding) (body : Sentence)
  | ex (bs : List Binding) (body : Sentence)
  deriving Repr

end

/-! ## The pure-CL subset

CL-without-IKL is the image of ISO/IEC 24707 inside this syntax: every
construct except `Term.that`. Stated as a Bool predicate so parsers
and tests can decide membership; each function recurses only on
structurally smaller pieces, so the group transcribes to F* with a
`decreases` on the term. -/

mutual

/-- `true` iff the term contains no IKL `that` subterm
(ISO/IEC 24707 terms only). -/
def Term.isPureCL : Term → Bool
  | .name _ => true
  | .str _ => true
  | .funapp op args => op.isPureCL && seqItemsPureCL args
  | .that _ => false

/-- All items of a term sequence are pure CL. -/
def seqItemsPureCL : List SeqItem → Bool
  | [] => true
  | .term t :: r => t.isPureCL && seqItemsPureCL r
  | .seqmark _ :: r => seqItemsPureCL r

/-- All bindings are pure CL (a restricted binding's guard is a term
and may hide a `that`). -/
def bindingsPureCL : List Binding → Bool
  | [] => true
  | .plain _ :: r => bindingsPureCL r
  | .seqmark _ :: r => bindingsPureCL r
  | .restricted _ g :: r => g.isPureCL && bindingsPureCL r

/-- `true` iff the sentence contains no IKL `that` term anywhere —
i.e. it is a sentence of ISO/IEC 24707 Common Logic proper. -/
def Sentence.isPureCL : Sentence → Bool
  | .atom p args => p.isPureCL && seqItemsPureCL args
  | .eq a b => a.isPureCL && b.isPureCL
  | .conj ss => sentencesPureCL ss
  | .disj ss => sentencesPureCL ss
  | .neg s => s.isPureCL
  | .impl a b => a.isPureCL && b.isPureCL
  | .iff a b => a.isPureCL && b.isPureCL
  | .all bs body => bindingsPureCL bs && body.isPureCL
  | .ex bs body => bindingsPureCL bs && body.isPureCL

/-- All sentences of a list are pure CL. -/
def sentencesPureCL : List Sentence → Bool
  | [] => true
  | s :: r => s.isPureCL && sentencesPureCL r

end

/-! ## CLIF reserved words

ISO/IEC 24707 A.2.2 reserves the operator words; IKL adds `that`.
A bare name token equal to one of these is rejected in term position
by the reader (`CL.Clif`); an ENCLOSED name (`"and"`) is an ordinary
name and is not affected. -/

/-- The reserved words of the CLIF fragment read here, plus IKL's
`that`. `cl:` phrase keywords are listed so the reader can reject them
with a named "not covered" error instead of misreading them as
predications. -/
def reservedWords : List String :=
  ["and", "or", "not", "if", "iff", "forall", "exists", "=", "that",
   "cl:text", "cl:module", "cl:imports", "cl:comment"]

/-- Membership in `reservedWords`. -/
def isReservedWord (s : String) : Bool := reservedWords.contains s

end L4Factoidal.CL
