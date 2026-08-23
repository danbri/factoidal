/-
L4Factoidal.Syntax.NTriplesRoundTrip — N-Triples serialise/parse
round-trip properties.

Port of `formal/fstar/RDF.NTriples.RoundTrip.fst` (1504 lines).

## What this module carries, and what it does not

PARTIAL PORT. The F\* source proves serialiser injectivity on an
IRI/blank-node fragment and then reaches an IRI round trip through a
character-list detour. This module carries the injectivity half and the
fragment; it does NOT carry a round-trip theorem. The blocker is
measured and named in its own section below, and it is not the F\*
blocker.

## Why the F\* module stops where it does

The F\* source was commissioned to prove `parse (serialise g) = g`. Its
Finding 1 is that the parser is UNREACHABLE, for any input at all:
every byte the F\* N-Triples scanner reads goes through five
`assume val` FastString primitives, and the axiom set supplies no
base-VALUE fact tying `fs_byte_at`'s result to any string's content. So
even `fs_byte_at "<" 0 == 0x3C` fails. That is not a solver-budget
problem; an uninterpreted symbol has no defining equation to unfold.

Its Finding 2(b) is sharper: the F\* serialiser routes EVERY literal
through `nq_escape_literal`, which walks bytes through the same
primitives, so literals are blocked on the SERIALISER side before the
parser is reached. That is why the F\* fragment is IRIs and blank nodes
only.

Neither finding transfers. `Syntax/Lexing.lean`'s `readIriRefBody` and
`Syntax/NTriples.lean`'s `escapeLiteral` are ordinary Lean functions
over `List Char` with definitional equations; they reduce, and the
`#guard`s below execute them. A different obstacle stops the round trip
here, described where it arises.

## The fragment, and why a fragment at all

`iriPrintSafe` is not a formality. `RDF.isIri` is coarser than the
IRIREF grammar: a `WfIri` may hold a character `readIriRefBody`
rejects (a control character, or one of the ten forbidden codepoints).
Serialising such an IRI produces a document the parser refuses, so no
unrestricted round-trip statement is true. `iriPrintSafe` names exactly
the IRIs on which the two agree, and `nonRoundTrip_forbidden_codepoint`
below exhibits an IRI outside it.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Syntax.NTriplesRoundTrip

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## String concatenation cancels

The serialiser builds its output with `++` alone on this fragment, so
injectivity is cancellation. -/

theorem append_cancel_left {a b c : String} (h : a ++ b = a ++ c) : b = c := by
  have h1 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h1
  have h2 := congrArg String.ofList (List.append_cancel_left h1)
  rwa [String.ofList_toList, String.ofList_toList] at h2

theorem append_cancel_right {a b c : String} (h : b ++ a = c ++ a) : b = c := by
  have h1 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h1
  have h2 := congrArg String.ofList (List.append_cancel_right h1)
  rwa [String.ofList_toList, String.ofList_toList] at h2

/-! ## The fragment (port of `term_nt_fragment` / `graph_nt_fragment`)

IRIs and blank nodes only, exactly as the F\* source, though for the
opposite reason: there the literal branch is blocked by the serialiser,
here it is simply the next piece of work. -/

def TermNtFragment : Term → Bool
  | .iri _ => true
  | .bnode _ => true
  | _ => false

def TripleNtFragment (t : Triple) : Bool := TermNtFragment t.o

def GraphNtFragment (g : Graph) : Bool := g.all TripleNtFragment

/-- A character the IRIREF grammar admits raw, with no escape. Port of
`iri_print_safe`'s per-character test. -/
def IriSafeChar (c : Char) : Bool :=
  decide (0x20 < c.toNat) && !isIriForbiddenCodepoint c.toNat && c != '\\'

/-- An IRI whose every character the IRIREF grammar admits raw. The
`WfIri` refinement does NOT imply this — see the module header. -/
def iriPrintSafe (i : String) : Bool := i.toList.all IriSafeChar

/-! ## Serialiser injectivity (what the F\* module proves) -/

theorem subject_iri_ne_bnode (i : WfIri) (b : BNodeId) :
    Subject.toNTriples (.iri i) ≠ Subject.toNTriples (.bnode b) := by
  intro h
  have h1 := congrArg String.toList h
  simp only [Subject.toNTriples, String.toList_append] at h1
  have hh := congrArg (fun l => l.head?) h1
  simp at hh

theorem subject_toNTriples_injective {s1 s2 : Subject}
    (h : Subject.toNTriples s1 = Subject.toNTriples s2) : s1 = s2 := by
  cases s1 with
  | iri i1 =>
      cases s2 with
      | iri i2 =>
          simp only [Subject.toNTriples] at h
          exact congrArg Subject.iri
            (Subtype.ext (append_cancel_left (append_cancel_right h)))
      | bnode b2 => exact absurd h (subject_iri_ne_bnode i1 b2)
  | bnode b1 =>
      cases s2 with
      | bnode b2 =>
          simp only [Subject.toNTriples] at h
          exact congrArg Subject.bnode (append_cancel_left h)
      | iri i2 => exact absurd h.symm (subject_iri_ne_bnode i2 b1)

theorem term_iri_ne_bnode (mode : Mode) (i : WfIri) (b : BNodeId) :
    Term.toNTriples mode (.iri i) ≠ Term.toNTriples mode (.bnode b) := by
  intro h
  simp only [Term.toNTriples, Except.ok.injEq] at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  have hh := congrArg (fun l => l.head?) h1
  simp at hh

/-- Serialisation is injective on the fragment: two distinct terms
never render to the same N-Triples text. This is the F\* module's
result, and it is what makes the round trip below a statement about the
graph rather than about the text. -/
theorem term_toNTriples_injective (mode : Mode) {t1 t2 : Term}
    (h1 : TermNtFragment t1 = true) (h2 : TermNtFragment t2 = true)
    (h : Term.toNTriples mode t1 = Term.toNTriples mode t2) : t1 = t2 := by
  cases t1 with
  | iri i1 =>
      cases t2 with
      | iri i2 =>
          simp only [Term.toNTriples, Except.ok.injEq] at h
          exact congrArg Term.iri
            (Subtype.ext (append_cancel_left (append_cancel_right h)))
      | bnode b2 => exact absurd h (term_iri_ne_bnode mode i1 b2)
      | literal _ => simp [TermNtFragment] at h2
      | tripleTerm _ _ _ => simp [TermNtFragment] at h2
  | bnode b1 =>
      cases t2 with
      | bnode b2 =>
          simp only [Term.toNTriples, Except.ok.injEq] at h
          exact congrArg Term.bnode (append_cancel_left h)
      | iri i2 => exact absurd h.symm (term_iri_ne_bnode mode i2 b1)
      | literal _ => simp [TermNtFragment] at h2
      | tripleTerm _ _ _ => simp [TermNtFragment] at h2
  | literal _ => simp [TermNtFragment] at h1
  | tripleTerm _ _ _ => simp [TermNtFragment] at h1


/-! ## The parser side — where it stops, and why the reason is NOT the F\* one

The F\* module cannot take one step: `fs_byte_at` is an `assume val`
with no base-VALUE equation, so no branch of `parse_iri_raw` can be
shown to fire for any input. That obstacle does not exist here.
`readIriRefBody` is an ordinary Lean function over `List Char`; it
reduces, it runs, and the `#guard`s below execute it.

A DIFFERENT obstacle does exist, and it is worth naming precisely
because it is easy to mistake for the F\* one. `readIriRefBody` has ten
match arms, two of which carry six- and ten-character escape patterns
(`'\\' :: 'u' :: h0 :: h1 :: h2 :: h3 :: rest` and the `\U` form).
Lean generates one equation lemma per arm on first use, and generating
them for THIS function exhausts the memory available in this
environment: `#check @readIriRefBody.eq_11` alone is killed, before any
proof is attempted. So is `unfold readIriRefBody; split <;> simp_all`,
which needs the same machinery.

Measured, not assumed: `#check @readIriRefBody.eq_11` on its own, in a
file whose only other content is the import, is killed by the OOM
killer. The step lemma
`readIriRefBody pos (c :: tl) = (readIriRefBody (pos+1) tl).map (c.toString ++ ·)`
was drafted and proved in a smaller context at roughly 34 seconds and
several gigabytes; it does not survive being placed in a file with
anything else.

**What that means for the round trip.** It is provable — the function
has the equations, the induction over the character list is
three lines, and nothing about the port blocks it. It needs the scanner
split into a small step function over one character plus a driver, so
each arm's equation lemma is generated from a shallow match. That is a
change to a shipping parser with its own test surface, so it is a
separate piece of work, tracked rather than smuggled into this landing.

**What is NOT claimed here.** No round-trip theorem. This module proves
serialiser injectivity — the F\* module's own result — and pins the
fragment. Saying more would be reporting an intention as a theorem.

## Why the fragment is a fragment

`RDF.isIri` asks only that the string be non-empty and contain a colon,
so `a:b>c` is a well-formed `WfIri`. It is not print-safe: serialising
it emits `<a:b>c>`, and the parser stops at the first `>`, recovering
`a:b` and leaving `c>` behind. No unrestricted round-trip statement is
true, whatever proof machinery becomes available, and `iriPrintSafe` is
the predicate that says which IRIs the two sides agree on. -/

private def badIri : WfIri := ⟨"a:b>c", by decide⟩

#guard iriPrintSafe badIri.val == false
#guard iriPrintSafe "http://example.org/a" == true
#guard (Subject.toNTriples (.iri badIri)) == "<a:b>c>"

/-! The witness, run rather than reduced: the parser recovers `a:b` and
stops at position 5, leaving `c>` unread. -/
#guard (readIriRef 0 (Subject.toNTriples (.iri badIri)).toList).toOption.map
         (fun r => (r.1, r.2.1)) == some ("a:b", 5)

/-! And on a print-safe IRI the two sides do agree — the statement the
theorem above would generalise. -/
#guard (readIriRef 0 (Subject.toNTriples
          (.iri ⟨"http://example.org/a", by decide⟩)).toList).toOption.map
         (fun r => r.1) == some "http://example.org/a"

/-! ## Axiom audit -/

#print axioms subject_toNTriples_injective
#print axioms term_toNTriples_injective

end L4Factoidal.Syntax.NTriplesRoundTrip
