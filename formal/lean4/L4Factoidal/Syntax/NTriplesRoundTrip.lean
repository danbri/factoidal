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
import L4Factoidal.Syntax.IriScan

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

A DIFFERENT obstacle used to exist, and it is worth keeping the record
because it is easy to mistake for the F\* one. `readIriRefBody` had ten
match arms, two carrying six- and ten-character escape patterns. Lean
generates one equation lemma per arm, and generating them for THAT
function exhausted the memory available here: `#check
@readIriRefBody.eq_11` alone was killed before any proof was attempted.

**That obstacle is gone.** The scanner was split into a non-recursive
step classifier plus a three-arm recursion
(<https://github.com/danbri/factoidal/issues/565>, commits
`d09e828b224`, `fbbd2c4628a`, `80ee4521da2`), its three equations are
proved in `Syntax/IriScan.lean`, and the round trip below uses them.
The induction is the three lines this section predicted.

**What IS claimed now.** `readIriRefBody_printSafe` and
`readIriRef_toNTriples`: on the print-safe fragment the scanner reads
back exactly what the serialiser wrote, stops at the closing `>`,
reports the offset just past it, and leaves nothing unread. Together
with the injectivity results above, that is both directions on the
fragment.

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

/-! ## The round trip, now that the scanner has equations

`Syntax.Lexing`'s scanner was split (<https://github.com/danbri/factoidal/issues/565>)
and `Syntax/IriScan.lean` proves its three equations. The obstacle
described above is gone, and the statement this module could previously
only pin with `#guard`s is a theorem.

The induction is the three lines the section above predicted: a safe
character always takes the `emit` arm, so the scanner walks the IRI one
character at a time and stops at the `>` the serialiser appended. -/

/-- A print-safe character takes the plain-emit arm. It is neither `>`
nor `\`, both of which `IriSafeChar` excludes — `>` through the
forbidden-codepoint set, which contains `0x3E`. -/
theorem iriNextStep_safe {pos : Nat} {c : Char} {rest : List Char}
    (h : IriSafeChar c = true) : iriNextStep pos (c :: rest) = .emit c 1 rest := by
  simp only [IriSafeChar, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
             Bool.not_eq_true'] at h
  obtain ⟨⟨hgt, hforb⟩, hbs⟩ := h
  have hgt' : ¬ (c.toNat ≤ 0x20) := by omega
  have hne : c ≠ '>' := by
    intro hc; subst hc; simp [isIriForbiddenCodepoint] at hforb
  unfold iriNextStep
  split <;> simp_all

/-- **The round trip on the print-safe fragment.** The scanner reads
back exactly the characters the serialiser wrote, stops at the closing
`>`, reports the offset just past it, and leaves nothing unread. -/
theorem readIriRefBody_printSafe (pos : Nat) : ∀ cs : List Char,
    cs.all IriSafeChar = true →
    readIriRefBody pos (cs ++ ['>']) = .ok (String.ofList cs, pos + cs.length + 1, [])
  | [], _ => by
      have : iriNextStep pos ['>'] = .close [] := rfl
      simpa using readIriRefBody_close this
  | c :: tl, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [List.cons_append,
          readIriRefBody_emit (iriNextStep_safe (pos := pos) h.1),
          readIriRefBody_printSafe (pos + 1) tl h.2]
      have hstr : c.toString ++ String.ofList tl = String.ofList (c :: tl) := by
        first
          | rfl
          | simp [Char.toString, String.ofList_cons]
          | simp [Char.toString, String.ofList, String.singleton]
          | (apply String.ext; simp [Char.toString])
      have harith : pos + 1 + tl.length + 1 = pos + (tl.length + 1) + 1 := by omega
      simp only [Except.map, List.length_cons, hstr, harith]

/-- And at the whole-token entry point the serialiser uses. -/
theorem readIriRef_toNTriples (i : WfIri) (h : iriPrintSafe i.val = true) :
    readIriRef 0 (Subject.toNTriples (.iri i)).toList
      = .ok (i.val, i.val.length + 2, []) := by
  have hs : (Subject.toNTriples (.iri i)).toList = '<' :: (i.val.toList ++ ['>']) := by
    simp [Subject.toNTriples]
  rw [hs]
  show readIriRefBody 1 (i.val.toList ++ ['>']) = _
  rw [readIriRefBody_printSafe 1 i.val.toList h]
  have hlen : i.val.toList.length = i.val.length := rfl
  have harith : 1 + i.val.toList.length + 1 = i.val.length + 2 := by omega
  rw [String.ofList_toList, harith]

/-- Re-validating an IRI that is already well formed returns the same
`WfIri`. `WfIri` is a subtype, so the proof component is irrelevant. -/
theorem mkIri_val (pos : Nat) (i : WfIri) : mkIri pos i.val = .ok i := by
  simp only [mkIri, dif_pos i.property]

/-- **The subject round trip.** One step further out than
`readIriRef_toNTriples`: through `readSubject`, which re-validates the
scanned string, so the term recovered is the term serialised — not
merely the same characters. -/
theorem readSubject_toNTriples (i : WfIri) (h : iriPrintSafe i.val = true) :
    readSubject 0 (Subject.toNTriples (.iri i)).toList
      = .ok (.iri i, i.val.length + 2, []) := by
  have hs : (Subject.toNTriples (.iri i)).toList = '<' :: (i.val.toList ++ ['>']) := by
    simp [Subject.toNTriples]
  have hiri : readIriRef 0 ('<' :: (i.val.toList ++ ['>']))
      = .ok (i.val, i.val.length + 2, []) := by
    rw [← hs]; exact readIriRef_toNTriples i h
  rw [hs]
  simp only [readSubject, hiri, mkIri_val]

/-! ## What remains before this module covers `RDF.NTriples.RoundTrip`

The F\* module also carries the object-position term round trip and
`checkpoint_a_closed_triple_round_trip`, a whole-triple statement. Those
are not here, so `RDF.NTriples.RoundTrip` stays on the not-covered list
and no alias was added — the count did not move, and that is the
correct outcome rather than a measurement fault
(`skills/counting-coverage` rule 2). -/

/-! ## Axiom audit -/

#print axioms subject_toNTriples_injective
#print axioms term_toNTriples_injective
#print axioms readIriRefBody_printSafe
#print axioms readIriRef_toNTriples
#print axioms readSubject_toNTriples

end L4Factoidal.Syntax.NTriplesRoundTrip
