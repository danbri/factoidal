/-
L4Factoidal.Syntax.LexShift — position-shift invariance for the
N-Triples/N-Quads lexer.

## Why this module exists

Two open proofs need the same fact, and neither can be finished without
it:

* the N-Quads streaming homomorphism
  (<https://github.com/danbri/factoidal/issues/570>) — parsing `a ++ b`
  has to factor through the state parsing `a` reached, and positions
  inside `b` are then offset by `a.length`;
* the SPARQL ASK-BGP string round trip
  (<https://github.com/danbri/factoidal/issues/569>) — the same
  concatenation step, one layer up.

In both, the parser threads a character POSITION purely so an error can
say where it happened. That position is the only thing standing between
"parse `b` from here" and "parse `b` from the start", so the reusable
lemma is: **shifting the starting position shifts the reported position
and changes nothing else.**

This module proves it for every lexer helper the quad-line loop calls.

## The shape

Each helper returns `(pos, rest)`. `Shifts f` says: running `f` from
`pos + d` gives the same remaining input, and a position `d` larger.
Stating it that way — rather than as two separate equations — keeps the
composition proofs to one rewrite each.

The lemmas are ordinary inductions on the input list. There is no
string-slicing layer to bridge, which is the same reason the streaming
splitter was easy here and hard in F\* (findings A1 and A9c).

## What this does NOT yet cover

`readNQuad11` and `readNQuad12` read a whole quad and are built from
term readers this module does not reach. `parseQuadLinesAcc_shift`
below takes their shift property as an explicit HYPOTHESIS rather than
assuming it, so the residual for both open issues is now one named
lemma about the quad reader instead of an open-ended homomorphism.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.Syntax.LexShift

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## 1. What it means to shift -/

/-- `f` reports positions relative to where it started: running from
`pos + d` leaves the same input and reports `d` more. -/
def Shifts (f : Nat → List Char → Nat × List Char) : Prop :=
  ∀ (pos d : Nat) (cs : List Char),
    f (pos + d) cs = ((f pos cs).1 + d, (f pos cs).2)

/-! ## 2. The four helpers -/

theorem skipWs_shifts : Shifts skipWs := by
  intro pos d cs
  simp only [skipWs, Prod.mk.injEq, and_true]
  omega

theorem skipToEol_shifts : Shifts skipToEol := by
  intro pos d cs
  induction cs generalizing pos with
  | nil => simp [skipToEol]
  | cons c rest ih =>
      by_cases h : c = '\n' || c = '\r'
      · simp [skipToEol, h]
      · simp only [skipToEol, h, if_false, Bool.false_eq_true]
        rw [show pos + d + 1 = pos + 1 + d from by omega, ih (pos + 1)]

theorem skipComment_shifts : Shifts skipComment := by
  intro pos d cs
  cases cs with
  | nil => simp [skipComment]
  | cons c rest =>
      by_cases h : c = '#'
      · subst h
        simp only [skipComment]
        rw [show pos + d + 1 = pos + 1 + d from by omega,
            skipToEol_shifts (pos + 1) d rest]
      · simp [skipComment, h]

theorem skipEol_shifts : Shifts skipEol := by
  intro pos d cs
  unfold skipEol
  split
  · simp; omega
  · simp; omega
  · simp; omega
  · simp

/-! ### Plain-equation forms

`Shifts` is a definition, so `simp` cannot use the four theorems above
directly. These are the same facts as bare equations, which is the form
the composition proofs need. -/

theorem skipWs_shift (pos d : Nat) (cs : List Char) :
    skipWs (pos + d) cs = ((skipWs pos cs).1 + d, (skipWs pos cs).2) :=
  skipWs_shifts pos d cs

theorem skipToEol_shift (pos d : Nat) (cs : List Char) :
    skipToEol (pos + d) cs = ((skipToEol pos cs).1 + d, (skipToEol pos cs).2) :=
  skipToEol_shifts pos d cs

theorem skipComment_shift (pos d : Nat) (cs : List Char) :
    skipComment (pos + d) cs = ((skipComment pos cs).1 + d, (skipComment pos cs).2) :=
  skipComment_shifts pos d cs

theorem skipEol_shift (pos d : Nat) (cs : List Char) :
    skipEol (pos + d) cs = ((skipEol pos cs).1 + d, (skipEol pos cs).2) :=
  skipEol_shifts pos d cs

/-! ## 3. Composition

The quad-line loop calls the helpers in sequence, so the useful form is
that a sequence of shifting steps shifts. -/

theorem Shifts.comp {f g : Nat → List Char → Nat × List Char}
    (hf : Shifts f) (hg : Shifts g) :
    Shifts (fun pos cs => let (p, r) := f pos cs; g p r) := by
  intro pos d cs
  simp only [hf pos d cs, hg (f pos cs).1 d (f pos cs).2]

/-- The three-step tail the loop runs after a quad: skip spaces, skip a
comment, skip the line terminator. -/
theorem skipWsCommentEol_shifts :
    Shifts (fun pos cs =>
      let (p1, c1) := skipWs pos cs
      let (p2, c2) := skipComment p1 c1
      skipEol p2 c2) :=
  (skipWs_shifts.comp skipComment_shifts).comp skipEol_shifts

/-! ## 4. The quad-line loop

`parseQuadLinesAcc` reports positions only inside errors, so shifting
its start shifts any error it reports and leaves an `.ok` result
untouched. -/

/-- Add `d` to the position an error reports. -/
def shiftErr (d : Nat) : Except ParseError Dataset → Except ParseError Dataset
  | .ok ds => .ok ds
  | .error e => .error { e with pos := e.pos + d }

/-- What a quad reader has to satisfy for the loop's shift lemma to go
through. `readNQuad11` and `readNQuad12` are expected to satisfy it;
proving that is the one named residual this module leaves. -/
def QuadReaderShifts (mode : Mode) : Prop :=
  ∀ (pos d : Nat) (cs : List Char),
    (match mode with
     | .rdf11 => readNQuad11 (pos + d) cs
     | .rdf12 => readNQuad12 (pos + d) cs) =
      (match (match mode with
              | .rdf11 => readNQuad11 pos cs
              | .rdf12 => readNQuad12 pos cs) with
       | .ok (t, g, p, r) => .ok (t, g, p + d, r)
       | .error e => .error { e with pos := e.pos + d })

/-- **The loop shifts, given that its quad reader does.** Fuel and the
dataset are untouched; only the reported position moves. -/
theorem parseQuadLinesAcc_shift (mode : Mode) (hrd : QuadReaderShifts mode) :
    ∀ (fuel pos d : Nat) (cs : List Char) (ds : Dataset),
      parseQuadLinesAcc mode fuel (pos + d) cs ds
        = shiftErr d (parseQuadLinesAcc mode fuel pos cs ds)
  | 0, pos, d, cs, ds => by simp [parseQuadLinesAcc, shiftErr]
  | fuel + 1, pos, d, cs, ds => by
      cases mode with
      | rdf11 =>
        simp only [QuadReaderShifts] at hrd
        simp only [parseQuadLinesAcc, skipWs_shift, skipComment_shift,
                   skipEol_shift]
        split
        · simp [shiftErr]
        · exact parseQuadLinesAcc_shift .rdf11
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · exact parseQuadLinesAcc_shift .rdf11
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · exact parseQuadLinesAcc_shift .rdf11
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · rw [hrd (skipWs pos cs).1 d (skipWs pos cs).2]
          cases hstep : readNQuad11 (skipWs pos cs).1 (skipWs pos cs).2 with
          | error e => simp [shiftErr]
          | ok r =>
              obtain ⟨t, g, p2, cs2⟩ := r
              dsimp only
              simp only [skipWs_shift, skipComment_shift, skipEol_shift]
              exact parseQuadLinesAcc_shift .rdf11
                (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ (addQuad ds t g)
      | rdf12 =>
        simp only [QuadReaderShifts] at hrd
        simp only [parseQuadLinesAcc, skipWs_shift, skipComment_shift,
                   skipEol_shift]
        split
        · simp [shiftErr]
        · exact parseQuadLinesAcc_shift .rdf12
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · exact parseQuadLinesAcc_shift .rdf12
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · exact parseQuadLinesAcc_shift .rdf12
            (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ ds
        · rw [hrd (skipWs pos cs).1 d (skipWs pos cs).2]
          cases hstep : readNQuad12 (skipWs pos cs).1 (skipWs pos cs).2 with
          | error e => simp [shiftErr]
          | ok r =>
              obtain ⟨t, g, p2, cs2⟩ := r
              dsimp only
              simp only [skipWs_shift, skipComment_shift, skipEol_shift]
              exact parseQuadLinesAcc_shift .rdf12
                (by simp only [QuadReaderShifts]; exact hrd) fuel _ d _ (addQuad ds t g)

/-! ## Build-time checks -/

/-! Shifting the start shifts the reported position, on real input. -/
#guard (skipWs 0 "  a".toList).1 == 2
#guard (skipWs 7 "  a".toList).1 == 9
#guard (skipWs 0 "  a".toList).2 == (skipWs 7 "  a".toList).2

#guard (skipToEol 0 "abc\ndef".toList).1 == 3
#guard (skipToEol 5 "abc\ndef".toList).1 == 8
#guard (skipComment 0 "# hi\nx".toList).1 == 4
#guard (skipComment 5 "# hi\nx".toList).1 == 9
#guard (skipEol 0 "\r\nx".toList).1 == 2
#guard (skipEol 5 "\r\nx".toList).1 == 7
#guard (skipEol 0 "x".toList).1 == 0
#guard (skipEol 5 "x".toList).1 == 5

/-! The three-step tail, composed. -/
#guard ((fun (pos : Nat) (cs : List Char) =>
          let (p1, c1) := skipWs pos cs
          let (p2, c2) := skipComment p1 c1
          skipEol p2 c2) 0 "  # note\nrest".toList).1 == 9
#guard ((fun (pos : Nat) (cs : List Char) =>
          let (p1, c1) := skipWs pos cs
          let (p2, c2) := skipComment p1 c1
          skipEol p2 c2) 4 "  # note\nrest".toList).1 == 13

/-! `shiftErr` moves an error and leaves a success alone. -/
#guard (match shiftErr 3 (.error ⟨"x", 5⟩) with
        | .error e => e.pos | .ok _ => 0) == 8
#guard (match shiftErr 3 (.ok Dataset.empty) with
        | .ok ds => ds.default.length | .error _ => 99) == 0

/-! ## Axiom audit -/

#print axioms skipWs_shifts
#print axioms skipToEol_shifts
#print axioms skipComment_shifts
#print axioms skipEol_shifts
#print axioms parseQuadLinesAcc_shift

end L4Factoidal.Syntax.LexShift
