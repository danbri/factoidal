/-
L4Factoidal.Syntax.Locality — the Lean counterpart of
`Parser.NTriples.Locality`.

## What locality is, and why both trees need it

A reader is LOCAL when appending more input after it has already stopped
does not change its answer. `RDF.NQuads.Streaming`'s
`theorem_stream_eq_batch` rests on it: a chunk boundary splits the input
into `complete ++ carry`, and streaming agrees with batching only if
parsing the complete part answers the same on `complete` as it does on
`complete ++ carry`.

The F\* module's own banner says two theorems are blocked on this same
wall, and diagnoses the cause: `"" ^ s == s` and `(a^b)^c == a^(b^c)`
both FAIL for symbolic strings, because Z3 has no associativity theory
for `FStar.String.strcat`. Its 2,848 lines re-state every scanner over
BYTE READS to get out from under that.

⚠️ **The Lean tree does NOT escape this.** `tools/lean-port-gap.py`
classified `Parser.NTriples.Locality` as needing no counterpart BY
DESIGN, and recorded no reason — the only entry in that table without
one. The reason it would have needed is false. A list-based reader can
still read past the end of a prefix: `List.span isBnodeChar` on
`"_:abc"` stops at the end of input, and on `"_:abc" ++ "d"` it consumes
the `d` as well. Locality has to be proved here too.

What IS different is the register. In Lean the statement is about list
suffixes, so the proof is structural induction rather than byte-index
arithmetic, and the side condition is visible in the statement: a reader
that stopped with input LEFT OVER is local; one that ran to the end of
its input is not, and cannot be.

## What is proved here

The pilot the F\* program itself chose — the IRI scanner — in the Lean
register:

* `iriEmitAt_local` — the escape-emitting step passes its remainder
  through untouched.
* `iriEmitAt_ne_close` — that step never closes an IRIREF, so the
  close-locality case analysis can discard it.
* `iriNextStep_close_local` — a step that CLOSED on `cs` closes at the
  same place on `cs ++ extra`.

## What is NOT proved here, named

`iriNextStep_emit_local` — the same statement for the EMIT outcome —
and everything above it: `readIriRefBody`, `readIriRef`,
`readBlankNodeLabel`, `readLiteral`, and the `readNQuad11` composition.
Without those the streaming-equals-batch theorem cannot be stated in
this tree either.

The emit case is not blocked on an idea; it is the same case analysis as
the close case with the two escape arms surviving instead of being
discarded, and those arms need `iriEmitAt_local` applied under the
equation compiler's `split`. It is left unproved rather than half-proved
because a named gap is checkable and a weakened theorem is not.

Tracked at <https://github.com/danbri/factoidal/issues/570>.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-! ## 1. Locality, stated

The side condition is the whole content: a reader that stopped with
input left over answers the same on more input. A reader that ran to
the end of its input does not, and no hypothesis-free version of this
is true. -/

/-- A reader is local when, having stopped with a non-empty remainder,
it answers the same on a longer input. -/
def ReaderLocal {α : Type}
    (f : Nat → List Char → Except ParseError (α × Nat × List Char)) : Prop :=
  ∀ (pos : Nat) (cs extra : List Char) (r : α) (p' : Nat) (rest : List Char),
    f pos cs = .ok (r, p', rest) → rest ≠ [] →
    f pos (cs ++ extra) = .ok (r, p', rest ++ extra)

/-! ## 2. The escape-emitting step -/

/-- The step that emits a decoded escape never closes an IRIREF. This
is what lets the close-locality analysis discard both escape arms. -/
theorem iriEmitAt_ne_close (cp pos width : Nat) (rest : List Char)
    (which : String) (r : List Char) :
    iriEmitAt cp pos width rest which ≠ .close r := by
  unfold iriEmitAt
  split
  · simp
  · split <;> simp

/-- The escape step passes its remainder through untouched, so
appending to the input appends to the remainder. -/
theorem iriEmitAt_local (cp pos width : Nat) (rest extra : List Char)
    (which : String) (c : Char) (w : Nat) (r : List Char)
    (h : iriEmitAt cp pos width rest which = .emit c w r) :
    iriEmitAt cp pos width (rest ++ extra) which = .emit c w (r ++ extra) := by
  unfold iriEmitAt at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp_all

/-! ## 3. Closing is local -/

set_option maxHeartbeats 4000000 in
/-- **A step that closed the IRIREF closes at the same place on longer
input.** The `>` is already in `cs`, so nothing appended after it can
move the close. -/
theorem iriNextStep_close_local (pos : Nat) (cs extra rest : List Char)
    (h : iriNextStep pos cs = .close rest) :
    iriNextStep pos (cs ++ extra) = .close (rest ++ extra) := by
  unfold iriNextStep at h ⊢
  split at h <;> (try split at h) <;> simp_all [iriEmitAt_ne_close]

/-! ## 4. Why the side condition cannot be dropped

⚠️ **Locality is FALSE without the stopped-short condition.** The
blank-node reader spans as far as the input allows, so `_:abc` scans a
three-character label on its own and a four-character one when a `d`
follows. Any statement that drops `rest ≠ []` is refuted by that pair.

It is recorded below as two `#guard`s rather than as a theorem because
the values differ only in a `String`, and the kernel does not reduce
`String` equality — the same reason several other modules in this port
pin string-valued facts with `#guard`. -/

/-! ## Build-time checks -/

/-! Closing is local on a worked case. -/
#guard (match iriNextStep 0 "a>".toList with
         | .emit c _ r => c == 'a' && r == ">".toList | _ => false)
#guard (match iriNextStep 0 ">rest".toList with
         | .close r => r == "rest".toList | _ => false)
#guard (match iriNextStep 0 (">".toList ++ "more".toList) with
         | .close r => r == "more".toList | _ => false)

/-! ⚠️ And the step is NOT local when the input runs out mid-escape: on
its own the truncated escape fails, with more input it emits. This is
the reason `iriNextStep_emit_local` needs the same care as the close
case rather than being a corollary of it. -/
#guard (match iriNextStep 0 "\\u00".toList with
         | .fail _ => true | _ => false) == true
#guard (match iriNextStep 0 ("\\u00".toList ++ "41".toList) with
         | .fail _ => true | _ => false) == false

/-! The blank-node reader spans to the end of input, which is the
refutation above as a pair of values. -/
#guard (readBlankNodeLabel 0 "_:abc".toList).toOption.map (fun x => x.1)
        == some "abc"
#guard (readBlankNodeLabel 0 "_:abcd".toList).toOption.map (fun x => x.1)
        == some "abcd"

/-! ## Axiom audit -/

#print axioms iriEmitAt_local
#print axioms iriEmitAt_ne_close
#print axioms iriNextStep_close_local

end L4Factoidal.Syntax
