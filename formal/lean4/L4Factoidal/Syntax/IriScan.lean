/-
L4Factoidal.Syntax.IriScan — the IRIREF scanner's equation lemmas, and a
differential check against the scanner it replaced.

<https://github.com/danbri/factoidal/issues/565>. `Syntax.Lexing`'s
`readIriRefBody` used to be a ten-arm recursion. Lean generates one
equation lemma per arm and generating them exhausted the container's
memory, so nothing downstream could rewrite with it and the N-Triples
round trip could not be stated at all.

It is now a non-recursive step classifier (`iriNextStep`) plus a
three-arm recursion, so its equations are three small ones and they are
proved below.

## How the swap is gated

The old scanner is still in `Syntax.Lexing` as
`readIriRefBodyLegacy`, marked as scaffolding with a removal
condition. Its equations still cannot be generated, but EVALUATION is
unaffected, so the `#guard`s below run both scanners on the same input
and compare. That makes the transcription's faithfulness a build-time
check rather than a matter of my judgement — which mattered here,
because the tree's own tests barely reach this code: of the 325
`#guard`s in `SyntaxTests`, `TurtleTests` and `RdfXmlTests`, exactly one
touches an escape inside an IRIREF, and it is a rejection case. No test
in any suite decodes a `\u` or `\U` inside `<…>`.

## One deliberate difference

The old scanner was STRUCTURAL recursion on the input list. The new one
is well-founded recursion on `cs.length` (`termination_by`), because the
step classifier hands back a `rest` that Lean cannot see as a structural
subterm. Behaviour is unchanged — that is what the table below checks —
but definitional unfolding differs, so a proof that relied on the old
one reducing by `rfl` may need one of the equations instead.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-! ## The three equations the ten-arm version could not produce -/

theorem readIriRefBody_close {pos : Nat} {cs rest : List Char}
    (h : iriNextStep pos cs = .close rest) :
    readIriRefBody pos cs = .ok ("", pos + 1, rest) := by
  rw [readIriRefBody]; split <;> simp_all

theorem readIriRefBody_fail {pos : Nat} {cs : List Char} {e : ParseError}
    (h : iriNextStep pos cs = .fail e) : readIriRefBody pos cs = .error e := by
  rw [readIriRefBody]; split <;> simp_all

theorem readIriRefBody_emit {pos : Nat} {cs rest : List Char} {c : Char} {w : Nat}
    (h : iriNextStep pos cs = .emit c w rest) :
    readIriRefBody pos cs
      = (readIriRefBody (pos + w) rest).map (fun (s, p, r) => (c.toString ++ s, p, r)) := by
  rw [readIriRefBody]; split <;> simp_all

/-! ## The differential table

`Except` has no `BEq`, hence the explicit comparison. Every row runs both
scanners on one input and demands the same answer, error position and
message included. -/

private def eqRes : Except ParseError (String × Nat × List Char) →
    Except ParseError (String × Nat × List Char) → Bool
  | .ok a,    .ok b    => a == b
  | .error a, .error b => a == b
  | _,        _        => false

private def agrees (s : String) : Bool :=
  eqRes (readIriRefBody 0 s.toList) (readIriRefBodyLegacy 0 s.toList)

/-! Accepting inputs: a plain body, the empty body, both escape forms. -/
#guard agrees "http://example.org/a>"
#guard agrees ">"
#guard agrees "a\\u0041b>"
#guard agrees "a\\U0001F600b>"
#guard agrees "\\u0041\\U00000042>"

/-! Malformed escapes: bad hex digit, truncated, both widths. -/
#guard agrees "\\u00ZZ>"
#guard agrees "\\u12>"
#guard agrees "\\U0001F6ZZ>"
#guard agrees "\\U0001>"

/-! Escapes naming a codepoint the grammar forbids, and a surrogate. -/
#guard agrees "\\u0020>"
#guard agrees "\\u003C>"
#guard agrees "\\u003E>"
#guard agrees "\\u0022>"
#guard agrees "\\u007B>"
#guard agrees "\\u007D>"
#guard agrees "\\u007C>"
#guard agrees "\\u005C>"
#guard agrees "\\u005E>"
#guard agrees "\\u0060>"
#guard agrees "\\uD800>"

/-! Raw forbidden characters, one per member of the set. -/
#guard agrees "sp ace>"
#guard agrees "a<b>"
#guard agrees "a\"b>"
#guard agrees "a{b>"
#guard agrees "a}b>"
#guard agrees "a|b>"
#guard agrees "a^b>"
#guard agrees "a`b>"

/-! Raw control characters at and below 0x20. -/
#guard agrees "a\tb>"
#guard agrees "a\nb>"

/-! Escapes other than `\u`/`\U`, and a trailing backslash. -/
#guard agrees "bad\\q>"
#guard agrees "bad\\nq>"
#guard agrees "abc\\"

/-! Unterminated and empty input. -/
#guard agrees "no-terminator"
#guard agrees ""

/-! And the whole-token entry point, which is what callers use. -/
#guard (match readIriRef 0 "<http://example.org/a>".toList with
        | .ok (s, p, _) => some (s, p)
        | .error _ => none) == some ("http://example.org/a", 22)
#guard (match readIriRef 0 "http://example.org/a>".toList with
        | .ok _ => false | .error _ => true)

/-! ## Axiom audit -/

#print axioms iriNextStep_emit_shorter
#print axioms readIriRefBody_emit

end L4Factoidal.Syntax
