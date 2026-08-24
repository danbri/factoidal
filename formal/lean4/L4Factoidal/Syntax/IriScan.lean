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

## How the swap was gated

Commit `fbbd2c4628a` kept the old ten-arm scanner alongside the new one
and `#guard`ed the two against each other over the table below — every
row agreeing on answer, error position and message. This commit deletes
the old scanner and keeps its certified answers as literals.

That gate mattered, because the tree's own tests barely reach this code:
of the 325 `#guard`s in `SyntaxTests`, `TurtleTests` and `RdfXmlTests`,
exactly one touches an escape inside an IRIREF, and it is a rejection
case. No test in any suite decodes a `\u` or `\U` inside `<…>`. That
gap is tracked separately and is not closed by this module.

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

/-! ## Behaviour, pinned

These are the answers the PRE-SPLIT scanner gave. Commit `fbbd2c4628a`
ran both scanners over this table and every row agreed, error position
and message included; the old scanner was deleted in the commit that
introduced these literals, so what stands here is its certified output
rather than a value anyone reasoned out.

`Except` has no `BEq`, hence the explicit projections. -/

private def bodyOf (s : String) : Option (String × Nat) :=
  match readIriRefBody 0 s.toList with
  | .ok (body, pos, _) => some (body, pos)
  | .error _ => none

private def errOf (s : String) : Option (String × Nat) :=
  match readIriRefBody 0 s.toList with
  | .ok _ => none
  | .error e => some (e.msg, e.pos)

/-! Accepting inputs: a plain body, the empty body, both escape forms. -/
#guard bodyOf "http://example.org/a>" == some ("http://example.org/a", 21)
#guard bodyOf ">" == some ("", 1)
#guard bodyOf "a\\u0041b>" == some ("aAb", 9)
#guard bodyOf "a\\U0001F600b>" == some ("a" ++ String.singleton (Char.ofNat 0x1F600) ++ "b", 13)

/-! Malformed escapes, both widths. -/
#guard errOf "\\u00ZZ>" == some ("invalid hex digit in \\u escape", 0)
#guard errOf "\\U0001F6ZZ>" == some ("invalid hex digit in \\U escape", 0)
#guard errOf "\\u12>" == some ("incomplete \\u escape in IRIREF", 0)
#guard errOf "\\U0001>" == some ("incomplete \\U escape in IRIREF", 0)

/-! Every forbidden codepoint, named by an escape. -/
#guard errOf "\\u0020>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u003C>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u003E>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u0022>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u007B>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u007D>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u007C>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u005C>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u005E>" == some ("IRI-forbidden codepoint in \\u escape", 0)
#guard errOf "\\u0060>" == some ("IRI-forbidden codepoint in \\u escape", 0)

/-! A surrogate escape is rejected by the codepoint decoder, not the
forbidden-set test, so it carries a different message. -/
#guard (errOf "\\uD800>").map Prod.snd == some 0
#guard (errOf "\\uD800>") != none

/-! Raw forbidden characters, one per member of the set. -/
#guard errOf "sp ace>" == some ("invalid character in IRIREF", 2)
#guard errOf "a<b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a\"b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a{b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a}b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a|b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a^b>" == some ("invalid character in IRIREF", 1)
#guard errOf "a`b>" == some ("invalid character in IRIREF", 1)

/-! Raw control characters at and below 0x20. -/
#guard errOf "a\tb>" == some ("invalid character in IRIREF", 1)
#guard errOf "a\nb>" == some ("invalid character in IRIREF", 1)

/-! Escapes other than `\u`/`\U`, and a trailing backslash. -/
#guard errOf "bad\\q>" == some ("invalid escape in IRIREF (only \\u/\\U permitted)", 3)
#guard errOf "bad\\nq>" == some ("invalid escape in IRIREF (only \\u/\\U permitted)", 3)
#guard errOf "abc\\" == some ("backslash at end of IRIREF", 3)

/-! Unterminated and empty input. -/
#guard errOf "no-terminator" == some ("unterminated IRIREF (expected '>')", 13)
#guard errOf "" == some ("unterminated IRIREF (expected '>')", 0)

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
