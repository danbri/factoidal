/-
L4Factoidal.Syntax.LocalityLiteral — locality for the language-tag and
datatype readers.

⚠️ **The string-literal reader is NOT here, and the reason is a wall this
repository has hit before.** `readStringLiteralBody` has nineteen arms,
two of which (`\u`, `\U`) match on four and eight `hexVal` scrutinees
at once. Any tactic that unfolds it — `simp only [readStringLiteralBody]`
included — forces those apart, and the elaboration climbs past 10 GB and
is killed. Measured three ways: with `simp_all`, with a single `rw` then
`simp_all`, and with a per-arm helper lemma. All three reach ~10-12 GB
and take SIGKILL.

This is <https://github.com/danbri/factoidal/issues/565> again, one
reader over. That issue was the same shape for `readIriRefBody` — ten
arms, equation generation exhausted memory, nothing downstream could
rewrite with it — and the fix was `Syntax/IriScan.lean`: a non-recursive
step classifier plus a three-arm recursion, whose three equations are
provable. `readIriRefBody_local` in `Syntax.Locality` exists only because
that refactor already happened.

`readStringLiteralBody` needs the same treatment before its locality can
be stated. Filed as
<https://github.com/danbri/factoidal/issues/574>.

## What IS here

* `readLangTagRun_local` — ⚠️ WITH a side condition: it is a span, so it
  carries the same stopped-inside requirement the blank-node reader
  does.
`readDatatype_local` is NOT here either. It delegates to `readIriRef`,
which is already proved local, so it is not blocked in principle — it is
simply downstream of the literal reader in the only composition that
needs it (`readObject11`), and landing it alone would be a lemma with
nothing to feed. It goes in with the rest once
<https://github.com/danbri/factoidal/issues/574> clears.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Locality

namespace L4Factoidal.Syntax

/-- ⚠️ The language-tag run uses a span, so it carries the same
stopped-inside condition the blank-node reader does. -/
theorem readLangTagRun_local (pos : Nat) (cs extra : List Char) (a : Char)
    (t : List Char) (h : (cs.span isLangChar).2 = a :: t) :
    readLangTagRun pos (cs ++ extra)
      = ((readLangTagRun pos cs).1, (readLangTagRun pos cs).2.1,
         (readLangTagRun pos cs).2.2 ++ extra) := by
  simp only [readLangTagRun]
  cases hsp : cs.span isLangChar with
  | mk taken dropped =>
      rw [hsp] at h
      subst h
      rw [span_append_of_stopped isLangChar cs taken a t extra hsp]
      simp [hsp]




/-! ## Axiom audit -/

#print axioms readLangTagRun_local

end L4Factoidal.Syntax
