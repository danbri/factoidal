/-
L4Factoidal.Syntax.IriScan — the IRIREF body scanner, split so its
equations can be generated.

Unblocks <https://github.com/danbri/factoidal/issues/565>.

`Syntax.Lexing.readIriRefBody` is a ten-arm recursive match, two of its
arms carrying six- and ten-character literal patterns. Lean's
well-founded recursion generates one equation lemma per arm, and
generating them exhausts the container's memory: `#check
@readIriRefBody.eq_11`, alone in a file, is killed before any proof is
attempted. So the N-Triples round trip cannot be stated against it, and
`RDF.NTriples.RoundTrip` stays unported.

The fix is to move the deep patterns OUT of the recursion. `iriNextStep`
is NOT recursive, so its match compiles to a plain case tree whose
equations are cheap. `scanIriBody` recurses on a three-constructor
result, so its own equations are three small ones.

This module is the refactor proved to work — the termination argument
and the behavioural agreement with the shipping scanner on the fragment
below — before `Syntax.Lexing` is changed to use it. Swapping the
shipping lexer over is a separate landing, so a transcription error
cannot reach the 325 `#guard`s of the syntax tests unnoticed.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-- What the next characters of an IRIREF body are. `width` is how many
characters the step consumed, which is what makes the recursion below
terminate and what advances `pos`. -/
inductive IriStep where
  | close (rest : List Char)
  | emit  (c : Char) (width : Nat) (rest : List Char)
  | fail  (err : ParseError)
  deriving Repr

/-- The tail shared by the `\\u` and `\\U` arms: reject a forbidden
codepoint, then decode. Factored out so `iriNextStep` carries no `let`,
which is what lets `split` see through it in the proof below. -/
def iriEmitAt (cp pos width : Nat) (rest : List Char) (which : String) : IriStep :=
  if isIriForbiddenCodepoint cp then
    .fail ⟨"IRI-forbidden codepoint in " ++ which ++ " escape", pos⟩
  else
    match codepointToChar cp pos with
    | .error e => .fail e
    | .ok c => .emit c width rest

theorem iriEmitAt_emit {cp pos width : Nat} {rest : List Char} {which : String}
    {c : Char} {w : Nat} {r : List Char}
    (h : iriEmitAt cp pos width rest which = .emit c w r) : r = rest := by
  unfold iriEmitAt at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [IriStep.emit.injEq] at h; exact h.2.2.symm

/-- One step, with every deep pattern of the original in it and no
recursion. Transcribed arm for arm from `Lexing.readIriRefBody`. -/
def iriNextStep (pos : Nat) : List Char → IriStep
  | [] => .fail ⟨"unterminated IRIREF (expected '>')", pos⟩
  | '>' :: rest => .close rest
  | '\\' :: 'u' :: h0 :: h1 :: h2 :: h3 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3 with
      | some d0, some d1, some d2, some d3 =>
          iriEmitAt (d0 * 4096 + d1 * 256 + d2 * 16 + d3) pos 6 rest "\\u"
      | _, _, _, _ => .fail ⟨"invalid hex digit in \\u escape", pos⟩
  | '\\' :: 'u' :: _ => .fail ⟨"incomplete \\u escape in IRIREF", pos⟩
  | '\\' :: 'U' :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: rest =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3,
            hexVal h4, hexVal h5, hexVal h6, hexVal h7 with
      | some d0, some d1, some d2, some d3, some d4, some d5, some d6, some d7 =>
          iriEmitAt (d0 * 268435456 + d1 * 16777216 + d2 * 1048576 + d3 * 65536
                   + d4 * 4096 + d5 * 256 + d6 * 16 + d7) pos 10 rest "\\U"
      | _, _, _, _, _, _, _, _ => .fail ⟨"invalid hex digit in \\U escape", pos⟩
  | '\\' :: 'U' :: _ => .fail ⟨"incomplete \\U escape in IRIREF", pos⟩
  | '\\' :: [] => .fail ⟨"backslash at end of IRIREF", pos⟩
  | '\\' :: _ :: _ => .fail ⟨"invalid escape in IRIREF (only \\u/\\U permitted)", pos⟩
  | c :: rest =>
      if c.toNat ≤ 0x20 || isIriForbiddenCodepoint c.toNat then
        .fail ⟨"invalid character in IRIREF", pos⟩
      else
        .emit c 1 rest

/-- The step consumes at least one character. This is the whole
termination argument, and it is provable arm by arm because
`iriNextStep` does not recurse. -/
theorem iriNextStep_emit_shorter {pos : Nat} {cs : List Char}
    {c : Char} {w : Nat} {rest : List Char}
    (h : iriNextStep pos cs = .emit c w rest) : rest.length < cs.length := by
  unfold iriNextStep at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · rename_i h0 h1 h2 h3 tail _
    split at h
    · have := iriEmitAt_emit h; subst this; simp; omega
    · exact absurd h (by simp)
  · exact absurd h (by simp)
  · rename_i h0 h1 h2 h3 h4 h5 h6 h7 tail _
    split at h
    · have := iriEmitAt_emit h; subst this; simp; omega
    · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [IriStep.emit.injEq] at h
      obtain ⟨-, -, hr⟩ := h
      subst hr
      simp

/-- The body scanner, recursing on a three-constructor result. Its own
equations are three small ones. -/
def scanIriBody (pos : Nat) (cs : List Char) :
    Except ParseError (String × Nat × List Char) :=
  match h : iriNextStep pos cs with
  | .close rest => .ok ("", pos + 1, rest)
  | .fail e => .error e
  | .emit c w rest =>
      have : rest.length < cs.length := iriNextStep_emit_shorter h
      (scanIriBody (pos + w) rest).map (fun (s, p, r) => (c.toString ++ s, p, r))
termination_by cs.length

/-! ## Behavioural agreement with the shipping scanner

Checked on the fragment the tests exercise. A full equality would need
`readIriRefBody`'s equations, which is the thing that cannot be
generated — so this is what CAN be stated, and the swap landing will
rest on the syntax tests as well. -/

private def eqRes : Except ParseError (String × Nat × List Char) →
    Except ParseError (String × Nat × List Char) → Bool
  | .ok a,    .ok b    => a == b
  | .error a, .error b => a == b
  | _,        _        => false

private def agreesOn (s : String) : Bool :=
  eqRes (scanIriBody 0 s.toList) (readIriRefBody 0 s.toList)

#guard agreesOn "http://example.org/a>"
#guard agreesOn "a\\u0041b>"
#guard agreesOn "a\\U0001F600b>"
#guard agreesOn "no-terminator"
#guard agreesOn "bad\\q>"
#guard agreesOn "sp ace>"
#guard agreesOn "\\u00ZZ>"
#guard agreesOn "\\u12>"
#guard agreesOn ">"
#guard agreesOn ""

/-! ## The equations the shipping scanner cannot produce -/

theorem scanIriBody_close {pos : Nat} {cs rest : List Char}
    (h : iriNextStep pos cs = .close rest) :
    scanIriBody pos cs = .ok ("", pos + 1, rest) := by
  rw [scanIriBody]; split <;> simp_all

theorem scanIriBody_fail {pos : Nat} {cs : List Char} {e : ParseError}
    (h : iriNextStep pos cs = .fail e) : scanIriBody pos cs = .error e := by
  rw [scanIriBody]; split <;> simp_all

theorem scanIriBody_emit {pos : Nat} {cs rest : List Char} {c : Char} {w : Nat}
    (h : iriNextStep pos cs = .emit c w rest) :
    scanIriBody pos cs
      = (scanIriBody (pos + w) rest).map (fun (s, p, r) => (c.toString ++ s, p, r)) := by
  rw [scanIriBody]; split <;> simp_all

/-! ## Axiom audit -/

#print axioms iriNextStep_emit_shorter
#print axioms scanIriBody_emit

end L4Factoidal.Syntax
