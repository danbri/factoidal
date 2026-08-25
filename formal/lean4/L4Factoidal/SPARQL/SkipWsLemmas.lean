/-
L4Factoidal.SPARQL.SkipWsLemmas — whitespace skipping, and its fuel.

`TokenizerLemmas.lean` proves what one token does when the input begins
AT the token. A printer that separates tokens with spaces produces input
that begins at a space instead, so a walk over such text needs one more
fact: a leading space can be dropped.

That is not immediate, because `skipWs` seeds its own fuel from the
remaining input length, so dropping a character changes the fuel as well
as the list. The fix is the same one `TokenizeChain.lean` uses for
`tokenizeLoop`: prove the fuel irrelevant above the input length, and
the rest is an unfolding.
-/
import L4Factoidal.SPARQL.TokenizerLemmas

namespace L4Factoidal.SPARQL

/-- A comment scan returns a suffix, so it never grows the input. This
is what makes the fuel induction below well-founded through the `#`
branch. -/
theorem scanToEol_length : ∀ (pos : Nat) (cs : List Char),
    (skipWsComments.scanToEol pos cs).2.length ≤ cs.length := by
  intro pos cs
  induction cs generalizing pos with
  | nil => simp [skipWsComments.scanToEol]
  | cons c rest ih =>
      conv => lhs; unfold skipWsComments.scanToEol
      by_cases hc : c = '\n'
      · simp [hc]
      · simp only [hc, if_neg, beq_iff_eq]
        exact Nat.le_succ_of_le (ih (pos + 1))

/-- Above the input length, the fuel does not change what whitespace
skipping returns. -/
theorem skipWsComments_fuel : ∀ (n f f' pos : Nat) (cs : List Char),
    cs.length ≤ n → n < f → n < f' →
    skipWsComments f pos cs = skipWsComments f' pos cs := by
  intro n
  induction n with
  | zero =>
      intro f f' pos cs hlen hf hf'
      have : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this
      cases f with
      | zero => omega
      | succ a => cases f' with
                  | zero => omega
                  | succ b => simp [skipWsComments]
  | succ k ih =>
      intro f f' pos cs hlen hf hf'
      cases cs with
      | nil =>
          cases f with
          | zero => omega
          | succ a => cases f' with
                      | zero => omega
                      | succ b => simp [skipWsComments]
      | cons c rest =>
          cases f with
          | zero => omega
          | succ a =>
            cases f' with
            | zero => omega
            | succ b =>
                conv => lhs; unfold skipWsComments
                conv => rhs; unfold skipWsComments
                by_cases hws : isWsC c = true
                · simp only [hws, if_true]
                  exact ih a b (pos + 1) rest (by simp at hlen; omega)
                    (by omega) (by omega)
                · by_cases hh : c = '#'
                  · simp only [hws, if_false, hh, if_pos]
                    have hle := scanToEol_length (pos + 1) rest
                    exact ih a b _ _ (by simp at hlen; omega) (by omega) (by omega)
                  · simp [hws, hh]

/-- `skipWs` in front of a whitespace character is `skipWs` after it. -/
theorem skipWs_cons_ws (pos : Nat) (c : Char) (cs : List Char)
    (hws : isWsC c = true) :
    skipWs pos (c :: cs) = skipWs (pos + 1) cs := by
  simp only [skipWs, List.length_cons]
  conv => lhs; unfold skipWsComments
  -- The two fuels coincide: one step off `(c :: cs).length + 1` is
  -- exactly `cs.length + 1`, which is what `skipWs (pos + 1) cs` seeds.
  -- `skipWsComments_fuel` above is what would be needed if they did not,
  -- and is kept for the chains that print more than one space.
  simp only [hws, if_true]

/-- And therefore a leading whitespace character does not change which
token comes next — only where it starts. -/
theorem nextToken_cons_ws (pos : Nat) (c : Char) (cs : List Char)
    (hws : isWsC c = true) :
    nextToken false pos (c :: cs) = nextToken false (pos + 1) cs := by
  conv => lhs; unfold nextToken
  conv => rhs; unfold nextToken
  rw [skipWs_cons_ws pos c cs hws]

end L4Factoidal.SPARQL
