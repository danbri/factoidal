/-
L4Factoidal.SPARQL.TokenizeChain — walking a whole input, one token at
a time.

`TokenizerLemmas.lean` proves what ONE token does. This file composes
those steps into a statement about `tokenize` itself, which needs one
thing first: the fuel has to stop mattering.

## Why fuel is the obstacle, and why it is a small one

`tokenize s` seeds `tokenizeLoop` with `s.toList.length + 1`. A
per-token lemma leaves a shorter list and a fuel one smaller, so
chaining them means tracking an arithmetic relation between two numbers
that both shrink. Carrying that through an induction over a query is
noise, not content.

`tokenizeLoop_fuel` removes it: ABOVE the input length, the fuel does
not change the answer. The proof needs no knowledge of `nextToken` at
all, because the loop already carries its own progress guard —

    if rest.length ≥ cs.length then (eof :: acc).reverse
    else tokenizeLoop v12 f pos' rest (⟨tok, start⟩ :: acc)

so a recursive call always shrinks the list, and a strong induction on
that length is enough.

With fuel irrelevance in hand, `tokenizeLoop_cons` is a plain unfolding,
and a walk over a printed query is an induction with no arithmetic side
conditions beyond "the fuel started large enough".
-/
import L4Factoidal.SPARQL.TokenizerLemmas

namespace L4Factoidal.SPARQL

/-- The empty input tokenizes to end-of-input, at any positive fuel. -/
theorem tokenizeLoop_nil (f pos : Nat) (acc : List PosToken) (hf : 0 < f) :
    tokenizeLoop false f pos [] acc = (⟨Token.eof, pos⟩ :: acc).reverse := by
  cases f with
  | zero => omega
  | succ k =>
      conv => lhs; unfold tokenizeLoop
      simp [nextToken, skipWs, skipWsComments]

/-- **Fuel above the input length does not change the answer.** -/
theorem tokenizeLoop_fuel : ∀ (n f f' pos : Nat) (cs : List Char) (acc : List PosToken),
    cs.length ≤ n → n < f → n < f' →
    tokenizeLoop false f pos cs acc = tokenizeLoop false f' pos cs acc := by
  intro n
  induction n with
  | zero =>
      intro f f' pos cs acc hlen hf hf'
      have : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this
      rw [tokenizeLoop_nil f pos acc (by omega), tokenizeLoop_nil f' pos acc (by omega)]
  | succ k ih =>
      intro f f' pos cs acc hlen hf hf'
      cases f with
      | zero => omega
      | succ g =>
          cases f' with
          | zero => omega
          | succ g' =>
              conv => lhs; unfold tokenizeLoop
              conv => rhs; unfold tokenizeLoop
              rcases hnext : nextToken false pos cs with ⟨tok, start, pos', rest⟩
              simp only [hnext]
              split
              · rfl
              · by_cases hge : rest.length ≥ cs.length
                · simp [hge]
                · have hlt : rest.length < cs.length := Nat.lt_of_not_le hge
                  simp only [hge, if_false, ge_iff_le, decide_eq_true_eq]
                  exact ih g g' pos' rest _ (by omega) (by omega) (by omega)

/-- One step of the walk: a non-`eof` token that made progress. -/
theorem tokenizeLoop_cons (f pos : Nat) (cs rest : List Char) (tok : Token)
    (start pos' : Nat) (acc : List PosToken)
    (hnext : nextToken false pos cs = (tok, start, pos', rest))
    (hne : tok ≠ Token.eof) (hshrink : rest.length < cs.length) (hf : 0 < f) :
    tokenizeLoop false f pos cs acc
      = tokenizeLoop false (f - 1) pos' rest (⟨tok, start⟩ :: acc) := by
  cases f with
  | zero => omega
  | succ g =>
      conv => lhs; unfold tokenizeLoop
      simp only [hnext, Nat.add_sub_cancel]
      rw [if_neg (by omega)]

end L4Factoidal.SPARQL
