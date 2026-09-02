/-
L4Factoidal.Syntax.TurtleStatementScanTheorems — the incremental
`StatementScan.head` field equals its specification.

`StatementScan` carries `head`, the first `directiveHeadLength`
characters of the current statement candidate after its leading
whitespace. `beginsNoDotDirective` reads that field instead of
reversing `currentRev` at every line end, which is what made the
scanner quadratic in statement length (2026-09-02: about 280 G list
steps on a 134 MB statement group of the UK Parliament dump).

The meaning is `directiveHeadSpec currentRev`. This module proves that
`pushHead`, the per-character update, computes exactly that
specification, and lifts the result along `feedChar`, `feedChars`,
`feed` and a `List.foldl` of `feed` from `StatementScan.init`. The
specification form is kept as the meaning; the field is the
implementation, and this file is the bridge.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

/-- Appending one character to the source-order text either extends the
whitespace-stripped prefix, or — when everything so far was whitespace —
restarts it at that character unless the character is whitespace too. -/
theorem dropWs_append_single (xs : List Char) (c : Char) :
    dropWs (xs ++ [c]) =
      if (dropWs xs).isEmpty then (if isWs c then [] else [c])
      else dropWs xs ++ [c] := by
  induction xs with
  | nil => simp [dropWs]
  | cons x xs ih =>
    simp only [List.cons_append, dropWs]
    split
    · exact ih
    · simp

/-- `pushHead` commutes with truncation: extending a truncated
whitespace-stripped text is the same as truncating the extended one. -/
theorem pushHead_take (zs : List Char) (c : Char) :
    pushHead (zs.take directiveHeadLength) c =
      (if zs.isEmpty then (if isWs c then [] else [c]) else zs ++ [c]).take
        directiveHeadLength := by
  cases zs with
  | nil =>
    simp only [List.isEmpty_nil, if_true]
    split <;> simp_all [pushHead, directiveHeadLength]
  | cons z zs =>
    have h0 : ((z :: zs).take directiveHeadLength).isEmpty = false := by
      simp [directiveHeadLength]
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, pushHead, h0,
      List.length_take]
    by_cases hlt : (z :: zs).length < directiveHeadLength
    · rw [if_pos (by omega)]
      rw [List.take_of_length_le (Nat.le_of_lt hlt), List.take_of_length_le]
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [List.length_cons] at hlt
      omega
    · rw [if_neg (by omega)]
      exact (List.take_append_of_le_length (by omega)).symm

/-- The per-character head update computes the head specification. -/
theorem pushHead_spec (currentRev : List Char) (c : Char) :
    pushHead (directiveHeadSpec currentRev) c = directiveHeadSpec (c :: currentRev) := by
  unfold directiveHeadSpec
  rw [List.reverse_cons, dropWs_append_single]
  exact pushHead_take _ _

/-- The scanner invariant: the maintained head field equals the
specification of the current candidate. -/
def StatementScan.HeadInv (scan : StatementScan) : Prop :=
  scan.head = directiveHeadSpec scan.currentRev

/-- One fed character preserves the invariant. The two candidate-closing
branches restart both fields together (`currentRev := [c]`,
`head := pushHead [] c`); the ordinary branch extends both. -/
theorem feedChar_headInv (scan : StatementScan) (c : Char) (h : scan.HeadInv) :
    (scan.feedChar c).HeadInv := by
  unfold StatementScan.HeadInv at h ⊢
  unfold StatementScan.feedChar
  split
  · show pushHead [] c = directiveHeadSpec [c]
    exact pushHead_spec [] c
  · split
    · show pushHead [] c = directiveHeadSpec [c]
      exact pushHead_spec [] c
    · show pushHead scan.head c = directiveHeadSpec (c :: scan.currentRev)
      rw [h]
      exact pushHead_spec scan.currentRev c

/-- A fed character list preserves the invariant. -/
theorem feedChars_headInv (scan : StatementScan) (cs : List Char)
    (h : scan.HeadInv) : (scan.feedChars cs).HeadInv := by
  induction cs generalizing scan with
  | nil => exact h
  | cons c cs ih =>
    simp only [StatementScan.feedChars]
    exact ih _ (feedChar_headInv scan c h)

/-- A fed decoded chunk preserves the invariant. -/
theorem feed_headInv (scan : StatementScan) (chunk : String)
    (h : scan.HeadInv) : (scan.feed chunk).HeadInv :=
  feedChars_headInv scan chunk.toList h

/-- The initial scan satisfies the invariant: both sides are `[]`. -/
theorem init_headInv : StatementScan.init.HeadInv := rfl

/-- Any sequence of fed chunks preserves the invariant. -/
theorem foldl_feed_headInv (scan : StatementScan) (chunks : List String)
    (h : scan.HeadInv) : (chunks.foldl StatementScan.feed scan).HeadInv := by
  induction chunks generalizing scan with
  | nil => exact h
  | cons chunk rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (feed_headInv scan chunk h)

/-- After any run of the streaming scanner from `init`, the head field
that `beginsNoDotDirective` reads is exactly the specification form it
replaced. -/
theorem feed_head_eq_spec (chunks : List String) :
    (chunks.foldl StatementScan.feed StatementScan.init).head =
      directiveHeadSpec (chunks.foldl StatementScan.feed StatementScan.init).currentRev :=
  foldl_feed_headInv StatementScan.init chunks init_headInv

/-- The name `StatementScan.head`'s documentation comment refers to. -/
theorem head_eq_spec (chunks : List String) :
    (chunks.foldl StatementScan.feed StatementScan.init).head =
      directiveHeadSpec (chunks.foldl StatementScan.feed StatementScan.init).currentRev :=
  feed_head_eq_spec chunks

#print axioms pushHead_spec
#print axioms feedChar_headInv
#print axioms feed_head_eq_spec

end L4Factoidal.Syntax
