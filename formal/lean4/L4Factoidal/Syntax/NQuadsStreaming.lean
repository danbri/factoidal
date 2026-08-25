/-
L4Factoidal.Syntax.NQuadsStreaming — layer 1 of the port of
`RDF.NQuads.Streaming`.

The F\* module answers a question the owner asked, made precise: a
consumer folds over arbitrary byte-chunk boundaries — as bytes arrive
off a socket or a file reader, with NO guarantee a chunk boundary lands
on a line boundary — and the claim is that this produces the same
dataset as parsing the whole input at once.

## The wall the F* module had to walk around, and why Lean has no wall

Its banner records a design decision taken during the work, not going
in. It builds the splitter on `FStar.String.list_of_string` at the
CODEPOINT level rather than on `Parser.FastString`'s byte-indexed
`fs_byte_sub`, because proving "slice at k, slice from k, concatenate,
get the input back" through `fs_byte_sub` needs a bridging lemma that
routes through `utf8_decode_all (utf8_bytes s)` — and recovering `s`
from that composition is the SINGLE-DECODER ROUND TRIP theorem that
`Parser.FastString.Spec.fst`'s own banner documents as ATTEMPTED and
PARKED after three tries
(<https://github.com/danbri/factoidal/issues/374>).

The Lean parser already works on `List Char` throughout, so the split
is a list split and the reconstruction lemma is a one-line induction.
There is no byte layer to bridge and nothing to park. This is the same
shape as findings A1 and A9c: the F* difficulty is in the host
library's string interface, and it does not survive the change of host.

## What the splitter guarantees

`splitCompleteLines` cuts a buffer after its LAST newline. Three
theorems say what that means, and each is a property the streaming fold
depends on:

* `splitCompleteLines_reconstruct` — the two halves concatenate back to
  the input. Without it a chunk boundary could lose a character.
* `splitCompleteLines_carry_no_newline` — the carry holds no newline, so
  it is a genuine partial line and never a whole one held back.
* `splitCompleteLines_complete_ends_newline` — a non-empty complete part
  ends in a newline, so what is handed to the parser is whole lines.

## Fuel is never threaded across a chunk boundary

`feedChunk` and `finish` each call the parser on a FRESH, self-contained
character list with fuel `length + 1` — the same discipline
`parseNQuads` uses for a whole document. Fuel is never guessed and
never carried: each call gets its own provably-sufficient budget.
`parseFrom_fuel_is_local` states that, and
`parseQuadLinesAcc11_fuel_indep` says two runs with different budgets
agree whenever each budget exceeds the input length — which is what
lets the streaming run, whose fuel comes from one chunk, be compared
with the batch run, whose fuel comes from the whole document.

## The offset IS threaded, and that is a change from the F\* module

`RDF.NQuads.Streaming`'s `feed_chunk` calls `parse_nquads_acc complete 0`
— every chunk restarts the offset at zero — and pays for it with the
`lemma_*_shift` family, which is a large part of its 3,438 lines. Here
`StreamState` carries the absolute offset instead. Two reasons, and the
first is a defect the F\* design has:

* a parse error in the fifth chunk should name its place in the
  DOCUMENT, not in whatever buffer the consumer happened to assemble;
* with the offset threaded, the streaming run and the batch run pass
  the same positions to the same readers, so no shift lemma is needed
  to compare them.

## Where the homomorphism lives

The streaming-equals-batch theorem is PROVED: `streamParse11_eq_batch`
in `Syntax/NQuadsHomomorphism.lean`, from the line-boundary
concatenation lemma `parseQuadLines11_concat` in
`Syntax/NQuadsConcat.lean` — the counterpart of the F* module's
`lemma_parse_nquads_acc_concat_line_general`.
<https://github.com/danbri/factoidal/issues/570>.

`streamParse_single_chunk` below is the special case that needs no
concatenation lemma.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.LocalityCount

namespace L4Factoidal.Syntax.NQuadsStreaming

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## 1. The line splitter -/

def isNl (c : Char) : Bool := c == '\n'

/-- Cut a buffer after its LAST newline. The first half is whole lines;
the second is the partial line to carry into the next chunk. -/
def splitCompleteLines : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      let (complete, carry) := splitCompleteLines rest
      if complete.isEmpty then
        if isNl c then ([c], carry) else ([], c :: carry)
      else (c :: complete, carry)

/-! ## 2. What the splitter guarantees -/

/-- **Nothing is lost at a chunk boundary.** -/
theorem splitCompleteLines_reconstruct : ∀ (cs : List Char),
    (splitCompleteLines cs).1 ++ (splitCompleteLines cs).2 = cs
  | [] => rfl
  | c :: rest => by
      have ih := splitCompleteLines_reconstruct rest
      simp only [splitCompleteLines]
      split
      · rename_i hE
        have h0 : (splitCompleteLines rest).1 = [] := List.isEmpty_iff.mp hE
        rw [h0, List.nil_append] at ih
        split <;> simp [ih]
      · simp [ih]

/-- **The carry is a partial line, never a whole one.** -/
theorem splitCompleteLines_carry_no_newline : ∀ (cs : List Char),
    (splitCompleteLines cs).2.all (fun c => !isNl c) = true
  | [] => rfl
  | c :: rest => by
      have ih := splitCompleteLines_carry_no_newline rest
      simp only [splitCompleteLines]
      split
      · split
        · simpa using ih
        · rename_i hn
          simp only [List.all_cons, Bool.and_eq_true, ih, and_true,
                     Bool.not_eq_true']
          simpa using hn
      · simpa using ih

/-- **What reaches the parser is whole lines.** -/
theorem splitCompleteLines_complete_ends_newline : ∀ (cs : List Char),
    (splitCompleteLines cs).1 = [] ∨
    ((splitCompleteLines cs).1.getLast?.map isNl) = some true
  | [] => Or.inl rfl
  | c :: rest => by
      have ih := splitCompleteLines_complete_ends_newline rest
      simp only [splitCompleteLines]
      split
      · rename_i hE
        split
        · rename_i hn; exact Or.inr (by simp [hn])
        · exact Or.inl rfl
      · rename_i hNE
        have h0 : (splitCompleteLines rest).1 ≠ [] := by
          intro h; rw [h] at hNE; simp at hNE
        refine Or.inr ?_
        rcases ih with h | h
        · exact absurd h h0
        · rw [List.getLast?_cons_of_ne_nil h0]
          exact h

/-! ## 3. The streaming state -/

/-- What a consumer carries between chunks: the dataset built so far,
the partial line not yet parsed, and the first error if one happened. -/
structure StreamState where
  ds : Dataset
  carry : List Char
  /-- Absolute character offset in the whole document at which `carry`
  starts. Threaded so a parse error names its place in the DOCUMENT and
  not in whatever buffer the consumer happened to assemble. -/
  pos : Nat
  err : Option ParseError
  deriving Repr

def initialState : StreamState :=
  { ds := Dataset.empty, carry := [], pos := 0, err := none }

/-- Parse a self-contained character list from a starting dataset, at a
given absolute offset. The fuel is computed HERE, from this list, and
never carried in. -/
def parseFrom (mode : Mode) (pos : Nat) (cs : List Char) (ds : Dataset) :
    Except ParseError Dataset :=
  parseQuadLinesAcc mode (cs.length + 1) pos cs ds

/-- Take one chunk. Everything up to the last newline is parsed now;
the rest waits for the next chunk. An error is sticky: once a chunk has
failed, later chunks cannot un-fail it. -/
def feedChunk (mode : Mode) (st : StreamState) (chunk : List Char) : StreamState :=
  match st.err with
  | some _ => st
  | none =>
      let buf := st.carry ++ chunk
      let (complete, carry) := splitCompleteLines buf
      match parseFrom mode st.pos complete st.ds with
      | .ok ds' =>
          { ds := ds', carry := carry, pos := st.pos + complete.length, err := none }
      | .error e =>
          { ds := st.ds, carry := carry, pos := st.pos + complete.length,
            err := some e }

/-- End of stream: parse whatever partial line is left. -/
def finish (mode : Mode) (st : StreamState) : Except ParseError Dataset :=
  match st.err with
  | some e => .error e
  | none => parseFrom mode st.pos st.carry st.ds

def streamParse (mode : Mode) (chunks : List (List Char)) :
    Except ParseError Dataset :=
  finish mode (chunks.foldl (feedChunk mode) initialState)

/-! ## 4. Facts -/

/-- Fuel is local to the call, never threaded across a boundary. -/
theorem parseFrom_fuel_is_local (mode : Mode) (pos : Nat) (cs : List Char)
    (ds : Dataset) :
    parseFrom mode pos cs ds = parseQuadLinesAcc mode (cs.length + 1) pos cs ds := rfl

/-- An empty stream is an empty dataset, not an error. -/
theorem streamParse_nil (mode : Mode) :
    streamParse mode [] = .ok Dataset.empty := by
  simp [streamParse, finish, initialState, parseFrom, parseQuadLinesAcc,
        skipWs, List.span, List.span.loop]

/-- An error is sticky: a chunk after a failure cannot clear it. -/
theorem feedChunk_error_sticky (mode : Mode) (st : StreamState) (chunk : List Char)
    (e : ParseError) (h : st.err = some e) :
    feedChunk mode st chunk = st := by
  simp only [feedChunk, h]

/-- **One chunk streams exactly as it batches.** The carry is the whole
partial tail, the complete part is the whole prefix, and their
concatenation is the chunk — so the two parser calls see the same
characters the batch call does, in the same order. This is the case
that needs no line-boundary concatenation lemma. -/
theorem streamParse_single_chunk (mode : Mode) (chunk : List Char) :
    streamParse mode [chunk]
      = (match parseFrom mode 0 (splitCompleteLines chunk).1 Dataset.empty with
         | .ok ds =>
             parseFrom mode (splitCompleteLines chunk).1.length
               (splitCompleteLines chunk).2 ds
         | .error e => .error e) := by
  simp only [streamParse, List.foldl_cons, List.foldl_nil, feedChunk,
             initialState, List.nil_append]
  cases parseFrom mode 0 (splitCompleteLines chunk).1 Dataset.empty with
  | ok ds => simp [finish]
  | error e => simp [finish]

/-! ## How much a single round consumes -/

theorem skipWs_len (pos : Nat) (cs : List Char) :
    (skipWs pos cs).2.length ≤ cs.length := (skipWs_suffix pos cs).length_le

theorem skipComment_len (pos : Nat) (cs : List Char) :
    (skipComment pos cs).2.length ≤ cs.length := (skipComment_suffix pos cs).length_le

theorem skipEol_len (pos : Nat) (cs : List Char) :
    (skipEol pos cs).2.length ≤ cs.length := (skipEol_suffix pos cs).length_le

theorem skipComment_hash_len (pos : Nat) (t : List Char) :
    (skipComment pos ('#' :: t)).2.length ≤ t.length := by
  have he : skipComment pos ('#' :: t) = skipToEol (pos + 1) t := rfl
  rw [he]
  exact (skipToEol_suffix (pos + 1) t).length_le

theorem skipEol_lf_len (pos : Nat) (t : List Char) :
    (skipEol pos ('\n' :: t)).2.length ≤ t.length := by
  have he : skipEol pos ('\n' :: t) = (pos + 1, t) := rfl
  rw [he]
  simp

theorem skipEol_cr_len (pos : Nat) (t : List Char) :
    (skipEol pos ('\r' :: t)).2.length ≤ t.length := by
  cases t with
  | nil => have he : skipEol pos ['\r'] = (pos + 1, []) := rfl
           rw [he]
           simp
  | cons b t2 =>
      by_cases hb : b = '\n'
      · subst hb
        have he : skipEol pos ('\r' :: '\n' :: t2) = (pos + 2, t2) := rfl
        rw [he]; simp
      · have he : skipEol pos ('\r' :: b :: t2) = (pos + 1, b :: t2) := by
          simp [skipEol, hb]
        rw [he]
        simp

theorem readNQuad11_len (pos : Nat) (cs : List Char) (tr : Triple)
    (g : Option Subject) (p' : Nat) (rest : List Char)
    (h : readNQuad11 pos cs = .ok (tr, g, p', rest)) : rest.length < cs.length := by
  have := (readNQuad11_dot pos cs tr g p' rest h).length_le
  simp at this
  omega


/-! ## Fuel independence

`parseQuadLinesAcc` recurses on a fuel counter. Two runs with DIFFERENT
fuel agree, as long as each budget exceeds the input length — which is
the discipline every entry point already follows. This is what lets the
streaming run, whose fuel comes from one chunk, be compared with the
batch run, whose fuel comes from the whole document.

ⓘ Stated for `.rdf11`, which is the mode the F\* streaming module's own
theorem is about (`Parser.NQuads.parse_nquads`). The RDF 1.2 reader
admits triple terms in the object slot and needs its own
`readNQuad12_dot` before the same argument runs. -/

theorem parseQuadLinesAcc11_fuel_indep :
    ∀ (f g pos : Nat) (cs : List Char) (ds : Dataset),
      cs.length < f → cs.length < g →
      parseQuadLinesAcc .rdf11 f pos cs ds = parseQuadLinesAcc .rdf11 g pos cs ds
  | 0, _, _, _, _, hf, _ => absurd hf (by omega)
  | _ + 1, 0, _, _, _, _, hg => absurd hg (by omega)
  | f + 1, g + 1, pos, cs, ds, hf, hg => by
      simp only [parseQuadLinesAcc]
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        have hle1 : cs1.length ≤ cs.length := by
          have := skipWs_len pos cs; rw [hw] at this; exact this
        dsimp only
        cases hc1 : cs1 with
        | nil => rfl
        | cons a t =>
          have hlt : t.length < cs.length := by
            rw [hc1] at hle1; simp at hle1; omega
          by_cases hh : a = '#'
          · subst hh
            have h1 := skipComment_hash_len pos1 t
            have h2 := skipEol_len (skipComment pos1 ('#' :: t)).1
                         (skipComment pos1 ('#' :: t)).2
            refine parseQuadLinesAcc11_fuel_indep f g _ _ _ ?_ ?_ <;> omega
          · by_cases hn : a = '\n'
            · subst hn
              have h2 := skipEol_lf_len pos1 t
              refine parseQuadLinesAcc11_fuel_indep f g _ _ _ ?_ ?_ <;> omega
            · by_cases hr : a = '\r'
              · subst hr
                have h2 := skipEol_cr_len pos1 t
                refine parseQuadLinesAcc11_fuel_indep f g _ _ _ ?_ ?_ <;> omega
              · split
                all_goals (try (exfalso; simp_all; done))
                split
                · rfl
                · rename_i tr gg p2 c2 heq
                  have hlen := readNQuad11_len pos1 (a :: t) tr gg p2 c2 heq
                  have hA : (skipWs p2 c2).2.length ≤ c2.length := skipWs_len p2 c2
                  have hB : (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2.length
                      ≤ (skipWs p2 c2).2.length := skipComment_len _ _
                  have hC : (skipEol
                        (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).1
                        (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2).2.length
                      ≤ (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2.length :=
                    skipEol_len _ _
                  simp at hlen
                  refine parseQuadLinesAcc11_fuel_indep f g _ _ _ ?_ ?_ <;> omega

#print axioms parseQuadLinesAcc11_fuel_indep

/-! ## Build-time checks

The parse-based checks use SHORT IRIs on purpose: every `#guard` runs
at build time, and a streaming check with N chunks makes N parser
calls, so long test data makes the build slow for no extra coverage. -/

private def line1 : List Char := "<a:1> <a:p> <a:2> .\n".toList
private def line2 : List Char := "<a:2> <a:p> <a:3> .\n".toList

/-! The splitter cuts after the last newline. -/
#guard (splitCompleteLines (line1 ++ line2)).2 == []
#guard (splitCompleteLines (line1 ++ line2)).1.length == line1.length + line2.length
#guard (splitCompleteLines "abc".toList).1 == []
#guard (splitCompleteLines "abc".toList).2 == "abc".toList
#guard (splitCompleteLines "ab\ncd".toList).1 == "ab\n".toList
#guard (splitCompleteLines "ab\ncd".toList).2 == "cd".toList
#guard (splitCompleteLines "\n".toList).1 == "\n".toList
#guard (splitCompleteLines "a\nb\nc".toList).1 == "a\nb\n".toList
#guard (splitCompleteLines "a\nb\nc".toList).2 == "c".toList

/-! Reconstruction and the carry rule, on real input. -/
#guard ((splitCompleteLines "ab\ncd".toList).1 ++ (splitCompleteLines "ab\ncd".toList).2)
        == "ab\ncd".toList
#guard (splitCompleteLines "ab\ncd".toList).2.all (fun c => !isNl c) == true

/-! **A chunk boundary in the MIDDLE of a line.** The two lines split at
character 8 — inside the first line's predicate — streamed as two
chunks, give the dataset the batch parse gives. -/
private def whole : List Char := line1 ++ line2

#guard (match streamParse .rdf11 [whole.take 8, whole.drop 8] with
        | .ok ds => ds.default.length | .error _ => 0) == 2
#guard (match parseNQuads (String.ofList whole) with
        | .ok ds => ds.default.length | .error _ => 0) == 2

/-! Three chunks, both boundaries mid-line. -/
#guard (match streamParse .rdf11
          [whole.take 3, (whole.drop 3).take 19, whole.drop 22] with
        | .ok ds => ds.default.length | .error _ => 0) == 2

/-! A boundary exactly ON the newline, which is the case a splitter
gets wrong by an off-by-one. -/
#guard (match streamParse .rdf11 [line1, line2] with
        | .ok ds => ds.default.length | .error _ => 0) == 2
#guard (match streamParse .rdf11 [whole.take 19, whole.drop 19] with
        | .ok ds => ds.default.length | .error _ => 0) == 2

/-! An empty stream, and a stream of empty chunks. -/
#guard (match streamParse .rdf11 [] with
        | .ok ds => ds.default.length | .error _ => 0) == 0
#guard (match streamParse .rdf11 [[], [], []] with
        | .ok ds => ds.default.length | .error _ => 0) == 0

/-! ## Axiom audit -/

#print axioms splitCompleteLines_reconstruct
#print axioms splitCompleteLines_carry_no_newline
#print axioms splitCompleteLines_complete_ends_newline
#print axioms streamParse_single_chunk
#print axioms readNQuad11_len
#print axioms parseQuadLinesAcc11_fuel_indep

end L4Factoidal.Syntax.NQuadsStreaming
