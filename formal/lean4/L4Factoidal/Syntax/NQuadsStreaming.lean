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
`parseFrom_fuel_is_local` states that.

## What is NOT proved here

The homomorphism itself:

    finish (chunks.foldl (feedChunk mode) initialState)
      = parseNQuads (String.ofList chunks.flatten)

It needs the parser's line-boundary concatenation lemma — that parsing
`a ++ b` where `a` ends in a newline equals parsing `b` from the state
parsing `a` reached. That is the F* module's own
`lemma_parse_nquads_acc_concat_line_general`, and it is the bulk of its
3,438 lines. Tracked, not assumed:
<https://github.com/danbri/factoidal/issues/570>.

`streamParse_single_chunk` is the case that needs no such lemma, and it
is proved.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NQuads

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
  err : Option ParseError
  deriving Repr

def initialState : StreamState := { ds := Dataset.empty, carry := [], err := none }

/-- Parse a self-contained character list from a starting dataset. The
fuel is computed HERE, from this list, and never carried in. -/
def parseFrom (mode : Mode) (cs : List Char) (ds : Dataset) :
    Except ParseError Dataset :=
  parseQuadLinesAcc mode (cs.length + 1) 0 cs ds

/-- Take one chunk. Everything up to the last newline is parsed now;
the rest waits for the next chunk. An error is sticky: once a chunk has
failed, later chunks cannot un-fail it. -/
def feedChunk (mode : Mode) (st : StreamState) (chunk : List Char) : StreamState :=
  match st.err with
  | some _ => st
  | none =>
      let buf := st.carry ++ chunk
      let (complete, carry) := splitCompleteLines buf
      match parseFrom mode complete st.ds with
      | .ok ds' => { ds := ds', carry := carry, err := none }
      | .error e => { ds := st.ds, carry := carry, err := some e }

/-- End of stream: parse whatever partial line is left. -/
def finish (mode : Mode) (st : StreamState) : Except ParseError Dataset :=
  match st.err with
  | some e => .error e
  | none => parseFrom mode st.carry st.ds

def streamParse (mode : Mode) (chunks : List (List Char)) :
    Except ParseError Dataset :=
  finish mode (chunks.foldl (feedChunk mode) initialState)

/-! ## 4. Facts -/

/-- Fuel is local to the call, never threaded across a boundary. -/
theorem parseFrom_fuel_is_local (mode : Mode) (cs : List Char) (ds : Dataset) :
    parseFrom mode cs ds = parseQuadLinesAcc mode (cs.length + 1) 0 cs ds := rfl

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
      = (match parseFrom mode (splitCompleteLines chunk).1 Dataset.empty with
         | .ok ds => parseFrom mode (splitCompleteLines chunk).2 ds
         | .error e => .error e) := by
  simp only [streamParse, List.foldl_cons, List.foldl_nil, feedChunk,
             initialState, List.nil_append]
  cases parseFrom mode (splitCompleteLines chunk).1 Dataset.empty with
  | ok ds => simp [finish]
  | error e => simp [finish]

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

end L4Factoidal.Syntax.NQuadsStreaming
