/-
L4Factoidal.Syntax.Utf8Stream — bounded incremental UTF-8 decoding.

File-backed RDF ingestion receives byte chunks, while Turtle semantics operate
on Unicode characters. A UTF-8 code point may straddle two reads, so callers
must not apply `String.fromUTF8?` independently to each chunk. This module
retains at most the final three undecoded bytes (the longest possible proper
prefix of a four-byte UTF-8 sequence) and rejects invalid interior data.

It intentionally does not choose a Turtle statement boundary. That remains
the grammar-aware layer above it: line splitting is unsound for Turtle.
-/

namespace L4Factoidal.Syntax

/-- The undecoded suffix carried between byte reads. A successful `feed`
    leaves this empty unless the input ends in a partial UTF-8 sequence. -/
structure Utf8Stream where
  tail : ByteArray := ByteArray.empty

def Utf8Stream.init : Utf8Stream := {}

/-- UTF-8 continuation-byte predicate. -/
private def isContinuation (byte : UInt8) : Bool :=
  let n := byte.toNat
  0x80 ≤ n && n ≤ 0xbf

/-- Is the final `k` bytes a genuine proper prefix of one UTF-8 code point?
    This rejects e.g. `FF`: failure to decode alone is not evidence that a
    byte should be deferred to a later read. -/
private def isPartialCodepoint (suffix : ByteArray) : Bool :=
  match suffix.size with
  | 1 =>
      let a := suffix[0]!.toNat
      (0xc2 ≤ a && a ≤ 0xdf) || (0xe0 ≤ a && a ≤ 0xef) || (0xf0 ≤ a && a ≤ 0xf4)
  | 2 =>
      let a := suffix[0]!.toNat
      ((0xe0 ≤ a && a ≤ 0xef) || (0xf0 ≤ a && a ≤ 0xf4)) && isContinuation suffix[1]!
  | 3 =>
      let a := suffix[0]!.toNat
      0xf0 ≤ a && a ≤ 0xf4 && isContinuation suffix[1]! && isContinuation suffix[2]!
  | _ => false

/-- Try to decode `data`, allowing only a short suffix to be deferred to the
    next chunk. -/
private def decodeWithTail? (data : ByteArray) : Option (String × ByteArray) :=
  match String.fromUTF8? data with
  | some text => some (text, ByteArray.empty)
  | none =>
      let n := data.size
      let trySuffix (k : Nat) : Option (String × ByteArray) :=
        if k > n then none
        else let suffix := data.extract (n - k) n
        if !isPartialCodepoint suffix then none
        else match String.fromUTF8? (data.extract 0 (n - k)) with
        | none => none
        | some text => some (text, suffix)
      match trySuffix 1 with
      | some result => some result
      | none => match trySuffix 2 with
      | some result => some result
      | none => trySuffix 3

/-- Decode one file/network byte chunk. The result text is the maximal valid
    UTF-8 prefix and the next state contains only a possible split code point.
    An invalid byte sequence away from the final three bytes is rejected. -/
def Utf8Stream.feed (stream : Utf8Stream) (chunk : ByteArray) : Except String (String × Utf8Stream) :=
  match decodeWithTail? (stream.tail ++ chunk) with
  | none => .error "invalid UTF-8 byte sequence"
  | some (text, tail) => .ok (text, { tail })

/-- Finish a stream. A pending suffix is an incomplete UTF-8 sequence, not a
    silently dropped character. -/
def Utf8Stream.finish (stream : Utf8Stream) : Except String Unit :=
  if stream.tail.isEmpty then .ok () else .error "incomplete UTF-8 sequence at end of stream"

end L4Factoidal.Syntax
