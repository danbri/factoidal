/-
Wasm.Ops.Block — narrow, stateless IBK2 block-worker operations.

This module deliberately does NOT parse a SPARQL query.  A coordinator lowers
its predicate-bound triple-pattern fragment to this operation; the operation
then invokes the existing canonical IBK2 selective-scan implementation.  That
keeps one meaning for physical predicate scans across native and WASM builds.

The dispatch ABI currently carries strings, so `scanIBK2Predicate` accepts
lower- or upper-case hexadecimal IBK2 bytes.  Hex is a portable diagnostic
transport, not the eventual high-throughput host boundary: a PG/TiKV/WASM
worker should pass validated byte buffers directly once its buffer ABI exists.

  scanIBK2Predicate(ibk2Hex, predicateIri)
    -> {"ok":true,"rows":N,"ntriples":"…"}
     | {"ok":false,"error":"…"}
-/
import Wasm.Ops.Support
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Syntax.NTriples

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Syntax
open L4Factoidal.JSON

private def hexDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n && n ≤ 0x46 then some (n - 0x41 + 10)
  else none

private def bytesOfHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
      let h ← hexDigitValue? hi
      let l ← hexDigitValue? lo
      let tail ← bytesOfHexChars? rest
      some (UInt8.ofNat (h * 16 + l) :: tail)

private def bytesOfHex? (s : String) : Option ByteArray :=
  (bytesOfHexChars? s.toList).map fun bytes => ByteArray.mk bytes.toArray

/-- Evaluate one predicate-bound triple-pattern fragment over canonical IBK2
bytes.  `scanPredicateDecoded` checks IBK2 framing, CRC, dictionary, directory
and the selected predicate segment before returning RDF triples. -/
def scanIBK2Predicate (ibk2Hex predicateText : String) : String :=
  match bytesOfHex? ibk2Hex with
  | none => errJson "scanIBK2Predicate: ibk2Hex must contain an even number of hexadecimal digits"
  | some bytes =>
    match open? bytes with
    | none => errJson "scanIBK2Predicate: invalid or corrupt canonical IBK2 artifact"
    | some opened =>
      match mkIri 0 predicateText with
      | .error e => errJson s!"scanIBK2Predicate: {fmtParseError e}"
      | .ok predicate =>
        let triples := scanBoundRange { p := some predicate } opened
        match Graph.toNTriples triples with
        | .error e => errJson s!"scanIBK2Predicate: N-Triples serialisation: {e}"
        | .ok ntriples => okWith [ ("rows", .number (toString triples.length))
                                  , ("ntriples", .string ntriples) ]

/-! ## Executable ABI pins

These are deliberately at the worker boundary, rather than merely testing
`IndexedBlockWireV2`: they pin hex decoding, artifact integrity rejection,
predicate validation and JSON envelope formation together. -/

private def testPredicate : WfIri := ⟨"http://example.org/p", by decide⟩
private def testSubject : Subject := .iri ⟨"http://example.org/s", by decide⟩
private def testObject : Term := .iri ⟨"http://example.org/o", by decide⟩
private def testBlock : L4Factoidal.Storage.IndexedBlock.Block :=
  L4Factoidal.Storage.IndexedBlock.fromGraph [{ s := testSubject, p := testPredicate, o := testObject }]
private def testBytes : ByteArray := (encode? testBlock).getD ByteArray.empty

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

private def hexOfBytes (bytes : ByteArray) : String :=
  bytes.data.toList.foldl (fun out byte =>
    out ++ String.ofList [hexChar (byte.toNat / 16), hexChar (byte.toNat % 16)]) ""

#guard (scanIBK2Predicate (hexOfBytes testBytes) testPredicate.val).contains "\"rows\":1"
#guard (scanIBK2Predicate (hexOfBytes testBytes) testPredicate.val).contains "<http://example.org/s>"
#guard (scanIBK2Predicate "00" testPredicate.val).contains "invalid or corrupt canonical IBK2 artifact"
#guard (scanIBK2Predicate (hexOfBytes testBytes) "not-an-iri").contains "invalid IRI"

end L4Wasm.Ops
