/-
Wasm.Ops.Block — narrow, stateless IBK2/IBK3 block-worker operations.

This module deliberately does NOT parse a SPARQL query.  A coordinator lowers
its predicate-bound triple-pattern fragment to one of these operations; the
operation then invokes the canonical block decoder and scan implementation.
That keeps one meaning for physical predicate scans across native and WASM
builds.

The dispatch ABI currently carries strings, so `scanIBK2Predicate` accepts
lower- or upper-case hexadecimal IBK2 bytes.  Hex is a portable diagnostic
transport, not the eventual high-throughput host boundary: a PG/TiKV/WASM
worker should pass validated byte buffers directly once its buffer ABI exists.

  scanIBK2Predicate(ibk2Hex, predicateIri)
    -> {"ok":true,"rows":N,"ntriples":"…"}
     | {"ok":false,"error":"…"}

  scanIBK3Predicate(ibk3Hex, predicateIri, blankNodeScope)
    -> {"ok":true,"format":"IBK3","blankNodeScope":"…",
        "rows":N,"ntriples":"…"}
     | {"ok":false,"error":"…"}

The IBK3 operation consumes one complete predicate-local artifact.  It checks
the enclosing CRC, PTD1 dictionary, source-position sequence, term references,
and predicate locality before scanning.  `blankNodeScope` names the RDF source
or dataset import unit whose blank-node labels the block retains.  Every block
partitioned from that unit must use the same non-empty scope; unrelated source
units must use different scopes.  This preserves a blank node split across
predicate blocks without coalescing equal document-local labels from unrelated
inputs when result fragments are composed.

SBM/Merkle verification, sidecar selection, deltas, and range transport remain
host responsibilities; this stateless diagnostic ABI does not claim them.
-/
import Wasm.Ops.Support
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.IndexedBlockWireV3
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

private def bytesOfHexCharsGo? : List Char → List UInt8 → Option (List UInt8)
  | [], reversed => some reversed.reverse
  | [_], _ => none
  | hi :: lo :: rest, reversed => do
      let h ← hexDigitValue? hi
      let l ← hexDigitValue? lo
      bytesOfHexCharsGo? rest (UInt8.ofNat (h * 16 + l) :: reversed)

private def bytesOfHexChars? (chars : List Char) : Option (List UInt8) :=
  bytesOfHexCharsGo? chars []

private def bytesOfHex? (s : String) : Option ByteArray :=
  (bytesOfHexChars? s.toList).map fun bytes => ByteArray.mk bytes.toArray

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

private def hexOfBytes (bytes : ByteArray) : String :=
  let reversed := bytes.data.toList.foldl (fun out byte =>
    hexChar (byte.toNat % 16) :: hexChar (byte.toNat / 16) :: out) []
  String.ofList reversed.reverse

/-- A grammar-safe, injective encoding of the caller's blank-node scope.
`s` supplies a legal leading character, hexadecimal UTF-8 avoids treating
caller punctuation as N-Triples syntax, and `_` separates it from the original
label. -/
private def blankNodePrefix (scope : String) : String :=
  "s" ++ hexOfBytes scope.toUTF8 ++ "_"

private def maxBlankNodeScopeBytes : Nat := 256

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

/-- Evaluate one predicate-bound triple-pattern fragment over a complete
canonical IBK3 artifact. The caller supplies the source/dataset blank-node
scope used for every block from the same RDF import unit. -/
def scanIBK3Predicate (ibk3Hex predicateText blankNodeScope : String) : String :=
  if blankNodeScope.isEmpty then
    errJson "scanIBK3Predicate: blankNodeScope must be non-empty"
  else if blankNodeScope.toUTF8.size > maxBlankNodeScopeBytes then
    errJson s!"scanIBK3Predicate: blankNodeScope exceeds {maxBlankNodeScopeBytes} UTF-8 bytes"
  else match bytesOfHex? ibk3Hex with
  | none => errJson "scanIBK3Predicate: ibk3Hex must contain an even number of hexadecimal digits"
  | some bytes =>
    match L4Factoidal.Storage.IndexedBlockWireV3.decode bytes with
    | none => errJson "scanIBK3Predicate: invalid or corrupt canonical IBK3 artifact"
    | some block =>
      match mkIri 0 predicateText with
      | .error e => errJson s!"scanIBK3Predicate: {fmtParseError e}"
      | .ok predicate =>
        let triples := Graph.prefixBnodes (blankNodePrefix blankNodeScope)
          (L4Factoidal.Storage.IndexedBlock.scanBound { p := some predicate } block)
        match Graph.toNTriples triples with
        | .error e => errJson s!"scanIBK3Predicate: N-Triples serialisation: {e}"
        | .ok ntriples => okWith [ ("format", .string "IBK3")
                                  , ("blankNodeScope", .string blankNodeScope)
                                  , ("rows", .number (toString triples.length))
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
private def testBytesV3 : ByteArray :=
  (L4Factoidal.Storage.IndexedBlockWireV3.encode? testBlock).getD ByteArray.empty
private def testBnodeBlock : L4Factoidal.Storage.IndexedBlock.Block :=
  L4Factoidal.Storage.IndexedBlock.fromGraph
    [{ s := .bnode "x", p := testPredicate, o := .bnode "x" }]
private def testBnodeBytesV3 : ByteArray :=
  (L4Factoidal.Storage.IndexedBlockWireV3.encode? testBnodeBlock).getD ByteArray.empty

#guard (scanIBK2Predicate (hexOfBytes testBytes) testPredicate.val).contains "\"rows\":1"
#guard (scanIBK2Predicate (hexOfBytes testBytes) testPredicate.val).contains "<http://example.org/s>"
#guard (scanIBK2Predicate "00" testPredicate.val).contains "invalid or corrupt canonical IBK2 artifact"
#guard (scanIBK2Predicate (hexOfBytes testBytes) "not-an-iri").contains "invalid IRI"
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) testPredicate.val "source-a").contains "\"format\":\"IBK3\""
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) testPredicate.val "source-a").contains "\"rows\":1"
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) testPredicate.val "source-a").contains "<http://example.org/s>"
#guard (scanIBK3Predicate "00" testPredicate.val "source-a").contains "invalid or corrupt canonical IBK3 artifact"
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) "not-an-iri" "source-a").contains "invalid IRI"
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) testPredicate.val "").contains "blankNodeScope must be non-empty"
#guard (scanIBK3Predicate (hexOfBytes testBytesV3) testPredicate.val
  (String.ofList (List.replicate 257 'x'))).contains "blankNodeScope exceeds 256 UTF-8 bytes"
#guard (scanIBK3Predicate (hexOfBytes testBnodeBytesV3) testPredicate.val "a").contains "_:s61_x"
#guard !(scanIBK3Predicate (hexOfBytes testBnodeBytesV3) testPredicate.val "b").contains "_:s61_x"

end L4Wasm.Ops
