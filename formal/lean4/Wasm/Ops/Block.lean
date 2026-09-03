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

  queryIBK3BlockSetPreview(blocksJson, blankNodeScope, sparql)
    -> the ordinary queryDataset SELECT / ASK / CONSTRUCT envelope

`blocksJson` is an array of `[predicateIri, ibk3Hex]` pairs.  The block-set
operation is a bounded browser-preview bridge: at most eight complete blocks,
eight MiB of decoded artifact bytes and 100,000 RDF rows.  SELECT and
CONSTRUCT must carry `LIMIT <= 1000`.  It avoids the large intermediate
N-Triples serialization/reparse of composing `scanIBK3Predicate` results, but
is not the future authenticated-range/PushIR worker API.

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
import Wasm.Ops.Query
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Syntax.NTriples

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- A grammar-safe, injective encoding of the caller's blank-node scope.
`s` supplies a legal leading character, hexadecimal UTF-8 avoids treating
caller punctuation as N-Triples syntax, and `_` separates it from the original
label. -/
private def blankNodePrefix (scope : String) : String :=
  "s" ++ hexOfBytes scope.toUTF8 ++ "_"

private def maxBlankNodeScopeBytes : Nat := 256

private def maxBlockSetArtifacts : Nat := 8
private def maxBlockSetBytes : Nat := 8 * 1024 * 1024
private def maxBlockSetRows : Nat := 100000
private def maxBlockSetResults : Nat := 1000

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

/-- Decode one `[predicateIri, ibk3Hex]` entry within the remaining byte and
row budgets.  Both budgets are checked BEFORE the expensive work they bound:
the byte budget against the hexadecimal length before any decoding, and the
row budget against the 13-byte IBK3 header before the full CRC/dictionary/row
admission.  An oversized artifact is refused without being decoded. -/
private def decodeBlockSetEntry (blankNodeScope : String) (bytesBudget rowsBudget : Nat)
    (item : Json) : Except String (Nat × Graph) :=
  match item with
  | .array [.string predicateText, .string ibk3Hex] => do
      if ibk3Hex.length / 2 > bytesBudget then
        throw s!"queryIBK3BlockSetPreview: decoded artifacts exceed {maxBlockSetBytes} bytes"
      let bytes ← match bytesOfHex? ibk3Hex with
        | none => throw "queryIBK3BlockSetPreview: every block must contain even-length hexadecimal bytes"
        | some value => pure value
      let header ← match L4Factoidal.Storage.IndexedBlockWireV3.decodePrefix
          (bytes.extract 0 L4Factoidal.Storage.IndexedBlockWireV3.prefixBytes) with
        | none => throw "queryIBK3BlockSetPreview: invalid IBK3 header"
        | some value => pure value
      if header.rowCount > rowsBudget then
        throw s!"queryIBK3BlockSetPreview: block set exceeds {maxBlockSetRows} RDF rows"
      let block ← match L4Factoidal.Storage.IndexedBlockWireV3.decode bytes with
        | none => throw "queryIBK3BlockSetPreview: invalid or corrupt canonical IBK3 artifact"
        | some value => pure value
      let predicate ← match mkIri 0 predicateText with
        | .error e => throw s!"queryIBK3BlockSetPreview: {fmtParseError e}"
        | .ok iri => pure iri
      let triples := L4Factoidal.Storage.IndexedBlock.scanBound { p := some predicate } block
      if triples.length != block.rows.size then
        throw "queryIBK3BlockSetPreview: declared predicate does not identify every block row"
      pure (bytes.size, Graph.prefixBnodes (blankNodePrefix blankNodeScope) triples)
  | _ => throw "queryIBK3BlockSetPreview: blocksJson entries must be [predicateIri, ibk3Hex]"

private def decodeBlockSetEntries (blankNodeScope : String) :
    List Json → Nat → Nat → Graph → Except String (Graph × Nat × Nat)
  | [], totalBytes, totalRows, reversed =>
      pure (reversed.reverse, totalBytes, totalRows)
  | item :: rest, totalBytes, totalRows, reversed => do
      let (artifactBytes, triples) ← decodeBlockSetEntry blankNodeScope
        (maxBlockSetBytes - totalBytes) (maxBlockSetRows - totalRows) item
      let nextBytes := totalBytes + artifactBytes
      let nextRows := totalRows + triples.length
      if nextBytes > maxBlockSetBytes then
        throw s!"queryIBK3BlockSetPreview: decoded artifacts exceed {maxBlockSetBytes} bytes"
      if nextRows > maxBlockSetRows then
        throw s!"queryIBK3BlockSetPreview: block set exceeds {maxBlockSetRows} RDF rows"
      let nextReversed := triples.foldl (fun out triple => triple :: out) reversed
      decodeBlockSetEntries blankNodeScope rest nextBytes nextRows nextReversed

private def decodeBlockSet (blocksJson blankNodeScope : String) :
    Except String (Graph × Nat × Nat) := do
  let json ← match parseJson blocksJson with
    | .error e => throw s!"queryIBK3BlockSetPreview: blocksJson parse error: {e}"
    | .ok value => pure value
  match json with
  | .array [] => throw "queryIBK3BlockSetPreview: at least one block is required"
  | .array items =>
      if items.length > maxBlockSetArtifacts then
        throw s!"queryIBK3BlockSetPreview: at most {maxBlockSetArtifacts} blocks are accepted"
      else decodeBlockSetEntries blankNodeScope items 0 0 []
  | _ => throw "queryIBK3BlockSetPreview: blocksJson must be an array"

private def boundedQueryReason? (query : Query) : Option String :=
  if !query.dataset.isEmpty then
    some "FROM/FROM NAMED dataset clauses are outside this explicit block set"
  else if query.groupBy.isSome || !query.having.isEmpty || query.postValues.isSome then
    some "GROUP BY, HAVING and trailing VALUES are outside this preview operation"
  else match query.pattern with
  | .bgp patterns =>
      if patterns.length > 4 then some "at most four basic triple patterns are accepted"
      else match query.form with
      | .ask => none
      | .select _ | .construct _ =>
          match query.modifier.limit with
          | some limit =>
              if limit <= maxBlockSetResults then none
              else some s!"LIMIT must be at most {maxBlockSetResults}"
          | none => some s!"SELECT and CONSTRUCT require LIMIT <= {maxBlockSetResults}"
      | .describe _ => some "DESCRIBE is not supported"
  | _ => some "only a basic graph pattern is accepted by this preview operation"

/-- Query a small explicit set of complete IBK3 blocks without materializing
their N-Triples across the WASM/JavaScript boundary. This is deliberately a
local browser-preview operation, not the authenticated remote-worker ABI. -/
def queryIBK3BlockSetPreview (blocksJson blankNodeScope sparql : String) : String :=
  if blankNodeScope.isEmpty then
    errJson "queryIBK3BlockSetPreview: blankNodeScope must be non-empty"
  else if blankNodeScope.toUTF8.size > maxBlankNodeScopeBytes then
    errJson s!"queryIBK3BlockSetPreview: blankNodeScope exceeds {maxBlankNodeScopeBytes} UTF-8 bytes"
  else match parseSparql sparql with
  | .error e => errJson s!"SPARQL parse error: {fmtParseError e}"
  | .ok query =>
      match boundedQueryReason? query with
      | some reason => errJson s!"queryIBK3BlockSetPreview: {reason}"
      | none =>
          match decodeBlockSet blocksJson blankNodeScope with
          | .error e => errJson e
          | .ok (graph, _, _) => queryParsedDataset { default := graph, named := [] } sparql

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
private def testBlockSetJson : String :=
  (Json.array [Json.array [.string testPredicate.val, .string (hexOfBytes testBytesV3)]]).toString

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
#guard (queryIBK3BlockSetPreview testBlockSetJson "source-a"
  "SELECT ?s WHERE { ?s <http://example.org/p> <http://example.org/o> } LIMIT 1").contains
    "http://example.org/s"
#guard (queryIBK3BlockSetPreview testBlockSetJson "source-a"
  "SELECT ?s WHERE { ?s <http://example.org/p> <http://example.org/o> }").contains
    "SELECT and CONSTRUCT require LIMIT"

end L4Wasm.Ops
