/- Versioned logical manifest for a Shardborough collection of independently
   decodable block artifacts.  This is deliberately separate from host I/O. -/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.IndexedBlockWireV2

namespace L4Factoidal.Storage.ShardManifest

open L4Factoidal.RDF

/-- `'SBM0'` in little-endian form: Shardborough Manifest, layout zero. -/
def magic : UInt32 := 0x304D4253
def wireVersion : UInt8 := 0

private def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
private def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

/-- Length-prefixed UTF-8.  Lengths in this first portable format are u32
    byte counts, never Lean character counts. -/
private def encodeString (s : String) : List UInt8 :=
  let bytes := s.toUTF8.toList
  writeU32LE (UInt32.ofNat bytes.length) ++ bytes

private def decodeString (bytes : List UInt8) : Option (String × List UInt8) := do
  let length ← readU32LE bytes 0
  let body := (bytes.drop 4).take length.toNat
  if body.length != length.toNat then none
  else do
    let value ← String.fromUTF8? ⟨body.toArray⟩
    some (value, (bytes.drop 4).drop length.toNat)

private def takeExact (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  let value := bytes.take n
  if value.length == n then some (value, bytes.drop n) else none

/-- A relative artifact key.  Host integrations decide whether this denotes a
    file, `bytea`, TiKV value, OPFS entry, or mapped byte range. -/
structure ArtifactKey where
  value : String
  deriving DecidableEq

/-- Identity and required byte extent of one immutable local block. -/
structure ArtifactRef where
  key : ArtifactKey
  bytes : Nat
  sha256 : ByteArray
  deriving DecidableEq

/-- The first Shardborough layout names one predicate-local IBK2 block.
    Later layouts retain the same artifact identity fields while adding graph,
    evidence and sort-order columns. -/
structure Entry where
  predicate : WfIri
  artifact : ArtifactRef
  rows : Nat
  ordinal : Nat
  deriving DecidableEq

/-- Metadata that makes a derived collection reproducible rather than an
    anonymous cache. -/
structure Manifest where
  version : Nat
  sourceIdentity : ByteArray
  termRegistryVersion : String
  layout : String
  entries : List Entry
  deriving DecidableEq

def uniquePredicates : List Entry → Bool
  | [] => true
  | entry :: rest => !(rest.map Entry.predicate).contains entry.predicate && uniquePredicates rest

def contiguousOrdinals : List Entry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected => entry.ordinal == expected && contiguousOrdinals rest (expected + 1)

/-- Structural acceptance before any host artifact is opened. -/
def valid (manifest : Manifest) : Bool :=
  manifest.version == 0 && uniquePredicates manifest.entries &&
    contiguousOrdinals manifest.entries 0 &&
    manifest.entries.all fun entry => entry.artifact.bytes > 0 && entry.rows > 0 && entry.artifact.sha256.size == 32

/-- Predicate selection is total and deterministic; a missing key means no
    candidate artifact, never a fallback that could hide an index error. -/
def select? (manifest : Manifest) (predicate : WfIri) : Option Entry :=
  if valid manifest then manifest.entries.find? fun entry => entry.predicate == predicate else none

/-- The field widths in SBM0.  Oversized manifests are refused rather than
    being truncated into an ambiguous byte stream. -/
private def fitsU32 (n : Nat) : Bool := n < 4294967296

private def encodableEntry (entry : Entry) : Bool :=
  fitsU32 entry.predicate.val.toUTF8.size && fitsU32 entry.artifact.key.value.toUTF8.size &&
    fitsU32 entry.artifact.bytes && fitsU32 entry.rows && fitsU32 entry.ordinal &&
    entry.artifact.sha256.size == 32

private def encodable (manifest : Manifest) : Bool :=
  fitsU32 manifest.sourceIdentity.size && fitsU32 manifest.termRegistryVersion.toUTF8.size &&
    fitsU32 manifest.layout.toUTF8.size && fitsU32 manifest.entries.length &&
    manifest.entries.all encodableEntry

private def encodeEntry (entry : Entry) : List UInt8 :=
  encodeString entry.predicate.val ++ encodeString entry.artifact.key.value ++
    writeU32LE (UInt32.ofNat entry.artifact.bytes) ++ entry.artifact.sha256.toList ++
    writeU32LE (UInt32.ofNat entry.rows) ++ writeU32LE (UInt32.ofNat entry.ordinal)

/-- Canonical SBM0 bytes: fixed magic/version, source identity, two
    length-prefixed UTF-8 labels, then predicate-ordered local block entries.
    There is intentionally no host path semantics in this representation. -/
def encode? (manifest : Manifest) : Option ByteArray :=
  if valid manifest && encodable manifest then
    some <| byteArrayOfList <|
      writeU32LE magic ++ [wireVersion] ++
      writeU32LE (UInt32.ofNat manifest.sourceIdentity.size) ++ manifest.sourceIdentity.toList ++
      encodeString manifest.termRegistryVersion ++ encodeString manifest.layout ++
      writeU32LE (UInt32.ofNat manifest.entries.length) ++ manifest.entries.flatMap encodeEntry
  else none

private def decodeEntry (bytes : List UInt8) : Option (Entry × List UInt8) := do
  let (predicateText, afterPredicate) ← decodeString bytes
  let (keyText, afterKey) ← decodeString afterPredicate
  let artifactBytes ← readU32LE afterKey 0
  let (digest, afterDigest) ← takeExact 32 (afterKey.drop 4)
  let rows ← readU32LE afterDigest 0
  let ordinal ← readU32LE afterDigest 4
  if h : isIri predicateText then
    some
      ({ predicate := ⟨predicateText, h⟩
         artifact := { key := { value := keyText }, bytes := artifactBytes.toNat,
                       sha256 := byteArrayOfList digest }
         rows := rows.toNat
         ordinal := ordinal.toNat }, afterDigest.drop 8)
  else none

private def decodeEntries : Nat → List UInt8 → Option (List Entry × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (entry, afterEntry) ← decodeEntry bytes
      let (entries, rest) ← decodeEntries n afterEntry
      some (entry :: entries, rest)

/-- Strict SBM0 decoding.  A decoder refuses bad framing, unknown versions,
    invalid UTF-8/IRIs, trailing bytes and structurally invalid manifests. -/
def decode? (bytes : ByteArray) : Option Manifest := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
  if foundVersion != wireVersion then none else do
  let sourceLength ← readU32LE afterVersion 0
  let (sourceIdentity, afterSource) ← takeExact sourceLength.toNat (afterVersion.drop 4)
  let (termRegistryVersion, afterRegistry) ← decodeString afterSource
  let (layout, afterLayout) ← decodeString afterRegistry
  let entryCount ← readU32LE afterLayout 0
  let (entries, rest) ← decodeEntries entryCount.toNat (afterLayout.drop 4)
  let manifest := { version := foundVersion.toNat, sourceIdentity := byteArrayOfList sourceIdentity,
                    termRegistryVersion, layout, entries }
  if rest.isEmpty && valid manifest then some manifest else none

private def samplePredicate : WfIri := ⟨"https://example.test/p", by decide⟩
private def sampleDigest : ByteArray := ByteArray.mk (List.replicate 32 7 |>.toArray)
private def sampleManifest : Manifest :=
  { version := 0, sourceIdentity := ByteArray.mk #[1, 2, 3], termRegistryVersion := "terms-v0",
    layout := "predicate-ibk2-v0",
    entries := [{ predicate := samplePredicate,
                  artifact := { key := { value := "blocks/p.ibk2" }, bytes := 91,
                                sha256 := sampleDigest }, rows := 2, ordinal := 0 }] }

#guard decode? (encode? sampleManifest |>.getD ByteArray.empty) == some sampleManifest
#guard (decode? (ByteArray.mk #[83, 66, 77, 48, 1])).isNone

end L4Factoidal.Storage.ShardManifest
