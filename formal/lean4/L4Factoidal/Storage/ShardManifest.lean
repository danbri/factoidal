/- Versioned logical manifest for a Shardborough collection of independently
   decodable block artifacts.  This is deliberately separate from host I/O. -/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.BlockArtifact
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.Storage.ShardManifest

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend

/-- `'SBM0'` in little-endian form: Shardborough Manifest, layout zero. -/
def magic : UInt32 := 0x304D4253
def wireVersion0 : UInt8 := 0
def wireVersion1 : UInt8 := 1
def wireVersion2 : UInt8 := 2
def wireVersion3 : UInt8 := 3
def wireVersion4 : UInt8 := 4
def wireVersion5 : UInt8 := 5
def wireVersion6 : UInt8 := 6
def wireVersion7 : UInt8 := 7
def wireVersion8 : UInt8 := 8

def byteArrayOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray
def listOfByteArray (bs : ByteArray) : List UInt8 := bs.data.toList

/-- Length-prefixed UTF-8.  Lengths in this first portable format are u32
    byte counts, never Lean character counts. -/
def encodeString (s : String) : List UInt8 :=
  let bytes := s.toUTF8.toList
  writeU32LE (UInt32.ofNat bytes.length) ++ bytes

def decodeString (bytes : List UInt8) : Option (String × List UInt8) := do
  let length ← readU32LE bytes 0
  let body := (bytes.drop 4).take length.toNat
  if body.length != length.toNat then none
  else do
    let value ← String.fromUTF8? ⟨body.toArray⟩
    some (value, (bytes.drop 4).drop length.toNat)

def takeExact (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
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
  /-- Present and mandatory for SBM1. SBM0 deliberately has no range-proof
      claim, so this remains absent in its byte-compatible layout. -/
  chunked : Option ChunkedArtifact.Ref := none
  deriving DecidableEq

/-- The primary block codec of one entry's artifact.

    SBM0 through SBM6 have no such field: their manifest-level `layout` label
    fixes one codec for every entry of the generation (`predicate-ibk2-*` is
    IBK2, `predicate-ibk3-*` is IBK3). SBM7 keeps that label — it still names
    the generation's physical family and its sidecar contract — and adds this
    per-entry kind, which names the block codec of THIS artifact. The two are
    checked against each other in `valid`: under the `quad-ibk4-ptd1-merkle-v0`
    label every entry must be `ibk4`. The `ibk3` constructor exists in the type
    and on the wire so that the mixed generation of option C in
    `docs/designissues/2026-09-02-quad-aware-block-layout.md` is a widening of
    SBM7 ADMISSION rather than a new wire version; it is not admitted today. -/
inductive BlockLayout where
  | ibk3
  | ibk4
  deriving DecidableEq

/-- One member of an entry's graph-set summary: the default graph, or the IRI
    or blank-node label naming a graph.

    This is the manifest's copy of the IBK4 header graph-set summary, resolved
    through that block's own dictionary. The header stores block-local term
    IDs, so the header alone cannot answer `GRAPH <iri>`: resolving an ID needs
    a PTD1 page. Storing the NAMES here is what lets the planner select entries
    for `GRAPH <iri> { ... }` from the manifest alone, and it is why a count
    plus a default-graph flag was not enough. `graphSet` order is the block's
    first-occurrence row order, so the manifest summary and the block header
    summary are compared position by position. -/
inductive GraphName where
  | defaultGraph
  | iri (value : WfIri)
  | bnode (label : String)
  deriving DecidableEq

/-- The manifest name of a decoded IBK4 graph column value. `none` is the
    default graph; a named graph is an IRI or a blank node (`GraphRef`). -/
def GraphName.ofGraphRef : Option Subject → GraphName
  | none => .defaultGraph
  | some (.iri value) => .iri value
  | some (.bnode label) => .bnode label

/-- One predicate-local IBK2 block. SBM0/SBM1 admit one entry per predicate;
    SBM2 permits several bounded immutable blocks for one predicate. -/
structure Entry where
  predicate : WfIri
  artifact : ArtifactRef
  /-- Present and mandatory for SBM3. This independently committed SRI1
      object maps this artifact's local subject IDs to source-row offsets. -/
  subjectIndex : Option ArtifactRef := none
  /-- Present and mandatory for SBM4. This independently committed TLI1
      object maps canonical RDF-term bytes to this IBK3 artifact's local
      dictionary IDs. -/
  termIndex : Option ArtifactRef := none
  /-- Present and mandatory for SBM6. This independently committed OLI2
      object maps this artifact's local object IDs to source-row offsets. -/
  objectIndex : Option ArtifactRef := none
  /-- Present and mandatory for SBM8. This independently committed LGI1
      object holds the character 3-grams of the case-folded lexical form of
      every literal in this IBK4 artifact's dictionary, with the local term
      IDs that carry each gram. It is a CANDIDATE FILTER: a planner that uses
      it re-evaluates the original SPARQL expression on the candidates, so
      the rows are the scan's rows. Design record:
      `docs/designissues/2026-09-04-literal-token-index.md`.

      A block whose dictionary holds no literal carries an LGI1 with no gram
      rather than no sidecar, so an SBM8 reader never asks whether the role is
      present; it asks whether the manifest is SBM8. -/
  literalIndex : Option ArtifactRef := none
  /-- Present and mandatory for SBM7 and SBM8: the primary block codec of
      `artifact`. -/
  blockLayout : Option BlockLayout := none
  /-- Present and mandatory for SBM7: the blank-node scope of the source
      partition this entry was packed from (specification section 2.4.1). The
      packer writes the source file's SHA-256 as lowercase hexadecimal, which
      is a content digest and is therefore sufficient only under the
      `content-digest-shared` publication profile recorded on the manifest.
      Empty for SBM0 through SBM6, which commit no scope. -/
  blankNodeScope : String := ""
  /-- Present and mandatory for SBM7: the graph set of the IBK4 artifact, in
      the block's first-occurrence row order. Empty for SBM0 through SBM6. -/
  graphSet : List GraphName := []
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
  /-- Present and mandatory for SBM7, empty before it: the publication profile
      under which each entry's `blankNodeScope` is read. Specification section
      2.4.1 says a content digest identifies a blank-node allocation only when
      the publication profile also says that repeated imports of those bytes
      share one allocation; otherwise the scope must carry the import
      occurrence. Two profiles are defined:

      * `content-digest-shared` — repeated imports of the same source bytes
        share one blank-node allocation, so a content digest is a sufficient
        scope. This is what `l4block-shard-pack` writes.
      * `import-occurrence` — the scope carries an import occurrence or
        equivalent provenance identity, and two imports of identical bytes are
        two allocations.

      A reader that does not know the profile refuses the generation, so
      widening this set later is a compatible change. -/
  blankNodeProfile : String := ""
  entries : List Entry
  deriving DecidableEq

def uniquePredicates : List Entry → Bool
  | [] => true
  | entry :: rest => !(rest.map Entry.predicate).contains entry.predicate && uniquePredicates rest

def contiguousOrdinals : List Entry → Nat → Bool
  | [], _ => true
  | entry :: rest, expected => entry.ordinal == expected && contiguousOrdinals rest (expected + 1)

/-- The manifest wire version owns the sidecar contract; layout names must not
    silently select a weaker reader.  Versions zero through two predate the
    IBK3 sidecars and deliberately remain layout-extensible. -/
def layoutConsistent (version : Nat) (layout : String) : Bool :=
  match version with
  | 3 => layout == "predicate-ibk3-ptd1-sri1-merkle-v0" ||
      layout == "predicate-ibk3-ptd1-sri1-merkle-v0-compacted-default-dlog-v1"
  | 4 => layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0" ||
      layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0-compacted-default-dlog-v1"
  | 5 => layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0" ||
      layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0-compacted-default-dlog-v1"
  | 6 => layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0" ||
      layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0-compacted-default-dlog-v1"
  /- SBM7 carries no index sidecar: the specification says SRI2, OLI2 and TLI1
     need a graph dimension before they can describe an IBK4 artifact, and none
     is defined yet. There is deliberately no compacted SBM7 layout name here
     either; the compactor does not build IBK4 generations, and admitting a
     label nothing writes would be an untested reader path. -/
  | 7 => layout == "quad-ibk4-ptd1-merkle-v0"
  /- SBM8 is SBM7 plus the LGI1 literal search index in a fourth sidecar
     role. The label changes because the sidecar contract changed, and a
     reader must not select a weaker reader by name. -/
  | 8 => layout == "quad-ibk4-ptd1-lgi1-merkle-v0"
  | _ => true

/-- The block codec every entry of a generation must use, from its
    manifest-level layout label. `none` for the labels that predate the
    per-entry field. -/
def layoutBlockKind (layout : String) : Option BlockLayout :=
  if layout == "quad-ibk4-ptd1-merkle-v0" || layout == "quad-ibk4-ptd1-lgi1-merkle-v0" then
    some .ibk4 else none

/-- The layout labels naming a generation of IBK4 quad blocks: SBM7's, and
    SBM8's, which adds the LGI1 literal search index sidecar. -/
def isIbk4Layout (layout : String) : Bool :=
  layout == "quad-ibk4-ptd1-merkle-v0" || layout == "quad-ibk4-ptd1-lgi1-merkle-v0"

/-- Every layout label naming a generation of IBK3 blocks, base or compacted.

    A reader must select its block codec by NAME rather than by attempting a
    decode: an IBK4 reader over IBK3 bytes, or the reverse, misreads rows
    rather than failing. `Harness/IndexedBlockV3Query.lean` and
    `Wasm/Ops/Store.lean` share this list so the two hosts admit the same
    generations. -/
def isIbk3Layout (layout : String) : Bool :=
  layout == "predicate-ibk3-ptd1-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-sri1-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0" ||
  layout == "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1" ||
  layout == "predicate-ibk3-ptd1-sri1-merkle-v0-compacted-default-dlog-v1" ||
  layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0-compacted-default-dlog-v1" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0-compacted-default-dlog-v1" ||
  layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0-compacted-default-dlog-v1"

/-- The distinct predicates of an entry list, in manifest order. This is the
    count the native query tools report in their `open-mode=NAME(n)` header,
    so every host that reports a mode reports the same `n`. -/
def predicateOrder (entries : List Entry) : List WfIri :=
  entries.foldl (fun seen entry =>
    if seen.contains entry.predicate then seen else seen ++ [entry.predicate]) []

/-- The publication profiles this version of the manifest understands
    (specification section 2.4.1). -/
def knownBlankNodeProfile (profile : String) : Bool :=
  profile == "content-digest-shared" || profile == "import-occurrence"

/-- The scope string is bounded by the same 256 UTF-8 bytes the diagnostic ABI
    of specification section 2.4.1 already imposes on a blank-node scope. -/
def blankNodeScopeAdmitted (scope : String) : Bool :=
  !scope.isEmpty && scope.toUTF8.size <= 256

/-- A named graph's blank-node label must be nonempty; an IRI is already
    well formed by its type. -/
def graphNameAdmitted : GraphName → Bool
  | .defaultGraph => true
  | .iri _ => true
  | .bnode label => !label.isEmpty

/-- An entry's graph set is nonempty — an admitted IBK4 block has at least one
    row and therefore at least one graph — and lists no graph twice, because it
    is a copy of the block's DISTINCT graph column values. -/
def graphSetAdmitted (names : List GraphName) : Bool :=
  !names.isEmpty && names.all graphNameAdmitted &&
    names.length == names.eraseDups.length

/-- No immutable artifact key may play two manifest roles.  In particular an
    SBM3 subject-index sidecar cannot alias another block or sidecar. -/
def uniqueArtifactKeys (entries : List Entry) : Bool :=
  let keys := entries.flatMap fun entry =>
    entry.artifact.key :: (entry.subjectIndex.map ArtifactRef.key).toList ++
      (entry.termIndex.map ArtifactRef.key).toList ++
      (entry.objectIndex.map ArtifactRef.key).toList ++
      (entry.literalIndex.map ArtifactRef.key).toList
  keys.length == keys.eraseDups.length

/-- Structural acceptance before any host artifact is opened. -/
def artifactValidFor (version : Nat) (artifact : ArtifactRef) : Bool :=
  artifact.bytes > 0 && artifact.sha256.size == 32 &&
    match version, artifact.chunked with
    | 0, none => true
    | 1, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 2, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 3, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 4, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 5, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 6, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 7, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | 8, some chunked => ChunkedArtifact.valid chunked && chunked.totalBytes == artifact.bytes
    | _, _ => false

def entryValid (version : Nat) (entry : Entry) : Bool :=
  entry.rows > 0 && artifactValidFor version entry.artifact &&
  (match version, entry.subjectIndex with
    | 3, some index => artifactValidFor 3 index && index.key != entry.artifact.key
    | 4, some index => artifactValidFor 4 index && index.key != entry.artifact.key
    | 5, some index => artifactValidFor 5 index && index.key != entry.artifact.key
    | 6, some index => artifactValidFor 6 index && index.key != entry.artifact.key
    | 0, none | 1, none | 2, none | 7, none | 8, none => true
    | _, _ => false) &&
  (match version, entry.termIndex with
    | 4, some index => artifactValidFor 4 index && index.key != entry.artifact.key
    | 5, some index => artifactValidFor 5 index && index.key != entry.artifact.key
    | 6, some index => artifactValidFor 6 index && index.key != entry.artifact.key
    | 0, none | 1, none | 2, none | 3, none | 7, none | 8, none => true
    | _, _ => false) &&
  (match version, entry.objectIndex with
    | 6, some index => artifactValidFor 6 index && index.key != entry.artifact.key
    | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 7, none | 8, none => true
    | _, _ => false) &&
  /- SBM8's literal search index. It is MANDATORY at 8 and MUST BE ABSENT
     before it, for the same reason the SBM7 additions are: a manifest below 8
     carrying one would encode to bytes that drop it. -/
  (match version, entry.literalIndex with
    | 8, some index => artifactValidFor 8 index && index.key != entry.artifact.key
    | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 6, none | 7, none => true
    | _, _ => false) &&
  /- SBM7's three additions. They are MANDATORY at 7 and MUST BE ABSENT
     before it: a pre-SBM7 manifest carrying them would encode to bytes that
     drop them, and the round trip would silently lose data. -/
  (match version, entry.blockLayout with
    | 7, some _ | 8, some _ => true
    | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 6, none => true
    | _, _ => false) &&
  (if version == 7 || version == 8 then blankNodeScopeAdmitted entry.blankNodeScope &&
      graphSetAdmitted entry.graphSet
   else entry.blankNodeScope == "" && entry.graphSet == [])

/-- The manifest-level layout label and the per-entry block kind must agree.
    Before SBM7 the label is the only statement of the codec and there is no
    per-entry field; at SBM7 every entry must carry the kind the label names. -/
def entryLayoutsMatchLabel (manifest : Manifest) : Bool :=
  match layoutBlockKind manifest.layout with
  | none => manifest.entries.all fun entry => entry.blockLayout.isNone
  | some kind => manifest.entries.all fun entry => entry.blockLayout == some kind

def valid (manifest : Manifest) : Bool :=
  (manifest.version == 0 || manifest.version == 1 || manifest.version == 2 || manifest.version == 3 || manifest.version == 4 || manifest.version == 5 || manifest.version == 6 || manifest.version == 7 || manifest.version == 8) &&
    layoutConsistent manifest.version manifest.layout &&
    (if manifest.version == 7 || manifest.version == 8 then
        knownBlankNodeProfile manifest.blankNodeProfile
     else manifest.blankNodeProfile == "") &&
    entryLayoutsMatchLabel manifest &&
    (if manifest.version < 2 then uniquePredicates manifest.entries else true) &&
    uniqueArtifactKeys manifest.entries &&
    contiguousOrdinals manifest.entries 0 &&
    manifest.entries.all (entryValid manifest.version)

/-- SBM1 and later retain the fixed-chunk Merkle commitment required by the
range-backed local-file and remote readers. -/
def rangeCommitted (manifest : Manifest) : Bool :=
  manifest.version == 1 || manifest.version == 2 || manifest.version == 3 || manifest.version == 4 || manifest.version == 5 || manifest.version == 6 || manifest.version == 7 || manifest.version == 8

/-- Predicate selection is total and deterministic; a missing key means no
    candidate artifact, never a fallback that could hide an index error. -/
def select? (manifest : Manifest) (predicate : WfIri) : Option Entry :=
  if valid manifest then manifest.entries.find? fun entry => entry.predicate == predicate else none

/-- All committed blocks for a predicate, in manifest order. -/
def selectAll (manifest : Manifest) (predicate : WfIri) : List Entry :=
  if valid manifest then manifest.entries.filter fun entry => entry.predicate == predicate else []

/-- A host supplies bytes by relative artifact key.  Keeping this interface
    pure is what lets files, mmap, `bytea`, TiKV values, OPFS and WASM buffers
    share the same integrity-before-decode contract. -/
abbrev Reader := ArtifactKey → Option ByteArray

/-- Check the manifest's immutable child-artifact commitment before allowing
    any IBK2 parser to inspect those bytes. -/
def verifyEntry (entry : Entry) (bytes : ByteArray) : Bool :=
  bytes.size == entry.artifact.bytes &&
    L4Factoidal.Storage.BlockArtifact.verify entry.artifact.sha256 bytes

/-- Open a manifest child only after its declared extent and SHA-256 match.
    `none` deliberately conflates unavailable, substituted and malformed
    artifacts at this low-level boundary; hosts can attach richer diagnostics
    without weakening the acceptance rule. -/
def openVerified? (reader : Reader) (entry : Entry) : Option IndexedBlockWireV2.OpenBlock := do
  let bytes ← reader entry.artifact.key
  if verifyEntry entry bytes then do
    let block ← IndexedBlockWireV2.open? bytes
    /- `rows` is executable planning metadata only after it agrees with both
       the decoded row count and the declared predicate-local segment. This
       prevents a well-formed but incorrectly labelled manifest from feeding
       an unsound "exact" cardinality to the SPARQL join planner. -/
    if block.decoded.rows.size == entry.rows &&
        (IndexedBlockWireV2.scanBoundRange { p := some entry.predicate } block).length == entry.rows
    then some block else none
  else none

/-- The first executable Shardborough read: choose exactly the committed
    predicate-local artifact, verify it, then run the established IBK2
    selective scan.  No unlisted artifact and no full-manifest fallback is
    consulted. -/
def scanPredicate? (reader : Reader) (manifest : Manifest) (predicate : WfIri) : Option (List Triple) := do
  let entries := selectAll manifest predicate
  if entries.isEmpty then none else do
  let blocks ← entries.mapM fun entry => do
    let block ← openVerified? reader entry
    some (entry, block)
  some (blocks.flatMap fun (_, block) => IndexedBlockWireV2.scanBoundRange { p := some predicate } block)

/-- A Shardborough collection whose manifest and every child artifact have
    been accepted.  This eager opener is the correctness-first reference;
    later range/lazy variants must preserve its observable `readOps` results. -/
structure OpenStore where
  manifest : Manifest
  blocks : List (Entry × IndexedBlockWireV2.OpenBlock)

private def openEntries? (reader : Reader) : List Entry → Option (List (Entry × IndexedBlockWireV2.OpenBlock))
  | [] => some []
  | entry :: rest => do
      let block ← openVerified? reader entry
      let opened ← openEntries? reader rest
      some ((entry, block) :: opened)

/-- Verify and open every manifest child.  Failure is atomic at the API level:
    callers receive no partially trusted store. -/
def openStore? (reader : Reader) (manifest : Manifest) : Option OpenStore := do
  if !valid manifest then none else do
  let blocks ← openEntries? reader manifest.entries
  some { manifest, blocks }

/-- The manifest entries needed for a set of predicate-bound scans.  The order
    remains manifest order rather than query order, and duplicate predicates
    do not cause a block to be opened twice.  A predicate missing from the
    manifest deliberately contributes no entry: its backend search is empty,
    which is the same result as searching the complete store. -/
def entriesForPredicates (manifest : Manifest) (predicates : List WfIri) : List Entry :=
  manifest.entries.filter fun entry => predicates.contains entry.predicate

/-- Open only the manifest children selected by an already-established
    predicate-bound plan.  This is not a general replacement for `openStore?`:
    an unbound backend search over this store would be incomplete.  The query
    planner guard below exposes it only for native pattern shapes where every
    backend request has a syntactically constant predicate. -/
def openStoreForPredicates? (reader : Reader) (manifest : Manifest)
    (predicates : List WfIri) : Option OpenStore := do
  if !valid manifest then none else do
  let blocks ← openEntries? reader (entriesForPredicates manifest predicates)
  some { manifest, blocks }

/-- The total physical scan behind the existing SPARQL backend seam.  A
    predicate-bound request touches exactly its committed child; unbound scans
    are the reference concatenation over manifest order until a source-order
    / graph-aware layout is introduced. -/
def scanBound (bound : PatternBound) (store : OpenStore) : List Triple :=
  match bound.p with
  | some predicate =>
      store.blocks.filter (fun pair => pair.1.predicate == predicate) |>.flatMap
        fun (_, block) => IndexedBlockWireV2.scanBoundRange bound block
  | none => store.blocks.flatMap fun (_, block) => IndexedBlockWireV2.scanBoundRange bound block

/-- A predicate-local SBM0 entry has an exact admitted row count for an
    otherwise unbound triple pattern. More selective bounds still scan, so the
    planner never mistakes an upper bound for an exact estimate. -/
def estimateBound (bound : PatternBound) (store : OpenStore) : Nat :=
  match bound.s, bound.p, bound.o with
  | none, some predicate, none =>
      store.blocks.foldl (fun total pair =>
        if pair.1.predicate == predicate then total + pair.1.rows else total) 0
  | _, _, _ => (scanBound bound store).length

/-- Ordinary parsed SPARQL reaches the manifested physical collection through
    precisely the same `BackendReadOps` interface as Cottas, HDT and IBK2. -/
def readOps (store : OpenStore) : BackendReadOps :=
  { search := fun bound => scanBound bound store
  , estimate := fun bound => estimateBound bound store
  , predicatePresent := fun predicate => !(scanBound { p := some predicate } store).isEmpty }

/-- The step IRIs a property path can traverse, when every step is a constant
    IRI.

    §18.4 evaluates `iri` by a one-step lookup on that predicate, `^p` by
    swapping the pairs `p` denotes, `p1/p2` by relational composition and
    `p1|p2` by union.  Each of those four reads only triples whose predicate
    is one of the step IRIs collected here, so the pair relation the path
    denotes over the dataset restricted to those predicates equals the one it
    denotes over the whole dataset.

    `*`, `+`, `?` and the negated property set return `none`, for two separate
    reasons.  `*` and `?` have a ZERO-LENGTH case whose pairs are
    `(node, node)` for every node of the active graph (§18.4's
    `ZeroLengthPath`), so restricting the dataset removes pairs from their
    answer.  `+` reads only its step predicate, but `evalPath` bounds its
    fixpoint with a fuel counter seeded from the graph's node count, so
    admitting it needs an argument about the restricted seed as well as about
    the read set; it stays out until that argument is written.  A negated
    property set is defined by the predicates it does NOT name, so it has no
    finite constant read set. -/
def constantPathPredicates? : PropertyPath → Option (List WfIri)
  | .iri predicate => some [predicate]
  | .inverse path => constantPathPredicates? path
  | .sequence p1 p2
  | .alternative p1 p2 => do
      let l ← constantPathPredicates? p1
      let r ← constantPathPredicates? p2
      some (l ++ r)
  | _ => none

/-- Conservative syntactic admission test for the selective manifest opener.
    It accepts only pattern forms whose triple patterns all carry a constant
    IRI predicate.  Graph clauses, SERVICE, LATERAL, VALUES and sub-SELECT
    deliberately return `none`: those forms can materialise the active backend
    or introduce a nested pattern, so the complete-store opener remains the
    sound default until they receive their own planning proof.

    Soundness of the accepted set (BGP, `join`, `union`, `minus`, `leftJoin`,
    `bind` and `filter` with a `backendLocal` expression, and `propertyPath`
    over constant-IRI steps): the evaluation of each of those operators is a
    function of its operands' solution sequences and of the current solution
    mapping alone — `SPARQL.join`, `SPARQL.union`, `SPARQL.minus` and
    `SPARQL.leftJoin` read no triples themselves, and a `backendLocal`
    expression reads only the row (it carries no nested `QueryPattern`, so
    `substituteExistentials` is the identity on it).  §18.6 `BIND(e AS ?v)`
    extends each row of its sub-pattern with one value of `e`, so a
    `backendLocal` `e` adds no triple read of its own.  A BGP whose every
    triple pattern has a constant predicate matches only triples with those
    predicates, and `constantPathPredicates?` above carries the same argument
    for a path.  By induction, evaluating an accepted pattern over the dataset
    restricted to the collected predicates gives the same solution sequence as
    evaluating it over the whole dataset. -/
def nativeConstantPredicates? : QueryPattern → Option (List WfIri)
  | .bgp patterns =>
      patterns.foldr (fun pattern rest => do
        let predicates ← rest
        match pattern.p with
        | .iri predicate => some (predicate :: predicates)
        | _ => none) (some [])
  | .join left right
  | .union left right
  | .minus left right => do
      let l ← nativeConstantPredicates? left
      let r ← nativeConstantPredicates? right
      some (l ++ r)
  | .leftJoin left right cond =>
      if cond.backendLocal then do
        let l ← nativeConstantPredicates? left
        let r ← nativeConstantPredicates? right
        some (l ++ r)
      else none
  | .filter condition pattern =>
      if condition.backendLocal then nativeConstantPredicates? pattern else none
  -- §18.6 BIND: one extra binding per row of the sub-pattern, computed by
  -- `Expr.evalIn` from the row alone when the expression is `backendLocal`.
  -- A non-`backendLocal` expression can carry an EXISTS, which reads triples
  -- through `EvalEnv.dataset` and would then see only the opened shards.
  | .bind expression _ pattern =>
      if expression.backendLocal then nativeConstantPredicates? pattern else none
  -- §18.4 a path contributes exactly its step IRIs when every step is a
  -- constant IRI. The subject and object positions are irrelevant here: they
  -- constrain the pairs, they do not widen the set of predicates read.
  | .propertyPath _ path _ => constantPathPredicates? path
  | .empty => some []
  | _ => none

/-- The query-level form of `nativeConstantPredicates?`.  It is a planner
    capability, not a semantic shortcut: `none` means "open the full
    manifest", never "return no answers".

    `nativeConstantPredicates?` reads `query.pattern` and nothing else, so it
    cannot see the expressions a query carries in its SELECT projection, its
    GROUP BY keys, its HAVING conditions or its ORDER BY conditions.  §18.6
    evaluates an `EXISTS` / `NOT EXISTS` in any of those positions against the
    ACTIVE GRAPH, and a caller that opens only the predicates collected from
    the pattern would hand that sub-pattern a proper subset of the dataset —
    `Harness/IndexedBlockV3Query.lean` sets `env.dataset` from exactly the
    entries it materialised.  So the whole query is refused unless every
    expression outside the pattern is `Expr.existsFree`
    (https://github.com/danbri/factoidal/issues/638).

    The test is `Query.expressionsOutsidePatternExistsFree` and NOT
    `Expr.backendLocal`: an aggregate, `IRI()`, `REGEX` or an extension call
    is legitimate in those positions and reads no triples, so rejecting them
    would send every ordinary `GROUP BY` / `ORDER BY` query down the
    full-manifest path for no soundness gain. -/
def queryNativeConstantPredicates? (query : Query) : Option (List WfIri) :=
  if query.expressionsOutsidePatternExistsFree then
    nativeConstantPredicates? query.pattern
  else none

/-! ## SBM7 entry selection: which quad blocks a query can skip

An SBM7 generation holds one or more IBK4 blocks per predicate, and those
blocks together carry that predicate's rows for EVERY graph of the dataset.
`valid` admits several entries for one predicate at every version from SBM2
on, and `L4Factoidal/Storage/PredicateQuadBlocks.lean` cuts a predicate's rows
at graph changes and at two size targets
(`docs/designissues/2026-09-04-blocks-per-predicate.md`), so a block written
today holds ONE graph and its `graphSet` has one member. A generation packed
before that change holds one block per predicate carrying every graph, and
both read through the same rules below. Two independent facts about a query
let a planner drop an entry without reading a row:

* the predicates the pattern reads, which `nativeConstantPredicates?` above
  already collects for the IBK3 planner, and
* the graph names the pattern reads, which each entry's `graphSet` answers
  from the manifest alone. Specification section 6.3.1 fixes that the manifest
  summary carries graph NAMES rather than the block's graph column values, and
  activation checked the manifest summary against the block header
  (`Harness/ShardActivate.lean`, `verifyQuadEntry`).

Both collectors are conservative. `none` means "no restriction established",
never "no answers": the caller then opens every entry. -/

/-- The graph names a pattern can read, given the graph name active where the
    pattern appears.

    `none` is "cannot be established": a `GRAPH ?v`, a sub-SELECT, SERVICE,
    LATERAL, VALUES, or a FILTER / OPTIONAL / BIND expression that is not
    `Expr.backendLocal` — such an expression may carry an `EXISTS`, which
    reads triples through `EvalEnv.dataset` and so reads graphs this
    collector cannot see.

    A `GRAPH <iri> { ... }` contributes its own name even when its body reads
    no triple. Section 18.6 gives `GRAPH <g> { }` one solution when `<g>`
    names a graph of the dataset and none when it does not, so an entry whose
    rows put `<g>` into the materialised dataset must not be dropped. -/
def graphsReadFrom (active : GraphName) : QueryPattern → Option (List GraphName)
  | .bgp patterns => if patterns.isEmpty then some [] else some [active]
  | .propertyPath _ _ _ => some [active]
  | .empty => some []
  | .join left right
  | .union left right
  | .minus left right => do
      let l ← graphsReadFrom active left
      let r ← graphsReadFrom active right
      some (l ++ r)
  | .leftJoin left right cond =>
      if cond.backendLocal then do
        let l ← graphsReadFrom active left
        let r ← graphsReadFrom active right
        some (l ++ r)
      else none
  | .filter cond pattern =>
      if cond.backendLocal then graphsReadFrom active pattern else none
  | .bind expression _ pattern =>
      if expression.backendLocal then graphsReadFrom active pattern else none
  | .graph (.iri name) pattern => do
      let inner ← graphsReadFrom (.iri name) pattern
      some (if inner.contains (.iri name) then inner else .iri name :: inner)
  | _ => none

/-- The graph names a whole query reads. Outside a `GRAPH` clause the active
    graph is the default graph, so that is the seed.

    Two guards. `Query.expressionsOutsidePatternExistsFree` is the same
    EXISTS guard `queryNativeConstantPredicates?` carries: section 18.6
    evaluates an `EXISTS` in the projection, a GROUP BY key, a HAVING
    condition or an ORDER BY condition against the ACTIVE GRAPH, and
    `graphsReadFrom` reads only `query.pattern`. And a query carrying `FROM` /
    `FROM NAMED` gets no graph-based selection at all: section 13.2 rebuilds
    the default graph out of the `FROM` graphs, so a default-graph pattern
    under a `FROM <g>` reads `<g>` and not `GraphName.defaultGraph`. Modelling
    that here would duplicate `applyDataset`; refusing the selection costs
    only the reads it would have skipped. -/
def queryGraphNames? (query : Query) : Option (List GraphName) :=
  if query.expressionsOutsidePatternExistsFree && query.dataset.isEmpty then
    graphsReadFrom .defaultGraph query.pattern
  else none

/-- `nativeConstantPredicates?` widened for IBK4. It descends through a
    `GRAPH` clause, constant or variable: the IBK4 blocks of one predicate
    carry that predicate's rows for every graph, and selecting by predicate
    keeps ALL of them, so predicate selection does not restrict WHICH graphs
    the opened entries carry, and the soundness induction of
    `nativeConstantPredicates?` goes through unchanged with the active graph
    as a parameter.

    Two arms are NARROWER than the IBK3 collector: an empty BGP and the empty
    group pattern give `none` where the IBK3 collector gives `some []`. Under
    a `GRAPH` clause those read no triple but still observe whether the
    dataset names a graph, and a predicate-selected entry set can leave that
    graph out of the materialised dataset. -/
def quadNativeConstantPredicates? : QueryPattern → Option (List WfIri)
  | .bgp patterns =>
      if patterns.isEmpty then none else
      patterns.foldr (fun pattern rest => do
        let predicates ← rest
        match pattern.p with
        | .iri predicate => some (predicate :: predicates)
        | _ => none) (some [])
  | .join left right
  | .union left right
  | .minus left right => do
      let l ← quadNativeConstantPredicates? left
      let r ← quadNativeConstantPredicates? right
      some (l ++ r)
  | .leftJoin left right cond =>
      if cond.backendLocal then do
        let l ← quadNativeConstantPredicates? left
        let r ← quadNativeConstantPredicates? right
        some (l ++ r)
      else none
  | .filter condition pattern =>
      if condition.backendLocal then quadNativeConstantPredicates? pattern else none
  | .bind expression _ pattern =>
      if expression.backendLocal then quadNativeConstantPredicates? pattern else none
  | .graph _ pattern => quadNativeConstantPredicates? pattern
  | .propertyPath _ path _ => constantPathPredicates? path
  | _ => none

/-- The query-level form, under the same EXISTS guard as
    `queryNativeConstantPredicates?`. -/
def queryQuadConstantPredicates? (query : Query) : Option (List WfIri) :=
  if query.expressionsOutsidePatternExistsFree then
    quadNativeConstantPredicates? query.pattern
  else none

/-- The IBK4 entries a query can read, in manifest order.

    An entry survives unless a collector excludes it, so a `none` from either
    collector keeps every entry that collector could have excluded. An invalid
    manifest selects nothing, as `selectAll` does. -/
def quadEntriesForQuery (manifest : Manifest) (query : Query) : List Entry :=
  if !valid manifest then [] else
  let predicates := queryQuadConstantPredicates? query
  let graphs := queryGraphNames? query
  manifest.entries.filter fun entry =>
    (match predicates with
     | none => true
     | some wanted => wanted.contains entry.predicate) &&
    (match graphs with
     | none => true
     | some wanted => entry.graphSet.any fun name => wanted.contains name)

/-- The field widths in SBM0.  Oversized manifests are refused rather than
    being truncated into an ambiguous byte stream. -/
def fitsU32 (n : Nat) : Bool := n < 4294967296

/-! ## SBM7 field codecs

One byte of kind, then a length-prefixed UTF-8 name.  The kind byte is what
keeps the default graph distinguishable from a graph NAMED by an IRI, which is
the requirement of specification section 5 that also shapes the IBK4 graph
column. -/

def blockLayoutTag : BlockLayout → UInt8
  | .ibk3 => 0
  | .ibk4 => 1

def blockLayoutOfTag (tag : UInt8) : Option BlockLayout :=
  if tag == 0 then some .ibk3 else if tag == 1 then some .ibk4 else none

def graphNameTag : GraphName → UInt8
  | .defaultGraph => 0
  | .iri _ => 1
  | .bnode _ => 2

def graphNameText : GraphName → String
  | .defaultGraph => ""
  | .iri value => value.val
  | .bnode label => label

def encodeGraphName (name : GraphName) : List UInt8 :=
  [graphNameTag name] ++ encodeString (graphNameText name)

def graphNameEncodable (name : GraphName) : Bool :=
  fitsU32 (graphNameText name).toUTF8.size

def decodeGraphName (bytes : List UInt8) : Option (GraphName × List UInt8) := do
  let (tag, afterTag) ← parseU8 bytes
  let (text, rest) ← decodeString afterTag
  if tag == 0 then
    if text.isEmpty then some (.defaultGraph, rest) else none
  else if tag == 1 then
    if h : isIri text then some (.iri ⟨text, h⟩, rest) else none
  else if tag == 2 then
    if text.isEmpty then none else some (.bnode text, rest)
  else none

def decodeGraphNames : Nat → List UInt8 → Option (List GraphName × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (name, afterName) ← decodeGraphName bytes
      let (names, rest) ← decodeGraphNames n afterName
      some (name :: names, rest)

/-- The wire-field bounds every version's entry must satisfy, whatever its
    version-specific commitments are. -/
def encodableCommon (entry : Entry) : Bool :=
  fitsU32 entry.predicate.val.toUTF8.size && fitsU32 entry.artifact.key.value.toUTF8.size &&
    fitsU32 entry.artifact.bytes && fitsU32 entry.rows && fitsU32 entry.ordinal &&
    entry.artifact.sha256.size == 32

/-- The wire-field bounds of one Merkle chunk commitment. -/
def encodableChunked (chunked : ChunkedArtifact.Ref) : Bool :=
  fitsU32 chunked.chunkBytes && fitsU32 chunked.chunkCount && chunked.root.size == 32

/-- The wire-field bounds of one index sidecar reference. A sidecar with no
    chunk commitment encodes to no bytes, so it is refused here. -/
def encodableSidecar (index : ArtifactRef) : Bool :=
  fitsU32 index.key.value.toUTF8.size && fitsU32 index.bytes && index.sha256.size == 32 &&
    (match index.chunked with
     | some chunked => encodableChunked chunked
     | none => false)

/- Each version-dependent test below is PARENTHESISED. Before 2026-09-03 they
   were written as `&& match ... | _, _ => false && match ...`, and a `match`
   alternative extends as far as the parser can take it: every test after the
   first was swallowed into the fallback alternative of the one before it, so
   on a successful path only `encodableCommon` and the chunk-commitment test
   ran. The sidecar field-width tests of SBM3 through SBM6 were dead. Found
   2026-09-03 while proving `decodeEntry_encodeEntry`: the proof needed a
   sidecar bound that the definition did not supply. -/
def encodableEntry (version : Nat) (entry : Entry) : Bool :=
  encodableCommon entry &&
  (match version, entry.artifact.chunked with
   | 0, none => true
   | 1, some chunked | 2, some chunked | 3, some chunked | 4, some chunked
   | 5, some chunked | 6, some chunked | 7, some chunked
   | 8, some chunked => encodableChunked chunked
   | _, _ => false) &&
  (match version, entry.subjectIndex with
   | 3, some index | 4, some index | 5, some index | 6, some index => encodableSidecar index
   | 0, none | 1, none | 2, none | 7, none | 8, none => true
   | _, _ => false) &&
  (match version, entry.termIndex with
   | 4, some index | 5, some index | 6, some index => encodableSidecar index
   | 0, none | 1, none | 2, none | 3, none | 7, none | 8, none => true
   | _, _ => false) &&
  (match version, entry.objectIndex with
   | 6, some index => encodableSidecar index
   | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 7, none | 8, none => true
   | _, _ => false) &&
  (match version, entry.literalIndex with
   | 8, some index => encodableSidecar index
   | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 6, none | 7, none => true
   | _, _ => false) &&
  (match version, entry.blockLayout with
   | 7, some _ | 8, some _ => fitsU32 entry.blankNodeScope.toUTF8.size &&
       fitsU32 entry.graphSet.length && entry.graphSet.all graphNameEncodable
   | 0, none | 1, none | 2, none | 3, none | 4, none | 5, none | 6, none => true
   | _, _ => false)

def encodable (manifest : Manifest) : Bool :=
  fitsU32 manifest.sourceIdentity.size && fitsU32 manifest.termRegistryVersion.toUTF8.size &&
    fitsU32 manifest.layout.toUTF8.size && fitsU32 manifest.blankNodeProfile.toUTF8.size &&
    fitsU32 manifest.entries.length &&
    manifest.entries.all (encodableEntry manifest.version)

/-! ## The entry codec, as composable framed objects

`encodeEntry`/`decodeEntry` were one flat block each before 2026-09-03. They
are split here into the framed objects they always wrote — common fields,
Merkle chunk commitment, index sidecar, SBM7 quad tail — so each object has its
own round-trip lemma in `ShardManifestTheorems` instead of one proof repeated
per wire version. The bytes are unchanged. -/

/-- The fields every entry carries in every version, before any version's own
    commitments. -/
structure CommonFields where
  predicateText : String
  keyText : String
  artifactBytes : Nat
  digest : List UInt8
  rows : Nat
  ordinal : Nat
  deriving DecidableEq

def encodeCommon (entry : Entry) : List UInt8 :=
  encodeString entry.predicate.val ++ encodeString entry.artifact.key.value ++
    writeU32LE (UInt32.ofNat entry.artifact.bytes) ++ entry.artifact.sha256.toList ++
    writeU32LE (UInt32.ofNat entry.rows) ++ writeU32LE (UInt32.ofNat entry.ordinal)

def decodeCommon (bytes : List UInt8) : Option (CommonFields × List UInt8) := do
  let (predicateText, afterPredicate) ← decodeString bytes
  let (keyText, afterKey) ← decodeString afterPredicate
  let artifactBytes ← readU32LE afterKey 0
  let (digest, afterDigest) ← takeExact 32 (afterKey.drop 4)
  let rows ← readU32LE afterDigest 0
  let ordinal ← readU32LE afterDigest 4
  let (_, afterOrdinal) ← takeExact 8 afterDigest
  some ({ predicateText, keyText, artifactBytes := artifactBytes.toNat, digest,
          rows := rows.toNat, ordinal := ordinal.toNat }, afterOrdinal)

/-- The fixed-chunk Merkle commitment of one artifact. `totalBytes` is not on
    the wire here: it is the artifact byte extent already read. -/
def encodeChunkedRef (chunked : ChunkedArtifact.Ref) : List UInt8 :=
  writeU32LE (UInt32.ofNat chunked.chunkBytes) ++
    writeU32LE (UInt32.ofNat chunked.chunkCount) ++ chunked.root.toList

def decodeChunkedRef (totalBytes : Nat) (bytes : List UInt8) :
    Option (ChunkedArtifact.Ref × List UInt8) := do
  let chunkBytes ← readU32LE bytes 0
  let chunkCount ← readU32LE bytes 4
  let (root, rest) ← takeExact 32 (bytes.drop 8)
  some ({ totalBytes := totalBytes, chunkBytes := chunkBytes.toNat,
          chunkCount := chunkCount.toNat, root := byteArrayOfList root }, rest)

/-- One index sidecar reference: key, extent, SHA-256 and its own Merkle
    commitment. A sidecar with no chunk commitment encodes to nothing, which
    `encodable` refuses. -/
def encodeSidecarRef (index : ArtifactRef) : List UInt8 :=
  match index.chunked with
  | some chunked =>
      encodeString index.key.value ++ writeU32LE (UInt32.ofNat index.bytes) ++
        index.sha256.toList ++ encodeChunkedRef chunked
  | none => []

def decodeSidecarRef (bytes : List UInt8) : Option (ArtifactRef × List UInt8) := do
  let (indexKey, afterKey) ← decodeString bytes
  let indexBytes ← readU32LE afterKey 0
  let (indexDigest, afterDigest) ← takeExact 32 (afterKey.drop 4)
  let (chunked, rest) ← decodeChunkedRef indexBytes.toNat afterDigest
  some ({ key := { value := indexKey }, bytes := indexBytes.toNat,
          sha256 := byteArrayOfList indexDigest, chunked := some chunked }, rest)

/-- SBM7's tail: block kind, blank-node scope, graph-set summary. -/
def encodeQuadTail (kind : BlockLayout) (scope : String) (names : List GraphName) : List UInt8 :=
  [blockLayoutTag kind] ++ encodeString scope ++
    writeU32LE (UInt32.ofNat names.length) ++ names.flatMap encodeGraphName

def decodeQuadTail (bytes : List UInt8) :
    Option ((BlockLayout × String × List GraphName) × List UInt8) := do
  let (tag, afterTag) ← parseU8 bytes
  let kind ← blockLayoutOfTag tag
  let (scope, afterScope) ← decodeString afterTag
  let count ← readU32LE afterScope 0
  let (_, afterCount) ← takeExact 4 afterScope
  let (names, rest) ← decodeGraphNames count.toNat afterCount
  some ((kind, scope, names), rest)

def encodeEntry (version : Nat) (entry : Entry) : List UInt8 :=
  match version, entry.artifact.chunked with
  | 0, none => encodeCommon entry
  | 1, some chunked | 2, some chunked =>
      encodeCommon entry ++ encodeChunkedRef chunked
  | 3, some chunked | 4, some chunked | 5, some chunked | 6, some chunked =>
      let primary := encodeCommon entry ++ encodeChunkedRef chunked
      match version, entry.subjectIndex, entry.termIndex, entry.objectIndex with
      | 3, some subject, none, none => primary ++ encodeSidecarRef subject
      | 4, some subject, some term, none | 5, some subject, some term, none =>
          primary ++ encodeSidecarRef subject ++ encodeSidecarRef term
      | 6, some subject, some term, some object =>
          primary ++ encodeSidecarRef subject ++ encodeSidecarRef term ++ encodeSidecarRef object
      | _, _, _, _ => []
  /- SBM7 writes no index sidecar (there is no graph-aware SRI2/OLI2/TLI1 yet),
     and appends the three quad-aware fields after the Merkle commitment. -/
  | 7, some chunked =>
      match entry.blockLayout with
      | some kind =>
          encodeCommon entry ++ encodeChunkedRef chunked ++
            encodeQuadTail kind entry.blankNodeScope entry.graphSet
      | none => []
  /- SBM8 writes the LGI1 sidecar where SBM6 writes its object index, before
     the quad tail, so the decoder reads one field sequence rather than a
     version-dependent reordering. -/
  | 8, some chunked =>
      match entry.blockLayout, entry.literalIndex with
      | some kind, some literal =>
          encodeCommon entry ++ encodeChunkedRef chunked ++ encodeSidecarRef literal ++
            encodeQuadTail kind entry.blankNodeScope entry.graphSet
      | _, _ => []
  | _, _ => []

/-- Canonical SBM0/SBM1/SBM2 bytes. SBM1 and SBM2 retain every SBM0 field and
    append a fixed chunk-policy/root commitment to each artifact entry. -/
def encode? (manifest : Manifest) : Option ByteArray :=
  if valid manifest && encodable manifest then
    some <| byteArrayOfList <|
      writeU32LE magic ++ [UInt8.ofNat manifest.version] ++
      writeU32LE (UInt32.ofNat manifest.sourceIdentity.size) ++ manifest.sourceIdentity.toList ++
      encodeString manifest.termRegistryVersion ++ encodeString manifest.layout ++
      (if manifest.version == 7 || manifest.version == 8 then
        encodeString manifest.blankNodeProfile else []) ++
      writeU32LE (UInt32.ofNat manifest.entries.length) ++ manifest.entries.flatMap (encodeEntry manifest.version)
  else none

def decodeEntry (version : Nat) (bytes : List UInt8) : Option (Entry × List UInt8) := do
  let (common, afterCommon) ← decodeCommon bytes
  if h : isIri common.predicateText then do
    let (chunked, afterChunked) ← match version with
      | 0 => some ((none : Option ChunkedArtifact.Ref), afterCommon)
      | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => do
          let (ref, rest) ← decodeChunkedRef common.artifactBytes afterCommon
          some (some ref, rest)
      | _ => none
    let (subjectIndex, afterSubject) ← match version with
      | 3 | 4 | 5 | 6 => do
          let (ref, rest) ← decodeSidecarRef afterChunked
          some (some ref, rest)
      | _ => some ((none : Option ArtifactRef), afterChunked)
    let (termIndex, afterTerm) ← match version with
      | 4 | 5 | 6 => do
          let (ref, rest) ← decodeSidecarRef afterSubject
          some (some ref, rest)
      | _ => some ((none : Option ArtifactRef), afterSubject)
    let (objectIndex, afterObject) ← match version with
      | 6 => do
          let (ref, rest) ← decodeSidecarRef afterTerm
          some (some ref, rest)
      | _ => some ((none : Option ArtifactRef), afterTerm)
    let (literalIndex, afterLiteral) ← match version with
      | 8 => do
          let (ref, rest) ← decodeSidecarRef afterObject
          some (some ref, rest)
      | _ => some ((none : Option ArtifactRef), afterObject)
    let (quad, rest) ← match version with
      | 7 | 8 => do
          let (fields, rest) ← decodeQuadTail afterLiteral
          some ((some fields.1, fields.2.1, fields.2.2), rest)
      | _ => some (((none : Option BlockLayout), "", ([] : List GraphName)), afterLiteral)
    some
      ({ predicate := ⟨common.predicateText, h⟩
         artifact := { key := { value := common.keyText }, bytes := common.artifactBytes,
                       sha256 := byteArrayOfList common.digest, chunked }
         subjectIndex
         termIndex
         objectIndex
         literalIndex
         blockLayout := quad.1
         blankNodeScope := quad.2.1
         graphSet := quad.2.2
         rows := common.rows
         ordinal := common.ordinal }, rest)
  else none

def decodeEntries (version : Nat) : Nat → List UInt8 → Option (List Entry × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
      let (entry, afterEntry) ← decodeEntry version bytes
      let (entries, rest) ← decodeEntries version n afterEntry
      some (entry :: entries, rest)

/-- Strict SBM0/SBM1/SBM2 decoding. A decoder refuses bad framing, unknown versions,
    invalid UTF-8/IRIs, trailing bytes and structurally invalid manifests. -/
def decode? (bytes : ByteArray) : Option Manifest := do
  let allBytes := listOfByteArray bytes
  let foundMagic ← readU32LE allBytes 0
  if foundMagic != magic then none else do
  let (foundVersion, afterVersion) ← parseU8 (allBytes.drop 4)
  if foundVersion != wireVersion0 && foundVersion != wireVersion1 && foundVersion != wireVersion2 && foundVersion != wireVersion3 && foundVersion != wireVersion4 && foundVersion != wireVersion5 && foundVersion != wireVersion6 && foundVersion != wireVersion7 && foundVersion != wireVersion8 then none else do
  let sourceLength ← readU32LE afterVersion 0
  let (sourceIdentity, afterSource) ← takeExact sourceLength.toNat (afterVersion.drop 4)
  let (termRegistryVersion, afterRegistry) ← decodeString afterSource
  let (layout, afterLayout) ← decodeString afterRegistry
  let (blankNodeProfile, afterProfile) ←
    if foundVersion == wireVersion7 || foundVersion == wireVersion8 then decodeString afterLayout
    else some ("", afterLayout)
  let entryCount ← readU32LE afterProfile 0
  let (entries, rest) ← decodeEntries foundVersion.toNat entryCount.toNat (afterProfile.drop 4)
  let manifest := { version := foundVersion.toNat, sourceIdentity := byteArrayOfList sourceIdentity,
                    termRegistryVersion, layout, blankNodeProfile, entries }
  if rest.isEmpty && valid manifest then some manifest else none

private def samplePredicate : WfIri := ⟨"https://example.test/p", by decide⟩

private def sampleOtherPredicate : WfIri := ⟨"https://example.test/q", by decide⟩
private def sampleSubject : Subject := .iri ⟨"https://example.test/s", by decide⟩
private def sampleObject : Term := .iri ⟨"https://example.test/o", by decide⟩
private def sampleBlock : IndexedBlock.Block :=
  IndexedBlock.fromGraph [{ s := sampleSubject, p := samplePredicate, o := sampleObject }]
private def sampleBlockBytes : ByteArray :=
  (IndexedBlockWireV2.encode? sampleBlock).getD ByteArray.empty
private def sampleDigest : ByteArray := L4Factoidal.Crypto.sha256 sampleBlockBytes
private def sampleManifest : Manifest :=
  { version := 0, sourceIdentity := ByteArray.mk #[1, 2, 3], termRegistryVersion := "terms-v0",
    layout := "predicate-ibk2-v0",
    entries := [{ predicate := samplePredicate,
                  artifact := { key := { value := "blocks/p.ibk2" }, bytes := sampleBlockBytes.size,
                                sha256 := sampleDigest }, rows := 1, ordinal := 0 }] }
private def sampleReader (key : ArtifactKey) : Option ByteArray :=
  if key.value == "blocks/p.ibk2" then some sampleBlockBytes else none

private def sampleChunked : ChunkedArtifact.Ref :=
  match ChunkedArtifact.fromChunks? 64 (ChunkedArtifact.chunksOf 64 sampleBlockBytes) with
  | some ref => ref
  | none => { totalBytes := 1, chunkBytes := 1, chunkCount := 1, root := ByteArray.empty }

private def sampleManifestV1 : Manifest :=
  match sampleManifest.entries with
  | entry :: _ =>
      { { sampleManifest with version := 1 } with
        entries := [{ entry with artifact := { entry.artifact with chunked := some sampleChunked } }] }
  | [] => sampleManifest

/-- SBM2 keeps SBM1's range commitment but permits several committed blocks
for one predicate, which is the bounded-publication shape a spooler needs. -/
private def sampleManifestV2 : Manifest :=
  match sampleManifestV1.entries with
  | entry :: _ =>
      { { sampleManifestV1 with version := 2, layout := "predicate-ibk2-merkle-v2" } with
        entries := [entry, { entry with artifact := { entry.artifact with key := { value := "blocks/p-1.ibk2" } }, ordinal := 1 }] }
  | [] => sampleManifestV1

private def sampleManifestV3 : Manifest :=
  match sampleManifestV1.entries with
  | entry :: _ =>
      let index : ArtifactRef :=
        { key := { value := "blocks/p.sri1" }, bytes := sampleBlockBytes.size,
          sha256 := sampleDigest, chunked := some sampleChunked }
      { { sampleManifestV1 with version := 3, layout := "predicate-ibk3-ptd1-sri1-merkle-v0" } with
        entries := [{ entry with subjectIndex := some index }] }
  | [] => sampleManifestV1

private def sampleManifestV3MissingIndex : Manifest :=
  { sampleManifestV3 with entries := sampleManifestV3.entries.map fun entry =>
    { entry with subjectIndex := none } }

private def sampleManifestV4 : Manifest :=
  match sampleManifestV3.entries with
  | entry :: _ =>
      let index : ArtifactRef :=
        { key := { value := "blocks/p.tli1" }, bytes := sampleBlockBytes.size,
          sha256 := sampleDigest, chunked := some sampleChunked }
      { { sampleManifestV3 with version := 4, layout := "predicate-ibk3-ptd1-sri1-tli1-merkle-v0" } with
        entries := [{ entry with termIndex := some index }] }
  | [] => sampleManifestV3

private def sampleManifestV5 : Manifest :=
  { { sampleManifestV4 with version := 5, layout := "predicate-ibk3-ptd1-sri2-tli1-merkle-v0" } with
    entries := sampleManifestV4.entries.map fun entry =>
      { entry with subjectIndex := entry.subjectIndex.map fun index =>
          { index with key := { value := "blocks/p.sri2" } } } }

private def sampleManifestV6 : Manifest :=
  match sampleManifestV5.entries with
  | entry :: _ =>
      let index : ArtifactRef :=
        { key := { value := "blocks/p.oli2" }, bytes := sampleBlockBytes.size,
          sha256 := sampleDigest, chunked := some sampleChunked }
      { version := 6
        sourceIdentity := sampleManifestV5.sourceIdentity
        termRegistryVersion := sampleManifestV5.termRegistryVersion
        layout := "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0"
        entries := [{ entry with objectIndex := some index }] }
  | [] => sampleManifestV5

private def sampleManifestV6MissingObjectIndex : Manifest :=
  { sampleManifestV6 with entries := sampleManifestV6.entries.map fun entry =>
    { entry with objectIndex := none } }

private def sampleReaderV2 (key : ArtifactKey) : Option ByteArray :=
  if key.value == "blocks/p.ibk2" || key.value == "blocks/p-1.ibk2" then some sampleBlockBytes else none

/-- This remains structurally valid and carries the right artifact digest, but
    its planning cardinality is a lie. Admission must reject it rather than
    allowing an exact-estimate shortcut to influence join ordering. -/
private def sampleManifestWrongRows : Manifest :=
  match sampleManifest.entries with
  | entry :: _ => { sampleManifest with entries := [{ entry with rows := 2 }] }
  | [] => sampleManifest

/-! ## SBM7 samples

One IBK4 entry: no sidecar, a blank-node scope, and a two-member graph set
whose first member is the default graph, as an IBK4 header summary would give
it. -/

/-- A source file's SHA-256 as lowercase hexadecimal, the shape
    `l4block-shard-pack` writes into `blankNodeScope`. -/
private def sampleScope : String :=
  "0000000000000000000000000000000000000000000000000000000000000000"

private def sampleGraphSet : List GraphName :=
  [.defaultGraph, .iri ⟨"https://example.test/g1", by decide⟩]

private def sampleEntryV7 (entry : Entry) : Entry :=
  { entry with
    blockLayout := some BlockLayout.ibk4,
    blankNodeScope := sampleScope,
    graphSet := sampleGraphSet }

private def sampleManifestV7 : Manifest :=
  { version := 7,
    sourceIdentity := sampleManifestV1.sourceIdentity,
    termRegistryVersion := "local-ibk4-ptd1-v0",
    layout := "quad-ibk4-ptd1-merkle-v0",
    blankNodeProfile := "content-digest-shared",
    entries := sampleManifestV1.entries.map sampleEntryV7 }

private def sampleManifestV7BlankScope : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with blankNodeScope := "" } }

private def sampleManifestV7NoGraphSet : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with graphSet := [] } }

private def sampleManifestV7RepeatedGraph : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with graphSet := [.defaultGraph, .defaultGraph] } }

private def sampleManifestV7Ibk3Entry : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with blockLayout := some .ibk3 } }

private def sampleManifestV7UnknownProfile : Manifest :=
  { sampleManifestV7 with blankNodeProfile := "whatever" }

private def sampleManifestV7WithSidecar : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with subjectIndex := some { key := { value := "blocks/p.sri2" },
                                        bytes := sampleBlockBytes.size,
                                        sha256 := sampleDigest,
                                        chunked := some sampleChunked } } }

/-- An SBM6 manifest may not carry SBM7's fields: they would be dropped by the
    encoder and the round trip would silently lose them. -/
private def sampleManifestV6WithQuadFields : Manifest :=
  { sampleManifestV6 with entries := sampleManifestV6.entries.map fun entry =>
    { entry with blockLayout := some .ibk4 } }

#guard decode? (encode? sampleManifest |>.getD ByteArray.empty) == some sampleManifest
#guard decode? (encode? sampleManifestV1 |>.getD ByteArray.empty) == some sampleManifestV1
#guard decode? (encode? sampleManifestV2 |>.getD ByteArray.empty) == some sampleManifestV2
#guard decode? (encode? sampleManifestV3 |>.getD ByteArray.empty) == some sampleManifestV3
#guard decode? (encode? sampleManifestV4 |>.getD ByteArray.empty) == some sampleManifestV4
#guard decode? (encode? sampleManifestV5 |>.getD ByteArray.empty) == some sampleManifestV5
#guard decode? (encode? sampleManifestV6 |>.getD ByteArray.empty) == some sampleManifestV6
/-! ## SBM8 samples

SBM7 plus the LGI1 literal search index, which is mandatory at 8 and refused
before it. -/

private def sampleLiteralIndex : ArtifactRef :=
  { key := { value := "blocks/p.lgi1" }, bytes := sampleBlockBytes.size,
    sha256 := sampleDigest, chunked := some sampleChunked }

private def sampleManifestV8 : Manifest :=
  { sampleManifestV7 with
    version := 8,
    layout := "quad-ibk4-ptd1-lgi1-merkle-v0",
    entries := sampleManifestV7.entries.map fun entry =>
      { entry with literalIndex := some sampleLiteralIndex } }

private def sampleManifestV8MissingLiteralIndex : Manifest :=
  { sampleManifestV8 with entries := sampleManifestV8.entries.map fun entry =>
    { entry with literalIndex := none } }

private def sampleManifestV8OldLabel : Manifest :=
  { sampleManifestV8 with layout := "quad-ibk4-ptd1-merkle-v0" }

private def sampleManifestV8AliasedKey : Manifest :=
  { sampleManifestV8 with entries := sampleManifestV8.entries.map fun entry =>
    { entry with literalIndex := some { sampleLiteralIndex with key := entry.artifact.key } } }

/-- An SBM7 manifest may not carry SBM8's sidecar: the encoder would drop it. -/
private def sampleManifestV7WithLiteralIndex : Manifest :=
  { sampleManifestV7 with entries := sampleManifestV7.entries.map fun entry =>
    { entry with literalIndex := some sampleLiteralIndex } }

#guard decode? (encode? sampleManifestV7 |>.getD ByteArray.empty) == some sampleManifestV7
#guard decode? (encode? sampleManifestV8 |>.getD ByteArray.empty) == some sampleManifestV8
#guard rangeCommitted sampleManifestV8
#guard isIbk4Layout sampleManifestV8.layout
#guard layoutBlockKind sampleManifestV8.layout == some BlockLayout.ibk4
-- Every SBM8 admission condition refuses its own violation, on both sides.
#guard !(valid sampleManifestV8MissingLiteralIndex) &&
  (encode? sampleManifestV8MissingLiteralIndex).isNone
#guard !(valid sampleManifestV8OldLabel) && (encode? sampleManifestV8OldLabel).isNone
#guard !(valid sampleManifestV8AliasedKey) && (encode? sampleManifestV8AliasedKey).isNone
#guard !(valid sampleManifestV7WithLiteralIndex) &&
  (encode? sampleManifestV7WithLiteralIndex).isNone
-- SBM7 bytes are unchanged by SBM8's arrival: an old generation still reads.
#guard (encode? sampleManifestV7).isSome
#guard rangeCommitted sampleManifestV7
-- Every SBM7 admission condition refuses its own violation, on both sides.
#guard !(valid sampleManifestV7BlankScope) && (encode? sampleManifestV7BlankScope).isNone
#guard !(valid sampleManifestV7NoGraphSet) && (encode? sampleManifestV7NoGraphSet).isNone
#guard !(valid sampleManifestV7RepeatedGraph) && (encode? sampleManifestV7RepeatedGraph).isNone
#guard !(valid sampleManifestV7Ibk3Entry) && (encode? sampleManifestV7Ibk3Entry).isNone
#guard !(valid sampleManifestV7UnknownProfile) && (encode? sampleManifestV7UnknownProfile).isNone
#guard !(valid sampleManifestV7WithSidecar) && (encode? sampleManifestV7WithSidecar).isNone
#guard !(valid sampleManifestV6WithQuadFields) && (encode? sampleManifestV6WithQuadFields).isNone
-- SBM6 stays readable, and its bytes are unchanged by SBM7's arrival.
#guard (encode? sampleManifestV6).isSome
#guard GraphName.ofGraphRef none == GraphName.defaultGraph
#guard GraphName.ofGraphRef (some (.bnode "b0")) == GraphName.bnode "b0"
#guard !(valid sampleManifestV3MissingIndex)
#guard (encode? sampleManifestV3MissingIndex).isNone
#guard !(valid sampleManifestV6MissingObjectIndex)
#guard (encode? sampleManifestV6MissingObjectIndex).isNone
#guard (decode? (ByteArray.mk #[83, 66, 77, 48, 1])).isNone
#guard (scanPredicate? sampleReader sampleManifest samplePredicate).map List.length == some 1
#guard (scanPredicate? sampleReaderV2 sampleManifestV2 samplePredicate).map List.length == some 2
#guard (openStore? sampleReader sampleManifest).map
  (fun store => estimateBound { p := some samplePredicate } store) == some 1
#guard (openStore? sampleReaderV2 sampleManifestV2).map
  (fun store => estimateBound { p := some samplePredicate } store) == some 2
#guard (openStore? sampleReader sampleManifestWrongRows).isNone
#guard (scanPredicate? (fun _ => some ByteArray.empty) sampleManifest samplePredicate).isNone
#guard (openStore? sampleReader sampleManifest).map (fun store =>
  (readOps store).search { p := some samplePredicate } |>.length) == some 1
#guard (openStore? sampleReaderV2 sampleManifestV2).map (fun store =>
  (readOps store).search { p := some samplePredicate } |>.length) == some 2
#guard (openStoreForPredicates? sampleReader sampleManifest [samplePredicate]).map
  (fun store => store.blocks.length) == some 1
#guard queryNativeConstantPredicates?
  (mkQuery (.select .all) (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))
  == some [samplePredicate]

/-! https://github.com/danbri/factoidal/issues/638. `nativeConstantPredicates?`
sees only the WHERE clause, so the query-level entry point also refuses a
query whose HAVING, ORDER BY, GROUP BY key or SELECT projection carries an
EXISTS: §18.6 would evaluate it against the shards the pattern named instead
of the whole store. An aggregate in the same positions is NOT a reason to
refuse — it reads no triples. -/
private def selectiveBgp : QueryPattern :=
  .bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]
private def otherPredicateBgp : QueryPattern :=
  .bgp [{ s := .var "s", p := .iri sampleOtherPredicate, o := .var "z" }]
private def countStarItems : List SelectItem :=
  [.var "s", .expr (.aggregate .count false (.var "*")) "n"]

-- COUNT(*) in the projection with a GROUP BY key: still selective.
#guard queryNativeConstantPredicates?
  (mkQuery (.select (.vars countStarItems)) selectiveBgp
    (groupBy := some [.var "s"]))
  == some [samplePredicate]
-- HAVING EXISTS over the other predicate: refused.
#guard (queryNativeConstantPredicates?
  (mkQuery (.select (.vars countStarItems)) selectiveBgp
    (groupBy := some [.var "s"])
    (having := [.existsPat otherPredicateBgp]))).isNone
-- ORDER BY EXISTS: refused.
#guard (queryNativeConstantPredicates?
  (mkQuery (.select .all) selectiveBgp
    (modifier := { orderBy := some [.asc (.existsPat otherPredicateBgp)] }))).isNone
-- NOT EXISTS in a projected expression: refused.
#guard (queryNativeConstantPredicates?
  (mkQuery (.select (.vars [.var "s", .expr (.notExistsPat otherPredicateBgp) "e"]))
    selectiveBgp)).isNone
-- EXISTS in a GROUP BY key: refused.
#guard (queryNativeConstantPredicates?
  (mkQuery (.select .all) selectiveBgp
    (groupBy := some [.expr (.existsPat otherPredicateBgp) (some "g")]))).isNone
-- A sub-SELECT reaches an expression only through EXISTS, which is already
-- refused; the wrapper form is pinned too.
#guard (queryNativeConstantPredicates?
  (mkQuery (.select .all) selectiveBgp
    (having := [.and (.boolLit true)
                 (.existsPat (.subSelect (mkQuery (.select .all) otherPredicateBgp)))]))).isNone
#guard (nativeConstantPredicates? (.filter (.boolLit true)
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))
  == some [samplePredicate])
#guard (nativeConstantPredicates? (.filter (.existsPat .empty)
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))).isNone
#guard (nativeConstantPredicates? (.leftJoin
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o1" }])
  (.bgp [{ s := .var "s", p := .iri sampleOtherPredicate, o := .var "o2" }])
  (.boolLit true))
  == some [samplePredicate, sampleOtherPredicate])
#guard (nativeConstantPredicates? (.leftJoin
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o1" }])
  (.bgp [{ s := .var "s", p := .iri sampleOtherPredicate, o := .var "o2" }])
  (.existsPat .empty))).isNone
-- `isIRI(?o1)` is a §17.4.2 node test: term-only, so it stays selective.
#guard (nativeConstantPredicates? (.filter (.isIri (.var "o1")) (.leftJoin
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o1" }])
  (.bgp [{ s := .var "s", p := .iri sampleOtherPredicate, o := .var "o2" }])
  (.boolLit true)))
  == some [samplePredicate, sampleOtherPredicate])

/-! §18.6 BIND. `UCASE(SUBSTR(STR(?o), 1, 1))` is the shape the UK Parliament
first-letter query uses: three §17.4.2/§17.4.3 forms over one variable, so it
reads no triple and the sub-pattern's one predicate is the whole read set. An
EXISTS in the same position reads triples and must refuse. -/
#guard (nativeConstantPredicates? (.bind
  (.uCase (.substr (.str (.var "o")) (.numericLit 1) (some (.numericLit 1)))) "first"
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))
  == some [samplePredicate])
#guard (nativeConstantPredicates? (.bind (.existsPat .empty) "x"
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }]))).isNone

/-! §18.4 property paths. A sequence, an alternative and an inverse of
constant IRIs contribute their step IRIs; `*`, `+`, `?` and a negated set are
refused. -/
#guard (constantPathPredicates? (.sequence (.iri samplePredicate) (.iri sampleOtherPredicate))
  == some [samplePredicate, sampleOtherPredicate])
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.sequence (.iri samplePredicate) (.iri sampleOtherPredicate)) (.var "o"))
  == some [samplePredicate, sampleOtherPredicate])
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.alternative (.iri samplePredicate) (.inverse (.iri sampleOtherPredicate))) (.var "o"))
  == some [samplePredicate, sampleOtherPredicate])
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.zeroOrMore (.iri samplePredicate)) (.var "o"))).isNone
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.oneOrMore (.iri samplePredicate)) (.var "o"))).isNone
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.zeroOrOne (.iri samplePredicate)) (.var "o"))).isNone
#guard (nativeConstantPredicates? (.propertyPath (.var "s")
  (.negatedSet [.iri samplePredicate]) (.var "o"))).isNone
/-! A path step inside a MINUS still restricts, which is the shape of the UK
Parliament "work packages current" count query. -/
#guard (nativeConstantPredicates? (.minus
  (.bgp [{ s := .var "s", p := .iri samplePredicate, o := .var "o" }])
  (.propertyPath (.var "s") (.sequence (.iri sampleOtherPredicate)
    (.iri samplePredicate)) (.var "o")))
  == some [samplePredicate, sampleOtherPredicate, samplePredicate])

/-! ## SBM7 entry selection -/

private def sampleG1 : WfIri := ⟨"https://example.test/g1", by decide⟩
private def sampleG2 : WfIri := ⟨"https://example.test/g2", by decide⟩

private def sampleTp : TriplePattern :=
  { s := .var "s", p := .iri samplePredicate, o := .var "o" }
private def sampleOtherTp : TriplePattern :=
  { s := .var "s", p := .iri sampleOtherPredicate, o := .var "o" }
private def sampleVarTp : TriplePattern :=
  { s := .var "s", p := .var "p", o := .var "o" }

/-! A pattern outside a `GRAPH` clause reads the default graph. -/
#guard queryGraphNames? (mkQuery (.select .all) (.bgp [sampleVarTp]))
  == some [GraphName.defaultGraph]

/-! `GRAPH <g1> { ... }` reads `g1` and nothing else; a nested `GRAPH` adds
its own name; a union of two `GRAPH` clauses reads both. -/
#guard queryGraphNames? (mkQuery (.select .all)
  (.graph (.iri sampleG1) (.bgp [sampleVarTp]))) == some [GraphName.iri sampleG1]
#guard queryGraphNames? (mkQuery (.select .all)
  (.graph (.iri sampleG1) (.graph (.iri sampleG2) (.bgp [sampleVarTp]))))
  == some [GraphName.iri sampleG1, GraphName.iri sampleG2]
#guard queryGraphNames? (mkQuery (.select .all)
  (.union (.graph (.iri sampleG1) (.bgp [sampleVarTp]))
          (.graph (.iri sampleG2) (.bgp [sampleVarTp]))))
  == some [GraphName.iri sampleG1, GraphName.iri sampleG2]

/-! `GRAPH <g1> { }` still needs `g1` in the dataset — section 18.6 gives it
one solution exactly when the dataset names that graph. -/
#guard queryGraphNames? (mkQuery (.select .all)
  (.graph (.iri sampleG1) .empty)) == some [GraphName.iri sampleG1]

/-! `GRAPH ?g`, a sub-SELECT and a `FROM` clause each establish nothing. -/
#guard (queryGraphNames? (mkQuery (.select .all)
  (.graph (.var "g") (.bgp [sampleVarTp])))).isNone
#guard (queryGraphNames? (mkQuery (.select .all)
  (.subSelect (mkQuery (.select .all) (.bgp [sampleVarTp]))))).isNone
#guard (queryGraphNames? (mkQuery (.select .all) (.bgp [sampleVarTp])
  [DatasetClause.default sampleG1])).isNone

/-! The quad predicate collector descends through both `GRAPH` forms, and
refuses the two patterns that observe a graph name without reading a row. -/
#guard queryQuadConstantPredicates? (mkQuery (.select .all)
  (.graph (.iri sampleG1) (.bgp [sampleTp]))) == some [samplePredicate]
#guard queryQuadConstantPredicates? (mkQuery (.select .all)
  (.graph (.var "g") (.bgp [sampleTp]))) == some [samplePredicate]
#guard (queryQuadConstantPredicates? (mkQuery (.select .all)
  (.graph (.iri sampleG1) .empty))).isNone
#guard (queryQuadConstantPredicates? (mkQuery (.select .all)
  (.graph (.iri sampleG1) (.bgp [])))).isNone
#guard (queryQuadConstantPredicates? (mkQuery (.select .all)
  (.bgp [sampleVarTp]))).isNone

/-! Two IBK4 entries: `samplePredicate` with rows in the default graph and in
`g1`, `sampleOtherPredicate` with rows in `g2` only. -/
private def quadEntryA (entry : Entry) : Entry :=
  { entry with
    blockLayout := some BlockLayout.ibk4,
    blankNodeScope := sampleScope,
    graphSet := [.defaultGraph, .iri sampleG1],
    ordinal := 0 }
private def quadEntryB (entry : Entry) : Entry :=
  { entry with
    predicate := sampleOtherPredicate,
    artifact := { entry.artifact with key := { value := "blocks/q.ibk4" } },
    blockLayout := some BlockLayout.ibk4,
    blankNodeScope := sampleScope,
    graphSet := [.iri sampleG2],
    ordinal := 1 }

private def sampleQuadManifest : Manifest :=
  match sampleManifestV7.entries with
  | entry :: _ => { sampleManifestV7 with entries := [quadEntryA entry, quadEntryB entry] }
  | [] => sampleManifestV7

#guard valid sampleQuadManifest

/-! A constant predicate outside a `GRAPH` clause selects its one entry. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.bgp [sampleTp]))).map Entry.predicate == [samplePredicate]

/-! Both collectors at once: the predicate names one entry and `GRAPH <g2>`
names the same one. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.graph (.iri sampleG2) (.bgp [sampleOtherTp])))).map
  Entry.predicate == [sampleOtherPredicate]

/-! `GRAPH <g1>` with an unbound predicate selects the one entry whose
manifest graph set names `g1`, with no block read. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.graph (.iri sampleG1) (.bgp [sampleVarTp])))).map
  Entry.predicate == [samplePredicate]

/-! `GRAPH ?g` establishes no graph restriction, so both entries stay. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.graph (.var "g") (.bgp [sampleVarTp])))).length == 2

/-! A default-graph pattern drops the entry that carries no default-graph
row. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.bgp [sampleVarTp]))).map Entry.predicate
  == [samplePredicate]

/-! An EXISTS in the ORDER BY disables both collectors. -/
#guard (quadEntriesForQuery sampleQuadManifest
  (mkQuery (.select .all) (.bgp [sampleTp]) [] none []
    { orderBy := some [.asc (.existsPat (.bgp [sampleOtherTp]))] })).length == 2

end L4Factoidal.Storage.ShardManifest
