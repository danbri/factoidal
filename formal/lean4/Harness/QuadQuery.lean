/- SPARQL over an activated SBM7 generation of IBK4 quad blocks.

   `l4block-id-v3-query` reads IBK3 generations and refuses SBM7 by layout
   (commit 37a4592cb). This is its quad sibling rather than another arm of it,
   for two reasons that are about structure, not taste:

   * every selective access path in the IBK3 tool is driven by an SRI2, OLI2
     or TLI1 sidecar, and SBM7 admits NO index sidecar (specification section
     6.3.1, admission rule 2) — the graph-aware sidecars are the next piece of
     work;
   * the IBK3 tool threads a `List Triple` and a resolved DLOG overlay through
     about fifteen call sites, and an IBK4 generation yields a DATASET and
     carries no delta log.

   Sharing the two would mean making every one of those sites
   dataset-or-triples polymorphic to reach one shared `finish`. When the
   graph-aware sidecars land, the selective paths are what the two tools would
   share, and that is the point to revisit it.

   THIS STEP IS THE FULL-MANIFEST PATH ONLY. Every selected entry is read
   whole, verified, decoded and materialised; block SELECTION is what makes it
   less than the whole store (`ShardManifest.quadEntriesForQuery`). No
   `partial`, no `sorry`, no `native_decide`. -/
import Harness.GenerationPointer
import Harness.NativeHasher
import L4Factoidal.RDF.DatasetGraphs
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Geo.Functions
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.ShardManifest

namespace Harness.QuadQuery

open Harness.GenerationPointer
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.QuadDataset
open L4Factoidal.Storage.ShardManifest

/-- Manifest artifact keys denote leaf files, never paths supplied by a query.
    The same admission rule as `IndexedBlockV3Materialize.safeLeafKey`. -/
private def safeLeafKey (key : ArtifactKey) : Bool :=
  !key.value.isEmpty && !(key.value.contains '/') && !(key.value.contains '\\')

/-! ## Reading a selected entry

Integrity before decode, with the native hasher activation uses. The whole
artifact is read on this path, so its declared extent, its full SHA-256 and
its fixed-chunk Merkle commitment are all checked over the bytes just read —
the same three commitments `ShardActivate.verifyFullArtifact` checks, minus
the `.merkle` leaf-file comparison, which restates the root it recomputes. -/

private def artifactAdmitted (entry : Entry) (bytes : ByteArray) : Bool :=
  match entry.artifact.chunked with
  | none => false
  | some chunks =>
      bytes.size == entry.artifact.bytes &&
        L4Factoidal.Storage.BlockArtifact.verifyWith Harness.nativeHasher
          entry.artifact.sha256 bytes &&
        L4Factoidal.Storage.ChunkedArtifact.fromChunksWith? Harness.nativeHasher
          chunks.chunkBytes
          (L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes)
          == some chunks

/-- Decode one entry into the quads it denotes. `none` on any I/O, integrity
    or decode failure; the caller reports it as one refusal rather than
    answering from a partially trusted generation. -/
private def readEntry (directory : System.FilePath) (entry : Entry) :
    IO (Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow × Nat)) := do
  if !safeLeafKey entry.artifact.key then pure none else
  try
    let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
    if !artifactAdmitted entry bytes then pure none else
    match L4Factoidal.Storage.IndexedBlockWireV4.decode bytes with
    | none => pure none
    | some block =>
        if block.rows.size != entry.rows then pure none else
        pure (some (block.denotes, bytes.size))
  catch _ => pure none

/-! ## SBM10 entries and their out-of-line literals

An IBK5 block denotes quads whose object may be a `WireTerm.blob`: the block
names a byte extent and a SHA-256 digest, and the lexical form is one
`blob-<hex>.lit` artifact beside it. `IndexedBlockWireV5.resolveBlock` turns
those into RDF terms through a lookup, and refuses missing bytes, a wrong byte
count, a wrong digest and invalid UTF-8 — so a blob file that does not match
its term refuses the query rather than answering with a fabricated literal.

The lookup is backed by a cache held for the whole query, so one blob is read
once however many blocks name it. That is what content addressing buys: the
same large literal in twenty blocks is one file and one read. -/

abbrev BlobCache := Std.HashMap (List UInt8) ByteArray

/-- Fetch every blob one block names that the cache does not hold. A blob that
    cannot be read is left out; `resolve` then refuses the block. -/
private def fetchBlobs (directory : System.FilePath) (cache : BlobCache) :
    List ByteArray → IO BlobCache
  | [] => pure cache
  | digest :: rest => do
      if cache.contains digest.toList then fetchBlobs directory cache rest else
      let name := blobKeyOf digest
      let next ← try
          let bytes ← IO.FS.readBinFile (directory / name)
          pure (cache.insert digest.toList bytes)
        catch _ => pure cache
      fetchBlobs directory next rest

private def readEntryV5 (directory : System.FilePath) (cache : BlobCache) (entry : Entry) :
    IO (Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow × Nat × BlobCache)) := do
  if !safeLeafKey entry.artifact.key then pure none else
  try
    let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
    if !artifactAdmitted entry bytes then pure none else
    match L4Factoidal.Storage.IndexedBlockWireV5.decode bytes with
    | none => pure none
    | some block =>
        if block.rows.size != entry.rows then pure none else
        let cache ← fetchBlobs directory cache
          (L4Factoidal.Storage.IndexedBlockWireV5.blobDigests block)
        match L4Factoidal.Storage.IndexedBlockWireV5.resolveBlock Harness.nativeHasher.digest
            (fun d => cache[d.toList]?) block with
        | none => pure none
        | some quads => pure (some (quads, bytes.size, cache))
  catch _ => pure none

private def readEntriesV5 (directory : System.FilePath) :
    List Entry → List (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) → Nat →
    BlobCache → IO (Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow × Nat))
  | [], chunksRev, bytes, _ => pure (some (chunksRev.reverse.flatten, bytes))
  | entry :: rest, chunksRev, bytes, cache => do
      match ← readEntryV5 directory cache entry with
      | none => pure none
      | some (current, size, cache) =>
          readEntriesV5 directory rest (current :: chunksRev) (bytes + size) cache

/-- The selected entries, read in manifest order. Each entry's rows are kept
    as one chunk and the chunks are flattened once at the end: appending the
    running list per entry is quadratic in the entry count, and an SBM7
    generation of a large corpus now selects thousands of entries rather than
    one per predicate (`docs/designissues/2026-09-04-blocks-per-predicate.md`). -/
private def readEntries (directory : System.FilePath) :
    List Entry → List (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) → Nat →
    IO (Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow × Nat))
  | [], chunksRev, bytes => pure (some (chunksRev.reverse.flatten, bytes))
  | entry :: rest, chunksRev, bytes => do
      match ← readEntry directory entry with
      | none => pure none
      | some (current, size) => readEntries directory rest (current :: chunksRev) (bytes + size)

/-! ## Quads to an RDF dataset

`Storage/QuadDataset.lean` owns this: the WASM store operations
(`Wasm/Ops/Store.lean`) read the same generations and must answer the same
dataset. -/

/-! ## Evaluation

The dataset seam of `SPARQL/StoreDataset.lean` gives `GRAPH <iri>` its own
backend natively and materialises for every other arm, so `GRAPH ?g`,
`MINUS`, `EXISTS` and a sub-SELECT all reach the reference evaluator with the
whole dataset. Two things it cannot carry, so they are handled here:

* `FROM` / `FROM NAMED`. `runSelectQueryBackendDataset` does not apply
  `query.dataset`; §13.2's `applyDataset` is applied to the materialised
  dataset first, and the query is then evaluated with no dataset clause.
* A blank-node graph NAME. `materialiseDatasetBackend` keeps only graphs whose
  name is a well-formed IRI, so a generation with a blank-node-named graph
  would lose it in every delegating arm. SBM7 admits such a name
  (`GraphName.bnode`), so such a generation takes the reference evaluator
  directly over the materialised dataset instead. -/

private def stripDatasetClauses (query : Query) : Query :=
  .mk query.form [] query.pattern query.groupBy query.having query.modifier
      query.postValues query.base

private def previewOf (rows : SolutionSeq) : String :=
  toString (repr (rows.take 10))

/-- `zoneExcluded` is how many entries the predicate and graph collectors kept
    and the SBM10 zone maps then dropped. It is zero for every generation
    below version 10, which carries no zone map. -/
private def header (entries : List Entry) (mode : String) (graphs : Nat)
    (bytes : Nat) (zoneExcluded : Nat) : String :=
  s!"l4block-quad-query shards={entries.length} open-mode={mode}({entries.length}) graphs={graphs} logical-read-bytes={bytes} fetched-bytes={bytes} zone-excluded={zoneExcluded}"

private def finish (query : Query) (entries : List Entry) (codec : String) (ds : Dataset)
    (bytes : Nat) (zoneExcluded : Nat) : IO UInt32 := do
  let (applied, _) := applyDataset query.dataset ds ds.default
  let stripped := stripDatasetClauses query
  -- §18.6: EXISTS / NOT EXISTS evaluate against the query's dataset, which
  -- the backend runners read from `env.dataset`. It is the SAME dataset the
  -- backend answers from, so an EXISTS sub-pattern sees exactly the
  -- materialised generation.
  -- §17.6 extension functions: the GeoSPARQL simple-features predicates, so
  -- a `geof:sf*` FILTER is evaluated here rather than being a type error.
  -- `Geo.extFns` refuses every IRI outside the `geof:` namespace, which is
  -- what §17.6 requires of an unregistered IRI.
  let env : EvalEnv := { emptyEnv with dataset := some applied, ext := L4Factoidal.Geo.extFns }
  let indexed := namesAreIris applied
  let mode := if indexed then codec ++ "-full-manifest" else codec ++ "-full-manifest-reference"
  let graphs := applied.named.length
  match query.form with
  | .select _ =>
      let rows? :=
        if indexed then runSelectQueryBackendDataset env stripped (indexedDatasetBackend applied)
        else some (evalSelect env applied stripped).2
      match rows? with
      | none => IO.eprintln "l4block-quad-query failed: query was not evaluated as SELECT"; return 1
      | some rows =>
          IO.println (header entries mode graphs bytes zoneExcluded)
          IO.println s!"l4block-quad-query sse={query.toSse}"
          IO.println s!"l4block-quad-query rows={rows.length} preview={previewOf rows}"
          return 0
  | .ask =>
      let answer? :=
        if indexed then runAskQueryBackendDataset env stripped (indexedDatasetBackend applied)
        else some (evalAsk env applied stripped)
      match answer? with
      | none => IO.eprintln "l4block-quad-query failed: query was not evaluated as ASK"; return 1
      | some answer =>
          IO.println (header entries mode graphs bytes zoneExcluded)
          IO.println s!"l4block-quad-query sse={query.toSse}"
          IO.println s!"l4block-quad-query boolean={answer}"
          return 0
  | .construct _ =>
      let graph := evalConstruct env applied stripped
      IO.println (header entries mode graphs bytes zoneExcluded)
      IO.println s!"l4block-quad-query sse={query.toSse}"
      IO.println s!"l4block-quad-query triples={graph.length} preview={toString (repr (graph.take 10))}"
      return 0
  | .describe _ =>
      IO.eprintln "l4block-quad-query rejected: DESCRIBE needs an explicit description policy"
      return 1

/-- The zone-map key function: the canonical version-2 wire bytes of a term,
    which are the bytes the packer compared when it computed an entry's zone
    bounds (`ShardManifest.quadEntriesForQueryWithKeys`). A key function that
    disagreed with the packer's would drop entries holding matching rows, so
    this is `TermWireV2.keyBytes (TermWireV2.toWire h t)` and nothing else. -/
private def zoneTermKey (t : Term) : Option (List UInt8) :=
  L4Factoidal.Storage.TermWireV2.keyBytes
    (L4Factoidal.Storage.TermWireV2.toWire Harness.nativeHasher.digest t)

private def run (directoryText queryText : String) : IO UInt32 := do
  try
    let root := System.FilePath.mk directoryText
    let directory ← resolveStoreDirectory root
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
    match decode? manifestBytes with
    | none => IO.eprintln "l4block-quad-query rejected: malformed SBM7 manifest"; return 1
    | some manifest =>
        let ibk5 := manifest.version == 10 && isIbk5Layout manifest.layout
        let ibk4 := (manifest.version == 7 || manifest.version == 8 || manifest.version == 9) &&
          isIbk4Layout manifest.layout
        /- A version-10 generation can hold an RDF 1.2 triple term and a
           directional literal, so its queries are read as SPARQL 1.2, which
           is what makes `LANGDIR`, `hasLANGDIR`, `STRLANGDIR` and the triple
           term syntax available. Every earlier generation keeps SPARQL 1.1,
           where those spellings are prefixed names. -/
        match parseSparql queryText none (if ibk5 then .v12 else .v11) with
        | .error error =>
            IO.eprintln s!"l4block-quad-query query parse error at {error.pos}: {error.msg}"
            return 1
        | .ok query =>
        if !ibk4 && !ibk5 then
          IO.eprintln "l4block-quad-query rejected: not an SBM7, SBM8, SBM9 or SBM10 generation of quad blocks; use l4block-id-v3-query for an IBK3 generation"
          return 1
        if !rangeCommitted manifest then
          IO.eprintln "l4block-quad-query rejected: candidate manifest has no Merkle range commitment"
          return 1
        if !(← (root / currentName).pathExists) then
          IO.eprintln "l4block-quad-query rejected: SBM7 requires an activated collection root (CURRENT)"
          return 1
        /- Block selection. The predicate and graph-name collectors run for
           every version; the zone maps only exclude an entry of a version-10
           generation, because no earlier entry carries one. -/
        let withoutZones := quadEntriesForQuery manifest query
        let entries := quadEntriesForQueryWithKeys zoneTermKey manifest query
        let zoneExcluded := withoutZones.length - entries.length
        let read ← if ibk5 then readEntriesV5 directory entries [] 0 ∅
                   else readEntries directory entries [] 0
        match read with
        | none =>
            IO.eprintln "l4block-quad-query rejected: malformed or unavailable committed quad artifact"
            return 1
        | some (quads, bytes) =>
            finish query entries (if ibk5 then "ibk5" else "ibk4") (datasetOfQuads quads)
              bytes zoneExcluded
  catch error => IO.eprintln s!"l4block-quad-query failure: {error}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-quad-query requires a query"; return 2
      else run directory (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-quad-query COLLECTION-ROOT --query SELECT..."; return 2

end Harness.QuadQuery

def main (args : List String) : IO UInt32 := Harness.QuadQuery.main args
