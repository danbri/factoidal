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
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.IndexedBlockWireV4
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

private def header (entries : List Entry) (mode : String) (graphs : Nat)
    (bytes : Nat) : String :=
  s!"l4block-quad-query shards={entries.length} open-mode={mode}({entries.length}) graphs={graphs} logical-read-bytes={bytes} fetched-bytes={bytes}"

private def finish (query : Query) (entries : List Entry) (ds : Dataset) (bytes : Nat) :
    IO UInt32 := do
  let (applied, _) := applyDataset query.dataset ds ds.default
  let stripped := stripDatasetClauses query
  -- §18.6: EXISTS / NOT EXISTS evaluate against the query's dataset, which
  -- the backend runners read from `env.dataset`. It is the SAME dataset the
  -- backend answers from, so an EXISTS sub-pattern sees exactly the
  -- materialised generation.
  let env : EvalEnv := { emptyEnv with dataset := some applied }
  let indexed := namesAreIris applied
  let mode := if indexed then "ibk4-full-manifest" else "ibk4-full-manifest-reference"
  let graphs := applied.named.length
  match query.form with
  | .select _ =>
      let rows? :=
        if indexed then runSelectQueryBackendDataset env stripped (indexedDatasetBackend applied)
        else some (evalSelect env applied stripped).2
      match rows? with
      | none => IO.eprintln "l4block-quad-query failed: query was not evaluated as SELECT"; return 1
      | some rows =>
          IO.println (header entries mode graphs bytes)
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
          IO.println (header entries mode graphs bytes)
          IO.println s!"l4block-quad-query sse={query.toSse}"
          IO.println s!"l4block-quad-query boolean={answer}"
          return 0
  | .construct _ =>
      let graph := evalConstruct env applied stripped
      IO.println (header entries mode graphs bytes)
      IO.println s!"l4block-quad-query sse={query.toSse}"
      IO.println s!"l4block-quad-query triples={graph.length} preview={toString (repr (graph.take 10))}"
      return 0
  | .describe _ =>
      IO.eprintln "l4block-quad-query rejected: DESCRIBE needs an explicit description policy"
      return 1

private def run (directoryText queryText : String) : IO UInt32 := do
  try
    let root := System.FilePath.mk directoryText
    let directory ← resolveStoreDirectory root
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-quad-query rejected: malformed SBM7 manifest"; return 1
    | _, .error error =>
        IO.eprintln s!"l4block-quad-query query parse error at {error.pos}: {error.msg}"; return 1
    | some manifest, .ok query =>
        if (manifest.version != 7 && manifest.version != 8) || !isIbk4Layout manifest.layout then
          IO.eprintln "l4block-quad-query rejected: not an SBM7 or SBM8 generation of IBK4 quad blocks; use l4block-id-v3-query for an IBK3 generation"
          return 1
        if !rangeCommitted manifest then
          IO.eprintln "l4block-quad-query rejected: candidate manifest has no Merkle range commitment"
          return 1
        if !(← (root / currentName).pathExists) then
          IO.eprintln "l4block-quad-query rejected: SBM7 requires an activated collection root (CURRENT)"
          return 1
        let entries := quadEntriesForQuery manifest query
        match ← readEntries directory entries [] 0 with
        | none =>
            IO.eprintln "l4block-quad-query rejected: malformed or unavailable committed IBK4 artifact"
            return 1
        | some (quads, bytes) => finish query entries (datasetOfQuads quads) bytes
  catch error => IO.eprintln s!"l4block-quad-query failure: {error}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-quad-query requires a query"; return 2
      else run directory (String.intercalate " " queryParts)
  | _ => IO.eprintln "usage: l4block-quad-query COLLECTION-ROOT --query SELECT..."; return 2

end Harness.QuadQuery

def main (args : List String) : IO UInt32 := Harness.QuadQuery.main args
