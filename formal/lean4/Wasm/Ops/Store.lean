/-
Wasm.Ops.Store — SPARQL over a Shardborough generation whose bytes a
JavaScript host reads.

The WASM module has no file system: it is linked without libuv and Lean's IO
layer reaches no host facility (`Wasm/l4_stubs.c` stubs exactly one symbol).
So the host must do the file reads. Iron rule 7 of CLAUDE.md forbids
hand-written JavaScript that reimplements what the formal source defines, so
the host must never parse a manifest, verify a digest or interpret a block.
These three operations are what let it avoid doing any of that: it reads files
by name and carries bytes, and every decision stays in Lean.

  storeManifestInspect(manifestHex)
    -> {"ok":true,"wireVersion":N,"layout":"…","blankNodeProfile":"…",
        "termRegistryVersion":"…","rangeCommitted":true|false,
        "totalBytes":N,"totalRows":N,
        "entries":[{"ordinal":N,"predicate":"…","key":"…","bytes":N,
                    "sha256":"…","chunkBytes":N,"chunkCount":N,
                    "merkleRoot":"…","rows":N,"blockKind":"IBK3"|"IBK4",
                    "blankNodeScope":"…",
                    "graphs":[{"kind":"default"|"iri"|"bnode","value":"…"}],
                    "sidecars":{"subjectIndex":"…","termIndex":"…",
                                "objectIndex":"…"}}, …]}
     | {"ok":false,"error":"…"}

  storeQueryPlan(manifestHex, sparql)
    -> {"ok":true,"wireVersion":N,"layout":"…","mode":"…","shards":N,
        "keys":["…", …],"bytes":N,"rows":N}
     | {"ok":false,"error":"…"}

  storeQuery(manifestHex, sparql, artifactsJson) + one blob region
    -> the ordinary queryDataset SELECT / ASK / CONSTRUCT envelope, with
       "shards":N and "mode":"…" placed before "kind"
     | {"ok":false,"error":"…"}

## How artifact bytes cross the boundary

`artifactsJson` is a JSON array of artifact descriptors. Each one names its
manifest key and says where its bytes are:

  {"key":"predicate-0.ibk3","offset":0,"len":41230}   -- the blob path
  {"key":"predicate-0.ibk3","bytes":"<hex>"}          -- the diagnostic path

The BLOB PATH is what a host uses. The caller allocates ONE buffer inside the
wasm heap (`_malloc`), writes every artifact's bytes into it back to back with
no encoding at all, and passes it to `l4_call_blob_c`; the C shim copies that
region once into a Lean `ByteArray` and hands it over as a value. Each
descriptor is then a bounds-checked window into that `ByteArray`.

Two properties follow, and they are why this shape was chosen over a
pointer/length pair or a blob-handle table:

* Lean never receives a host pointer, so a stale or out-of-range pointer
  cannot exist. An offset outside the blob is an ordinary refusal
  (`storeQuery: artifact 'k' names blob bytes …`), never a memory fault.
* Nothing has a lifetime the host must track. A handle table would need
  mutable state in the shim and a second free the host could forget; the
  region is copied on entry and the host's buffer can be freed immediately
  after the call returns.

The `"bytes"` hexadecimal form is kept because it costs eight lines and it is
what makes `storeQuery` answerable through the plain `l4_call` / `l4wasm-cli
call` entry, which carries no blob — it is for diagnostics and small
fixtures. It doubles the bytes over the boundary and walks every character on
the way in, so a host must not use it.

The manifest stays a hexadecimal string in all three operations: it is a few
kilobytes, and one encoding for the small argument keeps the three signatures
uniform.

## What `storeQuery` checks before it answers

1. The manifest decodes and is admitted (`ShardManifest.decode?`, which
   returns `none` for a manifest `valid` refuses).
2. The manifest carries a fixed-chunk Merkle commitment (`rangeCommitted`),
   which every layout the packer writes does.
3. Each supplied artifact's byte length and SHA-256 match its manifest entry.
   A mismatch names the key and refuses the whole query — no partially trusted
   generation is answered from. The SHA-256 is the pure Lean `Crypto.sha256`,
   the specification hash of section 6.3 of `docs/shardborough-storage-spec.md`.
   The chunk Merkle ROOT is not recomputed here: this operation reads whole
   artifacts, so the full-artifact digest already covers every byte, and a
   second pass would double the hashing cost of the pure hasher. A host that
   fetches RANGES rather than whole artifacts needs the Merkle path and is not
   this operation.
4. Each block decodes under the codec its manifest layout names, and its
   decoded row count equals the entry's declared `rows` — the same admission
   `Harness/QuadQuery.lean` and `Harness/IndexedBlockV3Materialize.lean`
   apply natively.

## Caps

A cap trip is an explicit error naming the cap; nothing is ever truncated
silently (anti-pattern 25).

| Cap | Value | Checked against |
|---|---|---|
| selected artifacts | 64 | the plan's entry count |
| total artifact bytes | 8388608 (8 MiB) | the manifest's declared byte extents, and again the supplied hex lengths |
| total rows | 100000 | the manifest's declared row counts |

8 MiB is the same byte budget `queryIBK3BlockSetPreview` carries, and it is
set by the cost of the pure Lean SHA-256 rather than by memory: the hash is
the dominant term in a whole-artifact admission.

## What this operation is NOT

* It reads the manifest's committed artifacts only. A generation carrying a
  non-empty DLOG delta overlay is NOT served: this operation has no way to see
  one, and answering the base generation as though it were current would be
  wrong. A host with a delta log uses the native tools.
* It is the full-artifact path. Every selected block is read whole; block
  SELECTION (`ShardManifest.quadEntriesForQuery`,
  `ShardManifest.queryNativeConstantPredicates?`) is what makes it less than
  the whole generation. The selective sidecar paths of
  `Harness/IndexedBlockV3Query.lean` need range reads and are not offered here.

No `partial`, no `sorry`, no `native_decide`.
-/
import Wasm.Ops.Support
import Wasm.Ops.Query
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.ShardManifest

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.QuadDataset
open L4Factoidal.JSON

/-! ## Caps -/

/-- At most this many manifest entries may be selected for one `storeQuery`. -/
def maxStoreArtifacts : Nat := 64

/-- At most this many artifact bytes may be admitted by one `storeQuery`. -/
def maxStoreBytes : Nat := 8 * 1024 * 1024

/-- At most this many block rows may be materialised by one `storeQuery`. -/
def maxStoreRows : Nat := 100000

/-! ## Manifest inspection -/

private def graphNameJson (name : GraphName) : Json :=
  match name with
  | .defaultGraph => .object [("kind", .string "default"), ("value", .string "")]
  | .iri value => .object [("kind", .string "iri"), ("value", .string value.val)]
  | .bnode label => .object [("kind", .string "bnode"), ("value", .string label)]

/-- The block codec of one entry. SBM7 names it per entry; before SBM7 the
    manifest layout label is the only statement of it. -/
def entryBlockKind (manifest : Manifest) (entry : Entry) : String :=
  match entry.blockLayout with
  | some .ibk4 => "IBK4"
  | some .ibk3 => "IBK3"
  | none => if isIbk3Layout manifest.layout then "IBK3" else "IBK2"

private def sidecarMembers (entry : Entry) : List (String × Json) :=
  (entry.subjectIndex.map fun r => ("subjectIndex", Json.string r.key.value)).toList ++
  (entry.termIndex.map fun r => ("termIndex", Json.string r.key.value)).toList ++
  (entry.objectIndex.map fun r => ("objectIndex", Json.string r.key.value)).toList

private def chunkMembers (entry : Entry) : List (String × Json) :=
  match entry.artifact.chunked with
  | none => []
  | some chunks =>
      [ ("chunkBytes", .number (toString chunks.chunkBytes))
      , ("chunkCount", .number (toString chunks.chunkCount))
      , ("merkleRoot", .string (hexOfBytes chunks.root)) ]

private def entryJson (manifest : Manifest) (entry : Entry) : Json :=
  .object
    ([ ("ordinal", .number (toString entry.ordinal))
     , ("predicate", .string entry.predicate.val)
     , ("key", .string entry.artifact.key.value)
     , ("bytes", .number (toString entry.artifact.bytes))
     , ("sha256", .string (hexOfBytes entry.artifact.sha256)) ] ++
     chunkMembers entry ++
     [ ("rows", .number (toString entry.rows))
     , ("blockKind", .string (entryBlockKind manifest entry))
     , ("blankNodeScope", .string entry.blankNodeScope)
     , ("graphs", .array (entry.graphSet.map graphNameJson))
     , ("sidecars", .object (sidecarMembers entry)) ])

private def totalBytesOf (entries : List Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.artifact.bytes) 0

private def totalRowsOf (entries : List Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.rows) 0

private def decodeManifest? (op manifestHex : String) : Except String Manifest :=
  match bytesOfHex? manifestHex with
  | none => .error s!"{op}: manifestHex must contain an even number of hexadecimal digits"
  | some bytes =>
      match decode? bytes with
      | none => .error s!"{op}: bytes do not decode as an admitted SBM0 to SBM7 manifest"
      | some manifest => .ok manifest

/-- `storeManifestInspect(manifestHex)` — decode one Shardborough manifest and
report what a host needs in order to fetch its artifacts: the wire version,
the layout label, the blank-node publication profile, and one record per
entry. Nothing is read from a block; every value here is committed by the
manifest bytes themselves. -/
def storeManifestInspect (manifestHex : String) : String :=
  match decodeManifest? "storeManifestInspect" manifestHex with
  | .error e => errJson e
  | .ok manifest =>
      okWith
        [ ("wireVersion", .number (toString manifest.version))
        , ("layout", .string manifest.layout)
        , ("blankNodeProfile", .string manifest.blankNodeProfile)
        , ("termRegistryVersion", .string manifest.termRegistryVersion)
        , ("rangeCommitted", .bool (rangeCommitted manifest))
        , ("totalBytes", .number (toString (totalBytesOf manifest.entries)))
        , ("totalRows", .number (toString (totalRowsOf manifest.entries)))
        , ("entries", .array (manifest.entries.map (entryJson manifest))) ]

/-! ## Planning

The two collectors are the ones the native tools use, so the entry set and the
reported mode agree with `l4block-id-v3-query` and `l4block-quad-query` for the
same manifest and query.

The EXISTS-outside-pattern guard is carried by the collectors themselves and
is not re-implemented here: `queryNativeConstantPredicates?` and
`queryQuadConstantPredicates?` both answer `none` unless
`Query.expressionsOutsidePatternExistsFree`, and a `none` selects every entry.
Section 18.6 evaluates an EXISTS in a projection, a GROUP BY key, a HAVING
condition or an ORDER BY condition against the active graph, so a query
carrying one must see the whole generation. -/

/-- The blocks one query needs from one generation, plus the mode string the
native tools print for the same decision. -/
structure StorePlan where
  entries : List Entry
  mode : String
  ibk4 : Bool
  deriving Inhabited

private def planFor (op : String) (manifest : Manifest) (query : Query) :
    Except String StorePlan :=
  if !rangeCommitted manifest then
    .error s!"{op}: this manifest carries no fixed-chunk Merkle commitment"
  else if isIbk4Layout manifest.layout then
    let entries := quadEntriesForQuery manifest query
    .ok { entries, mode := s!"ibk4-full-manifest({entries.length})", ibk4 := true }
  else if isIbk3Layout manifest.layout then
    match queryNativeConstantPredicates? query with
    | some predicates =>
        let entries := entriesForPredicates manifest predicates
        .ok { entries, mode := s!"ibk3-paged-merkle({predicates.length})", ibk4 := false }
    | none =>
        let entries := manifest.entries
        .ok { entries
            , mode := s!"ibk3-paged-merkle-full-manifest({(predicateOrder entries).length})"
            , ibk4 := false }
  else
    .error s!"{op}: layout '{manifest.layout}' is neither an IBK3 nor an IBK4 generation"

private def parseQuery (op sparql : String) : Except String Query :=
  match parseSparql sparql with
  | .error e => .error s!"{op}: SPARQL parse error: {fmtParseError e}"
  | .ok query => .ok query

/-- `storeQueryPlan(manifestHex, sparql)` — the artifact keys a host must
fetch, in manifest order, with the open mode and the byte and row totals those
artifacts declare. It reads no block and applies no cap: a host uses it to
decide what to fetch, and `storeQuery` is where the caps are enforced. -/
def storeQueryPlan (manifestHex sparql : String) : String :=
  let outcome : Except String String := do
    let manifest ← decodeManifest? "storeQueryPlan" manifestHex
    let query ← parseQuery "storeQueryPlan" sparql
    let plan ← planFor "storeQueryPlan" manifest query
    pure (okWith
      [ ("wireVersion", .number (toString manifest.version))
      , ("layout", .string manifest.layout)
      , ("mode", .string plan.mode)
      , ("shards", .number (toString plan.entries.length))
      , ("keys", .array (plan.entries.map fun entry => .string entry.artifact.key.value))
      , ("bytes", .number (toString (totalBytesOf plan.entries)))
      , ("rows", .number (toString (totalRowsOf plan.entries))) ])
  match outcome with
  | .error e => errJson e
  | .ok envelope => envelope

/-! ## Reading the artifacts the host supplied -/

/-- Where one artifact's bytes are: a window into the blob region the host
allocated, or an inline hexadecimal string for the diagnostic path. -/
inductive ArtifactSource where
  /-- `offset` and `len`, both bounds-checked against the blob. -/
  | window (offset len : Nat)
  /-- Inline lowercase hexadecimal. Diagnostic only; see the module banner. -/
  | hex (text : String)

private def natOfJson? (value : Json) : Option Nat :=
  match value with
  | .number text => text.toNat?
  | _ => none

private def artifactSourceOf (members : List (String × Json)) :
    Except String ArtifactSource :=
  match members.find? (fun m => m.1 == "offset"), members.find? (fun m => m.1 == "len"),
        members.find? (fun m => m.1 == "bytes") with
  | some (_, offsetJson), some (_, lenJson), none =>
      match natOfJson? offsetJson, natOfJson? lenJson with
      | some offset, some len => .ok (.window offset len)
      | _, _ => .error "storeQuery: \"offset\" and \"len\" must be non-negative integers"
  | none, none, some (_, .string text) => .ok (.hex text)
  | _, _, _ =>
      .error "storeQuery: every artifact needs either \"offset\" and \"len\" (blob) or \"bytes\" (hex), not both"

private def artifactSources (artifactsJson : String) :
    Except String (List (String × ArtifactSource)) := do
  let json ← match parseJson artifactsJson with
    | .error e => throw s!"storeQuery: artifactsJson parse error: {e}"
    | .ok value => pure value
  match json with
  | .array items =>
      items.mapM fun item =>
        match item with
        | .object members =>
            match members.find? (fun m => m.1 == "key") with
            | some (_, .string key) => do
                let source ← artifactSourceOf members
                pure (key, source)
            | _ => throw "storeQuery: every artifact needs a string \"key\""
        | _ => throw "storeQuery: artifactsJson entries must be JSON objects"
  | _ => throw "storeQuery: artifactsJson must be a JSON array"

private def supplied? (sources : List (String × ArtifactSource)) (key : String) :
    Option ArtifactSource :=
  (sources.find? fun pair => pair.1 == key).map Prod.snd

/-- Admit one supplied artifact against its manifest entry: the bytes are
where the descriptor says they are, their length is the declared extent, and
their SHA-256 is the declared digest. -/
private def admitArtifact (entry : Entry) (sources : List (String × ArtifactSource))
    (blob : ByteArray) : Except String ByteArray := do
  let key := entry.artifact.key.value
  let source ← match supplied? sources key with
    | none => throw s!"storeQuery: no bytes were supplied for artifact '{key}'"
    | some source => pure source
  let bytes ← match source with
    | .window offset len =>
        if len != entry.artifact.bytes then
          throw s!"storeQuery: artifact '{key}' is {len} bytes, the manifest declares {entry.artifact.bytes}"
        else if offset + len > blob.size then
          throw s!"storeQuery: artifact '{key}' names blob bytes [{offset}, {offset + len}) but the call carried {blob.size} blob bytes"
        else pure (blob.extract offset (offset + len))
    | .hex text =>
        if text.length / 2 != entry.artifact.bytes then
          throw s!"storeQuery: artifact '{key}' is {text.length / 2} bytes, the manifest declares {entry.artifact.bytes}"
        else match bytesOfHex? text with
        | none => throw s!"storeQuery: artifact '{key}' is not an even-length hexadecimal string"
        | some bytes => pure bytes
  if bytes.size != entry.artifact.bytes then
    throw s!"storeQuery: artifact '{key}' is {bytes.size} bytes, the manifest declares {entry.artifact.bytes}"
  if !L4Factoidal.Storage.BlockArtifact.verify entry.artifact.sha256 bytes then
    throw s!"storeQuery: artifact '{key}' does not match the SHA-256 the manifest commits"
  pure bytes

private def ibk3TriplesOf (entry : Entry) (bytes : ByteArray) :
    Except String (List Triple) := do
  let key := entry.artifact.key.value
  let block ← match L4Factoidal.Storage.IndexedBlockWireV3.decode bytes with
    | none => throw s!"storeQuery: artifact '{key}' is not a decodable IBK3 block"
    | some block => pure block
  let triples := L4Factoidal.Storage.IndexedBlock.scanBound
    { p := some entry.predicate } block
  if triples.length != entry.rows then
    throw s!"storeQuery: artifact '{key}' holds {triples.length} rows for its predicate, the manifest declares {entry.rows}"
  pure triples

private def ibk4QuadsOf (entry : Entry) (bytes : ByteArray) :
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := do
  let key := entry.artifact.key.value
  let block ← match L4Factoidal.Storage.IndexedBlockWireV4.decode bytes with
    | none => throw s!"storeQuery: artifact '{key}' is not a decodable IBK4 block"
    | some block => pure block
  if block.rows.size != entry.rows then
    throw s!"storeQuery: artifact '{key}' holds {block.rows.size} rows, the manifest declares {entry.rows}"
  pure block.denotes

private def readIbk3 (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    List Entry → List Triple → Except String (List Triple)
  | [], acc => pure acc
  | entry :: rest, acc => do
      let bytes ← admitArtifact entry sources blob
      let triples ← ibk3TriplesOf entry bytes
      readIbk3 sources blob rest (acc ++ triples)

private def readIbk4 (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    List Entry → List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow →
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow)
  | [], acc => pure acc
  | entry :: rest, acc => do
      let bytes ← admitArtifact entry sources blob
      let quads ← ibk4QuadsOf entry bytes
      readIbk4 sources blob rest (acc ++ quads)

/-- Every cap, checked against the manifest's own declarations before a single
byte is hashed. -/
private def checkCaps (plan : StorePlan) : Except String Unit := do
  if plan.entries.length > maxStoreArtifacts then
    throw s!"storeQuery: the plan selects {plan.entries.length} artifacts, the cap is {maxStoreArtifacts}"
  let bytes := totalBytesOf plan.entries
  if bytes > maxStoreBytes then
    throw s!"storeQuery: the plan selects {bytes} artifact bytes, the cap is {maxStoreBytes}"
  let rows := totalRowsOf plan.entries
  if rows > maxStoreRows then
    throw s!"storeQuery: the plan selects {rows} rows, the cap is {maxStoreRows}"
  pure ()

/-- `storeQuery(manifestHex, sparql, artifactsJson)` over one blob region —
evaluate a SPARQL query against the blocks a host read for the plan
`storeQueryPlan` gave it.

`blob` is the byte region the host allocated inside the wasm heap and wrote
the artifacts into, back to back; every `{"key","offset","len"}` descriptor of
`artifactsJson` is a bounds-checked window into it. `ByteArray.empty` is the
correct argument for a call whose descriptors are all inline hexadecimal —
that is what the plain `l4_call` entry passes.

Caps: at most 64 selected artifacts, 8388608 total artifact bytes and 100000
total rows, each checked against the manifest's declarations before any byte
is hashed. A cap trip is an error naming the cap and the value that exceeded
it; nothing is truncated.

The answer is the ordinary `queryDataset` envelope with `"shards"` and
`"mode"` in front of `"kind"`, so a host handles the result exactly as it
handles `queryDataset`. -/
def storeQuery (manifestHex sparql artifactsJson : String) (blob : ByteArray) : String :=
  let outcome : Except String String := do
    let manifest ← decodeManifest? "storeQuery" manifestHex
    let query ← parseQuery "storeQuery" sparql
    let plan ← planFor "storeQuery" manifest query
    checkCaps plan
    let sources ← artifactSources artifactsJson
    let extra : List (String × Json) :=
      [ ("shards", .number (toString plan.entries.length))
      , ("mode", .string plan.mode) ]
    if plan.ibk4 then
      let quads ← readIbk4 sources blob plan.entries []
      let ds := datasetOfQuads quads
      -- A blank-node graph name cannot survive `materialiseDatasetBackend`,
      -- so such a dataset takes the reference evaluator, exactly as
      -- `Harness/QuadQuery.lean` does natively.
      let backend := if namesAreIris ds then some (indexedDatasetBackend ds) else none
      pure (queryParsedDatasetWith ds backend sparql extra)
    else
      let triples ← readIbk3 sources blob plan.entries []
      let ds : Dataset := { default := triples, named := [] }
      pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql extra)
  match outcome with
  | .error e => errJson e
  | .ok envelope => envelope

/-! ## Executable ABI pins

These pin the envelope shapes, the manifest refusal, the digest refusal and
the cap refusal together at the worker boundary — not the manifest codec,
which `ShardManifestTheorems` and `Storage/ShardManifest.lean`'s own guards
already carry. -/

private def pinPredicate : WfIri := ⟨"http://example.org/p", by decide⟩
private def pinBlock : L4Factoidal.Storage.IndexedBlock.Block :=
  L4Factoidal.Storage.IndexedBlock.fromGraph
    [{ s := .iri ⟨"http://example.org/s", by decide⟩
     , p := pinPredicate
     , o := .iri ⟨"http://example.org/o", by decide⟩ }]
private def pinBytes : ByteArray :=
  (L4Factoidal.Storage.IndexedBlockWireV3.encode? pinBlock).getD ByteArray.empty
private def pinChunkBytes : Nat := 65536
private def pinManifest : Manifest :=
  { version := 3
  , sourceIdentity := ByteArray.empty
  , termRegistryVersion := "pin"
  , layout := "predicate-ibk3-ptd1-sri1-merkle-v0"
  , entries :=
      [ { predicate := pinPredicate
        , artifact :=
            { key := ⟨"predicate-0.ibk3"⟩
            , bytes := pinBytes.size
            , sha256 := L4Factoidal.Storage.BlockArtifact.digest pinBytes
            , chunked := L4Factoidal.Storage.ChunkedArtifact.fromChunks? pinChunkBytes
                (L4Factoidal.Storage.ChunkedArtifact.chunksOf pinChunkBytes pinBytes) }
        , subjectIndex := some
            { key := ⟨"predicate-0.sri1"⟩
            , bytes := 1
            , sha256 := L4Factoidal.Storage.BlockArtifact.digest ByteArray.empty
            , chunked := L4Factoidal.Storage.ChunkedArtifact.fromChunks? pinChunkBytes
                (L4Factoidal.Storage.ChunkedArtifact.chunksOf pinChunkBytes
                  (ByteArray.mk #[0])) }
        , rows := 1
        , ordinal := 0 } ] }
private def pinManifestHex : String :=
  hexOfBytes ((encode? pinManifest).getD ByteArray.empty)
private def pinArtifactsJson : String :=
  (Json.array [.object [("key", .string "predicate-0.ibk3"),
                        ("bytes", .string (hexOfBytes pinBytes))]]).toString
private def pinTamperedJson : String :=
  (Json.array [.object [("key", .string "predicate-0.ibk3"),
                        ("bytes", .string (hexOfBytes (pinBytes.push 0)))]]).toString
/-- The blob path: the whole region is this one artifact. -/
private def pinWindowJson : String :=
  (Json.array [.object [("key", .string "predicate-0.ibk3"),
                        ("offset", .number "0"),
                        ("len", .number (toString pinBytes.size))]]).toString
/-- A window that runs past the end of the region the call carried. -/
private def pinOverrunJson : String :=
  (Json.array [.object [("key", .string "predicate-0.ibk3"),
                        ("offset", .number "1"),
                        ("len", .number (toString pinBytes.size))]]).toString

#guard (storeManifestInspect pinManifestHex).contains "\"wireVersion\":3"
#guard (storeManifestInspect pinManifestHex).contains "\"key\":\"predicate-0.ibk3\""
#guard (storeManifestInspect pinManifestHex).contains "\"blockKind\":\"IBK3\""
#guard (storeManifestInspect pinManifestHex).contains "\"subjectIndex\":\"predicate-0.sri1\""
#guard (storeManifestInspect "00").contains "do not decode"
#guard (storeManifestInspect "0").contains "even number of hexadecimal digits"

#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o }").contains "\"mode\":\"ibk3-paged-merkle(1)\""
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s ?p ?o }").contains "\"mode\":\"ibk3-paged-merkle-full-manifest(1)\""
-- The EXISTS guard: an EXISTS outside the pattern refuses the predicate
-- collector, so every entry is selected.
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o } ORDER BY (EXISTS { ?s ?q ?r })").contains
    "ibk3-paged-merkle-full-manifest"
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s (EXISTS { ?s ?q ?r } AS ?e) WHERE { ?s <http://example.org/p> ?o }").contains
    "ibk3-paged-merkle-full-manifest"
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o }").contains "\"keys\":[\"predicate-0.ibk3\"]"

#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinArtifactsJson ByteArray.empty).contains "http://example.org/s"
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinArtifactsJson ByteArray.empty).contains "\"mode\":\"ibk3-paged-merkle(1)\""
#guard (storeQuery pinManifestHex "ASK { ?s <http://example.org/p> ?o }"
  pinArtifactsJson ByteArray.empty).contains "\"boolean\":true"
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinTamperedJson ByteArray.empty).contains "the manifest declares"
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  "[]" ByteArray.empty).contains "no bytes were supplied for artifact 'predicate-0.ibk3'"

-- The blob path answers exactly what the hexadecimal path answers.
#guard storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinWindowJson pinBytes ==
    storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
      pinArtifactsJson ByteArray.empty
-- A window past the end of the region is a refusal, never a memory fault.
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinOverrunJson pinBytes).contains "names blob bytes"
-- The blob path through the plain entry, which carries no region, refuses.
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  pinWindowJson ByteArray.empty).contains "the call carried 0 blob bytes"
-- A descriptor may not name both forms.
#guard (storeQuery pinManifestHex "SELECT ?s WHERE { ?s <http://example.org/p> ?o }"
  "[{\"key\":\"predicate-0.ibk3\",\"offset\":0,\"len\":1,\"bytes\":\"00\"}]"
  pinBytes).contains "not both"

end L4Wasm.Ops
