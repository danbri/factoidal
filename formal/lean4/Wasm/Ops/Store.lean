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
                                "objectIndex":"…","literalIndex":"…"},
                    -- wire version 10 only
                    "blobRefs":["blob-<hex>.lit", …],
                    "subjectZone":{"min":"<hex>","max":"<hex>"},
                    "objectZone":{"min":"<hex>","max":"<hex>"}}, …],
        -- wire version 10 only
        "blobs":[{"key":"blob-<hex>.lit","bytes":N,"sha256":"…", …}, …]}
     | {"ok":false,"error":"…"}

  storeQueryPlan(manifestHex, sparql)
    -> {"ok":true,"wireVersion":N,"layout":"…","mode":"…","shards":N,
        "keys":["…", …],"sidecarKeys":["…", …],"blobKeys":["…", …],
        "bytes":N,"rows":N,"zoneExcluded":N}
     | {"ok":false,"error":"…"}

`blobKeys` is empty and `zoneExcluded` is zero for every generation below wire
version 10: no earlier manifest carries a blob table or a zone map. A host
fetches `keys` and `blobKeys` before it calls `storeQuery`, and `sidecarKeys`
as well before it calls `storeOpen`.

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

These three bound ONE CALL of an operation that pays the hash and the decode
EVERY time it is called, and they are unchanged by
https://github.com/danbri/factoidal/issues/657. The handle path answers a
different question — what may be RETAINED between calls — and carries its own
cap (`Wasm/Ops/StoreHandles.lean`). Raising these would make a single
stateless call slower without making any second call faster, which is the
opposite of what a host with a wide query needs; such a host opens a handle.

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
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Crypto.SHA2Native

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
  | some .ibk5 => "IBK5"
  | some .ibk4 => "IBK4"
  | some .ibk3 => "IBK3"
  | none => if isIbk3Layout manifest.layout then "IBK3" else "IBK2"

private def sidecarMembers (entry : Entry) : List (String × Json) :=
  (entry.subjectIndex.map fun r => ("subjectIndex", Json.string r.key.value)).toList ++
  (entry.termIndex.map fun r => ("termIndex", Json.string r.key.value)).toList ++
  (entry.objectIndex.map fun r => ("objectIndex", Json.string r.key.value)).toList ++
  (entry.literalIndex.map fun r => ("literalIndex", Json.string r.key.value)).toList ++
  (entry.geoIndex.map fun r => ("geoIndex", Json.string r.key.value)).toList

private def chunkMembers (entry : Entry) : List (String × Json) :=
  match entry.artifact.chunked with
  | none => []
  | some chunks =>
      [ ("chunkBytes", .number (toString chunks.chunkBytes))
      , ("chunkCount", .number (toString chunks.chunkCount))
      , ("merkleRoot", .string (hexOfBytes chunks.root)) ]

/-- The zone-map bound pair of one entry, as two hexadecimal prefixes. A bound
    is at most `zoneBytes` bytes of the smallest (or largest) version-2 term
    key the block holds, so a host can see the range without decoding a
    block. -/
private def zoneJson (zone : List UInt8 × List UInt8) : Json :=
  .object
    [ ("min", .string (hexOfBytes (byteArrayOfList zone.1)))
    , ("max", .string (hexOfBytes (byteArrayOfList zone.2))) ]

/-- The blob table members one entry names, as ARTIFACT KEYS. The manifest
    stores indices into its own blob table; a host fetches files by name, so
    the indices are resolved here and never cross the boundary. -/
def entryBlobKeys (manifest : Manifest) (entry : Entry) : List String :=
  entry.blobRefs.filterMap fun index =>
    (manifest.blobs[index]?).map fun ref => ref.key.value

/-- The SBM10 members of one entry: the out-of-line literals its dictionary
    names and the two zone maps. Every one of them is absent from a manifest
    below version 10, so an SBM9 entry answers exactly the members it
    answered before. -/
private def sbm10EntryMembers (manifest : Manifest) (entry : Entry) :
    List (String × Json) :=
  (if entry.blobRefs.isEmpty then []
   else [("blobRefs", .array ((entryBlobKeys manifest entry).map Json.string))]) ++
  (entry.subjectZone.map fun zone => ("subjectZone", zoneJson zone)).toList ++
  (entry.objectZone.map fun zone => ("objectZone", zoneJson zone)).toList

/-- One member of the manifest-level blob table. The same four values every
    other artifact reference carries, so a host admits a blob exactly as it
    admits a block. -/
private def blobRefJson (ref : ArtifactRef) : Json :=
  .object
    ([ ("key", .string ref.key.value)
     , ("bytes", .number (toString ref.bytes))
     , ("sha256", .string (hexOfBytes ref.sha256)) ] ++
     (match ref.chunked with
      | none => []
      | some chunks =>
          [ ("chunkBytes", .number (toString chunks.chunkBytes))
          , ("chunkCount", .number (toString chunks.chunkCount))
          , ("merkleRoot", .string (hexOfBytes chunks.root)) ]))

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
     , ("sidecars", .object (sidecarMembers entry)) ] ++
     sbm10EntryMembers manifest entry)

def totalBytesOf (entries : List Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.artifact.bytes) 0

def totalRowsOf (entries : List Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.rows) 0

def decodeManifest? (op manifestHex : String) : Except String Manifest :=
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
        ([ ("wireVersion", .number (toString manifest.version))
        , ("layout", .string manifest.layout)
        , ("blankNodeProfile", .string manifest.blankNodeProfile)
        , ("termRegistryVersion", .string manifest.termRegistryVersion)
        , ("rangeCommitted", .bool (rangeCommitted manifest))
        , ("totalBytes", .number (toString (totalBytesOf manifest.entries)))
        , ("totalRows", .number (toString (totalRowsOf manifest.entries)))
        , ("entries", .array (manifest.entries.map (entryJson manifest))) ] ++
        (if manifest.blobs.isEmpty then []
         else [("blobs", .array (manifest.blobs.map blobRefJson))]))

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

/-- Which block codec a generation's layout names. `ibk5` is wire version 10,
whose blocks may name out-of-line literals. -/
inductive StoreCodec where
  | ibk3
  | ibk4
  | ibk5
  deriving DecidableEq, Inhabited

/-- The blocks one query needs from one generation, plus the mode string the
native tools print for the same decision.

`blobs` is the manifest blob-table members the selected entries refer to, in
manifest order and without repeats; `zoneExcluded` is how many entries the
predicate and graph collectors kept and the SBM10 zone maps then dropped. Both
are empty and zero for every generation below wire version 10, which carries
neither field. -/
structure StorePlan where
  entries : List Entry
  mode : String
  codec : StoreCodec
  blobs : List ArtifactRef := []
  zoneExcluded : Nat := 0
  deriving Inhabited

/-- The quad codecs. IBK3 denotes triples; IBK4 and IBK5 denote quads. -/
def StorePlan.quads (plan : StorePlan) : Bool := plan.codec != .ibk3

/-- The index sidecars of the planned entries, in manifest order. A host that
opens a handle fetches these BESIDE the blocks: they are what makes a literal
search skip the scan (`L4Factoidal.Storage.LiteralIndexPlan`) and what makes a
geometry `FILTER` skip the WKT parse (`L4Factoidal.Storage.GeoIndexPlan`).
They are advisory — `storeQuery` never reads one, and `storeOpen` answers
without them — so a host that does not fetch them keeps working. -/
def planSidecarKeys (entries : List Entry) : List String :=
  entries.flatMap fun entry =>
    (entry.literalIndex.map fun ref => ref.key.value).toList ++
    (entry.geoIndex.map fun ref => ref.key.value).toList

/-- The blob artifacts the selected entries refer to, in MANIFEST order and
without repeats: the manifest blob table filtered to the members at least one
selected entry names. An entry's own `blobRefs` are indices into that table,
so the order is the table's, not the entries'. -/
def planBlobRefs (manifest : Manifest) (entries : List Entry) : List ArtifactRef :=
  manifest.blobs.zipIdx.filterMap fun (ref, index) =>
    if entries.any (fun entry => entry.blobRefs.contains index) then some ref else none

/-- The declared byte extent of a set of blob artifacts. -/
def blobBytesOf (refs : List ArtifactRef) : Nat :=
  refs.foldl (fun total ref => total + ref.bytes) 0

/-- The SBM10 zone-map key function: the canonical version-2 wire bytes of a
term, which are the bytes the packer compared when it computed an entry's zone
bounds. `Harness/QuadQuery.lean` uses the same function with the native
hasher; the two hashers agree on every input, and a key function that
disagreed with the packer's would drop entries holding matching rows. -/
def zoneTermKey (t : Term) : Option (List UInt8) :=
  L4Factoidal.Storage.TermWireV2.keyBytes
    (L4Factoidal.Storage.TermWireV2.toWire L4Factoidal.Crypto.sha256Hacl t)

def planFor (op : String) (manifest : Manifest) (query : Query) :
    Except String StorePlan :=
  if !rangeCommitted manifest then
    .error s!"{op}: this manifest carries no fixed-chunk Merkle commitment"
  else if isIbk5Layout manifest.layout then
    -- The predicate and graph collectors run first, exactly as for IBK4; the
    -- zone maps then drop an entry whose subject or object range cannot hold
    -- a constant the query names.
    let withoutZones := quadEntriesForQuery manifest query
    let entries := quadEntriesForQueryWithKeys zoneTermKey manifest query
    .ok { entries
        , mode := s!"ibk5-full-manifest({entries.length})"
        , codec := .ibk5
        , blobs := planBlobRefs manifest entries
        , zoneExcluded := withoutZones.length - entries.length }
  else if isIbk4Layout manifest.layout then
    let entries := quadEntriesForQuery manifest query
    .ok { entries, mode := s!"ibk4-full-manifest({entries.length})", codec := .ibk4 }
  else if isIbk3Layout manifest.layout then
    match queryNativeConstantPredicates? query with
    | some predicates =>
        let entries := entriesForPredicates manifest predicates
        .ok { entries, mode := s!"ibk3-paged-merkle({predicates.length})", codec := .ibk3 }
    | none =>
        let entries := manifest.entries
        .ok { entries
            , mode := s!"ibk3-paged-merkle-full-manifest({(predicateOrder entries).length})"
            , codec := .ibk3 }
  else
    .error s!"{op}: layout '{manifest.layout}' is not an IBK3, IBK4 or IBK5 generation"

def parseQuery (op sparql : String) : Except String Query :=
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
      , ("sidecarKeys", .array ((planSidecarKeys plan.entries).map Json.string))
      , ("blobKeys", .array ((plan.blobs.map fun ref => ref.key.value).map Json.string))
      , ("bytes", .number (toString (totalBytesOf plan.entries + blobBytesOf plan.blobs)))
      , ("rows", .number (toString (totalRowsOf plan.entries)))
      , ("zoneExcluded", .number (toString plan.zoneExcluded)) ])
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

def artifactSourceOf (op : String) (members : List (String × Json)) :
    Except String ArtifactSource :=
  match members.find? (fun m => m.1 == "offset"), members.find? (fun m => m.1 == "len"),
        members.find? (fun m => m.1 == "bytes") with
  | some (_, offsetJson), some (_, lenJson), none =>
      match natOfJson? offsetJson, natOfJson? lenJson with
      | some offset, some len => .ok (.window offset len)
      | _, _ => .error s!"{op}: \"offset\" and \"len\" must be non-negative integers"
  | none, none, some (_, .string text) => .ok (.hex text)
  | _, _, _ =>
      .error s!"{op}: every artifact needs either \"offset\" and \"len\" (blob) or \"bytes\" (hex), not both"

/-- The `[{"key","offset","len"}]` descriptor document, decoded once.
`activateVerify` (Wasm/Ops/Pack.lean) takes the same shape and calls this,
so there is one decoder for the window convention. -/
def artifactSources (op artifactsJson : String) :
    Except String (List (String × ArtifactSource)) := do
  let json ← match parseJson artifactsJson with
    | .error e => throw s!"{op}: artifactsJson parse error: {e}"
    | .ok value => pure value
  match json with
  | .array items =>
      items.mapM fun item =>
        match item with
        | .object members =>
            match members.find? (fun m => m.1 == "key") with
            | some (_, .string key) => do
                let source ← artifactSourceOf op members
                pure (key, source)
            | _ => throw s!"{op}: every artifact needs a string \"key\""
        | _ => throw s!"{op}: artifactsJson entries must be JSON objects"
  | _ => throw s!"{op}: artifactsJson must be a JSON array"

/-- The bytes of one descriptor, bounds-checked against the region the call
carried. This applies NO manifest expectation: `storeQuery` adds the declared
length and digest on top, and `activateVerify` gets them from
`L4Factoidal.Storage.GenerationVerify`. -/
def sourceBytes (op : String) (key : String) (source : ArtifactSource) (blob : ByteArray) :
    Except String ByteArray :=
  match source with
  | .window offset len =>
      if offset + len > blob.size then
        .error s!"{op}: artifact '{key}' names blob bytes [{offset}, {offset + len}) but the call carried {blob.size} blob bytes"
      else .ok (blob.extract offset (offset + len))
  | .hex text =>
      match bytesOfHex? text with
      | none => .error s!"{op}: artifact '{key}' is not an even-length hexadecimal string"
      | some bytes => .ok bytes

/-- Every descriptor resolved to its bytes, in the order the host gave them. -/
def resolveSources (op : String) (sources : List (String × ArtifactSource))
    (blob : ByteArray) : Except String (List (String × ByteArray)) :=
  sources.mapM fun pair => do
    let bytes ← sourceBytes op pair.1 pair.2 blob
    pure (pair.1, bytes)

def supplied? (sources : List (String × ArtifactSource)) (key : String) :
    Option ArtifactSource :=
  (sources.find? fun pair => pair.1 == key).map Prod.snd

/-- Admit one supplied artifact against the reference the manifest commits:
the bytes are where the descriptor says they are, their length is the declared
extent, and their SHA-256 is the declared digest. Blocks and index sidecars go
through this one function, so a sidecar is trusted on exactly the terms a
block is. -/
def admitRef (op : String) (ref : ArtifactRef) (sources : List (String × ArtifactSource))
    (blob : ByteArray) : Except String ByteArray := do
  let key := ref.key.value
  let source ← match supplied? sources key with
    | none => throw s!"{op}: no bytes were supplied for artifact '{key}'"
    | some source => pure source
  match source with
    | .window _ len =>
        if len != ref.bytes then
          throw s!"{op}: artifact '{key}' is {len} bytes, the manifest declares {ref.bytes}"
    | .hex text =>
        if text.length / 2 != ref.bytes then
          throw s!"{op}: artifact '{key}' is {text.length / 2} bytes, the manifest declares {ref.bytes}"
  let bytes ← sourceBytes op key source blob
  if bytes.size != ref.bytes then
    throw s!"{op}: artifact '{key}' is {bytes.size} bytes, the manifest declares {ref.bytes}"
  if !L4Factoidal.Storage.BlockArtifact.verify ref.sha256 bytes then
    throw s!"{op}: artifact '{key}' does not match the SHA-256 the manifest commits"
  pure bytes

/-- Admit one supplied BLOCK against its manifest entry. -/
def admitArtifact (op : String) (entry : Entry) (sources : List (String × ArtifactSource))
    (blob : ByteArray) : Except String ByteArray :=
  admitRef op entry.artifact sources blob

def ibk3TriplesOf (op : String) (entry : Entry) (bytes : ByteArray) :
    Except String (List Triple) := do
  let key := entry.artifact.key.value
  let block ← match L4Factoidal.Storage.IndexedBlockWireV3.decode bytes with
    | none => throw s!"{op}: artifact '{key}' is not a decodable IBK3 block"
    | some block => pure block
  let triples := L4Factoidal.Storage.IndexedBlock.scanBound
    { p := some entry.predicate } block
  if triples.length != entry.rows then
    throw s!"{op}: artifact '{key}' holds {triples.length} rows for its predicate, the manifest declares {entry.rows}"
  pure triples

def ibk4QuadsOf (op : String) (entry : Entry) (bytes : ByteArray) :
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := do
  let key := entry.artifact.key.value
  let block ← match L4Factoidal.Storage.IndexedBlockWireV4.decode bytes with
    | none => throw s!"{op}: artifact '{key}' is not a decodable IBK4 block"
    | some block => pure block
  if block.rows.size != entry.rows then
    throw s!"{op}: artifact '{key}' holds {block.rows.size} rows, the manifest declares {entry.rows}"
  pure block.denotes

/-! ## IBK5 blocks and their out-of-line literals

An IBK5 block denotes quads whose object may be a `TermWireV2.WireTerm.blob`:
the block names a byte extent and a SHA-256 digest, and the lexical form is
one `blob-<hex>.lit` artifact of the manifest blob table.
`IndexedBlockWireV5.resolveBlock` turns those into RDF terms through a lookup
and refuses missing bytes, a wrong byte count, a wrong digest and invalid
UTF-8, so a blob that does not match its term refuses the query rather than
answering with a fabricated literal. `Harness/QuadQuery.lean` reads the same
generations the same way, over files instead of a supplied region. -/

/-- One admitted blob keyed by its SHA-256, as `resolveBlock` looks it up. -/
abbrev BlobBytes := List (List UInt8 × ByteArray)

/-- Admit every blob the plan named, on exactly the terms a block is admitted
on: the declared byte extent and the manifest-committed SHA-256, through
`admitRef`. A blob the host did not supply is refused by name. -/
def admitBlobs (op : String) (refs : List ArtifactRef)
    (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    Except String BlobBytes :=
  refs.mapM fun ref => do
    let bytes ← admitRef op ref sources blob
    pure (ref.sha256.toList, bytes)

def blobLookup (blobs : BlobBytes) : ByteArray → Option ByteArray :=
  fun digest => (blobs.find? fun pair => pair.1 == digest.toList).map Prod.snd

/-- Decode one IBK5 block and hold it to the row count its manifest entry
declares. The block is returned so a caller that also wants the `WireTerm`
dictionary — `storeOpen`, for its candidate-filter indexes — decodes once. -/
def ibk5BlockOf (op : String) (entry : Entry) (bytes : ByteArray) :
    Except String L4Factoidal.Storage.IndexedBlockWireV5.QuadBlock := do
  let key := entry.artifact.key.value
  let block ← match L4Factoidal.Storage.IndexedBlockWireV5.decode bytes with
    | none => throw s!"{op}: artifact '{key}' is not a decodable IBK5 block"
    | some block => pure block
  if block.rows.size != entry.rows then
    throw s!"{op}: artifact '{key}' holds {block.rows.size} rows, the manifest declares {entry.rows}"
  pure block

/-- Resolve one decoded IBK5 block against the admitted blobs. -/
def resolveIbk5 (op : String) (entry : Entry)
    (block : L4Factoidal.Storage.IndexedBlockWireV5.QuadBlock) (blobs : BlobBytes) :
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  match L4Factoidal.Storage.IndexedBlockWireV5.resolveBlock
      L4Factoidal.Crypto.sha256Hacl (blobLookup blobs) block with
  | none =>
      .error s!"{op}: artifact '{entry.artifact.key.value}' names an out-of-line literal whose bytes are absent, of the wrong extent, or of the wrong SHA-256"
  | some quads => .ok quads

def ibk5QuadsOf (op : String) (entry : Entry) (bytes : ByteArray) (blobs : BlobBytes) :
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := do
  let block ← ibk5BlockOf op entry bytes
  resolveIbk5 op entry block blobs

private def readIbk3 (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    List Entry → List Triple → Except String (List Triple)
  | [], acc => pure acc
  | entry :: rest, acc => do
      let bytes ← admitArtifact "storeQuery" entry sources blob
      let triples ← ibk3TriplesOf "storeQuery" entry bytes
      readIbk3 sources blob rest (acc ++ triples)

private def readIbk4 (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    List Entry → List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow →
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow)
  | [], acc => pure acc
  | entry :: rest, acc => do
      let bytes ← admitArtifact "storeQuery" entry sources blob
      let quads ← ibk4QuadsOf "storeQuery" entry bytes
      readIbk4 sources blob rest (acc ++ quads)

private def readIbk5 (sources : List (String × ArtifactSource)) (blob : ByteArray)
    (blobs : BlobBytes) :
    List Entry → List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow →
    Except String (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow)
  | [], acc => pure acc
  | entry :: rest, acc => do
      let bytes ← admitArtifact "storeQuery" entry sources blob
      let quads ← ibk5QuadsOf "storeQuery" entry bytes blobs
      readIbk5 sources blob blobs rest (acc ++ quads)

/-- Every read cap of the STATELESS path, checked against the manifest's own
declarations before a single byte is hashed.

`subject` is the sentence opener, so the caps read correctly for the
operation that trips one.

`storeOpen` (Wasm/Ops/StoreHandles.lean) does NOT call this. A handle hashes
and decodes once and then answers many queries, so what bounds it is retained
BYTES, not the per-call cost these caps bound; it carries its own
`maxStoreHandleBytes`, derived from a measured resident multiplier. See that
module's banner and
https://github.com/danbri/factoidal/issues/657. -/
def checkEntryCaps (subject : String) (entries : List Entry)
    (blobBytes : Nat := 0) : Except String Unit := do
  if entries.length > maxStoreArtifacts then
    throw s!"{subject} {entries.length} artifacts, the cap is {maxStoreArtifacts}"
  -- An out-of-line literal is bytes the call must carry and hash, so it is
  -- counted here beside the blocks. It is zero below wire version 10.
  let bytes := totalBytesOf entries + blobBytes
  if bytes > maxStoreBytes then
    throw s!"{subject} {bytes} artifact bytes, the cap is {maxStoreBytes}"
  let rows := totalRowsOf entries
  if rows > maxStoreRows then
    throw s!"{subject} {rows} rows, the cap is {maxStoreRows}"
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
def storeQuery (manifestHex sparql artifactsJson : String) (blob : ByteArray)
    (extIris : List String := []) : String :=
  let outcome : Except String String := do
    let manifest ← decodeManifest? "storeQuery" manifestHex
    let query ← parseQuery "storeQuery" sparql
    let plan ← planFor "storeQuery" manifest query
    checkEntryCaps "storeQuery: the plan selects" plan.entries (blobBytesOf plan.blobs)
    let sources ← artifactSources "storeQuery" artifactsJson
    let extra : List (String × Json) :=
      [ ("shards", .number (toString plan.entries.length))
      , ("mode", .string plan.mode) ]
    match plan.codec with
    | .ibk5 =>
        let blobs ← admitBlobs "storeQuery" plan.blobs sources blob
        let quads ← readIbk5 sources blob blobs plan.entries []
        let ds := datasetOfQuads quads
        let backend := if namesAreIris ds then some (indexedDatasetBackend ds) else none
        pure (queryParsedDatasetWith ds backend sparql extra extIris)
    | .ibk4 =>
        let quads ← readIbk4 sources blob plan.entries []
        let ds := datasetOfQuads quads
        -- A blank-node graph name cannot survive `materialiseDatasetBackend`,
        -- so such a dataset takes the reference evaluator, exactly as
        -- `Harness/QuadQuery.lean` does natively.
        let backend := if namesAreIris ds then some (indexedDatasetBackend ds) else none
        pure (queryParsedDatasetWith ds backend sparql extra extIris)
    | .ibk3 =>
        let triples ← readIbk3 sources blob plan.entries []
        let ds : Dataset := { default := triples, named := [] }
        pure (queryParsedDatasetWith ds (some (indexedDatasetBackend ds)) sparql extra extIris)
  match outcome with
  | .error e => errJson e
  | .ok envelope => envelope

/-- `storeQuery` through the IO dispatch entry: the same envelope, with
the caller's §17.6 extension registrations in scope (snapshot read once,
before evaluation). -/
def storeQueryIO (manifestHex sparql artifactsJson : String) (blob : ByteArray) :
    IO String := do
  pure (storeQuery manifestHex sparql artifactsJson blob (← extSnapshot))

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
-- An SBM3 generation declares no literal index, so the sidecar list is empty.
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o }").contains "\"sidecarKeys\":[]"
-- No manifest below SBM10 carries a blob table or a zone map, so the two
-- version-10 plan fields report empty and zero rather than being absent.
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o }").contains "\"blobKeys\":[]"
#guard (storeQueryPlan pinManifestHex
  "SELECT ?s WHERE { ?s <http://example.org/p> ?o }").contains "\"zoneExcluded\":0"
-- An SBM3 entry names no out-of-line literal and no zone map, so inspect
-- reports exactly the members it reported before wire version 10.
#guard !(storeManifestInspect pinManifestHex).contains "blobRefs"
#guard !(storeManifestInspect pinManifestHex).contains "subjectZone"
#guard !(storeManifestInspect pinManifestHex).contains "\"blobs\""

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
