/-
Wasm.Ops.StoreHandles — store handles: verify and decode once, answer many.

https://github.com/danbri/factoidal/issues/641 (the stateful half).

`storeQuery` (Wasm/Ops/Store.lean) is stateless. Every call decodes the
manifest, hashes every artifact byte with the pure Lean SHA-256, decodes each
block, materialises the rows and builds an equivalence-aware index over them,
and only then evaluates. A host that answers many questions against ONE
generation pays all of that again for every question, and the decode and the
hash do not depend on the question at all.

These operations hold that work:

  storeOpen(manifestHex, artifactsJson) + blob
    -> {"ok":true,"handle":"s1","identity":"…","layout":"…","wireVersion":N,
        "artifacts":N,"bytes":N,"rows":N}
     | {"ok":false,"error":"…"}
  storeHandleQuery(handle, sparql)
    -> the SAME envelope family `storeQuery` answers with, unchanged:
       the queryDataset SELECT / ASK / CONSTRUCT envelope with "shards"
       and "mode" placed before "kind"
  storeHandleList()
    -> {"ok":true,"handles":[{…}, …],"bytes":N,"rows":N,
        "handleCap":N,"bytesCap":N}
  storeHandleClose(handle)
    -> {"ok":true}

## The trust argument is unchanged; it moves to `storeOpen`

Every artifact a handle retains was admitted by `admitArtifact` — the same
function `storeQuery` calls, with the same manifest-declared length and the
same manifest-committed SHA-256 (`Crypto.sha256`, section 6.3 of
`docs/shardborough-storage-spec.md`) — and decoded by the same
`ibk3TriplesOf` / `ibk4QuadsOf` row admission. A handle therefore never
answers from bytes it did not verify; it verifies them ONCE, at `storeOpen`,
instead of once per query. A generation whose bytes change on disk after
`storeOpen` is not re-read, so a host that replaces a generation closes its
handle and opens the new one — a handle names the bytes it admitted, not a
directory.

## Why an answer cannot differ from the stateless answer

`storeQuery` plans the query (`planFor`) and reads exactly the blocks the
plan selects. A handle is opened with an artifact set chosen by the host,
which may be larger. `storeHandleQuery` therefore plans the query in the same
way and then:

* refuses, naming the artifact, if the plan needs a block the handle does not
  retain — it never answers a partial generation as though it were whole;
* uses the handle's cached dataset and index when the plan selects exactly
  the retained set, which is the case a host that opened what it planned is
  in, and the case the cache exists for;
* otherwise assembles the dataset from the retained rows of exactly the
  planned artifacts and indexes that. This still skips the hash and the
  decode, which are the dominant per-call costs.

Either way the rows are the rows of the planned blocks, and `"shards"` and
`"mode"` are the plan's own, so the two paths answer identically.

## Caps

A cap trip is an explicit error naming the cap; nothing is evicted and
nothing is truncated (anti-pattern 25).

| Cap | Value | What it bounds |
|---|---|---|
| `maxStoreArtifacts` / `maxStoreBytes` / `maxStoreRows` | as `storeQuery` | one `storeOpen` |
| `maxStoreHandles` | 8 | open store handles in the process |
| `maxStoreHandleBytes` | 67108864 (64 MiB) | admitted artifact bytes retained across ALL open handles |

The three read caps are `storeQuery`'s own, so a handle can never retain an
artifact set `storeQuery` would refuse to read. The two residency caps are
new and are process-wide.

`maxStoreHandleBytes` counts ADMITTED ARTIFACT BYTES, which is what the
manifest declares and what the host transferred. It is not the resident cost:
a decoded block plus its index is a multiple of its packed size, and that
multiple depends on the data. A host that must bound resident memory reads
`storeHandleList` and measures its own process.

`storeOpen` REFUSES when a cap is reached. It does not evict another handle:
a handle belongs to whichever caller opened it, and a store disappearing
underneath a second caller is not a failure that caller can diagnose. A
least-recently-used policy, if one is ever wanted, is a decision for the
host, which knows who holds what.

## Concurrency

The wasm module is single-threaded and the handle table is process-global,
exactly as in `Wasm/Ops/Handles.lean` and `Wasm/Ops/Pack.lean`. A second call
arriving while one is in flight is queued by the HOST; the engine offers no
parallelism and no locking, and a handle is meaningful only inside the one
module instance (wasm) or the one process (native CLI) that opened it. A
server that wants concurrency runs several module instances.

Reachable only through `L4Wasm.callIO` and `L4Wasm.callBlobIO`
(Wasm/Dispatch.lean); the pure `L4Wasm.call` cannot reach the table.

No `partial`, no `sorry`, no `native_decide`.
-/
import Std.Data.HashMap
import Wasm.Ops.Store
import L4Factoidal.Storage.LiteralGramIndexWire
import L4Factoidal.Storage.LiteralIndexPlan

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.QuadDataset
open L4Factoidal.JSON

/-! ## Residency caps -/

/-- At most this many store handles may be open in one process at once. -/
def maxStoreHandles : Nat := 8

/-- At most this many admitted artifact bytes may be retained across every
open store handle. See the banner: this is the packed size, not the resident
size. -/
def maxStoreHandleBytes : Nat := 64 * 1024 * 1024

/-! ## What a handle retains -/

/-- The decoded rows of one artifact, in the form its generation's codec
denotes: triples for an IBK3 predicate block, quads for an IBK4 block. -/
inductive RetainedRows where
  | ibk3 (triples : List Triple)
  | ibk4 (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow)

/-- What one block's LGI1 sidecar lets a query skip.

`index` is the decoded sidecar. `rows` is the block's denoted quads by
position, and `objectRows` maps a dictionary local ID to the positions whose
OBJECT is that term — the OLI2 role, rebuilt here at `storeOpen` because SBM8
commits no graph-aware OLI2. `nonLiteralRows` is every position whose object
is not a literal; a `STR` shape keeps those, because `STR` of an IRI is a
string a `CONTAINS` can match and LGI1 indexes no IRI
(`LiteralIndexPlan.Plan.keepNonLiterals`). -/
structure RetainedLiteralIndex where
  index : L4Factoidal.Storage.LiteralGramIndex.Index
  rows : Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow
  objectRows : Array (Array Nat)
  nonLiteralRows : Array Nat

/-- One admitted artifact, decoded. `bytes` and `rows` are the manifest's own
declarations, which admission has already checked the bytes against.
`literal` is present when the manifest declared an LGI1 sidecar AND the host
supplied its bytes; a handle opened without them still answers, by scanning. -/
structure RetainedArtifact where
  key : String
  predicate : WfIri
  bytes : Nat
  rows : Nat
  payload : RetainedRows
  literal : Option RetainedLiteralIndex

/-- An open store: the manifest it was opened against, every artifact it
retains in manifest order, and the dataset and index over the whole retained
set. `backend` is `none` for an IBK4 dataset carrying a blank-node graph
name, which `materialiseDatasetBackend` cannot represent — the same rule
`storeQuery` applies. -/
structure OpenStore where
  ordinal : Nat
  identity : String
  layout : String
  wireVersion : Nat
  ibk4 : Bool
  manifest : Manifest
  artifacts : List RetainedArtifact
  retainedBytes : Nat
  retainedRows : Nat
  ds : Dataset
  backend : Option DatasetBackend

/-- Handle ids already issued; `storeOpen` numbers them "s1", "s2", … in open
order and never reuses one. -/
initialize storeHandleCounter : IO.Ref Nat ← IO.mkRef 0

/-- The open stores, keyed by handle string. -/
initialize storeHandleTable : IO.Ref (Std.HashMap String OpenStore) ← IO.mkRef ∅

/-! ## Assembling the dataset a query is answered from -/

private def ibk3RowsOf (art : RetainedArtifact) : List Triple :=
  match art.payload with
  | .ibk3 triples => triples
  | .ibk4 _ => []

private def ibk4RowsOf (art : RetainedArtifact) :
    List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow :=
  match art.payload with
  | .ibk4 quads => quads
  | .ibk3 _ => []

/-- The dataset denoted by a set of retained artifacts. The IBK3 arm puts
every triple in the default graph and the IBK4 arm takes the quads' own graph
names, exactly as `storeQuery` does for the blocks it read. -/
def datasetOfRetained (ibk4 : Bool) (arts : List RetainedArtifact) : Dataset :=
  if ibk4 then datasetOfQuads (arts.flatMap ibk4RowsOf)
  else { default := arts.flatMap ibk3RowsOf, named := [] }

/-- The indexed backend for such a dataset, or `none` where the reference
evaluator is required (an IBK4 dataset with a blank-node graph name). -/
def backendOfRetained (ibk4 : Bool) (ds : Dataset) : Option DatasetBackend :=
  if ibk4 then (if namesAreIris ds then some (indexedDatasetBackend ds) else none)
  else some (indexedDatasetBackend ds)

/-! ## storeOpen -/

/-- Which codec a manifest's layout names, with the same two refusals
`planFor` carries. -/
def storeLayoutIbk4? (op : String) (manifest : Manifest) : Except String Bool :=
  if !rangeCommitted manifest then
    .error s!"{op}: this manifest carries no fixed-chunk Merkle commitment"
  else if isIbk4Layout manifest.layout then .ok true
  else if isIbk3Layout manifest.layout then .ok false
  else
    .error s!"{op}: layout '{manifest.layout}' is neither an IBK3 nor an IBK4 generation"

/-- Build the retained literal index of one IBK4 block, or `none` when the
manifest declares no LGI1 sidecar, the host supplied no bytes for it, the
sidecar does not decode, or it names another block. Every one of those is a
FALLBACK, not an error: the handle then scans, which is what it did before
SBM8 existed. -/
def retainedLiteralIndex? (op : String) (entry : Entry)
    (sources : List (String × ArtifactSource)) (blob : ByteArray)
    (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) (blockBytes : ByteArray) :
    Option RetainedLiteralIndex := do
  let ref ← entry.literalIndex
  let _ ← supplied? sources ref.key.value
  let indexBytes ← (admitRef op ref sources blob).toOption
  let artifact ← L4Factoidal.Storage.LiteralGramIndexWire.decode? indexBytes
  if artifact.targetIBKSha256 != entry.artifact.sha256 then none else do
  let block ← L4Factoidal.Storage.IndexedBlockWireV4.decode blockBytes
  let rows := quads.toArray
  -- `denotes` filters, so a block whose rows do not all decode would make the
  -- positions disagree with the object IDs. Refuse rather than misalign.
  if block.rows.size != rows.size then none else
  if artifact.index.dictCount != block.dict.size then none else
  some (Id.run do
    let mut objectRows : Array (Array Nat) := Array.replicate block.dict.size #[]
    let mut nonLiteralRows : Array Nat := #[]
    for h : i in [0 : block.rows.size] do
      let o := block.rows[i].o
      if o < objectRows.size then
        objectRows := objectRows.set! o ((objectRows[o]!).push i)
      match block.dict[o]? with
      | some (.literal _) => pure ()
      | _ => nonLiteralRows := nonLiteralRows.push i
    pure { index := artifact.index, rows, objectRows, nonLiteralRows })

/-- Admit and decode each selected entry, in manifest order. Every artifact
goes through the same `admitArtifact` `storeQuery` uses, so the digest check
is the same check in the same place in the sequence. -/
def readRetained (op : String) (ibk4 : Bool)
    (sources : List (String × ArtifactSource)) (blob : ByteArray) :
    List Entry → List RetainedArtifact → Except String (List RetainedArtifact)
  | [], acc => pure acc.reverse
  | entry :: rest, acc => do
      let bytes ← admitArtifact op entry sources blob
      let (payload, literal) ← if ibk4 then
            (do
              let quads ← ibk4QuadsOf op entry bytes
              pure (RetainedRows.ibk4 quads,
                    retainedLiteralIndex? op entry sources blob quads bytes))
          else
            (do let triples ← ibk3TriplesOf op entry bytes
                pure (RetainedRows.ibk3 triples, none))
      readRetained op ibk4 sources blob rest
        ({ key := entry.artifact.key.value
         , predicate := entry.predicate
         , bytes := entry.artifact.bytes
         , rows := entry.rows
         , payload
         , literal } :: acc)

/-- Every key the host supplied bytes for must be a key this manifest
declares; an unknown key is a host fault, not a silently ignored argument. -/
private def checkSuppliedKeys (op : String) (manifest : Manifest)
    (sources : List (String × ArtifactSource)) : Except String Unit :=
  match sources.find? (fun pair =>
      !(manifest.entries.any fun entry => entry.artifact.key.value == pair.1 ||
          (entry.literalIndex.map fun ref => ref.key.value) == some pair.1)) with
  | some (key, _) => .error s!"{op}: artifact '{key}' is not declared by this manifest"
  | none => pure ()

/-- The admission of `storeOpen`, kept pure so the IO layer only inserts the
result. -/
private def buildOpenStore (manifestHex artifactsJson : String) (blob : ByteArray) :
    Except String OpenStore := do
  let manifest ← decodeManifest? "storeOpen" manifestHex
  let ibk4 ← storeLayoutIbk4? "storeOpen" manifest
  let sources ← artifactSources "storeOpen" artifactsJson
  checkSuppliedKeys "storeOpen" manifest sources
  let entries := manifest.entries.filter fun entry =>
    sources.any fun pair => pair.1 == entry.artifact.key.value
  if entries.isEmpty then
    throw "storeOpen: no artifact bytes were supplied; a handle retains at least one block"
  checkEntryCaps "storeOpen: the call supplies" entries
  let artifacts ← readRetained "storeOpen" ibk4 sources blob entries []
  let ds := datasetOfRetained ibk4 artifacts
  pure { ordinal := 0
       , identity := hexOfBytes manifest.sourceIdentity
       , layout := manifest.layout
       , wireVersion := manifest.version
       , ibk4
       , manifest
       , artifacts
       , retainedBytes := totalBytesOf entries
       , retainedRows := totalRowsOf entries
       , ds
       , backend := backendOfRetained ibk4 ds }

private def openStoreJson (handle : String) (store : OpenStore) : List (String × Json) :=
  [ ("handle", .string handle)
  , ("identity", .string store.identity)
  , ("layout", .string store.layout)
  , ("wireVersion", .number (toString store.wireVersion))
  , ("artifacts", .number (toString store.artifacts.length))
  , ("bytes", .number (toString store.retainedBytes))
  , ("rows", .number (toString store.retainedRows)) ]

/-- `storeOpen(manifestHex, artifactsJson)` over one blob region — verify
every supplied artifact against the SHA-256 its manifest commits, decode each
block once, index the retained rows once, and answer a handle.

`artifactsJson` and `blob` are exactly `storeQuery`'s: a JSON array of
`{"key","offset","len"}` windows into the region the host allocated, or the
diagnostic `{"key","bytes":"<hex>"}` form. A host normally supplies the keys
`storeQueryPlan` named for the queries it intends to ask, or every key
`storeManifestInspect` listed.

Refuses, naming the cap, when the process already holds `maxStoreHandles`
handles or when this open would push the retained artifact bytes above
`maxStoreHandleBytes`. Nothing is evicted. -/
def storeOpen (manifestHex artifactsJson : String) (blob : ByteArray) : IO String := do
  let table ← storeHandleTable.get
  if table.size ≥ maxStoreHandles then
    pure (errJson s!"storeOpen: {table.size} store handles are open, the cap is {maxStoreHandles}")
  else
    match buildOpenStore manifestHex artifactsJson blob with
    | .error e => pure (errJson e)
    | .ok store =>
        let held := table.fold (fun total _ opened => total + opened.retainedBytes) 0
        if held + store.retainedBytes > maxStoreHandleBytes then
          pure (errJson s!"storeOpen: this open would retain {held + store.retainedBytes} artifact bytes, the cap is {maxStoreHandleBytes}")
        else do
          let n ← storeHandleCounter.modifyGet fun n => (n + 1, n + 1)
          let handle := s!"s{n}"
          let opened := { store with ordinal := n }
          storeHandleTable.modify (·.insert handle opened)
          pure (okWith (openStoreJson handle opened))

/-! ## The literal search path

`LiteralIndexPlan.plan?` decides whether the index may serve a query at all.
What is done with its answer is a RESTRICTION of the rows that are
materialised, and then the ORIGINAL query is evaluated over them. No
expression is rewritten and no filter is dropped, so the answer is the scan's
answer whenever the restriction drops only rows that cannot appear in a
solution — which is exactly what `plan?` establishes. -/

/-- The rows of one block a needle can reach: the candidate terms' rows, plus
the non-literal-object rows when the shape applied `STR`. Positions are
returned ascending, so the reduced dataset keeps the block's row order and an
unordered SELECT answers in the order the scan answers in.

`none` means the index cannot serve this needle and the caller must scan. -/
def literalRows? (retained : RetainedLiteralIndex)
    (plan : L4Factoidal.Storage.LiteralIndexPlan.Plan) :
    Option (Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  match L4Factoidal.Storage.LiteralGramIndex.candidates? retained.index plan.needle with
  | none => none
  | some ids => Id.run do
      let mut positions : Array Nat :=
        if plan.keepNonLiterals then retained.nonLiteralRows else #[]
      for id in ids do
        if h : id < retained.objectRows.size then
          positions := positions ++ retained.objectRows[id]
      let ordered := positions.qsort (fun a b => decide (a < b))
      pure (some (ordered.filterMap fun position => retained.rows[position]?))

/-- The whole planned artifact set restricted by one literal search, or `none`
when any planned block cannot serve it: no retained index, or a predicate the
plan does not name, or a needle the index refuses. Every `none` is a
fallback to the scan. -/
def literalRestricted? (arts : List RetainedArtifact)
    (plan : L4Factoidal.Storage.LiteralIndexPlan.Plan) :
    Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  arts.foldlM (fun acc art => do
    if art.predicate != plan.predicate then none else do
    let retained ← art.literal
    let rows ← literalRows? retained plan
    some (acc ++ rows.toList)) []

/-! ## storeHandleQuery -/

/-- The shared error envelope for a handle that is not in the table. -/
def unknownStoreHandle (h : String) : String :=
  errJson s!"unknown store handle: {h}"

private def retainedFor (store : OpenStore) (keys : List String) :
    List RetainedArtifact :=
  store.artifacts.filter fun art => keys.contains art.key

/-- `storeHandleQuery(handle, sparql)` — the `storeQuery` envelope over the
blocks this handle already verified and decoded.

The plan is computed exactly as `storeQuery` computes it, so `"shards"` and
`"mode"` are the same values for the same query and manifest. A planned
artifact the handle does not retain is a refusal naming that artifact: the
handle answers the whole plan or it answers nothing. -/
def storeHandleQuery (h sparql : String) : IO String := do
  -- The caller-registered extension functions (SPARQL 1.1 section 17.6),
  -- read ONCE per query so the evaluator stays a function of its inputs.
  let extIris ← extSnapshot
  match (← storeHandleTable.get)[h]? with
  | none => pure (unknownStoreHandle h)
  | some store =>
    let outcome : Except String String := do
      let query ← parseQuery "storeHandleQuery" sparql
      let plan ← planFor "storeHandleQuery" store.manifest query
      let planKeys := plan.entries.map fun entry => entry.artifact.key.value
      match planKeys.find? (fun key => !(store.artifacts.any fun art => art.key == key)) with
      | some missing =>
          throw s!"storeHandleQuery: this query needs artifact '{missing}', which handle {h} does not retain; reopen the handle with it"
      | none => pure ()
      let extra : List (String × Json) :=
        [ ("shards", .number (toString plan.entries.length))
        , ("mode", .string plan.mode) ]
      let planned := retainedFor store planKeys
      /- The literal search path. It changes WHICH ROWS are materialised and
         nothing else: the same `sparql` text is evaluated, so the filter is
         re-applied to every candidate and the rows are the scan's rows. -/
      match (if store.ibk4 then
               (L4Factoidal.Storage.LiteralIndexPlan.plan? query).bind
                 (literalRestricted? planned)
             else none) with
      | some quads =>
          let ds := datasetOfQuads quads
          pure (queryParsedDatasetWith ds (backendOfRetained true ds) sparql extra extIris)
      | none =>
        if planKeys.length == store.artifacts.length then
          pure (queryParsedDatasetWith store.ds store.backend sparql extra extIris)
        else
          let ds := datasetOfRetained store.ibk4 planned
          pure (queryParsedDatasetWith ds (backendOfRetained store.ibk4 ds) sparql extra extIris)
    match outcome with
    | .error e => pure (errJson e)
    | .ok envelope => pure envelope

/-! ## storeHandleList and storeHandleClose -/

/-- `storeHandleList()` — what this process holds open, in open order, with
the two residency caps it is held against. A server that cannot see its own
residency cannot be operated. -/
def storeHandleList : IO String := do
  let table ← storeHandleTable.get
  let entries := table.toList.mergeSort fun a b => decide (a.2.ordinal ≤ b.2.ordinal)
  let bytes := entries.foldl (fun total pair => total + pair.2.retainedBytes) 0
  let rows := entries.foldl (fun total pair => total + pair.2.retainedRows) 0
  pure (okWith
    [ ("handles", .array (entries.map fun pair => .object (openStoreJson pair.1 pair.2)))
    , ("bytes", .number (toString bytes))
    , ("rows", .number (toString rows))
    , ("handleCap", .number (toString maxStoreHandles))
    , ("bytesCap", .number (toString maxStoreHandleBytes)) ])

/-- `storeHandleClose(handle)` — drop the store and everything it retained.
Closing an unknown (or already-closed) handle is the shared handle error. -/
def storeHandleClose (h : String) : IO String := do
  let table ← storeHandleTable.get
  if table.contains h then
    storeHandleTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownStoreHandle h)

end L4Wasm.Ops
