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

A cap trip is an explicit error naming the cap AND the value that tripped it;
nothing is evicted and nothing is truncated (anti-pattern 25).

| Cap | Value | What it bounds | What it protects against |
|---|---|---|---|
| `maxStoreHandles` | 8 | open store handles in the process | a host that opens and never closes: each handle carries a manifest, a dataset and an index whose fixed cost the byte cap counts only through its artifacts |
| `maxStoreHandleBytes` | 134217728 (128 MiB) | admitted artifact bytes retained across ALL open handles | resident memory, of which it is a measured proxy — see below |

These two are the handle path's OWN caps and they are process-wide.
`storeOpen` does NOT apply `storeQuery`'s `maxStoreArtifacts` (64),
`maxStoreBytes` (8 MiB) or `maxStoreRows` (100000); it did until
https://github.com/danbri/factoidal/issues/657, by inheritance rather than by
derivation.

### Why an artifact COUNT bounds nothing here

`storeQuery`'s 64-artifact cap was set when every query re-read, re-hashed and
re-decoded its blocks, so a wide plan meant a large cost paid AGAIN for every
question. A handle pays that cost once. What is left to bound is residency,
and residency is bytes: 257 small blocks may retain far less than four large
ones. On the skosdex corpus `skos:prefLabel` occupies 257 blocks — one per
graph, because the split cuts at graph boundaries — totalling 103341302
bytes, and the COUNT refused a set the BYTES admit. A count would have to
name a per-artifact cost that bytes does not already carry; there is none
large enough to bound, so there is no count cap.

`maxStoreRows` is dropped for the same reason. A row cannot be smaller than a
few packed bytes, so the byte cap bounds rows too, and `storeHandleList`
reports the retained row count for a host that wants to see it.

### Where 128 MiB comes from

`maxStoreHandleBytes` counts ADMITTED ARTIFACT BYTES — what the manifest
declares and what the host transferred. It is a PROXY for resident memory,
and the multiplier between the two is measured rather than assumed.

Measured 2026-09-05 on the full skosdex corpus (7,315,251 quads, 3,286
blocks, 204 named graphs, SBM8 with an LGI1 per block), through
`l4block-literal-gate --probe`, one handle over the corpus-wide
`skos:prefLabel` plan:

    retained artifact bytes        103,341,302   (257 IBK4 blocks)
    region transferred             159,673,831   (those blocks + 257 LGI1)
    peak resident                1,675,345,920
    resident per retained byte            16.2

The peak covers the transferred region, the decoded rows, the rebuilt
object-row index, the decoded sidecars and the working set of the queries
that followed. The row-identity gate, which opens the SAME set twice (once
without the sidecars), measured 2,569,797,632 resident for 206,682,604
retained bytes — 12.4. A second run of the same one-handle probe measured
1,369,391,104 resident — 13.3. Three readings on one shared machine spread
from 12.4 to 16.2, and the cap is derived from the LARGEST of them.

wasm32 gives 4,294,967,296 bytes of address space in total, and a browser tab
in practice holds less. Half of it is reserved here for the host's own
allocations, for the incoming region before the engine consumes it, and for
growth:

    2,147,483,648 / 16.2  =  132,464,438 bytes

The cap is the nearest power of two, 134217728 (128 MiB). That is 1.3 percent
above the computed bound and predicts 2,175,907,586 bytes resident, 50.7
percent of the wasm32 address space; the rounding is inside the variation of
the multiplier itself, which is data-dependent. It admits the corpus-wide
`skos:prefLabel` set with 30,876,426 bytes of headroom, and refuses a second
handle over the same set.

A SINGLE SMALL block measures a much larger multiple — about 32 for a 5.5 MB
block — because it carries the fixed cost of the process. The marginal figure
above is the one a cap is derived from. The multiplier stays data-dependent:
many short literals over a large dictionary cost more per packed byte than
few long ones. A host that must bound its OWN memory reads `storeHandleList`
and measures its own process; this cap bounds the engine, not the host.

### Why `storeQuery`'s caps did not move

They answer a different question. `storeQuery` pays the hash and the decode
on EVERY call, so its caps bound one call's latency, and 8 MiB is set by the
throughput of the pure Lean SHA-256, not by memory. Raising them would make a
single stateless call slower without making any second call faster. A host
with a wide query opens a handle.

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
import L4Factoidal.Storage.GeoBBoxIndexWire
import L4Factoidal.Storage.GeoIndexPlan

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
open store handle. This is the packed size, not the resident size; the banner
carries the measured multiplier between them and the arithmetic that turns it
into this number. -/
def maxStoreHandleBytes : Nat := 128 * 1024 * 1024

/-! ## What a handle retains -/

/-- The decoded rows of one artifact, in the form its generation's codec
denotes: triples for an IBK3 predicate block, quads for an IBK4 block. -/
inductive RetainedRows where
  | ibk3 (triples : List Triple)
  | ibk4 (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow)

/-- What one block's candidate-filter sidecars let a query skip.

`literal` and `geo` are the decoded LGI1 and GBI1 sidecars, each present only
when the manifest declared it, the host supplied its bytes, it decoded, and it
names THIS block. They share the row machinery below because they index the
SAME local dictionary IDs.

`rows` is the block's denoted quads by position, and `objectRows` maps a
dictionary local ID to the positions whose OBJECT is that term — the OLI2
role, rebuilt here at `storeOpen` because SBM8 and SBM9 commit no graph-aware
OLI2. `nonLiteralRows` is every position whose object is not a literal; a
`STR` shape keeps those, because `STR` of an IRI is a string a `CONTAINS` can
match and LGI1 indexes no IRI (`LiteralIndexPlan.Plan.keepNonLiterals`). The
geometry path never keeps them: `Geo.wktArg` refuses a non-literal term, so
such a row is a type error and the filter excludes it. -/
structure RetainedIndexes where
  literal : Option L4Factoidal.Storage.LiteralGramIndex.Index
  geo : Option L4Factoidal.Storage.GeoBBoxIndex.Index
  rows : Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow
  objectRows : Array (Array Nat)
  nonLiteralRows : Array Nat

/-- One admitted artifact, decoded. `bytes` and `rows` are the manifest's own
declarations, which admission has already checked the bytes against.
`indexes` is present when the manifest declared at least one candidate-filter
sidecar AND the host supplied its bytes; a handle opened without them still
answers, by scanning. -/
structure RetainedArtifact where
  key : String
  predicate : WfIri
  bytes : Nat
  rows : Nat
  payload : RetainedRows
  indexes : Option RetainedIndexes

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

/-- One sidecar the manifest declared, decoded and checked against this block,
or `none`. Every `none` is a FALLBACK, not an error: the handle then scans,
which is what it did before the sidecar existed. -/
private def retainedSidecar? {α : Type} (op : String) (ref? : Option ArtifactRef)
    (sources : List (String × ArtifactSource)) (blob : ByteArray)
    (decode : ByteArray → Option α) : Option α := do
  let ref ← ref?
  let _ ← supplied? sources ref.key.value
  let indexBytes ← (admitRef op ref sources blob).toOption
  decode indexBytes

/-- Build the retained candidate-filter indexes of one IBK4 block, or `none`
when the manifest declares neither sidecar, the host supplied bytes for
neither, neither decodes, or neither names this block. -/
def retainedIndexes? (op : String) (entry : Entry)
    (sources : List (String × ArtifactSource)) (blob : ByteArray)
    (quads : List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) (blockBytes : ByteArray) :
    Option RetainedIndexes := do
  let literal? := retainedSidecar? op entry.literalIndex sources blob (fun bytes =>
    match L4Factoidal.Storage.LiteralGramIndexWire.decode? bytes with
    | some artifact =>
        if artifact.targetIBKSha256 == entry.artifact.sha256 then some artifact.index else none
    | none => none)
  let geo? := retainedSidecar? op entry.geoIndex sources blob (fun bytes =>
    match L4Factoidal.Storage.GeoBBoxIndexWire.decode? bytes with
    | some artifact =>
        if artifact.targetIBKSha256 == entry.artifact.sha256 then some artifact.index else none
    | none => none)
  if literal?.isNone && geo?.isNone then none else do
  let block ← L4Factoidal.Storage.IndexedBlockWireV4.decode blockBytes
  let rows := quads.toArray
  -- `denotes` filters, so a block whose rows do not all decode would make the
  -- positions disagree with the object IDs. Refuse rather than misalign.
  if block.rows.size != rows.size then none else
  -- A sidecar sized for another dictionary is dropped rather than trusted.
  let literal? := literal?.filter fun index => index.dictCount == block.dict.size
  let geo? := geo?.filter fun index => index.dictCount == block.dict.size
  if literal?.isNone && geo?.isNone then none else
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
    pure { literal := literal?, geo := geo?, rows, objectRows, nonLiteralRows })

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
                    retainedIndexes? op entry sources blob quads bytes))
          else
            (do let triples ← ibk3TriplesOf op entry bytes
                pure (RetainedRows.ibk3 triples, none))
      readRetained op ibk4 sources blob rest
        ({ key := entry.artifact.key.value
         , predicate := entry.predicate
         , bytes := entry.artifact.bytes
         , rows := entry.rows
         , payload
         , indexes := literal } :: acc)

/-- Every key an entry declares, in any role: the block itself and each
sidecar the manifest names for it.

This must agree with what `storeManifestInspect` REPORTS, or a host that
supplies exactly what one operation told it is refused by the other. It
did not: the check admitted only the block, `literalIndex` and
`geoIndex`, while inspect reports `subjectIndex`, `termIndex` and
`objectIndex` too, so `openStoreHandle` with no options failed on any
IBK3 generation with `artifact 'predicate-0.ibk3.sri2' is not declared
by this manifest` (measured 2026-09-05 on the bundled sample store).
A handle does not USE the SRI2, TLI1 and OLI2 sidecars, but they ARE
declared, and refusing a declared artifact is a different statement from
refusing an undeclared one. -/
private def entryDeclaredKeys (entry : Entry) : List String :=
  entry.artifact.key.value ::
    ([entry.subjectIndex, entry.termIndex, entry.objectIndex,
      entry.literalIndex, entry.geoIndex].filterMap
        (fun ref? => ref?.map fun ref => ref.key.value))

/-- Every key the host supplied bytes for must be a key this manifest
declares; an unknown key is a host fault, not a silently ignored argument. -/
private def checkSuppliedKeys (op : String) (manifest : Manifest)
    (sources : List (String × ArtifactSource)) : Except String Unit :=
  match sources.find? (fun pair =>
      !(manifest.entries.any fun entry =>
          (entryDeclaredKeys entry).contains pair.1)) with
  | some (key, _) => .error s!"{op}: artifact '{key}' is not declared by this manifest"
  | none => pure ()

/-- The retained-bytes admission of one `storeOpen`. `held` is the artifact
bytes every already-open handle retains; `entries` are the manifest entries
this open would add. It is checked BEFORE any artifact is hashed or decoded,
so a refusal costs the manifest decode and nothing more. -/
def checkHandleBytes (held : Nat) (entries : List Entry) : Except String Unit := do
  let want := held + totalBytesOf entries
  if want > maxStoreHandleBytes then
    throw s!"storeOpen: this open would retain {want} artifact bytes, the cap is {maxStoreHandleBytes}"
  pure ()

/-- The admission of `storeOpen`, kept pure so the IO layer only inserts the
result. -/
private def buildOpenStore (held : Nat) (manifestHex artifactsJson : String)
    (blob : ByteArray) : Except String OpenStore := do
  let manifest ← decodeManifest? "storeOpen" manifestHex
  let ibk4 ← storeLayoutIbk4? "storeOpen" manifest
  let sources ← artifactSources "storeOpen" artifactsJson
  checkSuppliedKeys "storeOpen" manifest sources
  let entries := manifest.entries.filter fun entry =>
    sources.any fun pair => pair.1 == entry.artifact.key.value
  if entries.isEmpty then
    throw "storeOpen: no artifact bytes were supplied; a handle retains at least one block"
  checkHandleBytes held entries
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

Refuses, naming the cap and the value, when the process already holds
`maxStoreHandles` handles or when this open would push the retained artifact
bytes above `maxStoreHandleBytes`. The byte refusal is decided from the
manifest's own declarations BEFORE any artifact is hashed or decoded, so it
costs the manifest decode and nothing more. Nothing is evicted. -/
def storeOpen (manifestHex artifactsJson : String) (blob : ByteArray) : IO String := do
  let table ← storeHandleTable.get
  if table.size ≥ maxStoreHandles then
    pure (errJson s!"storeOpen: {table.size} store handles are open, the cap is {maxStoreHandles}")
  else
    let held := table.fold (fun total _ opened => total + opened.retainedBytes) 0
    match buildOpenStore held manifestHex artifactsJson blob with
    | .error e => pure (errJson e)
    | .ok store => do
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
def rowsOfCandidates (retained : RetainedIndexes) (extra : Array Nat) (ids : List Nat) :
    Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow := Id.run do
  let mut positions : Array Nat := extra
  for id in ids do
    if h : id < retained.objectRows.size then
      positions := positions ++ retained.objectRows[id]
  let ordered := positions.qsort (fun a b => decide (a < b))
  pure (ordered.filterMap fun position => retained.rows[position]?)

def literalRows? (retained : RetainedIndexes)
    (plan : L4Factoidal.Storage.LiteralIndexPlan.Plan) :
    Option (Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := do
  let index ← retained.literal
  let ids ← L4Factoidal.Storage.LiteralGramIndex.candidates? index plan.needle
  some (rowsOfCandidates retained
    (if plan.keepNonLiterals then retained.nonLiteralRows else #[]) ids)

/-- The rows of one block a geometry `FILTER` can reach: the candidate terms'
rows and nothing else. No non-literal row is kept, because `Geo.wktArg`
refuses a term that is not a `geo:wktLiteral` and the filter drops it.

`none` means the index cannot serve this query — `sfDisjoint`, or a query
geometry outside the proved fragment — and the caller must scan. -/
def geoRows? (retained : RetainedIndexes)
    (plan : L4Factoidal.Storage.GeoIndexPlan.Plan) :
    Option (Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) := do
  let index ← retained.geo
  let ids ← L4Factoidal.Storage.GeoBBoxIndex.candidates? index plan.op plan.query
  some (rowsOfCandidates retained #[] ids)

/-- The whole planned artifact set restricted by one candidate filter, or
`none` when any planned block cannot serve it: no retained index, or a
predicate the plan does not name, or an argument the index refuses. Every
`none` is a fallback to the scan.

The `restrict` argument is `literalRows?` or `geoRows?`. Both return a
SUPERSET of the rows their filter accepts, and `storeHandleQuery` then
evaluates the original query text over the result, so neither can add a row
and neither can drop one. -/
def restricted? {π : Type} (arts : List RetainedArtifact) (predicate : WfIri)
    (restrict : RetainedIndexes → π → Option (Array L4Factoidal.Storage.IndexedBlockWireV4.QuadRow))
    (plan : π) : Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  arts.foldlM (fun acc art => do
    if art.predicate != predicate then none else do
    let retained ← art.indexes
    let rows ← restrict retained plan
    some (acc ++ rows.toList)) []

def literalRestricted? (arts : List RetainedArtifact)
    (plan : L4Factoidal.Storage.LiteralIndexPlan.Plan) :
    Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  restricted? arts plan.predicate literalRows? plan

def geoRestricted? (arts : List RetainedArtifact)
    (plan : L4Factoidal.Storage.GeoIndexPlan.Plan) :
    Option (List L4Factoidal.Storage.IndexedBlockWireV4.QuadRow) :=
  restricted? arts plan.predicate geoRows? plan

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
      /- The candidate-filter paths, literal search and geometry. Each changes
         WHICH ROWS are materialised and nothing else: the same `sparql` text
         is evaluated, so the filter is re-applied to every candidate and the
         rows are the scan's rows. A bounding box in particular can EXCLUDE
         and can never CONFIRM, so dropping the re-evaluation would return
         rows the query does not license.

         The two plans cannot both admit one query: `LiteralIndexPlan` needs a
         `CONTAINS`/`STRSTARTS`/`STRENDS` conjunct and `GeoIndexPlan` needs a
         `geof:` call. The literal plan is tried first, and its answer is used
         when it applies. -/
      match (if store.ibk4 then
               ((L4Factoidal.Storage.LiteralIndexPlan.plan? query).bind
                  (literalRestricted? planned)).orElse (fun _ =>
                (L4Factoidal.Storage.GeoIndexPlan.plan? query).bind
                  (geoRestricted? planned))
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

/-! ## Cap tests

`checkHandleBytes` is the function `storeOpen` calls, against the shipped
constant, so these exercise the refusal a host sees rather than a copy of
it. -/

private def capEntry (bytes : Nat) : Entry :=
  { predicate := ⟨"http://example.org/p", by decide⟩
  , artifact := { key := ⟨"predicate-0.ibk4"⟩, bytes, sha256 := ByteArray.empty,
                  chunked := none }
  , rows := 0
  , ordinal := 0 }

-- Exactly the cap is admitted; one byte more is refused, and the refusal
-- names the value that tripped it AND the cap (anti-pattern 25).
#guard (checkHandleBytes 0 [capEntry maxStoreHandleBytes]).toOption.isSome
#guard match checkHandleBytes 0 [capEntry (maxStoreHandleBytes + 1)] with
  | .error e => e.contains (toString (maxStoreHandleBytes + 1)) &&
                e.contains (toString maxStoreHandleBytes)
  | .ok _ => false

-- The bound is over EVERY open handle. A set that fits on its own is refused
-- once another handle already holds the budget, and the message names the
-- TOTAL, not this call's share.
#guard match checkHandleBytes maxStoreHandleBytes [capEntry 1] with
  | .error e => e.contains (toString (maxStoreHandleBytes + 1))
  | .ok _ => false

-- The count of artifacts bounds nothing here: 512 blocks of 1024 bytes are
-- admitted, where `storeQuery`'s inherited 64-artifact cap refused them.
#guard (checkHandleBytes 0 (List.replicate 512 (capEntry 1024))).toOption.isSome

-- The corpus-wide `skos:prefLabel` artifact set of the skosdex corpus,
-- measured 2026-09-05: 257 blocks, 103341302 bytes. It is admitted, and a
-- second handle over the same set is not.
#guard (checkHandleBytes 0 [capEntry 103341302]).toOption.isSome
#guard (checkHandleBytes 103341302 [capEntry 103341302]).toOption.isNone

end L4Wasm.Ops
