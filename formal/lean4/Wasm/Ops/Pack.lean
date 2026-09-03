/-
Wasm.Ops.Pack — building a Shardborough generation inside the module, and
verifying one before a host activates it.

https://github.com/danbri/factoidal/issues/641 stage 3. Design record:
`docs/designissues/2026-09-03-npm-pack-in-wasm.md`.

`Wasm/Ops/Store.lean` reads a generation a host already has. These
operations MAKE one. There is no file system inside the module — it is
linked without libuv by build decision — so the host reads the input and
writes the output, and every format decision stays here: which bytes an
artifact holds, what it is called, what its digest is, and what the manifest
commits. A JavaScript host that decides any of those is a violation of iron
rule 7 of CLAUDE.md.

## The two passes

`L4Factoidal/Storage/PackStream.lean` is the packer, and it has TWO bounded
passes over the source, not one. The first computes the source SHA-256 and
the generated-blank-node prefix (which must be free of the longest run of
underscores in the whole source, so it cannot be known from a prefix of it).
The second parses and publishes blocks. The operations therefore expose the
pass, and a host feeds the source twice:

  packBegin(syntaxTag, layoutTag)
    syntaxTag : turtle | trig | nquads | ntriples
    layoutTag : ibk2 | ibk3 | ibk4
    -> {"ok":true,"handle":"p1","pass":"prepass"}

  packFeed(handle)            -- the input chunk is the IN region
    -> {"ok":true,"pass":"prepass"|"ingest","pending":N}
       Feeding in the prepass produces no artifact, so `pending` is 0
       there; in the ingest pass it counts artifacts waiting.

  packEndPass(handle)
    -> {"ok":true,"pass":"ingest","pending":0}   -- after the first pass
    -> {"ok":true,"pass":"done","pending":N}     -- after the second

  packNext(handle)            -- one artifact comes back in the OUT region
    -> {"ok":true,"name":"predicate-0.ibk3","bytes":N}
    -> {"ok":true,"done":true}                   -- the queue is empty

  packFinish(handle)
    -> {"ok":true,"rows":N,"blocks":N,"layout":"…","wireVersion":N,
        "pending":N}
       Publishes the manifest and its TSV. Refused unless the pass is
       "done", because the manifest commits an artifact set which the
       ingest pass has not finished producing before then.

  packClose(handle)
    -> {"ok":true}

  activateVerify(manifestHex, windowsJson)  -- the artifacts are the IN region
    -> {"ok":true,"artifacts":N,"bytes":N} | {"ok":false,"error":"…"}

The host drives a pack as: `packBegin`, feed the whole source, `packEndPass`,
feed the whole source again, `packEndPass`, drain `packNext`, `packFinish`,
drain `packNext`, `packClose`. Draining after every feed keeps the queue, and
so the module's heap, bounded on the IBK3 path.

Every operation naming a handle which was never opened or is closed answers
the shared unknown-handle envelope, as `Wasm/Ops/Handles.lean` does. An
operation called in the wrong pass answers `{"ok":false,"error":"…"}` naming
the pass it is in and the pass it needs.

## The hasher

`build-wasm.sh` skips every `Harness_*` translation unit, so
`Harness.nativeHasher` is not reachable inside the module. The HACL* PRIMITIVE is
reachable: `Wasm/build-wasm.sh` compiles `Hacl_Hash_SHA2.c` and links
`l4_hacl_sha256`. These operations therefore pass the library's own binding,
`L4Factoidal.Crypto.sha256Hacl`, which is the same function the native
packer hashes with. The committed bytes are identical to the pure Lean
specification hasher's — the two hashers agree on every
input, which `lake exe l4vc-probe` measures — and that is what makes the
byte-identity gate against `l4block-shard-pack` meaningful. `PackStream`
takes the hasher as a parameter for exactly this reason.

## Where the state lives

The handle table is an `IO.Ref` in `Wasm/*`, the one IO-permitted layer, and
never in `L4Factoidal/*`. The table is per module instance (wasm) or per
process (native CLI). The pure `L4Wasm.call` cannot reach it and answers
"unknown op" for every operation here.

## Caps

A cap trip is an explicit error naming the cap and the value which exceeded
it; nothing is ever truncated silently (anti-pattern 25).

| Cap | Value | What it bounds |
|---|---|---|
| `maxPackFeedBytes` | 4194304 (4 MiB) | one `packFeed` region |
| `maxPackQueuedBytes` | 134217728 (128 MiB) | artifacts waiting for `packNext` |
| `maxPackSourceBytes` | 134217728 (128 MiB) | the IBK4 buffered source |
| `maxPackHandles` | 8 | open pack handles |
| `maxActivateBytes` | 134217728 (128 MiB) | one `activateVerify` region |

The two 128 MiB figures are chosen for a few hundred thousand triples on a
32-bit address space, which is what the module has. Measured on the
skosdex corpus: an IBK3 generation runs about 100 bytes per triple, so
128 MiB of queued artifacts is above a million triples, and the IBK3 path
never queues more than one publication batch anyway because the host drains
after every feed. The IBK4 path is the binding one: it holds the whole
source text as well as the whole generation, so 128 MiB of source is the
real limit there — roughly 1.3 million N-Quads lines. A larger corpus takes
the native packer, which streams from a file and is not addressed by 32
bits.

`maxPackFeedBytes` is 64 times the 65,536-byte chunk the native packer reads
and the JavaScript host feeds, so an ordinary host never approaches it; it is
there so a malformed call cannot ask the module for an unbounded copy.

No `partial`, no `sorry`, no `native_decide`.
-/
import Std.Data.HashMap
import Wasm.Ops.Store
import L4Factoidal.Storage.PackStream
import L4Factoidal.Storage.GenerationVerify
import L4Factoidal.Crypto.SHA2Native

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Storage.ShardManifest
open L4Factoidal.Storage.PackStream

/-! ## Caps -/

/-- The largest region one `packFeed` may carry: 4,194,304 bytes. -/
def maxPackFeedBytes : Nat := 4 * 1024 * 1024

/-- The largest total of artifact bytes which may wait for `packNext`:
    134,217,728 bytes. -/
def maxPackQueuedBytes : Nat := 128 * 1024 * 1024

/-- The largest source an IBK4 pack may buffer: 134,217,728 bytes. The IBK3
    path buffers no source at all. -/
def maxPackSourceBytes : Nat := 128 * 1024 * 1024

/-- The largest number of pack handles which may be open at once. -/
def maxPackHandles : Nat := 8

/-- The largest region one `activateVerify` may carry: 134,217,728 bytes. -/
def maxActivateBytes : Nat := 128 * 1024 * 1024

/-! ## The handle -/

/-- Which pass a handle is in. `prepass` computes the source identity and
    the blank-node prefix, `ingest` publishes blocks, `done` has published
    every block and awaits `packFinish`. -/
inductive PackPass where
  | prepass
  | ingest
  | done
  deriving DecidableEq

def passName : PackPass → String
  | .prepass => "prepass"
  | .ingest => "ingest"
  | .done => "done"

/-- One open pack. `ingest` is the streaming fold of the IBK2 and IBK3
    layouts; `source` is the buffered text of the IBK4 layout, which commits
    a graph-set summary over the whole source and so cannot stream. Exactly
    one of the two is used, decided by `format`. -/
structure OpenPack where
  format : PackFormat
  grammar : PackSyntax
  /-- The base IRI the grammar resolves relative IRIs against, as the host
      gave it. `none` is no base. The native packer uses `file://<input>`;
      a host that wants byte-identical output must pass the same string. -/
  base : Option String
  pass : PackPass
  pre : PrepassState
  prepass : Option SourcePrepass
  ingest : Option IngestState
  source : ByteArray
  packed : PackState
  queue : List Artifact
  queueBytes : Nat
  manifestPublished : Bool

/-- Handle ids already issued; `packBegin` numbers handles "p1", "p2", … in
    open order. Closing a handle never reuses its id. -/
initialize packCounter : IO.Ref Nat ← IO.mkRef 0

/-- The open packs, keyed by handle string. -/
initialize packTable : IO.Ref (Std.HashMap String OpenPack) ← IO.mkRef ∅

/-- The shared error envelope for a handle which is not in the table. -/
def unknownPackHandle (h : String) : String :=
  errJson s!"unknown pack handle: {h}"

private def wrongPass (op : String) (h : String) (state : PackPass) (needs : String) : String :=
  errJson s!"{op}: handle {h} is in pass '{passName state}', it needs pass {needs}"

private def withPack (h : String) (f : OpenPack → IO String) : IO String := do
  match (← packTable.get)[h]? with
  | none => pure (unknownPackHandle h)
  | some pack => f pack

/-- HACL* SHA-256, the same primitive the native packer hashes with.
    `Wasm/build-wasm.sh` compiles `Hacl_Hash_SHA2.c` and links
    `l4_hacl_sha256` into the module, so the extern resolves here. What is
    absent from the module is `Harness.nativeHasher`, because the build
    skips every `Harness_*` translation unit -- so this names the library's
    own binding (`L4Factoidal.Crypto.sha256Hacl`) rather than the harness
    wrapper. Crypto policy: HACL* on every target. -/
private def packHasher : L4Factoidal.Storage.BlockMerkle.Hasher :=
  ⟨L4Factoidal.Crypto.sha256Hacl⟩

private def totalBytes (artifacts : List Artifact) : Nat :=
  artifacts.foldl (fun total artifact => total + artifact.bytes.size) 0

/-- Add published artifacts to a handle's queue, or refuse against the queue
    cap. Nothing is dropped: a refusal leaves the handle unchanged. -/
private def enqueue (op : String) (pack : OpenPack) (artifacts : List Artifact) :
    Except String OpenPack :=
  let added := totalBytes artifacts
  if pack.queueBytes + added > maxPackQueuedBytes then
    .error s!"{op}: this pack has {pack.queueBytes + added} artifact bytes waiting, the cap is {maxPackQueuedBytes}"
  else
    .ok { pack with queue := pack.queue ++ artifacts, queueBytes := pack.queueBytes + added }

private def passEnvelope (pass : PackPass) (pending : Nat) : String :=
  okWith [("pass", .string (passName pass)), ("pending", .number (toString pending))]

/-! ## The operations -/

/-- `packBegin(syntaxTag, layoutTag, baseIri)` — open a pack and enter the
    prepass. An empty `baseIri` means no base, and a relative IRI in the
    source is then a parse error rather than a silently different term. The
    native packer passes `file://<input>`; a host that wants the same bytes
    must pass the same string, which is why this is an argument and not a
    default chosen here.
    A tag which names no grammar or no layout issues no handle. -/
def packBegin (syntaxTag layoutTag baseIri : String) : IO String := do
  match syntaxOfTag? syntaxTag, formatOfTag? layoutTag with
  | none, _ =>
      pure (errJson s!"packBegin: unknown grammar tag '{syntaxTag}' (turtle | trig | nquads | ntriples)")
  | _, none =>
      pure (errJson s!"packBegin: unknown layout tag '{layoutTag}' (ibk2 | ibk3 | ibk4)")
  | some grammar, some format =>
      -- The streaming fold of IBK2 and IBK3 reads with the Turtle grammar,
      -- which is what the native packer does for those layouts. N-Triples is
      -- a subset of Turtle, so it needs no separate fold; TriG and N-Quads
      -- carry named graphs, which an IBK3 block cannot hold.
      if (format == .ibk2 || format == .ibk3) &&
          !(grammar == .turtle || grammar == .ntriples) then
        pure (errJson s!"packBegin: layout {formatName format} reads turtle or ntriples, not {syntaxName grammar}; use layout ibk4 for named graphs")
      else do
        let table ← packTable.get
        if table.size >= maxPackHandles then
          pure (errJson s!"packBegin: {table.size} pack handles are open, the cap is {maxPackHandles}")
        else do
          let n ← packCounter.modifyGet fun n => (n + 1, n + 1)
          let h := s!"p{n}"
          packTable.modify (·.insert h
            { format, grammar, base := if baseIri.isEmpty then none else some baseIri,
              pass := .prepass, pre := prepassInit, prepass := none,
              ingest := none, source := ByteArray.empty, packed := {},
              queue := [], queueBytes := 0, manifestPublished := false })
          pure (okWith [("handle", .string h), ("pass", .string (passName PackPass.prepass))])

/-- `packFeed(handle)` over one IN region — one chunk of the source, in
    whichever pass the handle is in. -/
def packFeed (h : String) (blob : ByteArray) : IO String :=
  withPack h fun pack => do
    if blob.size > maxPackFeedBytes then
      pure (errJson s!"packFeed: the call carried {blob.size} bytes, the cap is {maxPackFeedBytes}")
    else match pack.pass with
    | .done => pure (wrongPass "packFeed" h pack.pass "'prepass' or 'ingest'")
    | .prepass =>
        match prepassFeed pack.pre blob with
        | .error e => pure (errJson e)
        | .ok pre => do
            packTable.modify (·.insert h { pack with pre })
            pure (passEnvelope .prepass 0)
    | .ingest =>
        match pack.ingest with
        | some state =>
            match ingestFeed state blob with
            | .error e => pure (errJson e)
            | .ok (next, made) =>
                match enqueue "packFeed" { pack with ingest := some next } made with
                | .error e => pure (errJson e)
                | .ok pack' => do
                    packTable.modify (·.insert h pack')
                    pure (passEnvelope .ingest pack'.queue.length)
        | none =>
            if pack.source.size + blob.size > maxPackSourceBytes then
              pure (errJson s!"packFeed: this pack has buffered {pack.source.size + blob.size} source bytes, the cap is {maxPackSourceBytes}")
            else do
              packTable.modify (·.insert h { pack with source := pack.source ++ blob })
              pure (passEnvelope .ingest pack.queue.length)

/-- The end of the ingest pass for the IBK4 layout: decode the buffered
    source, parse it, and publish every block. The source digest the prepass
    committed is checked here, as `ingestFinish` checks it on the streaming
    path — a source which changed between the two passes must not commit. -/
private def finishQuadPass (pack : OpenPack) (prepass : SourcePrepass) :
    Except String (PackState × List Artifact) := do
  let observed := (L4Factoidal.Crypto.Sha256Stream.init.update pack.source).finish
  if observed != prepass.sourceIdentity then
    .error "l4block-shard-pack input changed between pre-pass and parse pass"
  let text ← match String.fromUTF8? pack.source with
    | none => .error "l4block-shard-pack UTF-8 error: the source is not valid UTF-8"
    | some text => pure text
  let result ← quadArtifacts packHasher pack.grammar prepass text pack.base
  .ok (result.packed, result.artifacts)

/-- `packEndPass(handle)` — end the pass the handle is in.

    Ending the prepass computes the source digest and the generated
    blank-node prefix and starts the ingest pass. Ending the ingest pass runs
    the packer's own finish, which re-checks the source digest, and queues
    the last artifacts. -/
def packEndPass (h : String) : IO String :=
  withPack h fun pack => do
    match pack.pass with
    | .done => pure (wrongPass "packEndPass" h pack.pass "'prepass' or 'ingest'")
    | .prepass =>
        match prepassFinish pack.pre with
        | .error e => pure (errJson e)
        | .ok prepass => do
            let ingest :=
              if pack.format == .ibk4 then none
              else some (ingestInit packHasher pack.format prepass pack.base)
            packTable.modify (·.insert h
              { pack with pass := .ingest, prepass := some prepass, ingest })
            pure (passEnvelope .ingest 0)
    | .ingest =>
        match pack.prepass with
        | none => pure (errJson "packEndPass: this pack has no first-pass result")
        | some prepass =>
            let outcome :=
              match pack.ingest with
              | some state => ingestFinish state
              | none => finishQuadPass pack prepass
            match outcome with
            | .error e => pure (errJson e)
            | .ok (packed, made) =>
                let finished : OpenPack :=
                  { pack with pass := .done, packed := packed, ingest := none,
                              source := ByteArray.empty }
                match enqueue "packEndPass" finished made with
                | .error e => pure (errJson e)
                | .ok pack' => do
                    packTable.modify (·.insert h pack')
                    pure (passEnvelope .done pack'.queue.length)

/-- `packNext(handle)` — the next artifact, with its bytes in the OUT region.
    `{"ok":true,"done":true}` and an empty region when the queue is empty. -/
def packNext (h : String) : IO (String × ByteArray) := do
  match (← packTable.get)[h]? with
  | none => pure (unknownPackHandle h, ByteArray.empty)
  | some pack =>
      match pack.queue with
      | [] => pure (okWith [("done", .bool true)], ByteArray.empty)
      | artifact :: rest => do
          packTable.modify (·.insert h
            { pack with queue := rest, queueBytes := pack.queueBytes - artifact.bytes.size })
          pure (okWith [("name", .string artifact.name),
                        ("bytes", .number (toString artifact.bytes.size))],
                artifact.bytes)

/-- `packFinish(handle)` — publish the manifest and its TSV.

    Refused unless the pass is "done": the manifest commits the whole
    artifact set, and the ingest pass has not produced all of it before
    then. A second call is refused rather than queueing a second manifest. -/
def packFinish (h : String) : IO String :=
  withPack h fun pack => do
    if pack.pass != .done then
      pure (wrongPass "packFinish" h pack.pass "'done'")
    else if pack.manifestPublished then
      pure (errJson s!"packFinish: handle {h} has already published its manifest")
    else match pack.prepass with
    | none => pure (errJson "packFinish: this pack has no first-pass result")
    | some prepass =>
        let made :=
          if pack.format == .ibk4 then quadManifestArtifacts prepass pack.packed
          else manifestArtifacts pack.format prepass pack.packed
        match made with
        | .error e => pure (errJson e)
        | .ok artifacts =>
            match enqueue "packFinish" { pack with manifestPublished := true } artifacts with
            | .error e => pure (errJson e)
            | .ok pack' => do
                packTable.modify (·.insert h pack')
                pure (okWith
                  [ ("rows", .number (toString pack.packed.tripleCount))
                  , ("blocks", .number (toString pack.packed.entriesRev.length))
                  , ("layout", .string (layoutName pack.format))
                  , ("wireVersion", .number (toString (manifestVersion pack.format)))
                  , ("pending", .number (toString pack'.queue.length)) ])

/-- `packClose(handle)` — drop the pack. Closing an unknown or already
    closed handle is the shared handle error. -/
def packClose (h : String) : IO String := do
  let table ← packTable.get
  if table.contains h then
    packTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownPackHandle h)

/-! ## Verifying a generation before it is activated

The host reads every file of the candidate generation and carries them in one
region; each `{"key","offset","len"}` descriptor is a bounds-checked window
into it, exactly as `storeQuery` takes them, and the same decoder reads them.

Every rule is `L4Factoidal.Storage.GenerationVerify`, which
`Harness/ShardActivate.lean` also runs. Replacing CURRENT is the host's step;
this operation only answers a verdict.

Pre-SBM5 generations are refused by name. Their subject index is SRI1, whose
postings only the native paged materializer reads; refusing is correct where
admitting something unchecked is not. No packer in this repository writes one. -/

private def activateReader (resolved : List (String × ByteArray)) :
    L4Factoidal.Storage.GenerationVerify.Reader Id := fun name =>
  (resolved.find? fun pair => pair.1 == name).map Prod.snd

private def noLegacySubject : Entry → ArtifactRef → Id Bool := fun _ _ => pure false

/-- `activateVerify(manifestHex, windowsJson)` over one IN region — the
    verdict `Harness/ShardActivate.lean` reaches on the same bytes, minus the
    positioned-read pass which needs a file system. -/
def activateVerify (manifestHex windowsJson : String) (blob : ByteArray) : String :=
  let outcome : Except String String := do
    if blob.size > maxActivateBytes then
      throw s!"activateVerify: the call carried {blob.size} bytes, the cap is {maxActivateBytes}"
    let manifest ← decodeManifest? "activateVerify" manifestHex
    if !rangeCommitted manifest then
      throw "activateVerify: candidate manifest has no Merkle range commitment"
    if manifest.version < 5 then
      throw s!"activateVerify: this manifest is SBM{manifest.version}; the wasm activation check serves SBM5 and later, because an SBM4 subject index needs positioned reads"
    let sources ← artifactSources "activateVerify" windowsJson
    let resolved ← resolveSources "activateVerify" sources blob
    let read := activateReader resolved
    if !Id.run (L4Factoidal.Storage.GenerationVerify.verifyFullEntries packHasher read manifest.entries) then
      throw "candidate child artifact fails its declared SHA-256 commitment"
    match Id.run (L4Factoidal.Storage.GenerationVerify.verifyIndexSidecars read manifest.version
        noLegacySubject manifest.entries) with
    | some failure => throw failure
    | none => pure ()
    let readable : Option Nat :=
      if isIbk4Layout manifest.layout then
        Id.run (L4Factoidal.Storage.GenerationVerify.verifyQuadEntries read manifest.entries 0)
      else if isIbk3Layout manifest.layout then
        Id.run (L4Factoidal.Storage.GenerationVerify.verifyIbk3Entries read manifest.entries 0)
      else
        none
    match readable with
    | none =>
        if isIbk4Layout manifest.layout then throw L4Factoidal.Storage.GenerationVerify.quadEntryFailure
        else if isIbk3Layout manifest.layout then
          throw "candidate child artifact is missing, changed, or malformed"
        else
          throw s!"activateVerify: layout '{manifest.layout}' is neither an IBK3 nor an IBK4 generation"
    | some _ =>
        pure (okWith [("artifacts", .number (toString resolved.length)),
                      ("bytes", .number (toString (resolved.foldl
                        (fun total pair => total + pair.2.size) 0)))])
  match outcome with
  | .error e => errJson e
  | .ok envelope => envelope

/-! ## Executable ABI pins

These pin the pass machine, the handle envelope and the verification verdict
at the worker boundary. The byte-level agreement with `l4block-shard-pack` is
a separate gate: `lake exe l4wasm-cli pack` drives exactly these operations
and its generation directory is compared file by file with the native
packer's. -/

#guard (activateVerify "00" "[]" ByteArray.empty).contains "do not decode"
#guard (activateVerify "0" "[]" ByteArray.empty).contains "even number of hexadecimal digits"

end L4Wasm.Ops
