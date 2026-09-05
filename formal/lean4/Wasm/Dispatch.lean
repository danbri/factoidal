/-
Wasm.Dispatch — the dispatch entries `L4Wasm.call` and `L4Wasm.callIO`.

  L4Wasm.call   (op : String) (argsJson : String) : String
  L4Wasm.callIO (op : String) (argsJson : String) : IO String

`argsJson` is a JSON ARRAY OF STRINGS (positional arguments); the
result is one JSON envelope, `{"ok":true,…}` or
`{"ok":false,"error":"…"}`. Method names and envelopes match the F*
npm entry point (`bin/npm-entry/entry_jsoo.ml`) op for op, so the JS
side can drive either engine through the same result handling
(`api.js`'s `entryResult`).

`call` serves the stateless ops. `callIO` serves those SAME ops
unchanged (it delegates to `call`) PLUS the dataset-handle ops of
https://github.com/danbri/factoidal/issues/585, whose store
(`Wasm/Ops/Handles.lean`) is an `IO.Ref` a pure entry cannot reach.
The wire entry (`l4_call_c` in `Wasm/l4_shim.c`) and the native CLI
(`Wasm/Main.lean`) route through `callIO`; the pure `call` stays
`@[export]`ed as `l4_call` with its signature unchanged.

The op tables below are the whole v1 surface plus a reflection op:

  "ops" -> {"ok":true,"abiVersion":"…","ops":[…names…]}

(through `callIO` the list includes the handle ops; through the pure
`call` it does not, because that entry cannot serve them).

This module owns the tables; the op bodies live in `Wasm/Ops/*.lean`
(split-ready: each imports only the `L4Factoidal.*` modules it needs —
never the umbrella, whose initializer dies under wasm32; see
`Wasm/Abi.lean`'s import note). The phase-1 `bgpQuery`/`version`
exports in `Wasm/Abi.lean` are a separate, pinned surface (hub post
36) and are not routed through this dispatch.
-/
import Wasm.Ops.Parse
import Wasm.Ops.Query
import Wasm.Ops.Reason
import Wasm.Ops.Canon
import Wasm.Ops.Block
import Wasm.Ops.Store
import Wasm.Ops.StoreHandles
import Wasm.Ops.CL
import Wasm.Ops.Proof
import Wasm.Ops.Handles
import Wasm.Ops.Pack
import Wasm.Ops.ExtFns

namespace L4Wasm

open L4Wasm.Ops
open L4Factoidal.JSON

/-- Version of the DISPATCH ABI's envelope contract. "1" — the same
value the F* npm entry reports (`entry_jsoo.ml`'s `abi_version`),
because the envelopes are the same contract. Bump when a signature or
JSON shape changes. -/
def dispatchAbiVersion : String := "1"

/-- The stateless op names, in the order they are matched. Served by
both `call` and `callIO`. -/
def opNames : List String :=
  [ "parseToDatasetJson"
  , "queryDataset"
  , "updateDataset"
  , "serializeNQuads"
  , "serializeTurtle"
  , "canonicalizeToNQuads"
  , "scanIBK2Predicate"
  , "scanIBK3Predicate"
  , "queryIBK3BlockSetPreview"
  , "storeManifestInspect"
  , "storeQueryPlan"
  , "storeQuery"
  , "activateVerify"
  , "owlClosure"
  , "owlIsConsistent"
  , "owlEntails"
  , "rhoDfClosure"
  , "rhoDfFragmentCheck"
  , "rdfsPlusClosure"
  , "clParse"
  , "clSerialize"
  , "clAlphaNorm"
  , "clNormalize"
  , "clFiniteSat"
  , "proofCheck"
  , "proofInspect"
  , "ops" ]

/-- The op names that read a BLOB REGION as well as their string arguments,
served by `callBlob` below.

The dispatch ABI carries strings, so an op that must read megabytes of block
bytes cannot use it: hexadecimal doubles the bytes over the boundary and then
walks every character on the way in. `callBlob` takes one contiguous byte
region the host wrote directly into the wasm heap, and the op's JSON argument
describes windows into it (`Wasm/Ops/Store.lean`). Through the plain `call`
these ops still answer — with an empty region, so a descriptor naming blob
bytes is refused by name rather than silently reading nothing. -/
def blobOpNames : List String := [ "storeQuery", "activateVerify" ]

/-- The op names that also RETURN a contiguous byte region, served by
`callBlobIO` below (the `l4_call_blob_io` C export, wired to
`l4_call_blob_io_c` in `Wasm/l4_shim.c`).

`blobOpNames` above carries bytes IN. This table carries bytes OUT, for the
same reason and with no encoding: an artifact returned as hexadecimal doubles
the bytes over the boundary, and base64 was refused (owner, 2026-09-03). The
measured cost on the read path was 242,416 bytes and 96 ms for hexadecimal
against 4,893 bytes and 70 ms for the raw region.

`blobEcho` is a self test and nothing else: it builds a region whose byte `i`
is `(i * 7 + 3) mod 256`, so a host can prove the whole path — Lean, the
shim, the Emscripten export, the JavaScript binder — moves every byte without
truncation.

`packFeed` and `packNext` (`Wasm/Ops/Pack.lean`) are the pack operations of
stage C in `docs/designissues/2026-09-03-npm-pack-in-wasm.md`. `packFeed`
reads one chunk of the source from the IN region and builds no OUT region;
`packNext` reads nothing and returns one artifact's bytes. Both are here
because both are served by the one entry which carries a region in either
direction. -/
def blobIoOpNames : List String := [ "blobEcho", "packFeed", "packNext" ]

/-- Largest out region `blobEcho` builds: 67,108,864 bytes. A count above
this is refused by name rather than made into an allocation the module
cannot serve. -/
def blobEchoMaxBytes : Nat := 67108864

/-- Byte `i` of the self-test region: `(i * 7 + 3) mod 256`. The stride is
odd and coprime with 256, so a host that drops, duplicates or reorders a
byte sees it. -/
def blobEchoByte (i : Nat) : UInt8 := UInt8.ofNat ((i * 7 + 3) % 256)

private def blobEchoFill : Nat → Nat → ByteArray → ByteArray
  | 0,          _, acc => acc
  | Nat.succ k, i, acc => blobEchoFill k (i + 1) (acc.push (blobEchoByte i))

/-- The `n`-byte self-test region. -/
def blobEchoRegion (n : Nat) : ByteArray :=
  blobEchoFill n 0 (ByteArray.emptyWithCapacity n)

/-- `blobEcho(lengthHint)`: `{"ok":true,"bytes":N}` plus an `N`-byte out
region. This op has no RDF, SPARQL or storage content — it exists to prove
the byte path, so it deliberately has no `Wasm/Ops/*.lean` module. -/
private def blobEcho (arg : String) : String × ByteArray :=
  match arg.toNat? with
  | none => (errJson s!"blobEcho: '{arg}' is not a decimal byte count",
             ByteArray.empty)
  | some n =>
    if n > blobEchoMaxBytes then
      (errJson s!"blobEcho: {n} bytes is above the {blobEchoMaxBytes}-byte limit",
       ByteArray.empty)
    else
      ((Json.object [("ok", .bool true), ("bytes", .number (toString n))]).toString,
       blobEchoRegion n)

private def arity1 (op : String) (f : String → String) :
    List String → String
  | [a] => f a
  | args => errJson s!"{op} expects 1 argument, got {args.length}"

private def arity2 (op : String) (f : String → String → String) :
    List String → String
  | [a, b] => f a b
  | args => errJson s!"{op} expects 2 arguments, got {args.length}"

private def arity3 (op : String) (f : String → String → String → String) :
    List String → String
  | [a, b, c] => f a b c
  | args => errJson s!"{op} expects 3 arguments, got {args.length}"

/-- The dataset-handle op names (`Wasm/Ops/Handles.lean`), served ONLY
by `callIO` — the pure `call` cannot reach the handle store and
answers "unknown op" for these. -/
def handleOpNames : List String :=
  [ "datasetOpen"
  , "datasetQuery"
  , "datasetUpdate"
  , "datasetSerialize"
  , "datasetClose" ]

/-- The store-handle op names (`Wasm/Ops/StoreHandles.lean`), served ONLY by
`callIO` and `callBlobIO` — the pure `call` cannot reach the store-handle
table. `storeOpen` also carries a byte region IN; through `callIO`, which
carries none, it still answers, with an empty region, so the diagnostic
`{"key","bytes":"<hex>"}` descriptor form works through the plain entry and
through `Wasm/Main.lean`'s `callseq`. -/
def storeHandleOpNames : List String :=
  [ "storeOpen"
  , "storeHandleQuery"
  , "storeHandleList"
  , "storeHandleClose" ]

/-- The SPARQL 1.1 §17.6 extension-registry op names
(`Wasm/Ops/ExtFns.lean`), served ONLY by `callIO` and `callBlobIO` — the
registry is an `IO.Ref` the pure `call` cannot reach, so that entry keeps
answering with the built-in `geof:` table alone. -/
def extOpNames : List String :=
  [ "extRegister"
  , "extUnregister"
  , "extClear"
  , "extList" ]

/-- The pack op names (`Wasm/Ops/Pack.lean`), served ONLY by `callIO` and
`callBlobIO` — the pure `call` cannot reach the pack table. `packFeed` and
`packNext` also need a byte region and are listed in `blobIoOpNames`; through
`callIO`, which carries none, they answer an error naming the entry they
need rather than feeding nothing. -/
def packOpNames : List String :=
  [ "packBegin"
  , "packFeed"
  , "packEndPass"
  , "packNext"
  , "packFinish"
  , "packClose" ]

/-- `{"ok":true,"abiVersion":"…","ops":[…],"blobOps":[…],"blobIoOps":[…]}`. -/
private def opsReflectionFor (names : List String) : String :=
  (Json.object
    [ ("ok", .bool true)
    , ("abiVersion", .string dispatchAbiVersion)
    , ("ops", .array (names.map Json.string))
    , ("blobOps", .array (blobOpNames.map Json.string))
    , ("blobIoOps", .array (blobIoOpNames.map Json.string)) ]).toString

private def opsReflection : String := opsReflectionFor opNames

/-- The dispatch entry the `l4_call` C export serves. -/
def call (op : String) (argsJson : String) : String :=
  match decodeArgs argsJson with
  | .error e => errJson e
  | .ok args =>
    match op with
    | "parseToDatasetJson"   => arity3 op parseToDatasetJson args
    | "queryDataset"         => arity2 op queryDataset args
    | "updateDataset"        => arity2 op updateDataset args
    | "serializeNQuads"      => arity1 op serializeNQuads args
    | "serializeTurtle"      => arity1 op serializeTurtle args
    | "canonicalizeToNQuads" => arity1 op canonicalizeToNQuads args
    | "scanIBK2Predicate"    => arity2 op scanIBK2Predicate args
    | "scanIBK3Predicate"    => arity3 op scanIBK3Predicate args
    | "queryIBK3BlockSetPreview"    => arity3 op queryIBK3BlockSetPreview args
    | "storeManifestInspect" => arity1 op storeManifestInspect args
    | "storeQueryPlan"       => arity2 op storeQueryPlan args
    | "storeQuery"           => arity3 op (fun a b c => storeQuery a b c ByteArray.empty) args
    | "activateVerify"       => arity2 op (fun a b => activateVerify a b ByteArray.empty) args
    | "owlClosure"           => arity2 op owlClosure args
    | "owlIsConsistent"      => arity2 op owlIsConsistent args
    | "owlEntails"           => arity3 op owlEntails args
    | "rhoDfClosure"         => arity1 op rhoDfClosure args
    | "rhoDfFragmentCheck"   => arity1 op rhoDfFragmentCheck args
    | "rdfsPlusClosure"      => arity1 op rdfsPlusClosure args
    | "clParse"              => arity1 op clParse args
    | "clSerialize"          => arity1 op clSerialize args
    | "clAlphaNorm"          => arity1 op clAlphaNorm args
    | "clNormalize"          => arity1 op clNormalize args
    | "clFiniteSat"          => arity2 op clFiniteSat args
    | "proofCheck"           => arity1 op proofCheck args
    | "proofInspect"         => arity1 op proofInspect args
    | "ops"                  => opsReflection
    | _                      => errJson s!"unknown op '{op}'"

/-- The dispatch entry the `l4_call_blob` C export serves: the string
arguments of `call`, plus one byte region. Every other op delegates to `call`,
envelope for envelope, so a host may route everything through this entry. -/
def callBlob (op : String) (argsJson : String) (blob : ByteArray) : String :=
  match op with
  | "storeQuery" =>
      match decodeArgs argsJson with
      | .error e => errJson e
      | .ok [a, b, c] => storeQuery a b c blob
      | .ok args => errJson s!"storeQuery expects 3 arguments, got {args.length}"
  | "activateVerify" =>
      match decodeArgs argsJson with
      | .error e => errJson e
      | .ok [a, b] => activateVerify a b blob
      | .ok args => errJson s!"activateVerify expects 2 arguments, got {args.length}"
  | _ => call op argsJson

private def arityIO1 (op : String) (f : String → IO String) :
    List String → IO String
  | [a] => f a
  | args => pure (errJson s!"{op} expects 1 argument, got {args.length}")

private def arityIO2 (op : String) (f : String → String → IO String) :
    List String → IO String
  | [a, b] => f a b
  | args => pure (errJson s!"{op} expects 2 arguments, got {args.length}")

private def arityIO3 (op : String) (f : String → String → String → IO String) :
    List String → IO String
  | [a, b, c] => f a b c
  | args => pure (errJson s!"{op} expects 3 arguments, got {args.length}")

/-- The dispatch entry the wire (`l4_call_c` via the `l4_call_io` C
export) and the native CLI serve: the dataset-handle ops, plus every
stateless op via `call`, envelope for envelope. -/
def callIO (op : String) (argsJson : String) : IO String :=
  let withArgs (k : List String → IO String) : IO String :=
    match decodeArgs argsJson with
    | .error e  => pure (errJson e)
    | .ok args  => k args
  match op with
  -- §17.6 extension functions. `queryDataset` and `storeQuery` are
  -- overridden here (rather than delegating to the pure `call`) so a
  -- caller registration reaches the stateless query ops too; every other
  -- stateless op still falls through to `call` unchanged.
  | "extRegister"      => withArgs (arityIO1 op Ops.extRegister)
  | "extUnregister"    => withArgs (arityIO1 op Ops.extUnregister)
  | "extClear" =>
      withArgs (fun args =>
        match args with
        | [] => Ops.extClear
        | args => pure (errJson s!"extClear expects 0 arguments, got {args.length}"))
  | "extList" =>
      withArgs (fun args =>
        match args with
        | [] => Ops.extList
        | args => pure (errJson s!"extList expects 0 arguments, got {args.length}"))
  | "queryDataset"     => withArgs (arityIO2 op Ops.queryDatasetIO)
  | "storeQuery"       => withArgs (arityIO3 op
                            (fun a b c => Ops.storeQueryIO a b c ByteArray.empty))
  | "datasetOpen"      => withArgs (arityIO3 op Ops.datasetOpen)
  | "datasetQuery"     => withArgs (arityIO2 op Ops.datasetQuery)
  | "datasetUpdate"    => withArgs (arityIO2 op Ops.datasetUpdate)
  | "datasetSerialize" => withArgs (arityIO2 op Ops.datasetSerialize)
  | "datasetClose"     => withArgs (arityIO1 op Ops.datasetClose)
  -- packBegin takes an optional third argument, the base IRI, and an
  -- optional fourth, the publication batch in source bytes. Fewer arguments
  -- means no base and the default batch, which keeps every host written
  -- against the stage-C contract working and makes a relative IRI a parse
  -- error rather than a silently different term.
  | "packBegin" =>
      withArgs (fun args =>
        match args with
        | [a, b]       => Ops.packBegin a b "" ""
        | [a, b, c]    => Ops.packBegin a b c ""
        | [a, b, c, d] => Ops.packBegin a b c d
        | args => pure (errJson s!"packBegin expects 2, 3 or 4 arguments, got {args.length}"))
  | "packEndPass"      => withArgs (arityIO1 op Ops.packEndPass)
  | "packFinish"       => withArgs (arityIO1 op Ops.packFinish)
  | "packClose"        => withArgs (arityIO1 op Ops.packClose)
  | "packFeed" | "packNext" =>
      pure (errJson s!"{op} carries a byte region; call it through l4_call_blob_io")
  | "storeOpen"        => withArgs (arityIO2 op (fun a b => Ops.storeOpen a b ByteArray.empty))
  | "storeHandleQuery" => withArgs (arityIO2 op Ops.storeHandleQuery)
  | "storeHandleClose" => withArgs (arityIO1 op Ops.storeHandleClose)
  | "storeHandleList" =>
      withArgs (fun args =>
        match args with
        | [] => Ops.storeHandleList
        | args => pure (errJson s!"storeHandleList expects 0 arguments, got {args.length}"))
  | "ops"              => pure (opsReflectionFor
                                 (opNames ++ handleOpNames ++ storeHandleOpNames ++ packOpNames
                                    ++ extOpNames))
  | _                  => pure (call op argsJson)

/-- The dispatch entry the `l4_call_blob_io` C export serves: the string
arguments of `callIO`, ONE byte region in, and ONE byte region out.

Only the ops of `blobIoOpNames` build an out region. Every other op answers
exactly as it does today with an EMPTY out region — the blob-in ops of
`blobOpNames` still read their region through `callBlob`, and everything else
goes to `callIO` — so a host may route every call through this entry without
changing any envelope. -/
def callBlobIO (op : String) (argsJson : String) (blob : ByteArray) :
    IO (String × ByteArray) :=
  match op with
  | "blobEcho" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => pure (blobEcho a)
      | .ok args  => pure (errJson s!"blobEcho expects 1 argument, got {args.length}",
                           ByteArray.empty)
  | "packFeed" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => do pure (← Ops.packFeed a blob, ByteArray.empty)
      | .ok args  => pure (errJson s!"packFeed expects 1 argument, got {args.length}",
                           ByteArray.empty)
  | "packNext" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => Ops.packNext a
      | .ok args  => pure (errJson s!"packNext expects 1 argument, got {args.length}",
                           ByteArray.empty)
  -- `storeOpen` is the one op that needs BOTH the incoming region and the
  -- handle table, so neither `callBlob` (pure) nor `callIO` (no region) can
  -- serve it. It builds no out region.
  -- `storeQuery` needs BOTH the incoming region and the §17.6 registry,
  -- so neither `callBlob` (pure) nor `callIO` (no region) can serve it.
  | "storeQuery" =>
      match decodeArgs argsJson with
      | .error e      => pure (errJson e, ByteArray.empty)
      | .ok [a, b, c] => do pure (← Ops.storeQueryIO a b c blob, ByteArray.empty)
      | .ok args      => pure (errJson s!"storeQuery expects 3 arguments, got {args.length}",
                               ByteArray.empty)
  | "storeOpen" =>
      match decodeArgs argsJson with
      | .error e   => pure (errJson e, ByteArray.empty)
      | .ok [a, b] => do pure (← Ops.storeOpen a b blob, ByteArray.empty)
      | .ok args   => pure (errJson s!"storeOpen expects 2 arguments, got {args.length}",
                            ByteArray.empty)
  | _ =>
      if blobOpNames.contains op then
        pure (callBlob op argsJson blob, ByteArray.empty)
      else do
        let envelope ← callIO op argsJson
        pure (envelope, ByteArray.empty)

/-- Decode a `callseq` document — a JSON array of `[op, [arg, …]]`
pairs — into each op paired with its args RE-SERIALISED as the JSON
array-of-strings document `callIO` takes. Handle state lives in the
process, so a sequence of dependent calls (open → query → close) must
run in ONE process; `Wasm/Main.lean`'s `callseq` subcommand drives
this decoder. -/
def decodeCallSeq (seqJson : String) :
    Except String (List (String × String)) :=
  match parseJson seqJson with
  | .error e => .error s!"callseq: {toString e}"
  | .ok (.array items) =>
      items.mapM fun it =>
        match it with
        | .array [.string op, .array argItems] =>
            let argStrs : Except String (List String) :=
              argItems.mapM fun a =>
                match a with
                | Json.string s => .ok s
                | _ => .error "callseq: every argument must be a string"
            argStrs.map fun ss =>
              (op, (Json.array (ss.map Json.string)).toString)
        | _ => .error "callseq: each entry must be [op, [arg, …]]"
  | .ok _ => .error "callseq: document must be a JSON array"

end L4Wasm
