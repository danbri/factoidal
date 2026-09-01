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
import Wasm.Ops.CL
import Wasm.Ops.Proof
import Wasm.Ops.Handles

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

/-- `{"ok":true,"abiVersion":"…","ops":[…names…]}`. -/
private def opsReflectionFor (names : List String) : String :=
  (Json.object
    [ ("ok", .bool true)
    , ("abiVersion", .string dispatchAbiVersion)
    , ("ops", .array (names.map Json.string)) ]).toString

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
  | "datasetOpen"      => withArgs (arityIO3 op Ops.datasetOpen)
  | "datasetQuery"     => withArgs (arityIO2 op Ops.datasetQuery)
  | "datasetUpdate"    => withArgs (arityIO2 op Ops.datasetUpdate)
  | "datasetSerialize" => withArgs (arityIO2 op Ops.datasetSerialize)
  | "datasetClose"     => withArgs (arityIO1 op Ops.datasetClose)
  | "ops"              => pure (opsReflectionFor (opNames ++ handleOpNames))
  | _                  => pure (call op argsJson)

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
