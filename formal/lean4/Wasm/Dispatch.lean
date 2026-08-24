/-
Wasm.Dispatch — the single dispatch entry `L4Wasm.call`.

  L4Wasm.call (op : String) (argsJson : String) : String

`argsJson` is a JSON ARRAY OF STRINGS (positional arguments); the
result is one JSON envelope, `{"ok":true,…}` or
`{"ok":false,"error":"…"}`. Method names and envelopes match the F*
npm entry point (`bin/npm-entry/entry_jsoo.ml`) op for op, so the JS
side can drive either engine through the same result handling
(`api.js`'s `entryResult`).

The op table below is the whole v1 surface plus a reflection op:

  "ops" -> {"ok":true,"abiVersion":"…","ops":[…names…]}

This module owns the table; the op bodies live in `Wasm/Ops/*.lean`
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

namespace L4Wasm

open L4Wasm.Ops
open L4Factoidal.JSON

/-- Version of the DISPATCH ABI's envelope contract. "1" — the same
value the F* npm entry reports (`entry_jsoo.ml`'s `abi_version`),
because the envelopes are the same contract. Bump when a signature or
JSON shape changes. -/
def dispatchAbiVersion : String := "1"

/-- The op names this dispatch serves, in the order they are matched. -/
def opNames : List String :=
  [ "parseToDatasetJson"
  , "queryDataset"
  , "updateDataset"
  , "serializeNQuads"
  , "serializeTurtle"
  , "canonicalizeToNQuads"
  , "owlClosure"
  , "rhoDfClosure"
  , "rhoDfFragmentCheck"
  , "rdfsPlusClosure"
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

/-- `{"ok":true,"abiVersion":"…","ops":[…]}`. -/
private def opsReflection : String :=
  (Json.object
    [ ("ok", .bool true)
    , ("abiVersion", .string dispatchAbiVersion)
    , ("ops", .array (opNames.map Json.string)) ]).toString

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
    | "owlClosure"           => arity2 op owlClosure args
    | "rhoDfClosure"         => arity1 op rhoDfClosure args
    | "rhoDfFragmentCheck"   => arity1 op rhoDfFragmentCheck args
    | "rdfsPlusClosure"      => arity1 op rdfsPlusClosure args
    | "ops"                  => opsReflection
    | _                      => errJson s!"unknown op '{op}'"

end L4Wasm
