/-
Wasm.Ops.Support — envelope helpers shared by the op modules.

The dispatch ABI (`Wasm/Dispatch.lean`) speaks the SAME method names and
JSON envelopes as the F* npm entry point (`bin/npm-entry/entry_jsoo.ml`):
every op returns `{"ok":true,…}` or `{"ok":false,"error":"…"}`, so the
JS side (`api.js`'s `entryResult`) can treat the two engines alike.

JSON parsing and serialisation delegate to `L4Factoidal.JSON` (the
ported `Parser.JSON.fst` / `SPARQL.JSON.Escape.fst`), NOT to the
phase-1 `L4Wasm.Json` shim in `Wasm/Abi.lean` — that shim is pinned by
hub post 36 and is not extended (see its own banner).

Targeted imports, not the L4Factoidal umbrella: the wasm module
initializes every module its root imports, so the umbrella pays init
cost (and init RISK) for all modules when an op needs a fraction of
them (same rule as `Wasm/Abi.lean`).
-/
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Lexing

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- `{"ok":false,"error":"…"}` — the error envelope every op shares
with the F* npm entry. -/
def errJson (msg : String) : String :=
  (Json.object [("ok", .bool false), ("error", .string msg)]).toString

/-- `{"ok":true,…fields…}` — the success envelope, fields in the given
order (`L4Factoidal.JSON.Json.object` preserves member order). -/
def okWith (fields : List (String × Json)) : String :=
  (Json.object (("ok", Json.bool true) :: fields)).toString

/-- The harness's error rendering (`Harness/Run.lean`'s
`fmtParseError`): message plus codepoint offset. -/
def fmtParseError (e : L4Factoidal.Syntax.ParseError) : String :=
  s!"{e.msg} (offset {e.pos})"

/-- Decode the dispatch argument envelope: a JSON ARRAY OF STRINGS
(positional arguments). Anything else is a caller error. -/
def decodeArgs (argsJson : String) : Except String (List String) :=
  match parseJson argsJson with
  | .error e => .error s!"argsJson: {toString e}"
  | .ok (.array items) =>
      items.mapM fun it =>
        match it with
        | .string s => .ok s
        | _ => .error "argsJson must be a JSON array of strings"
  | .ok _ => .error "argsJson must be a JSON array of strings"

/-! ## Hexadecimal byte transport

The dispatch ABI carries strings, so every op that moves BYTES across it
encodes them as lowercase hexadecimal.  Hex is a portable diagnostic
transport, not the eventual high-throughput host boundary: a worker that owns
a buffer ABI should pass validated byte buffers directly.  These helpers are
shared by `Wasm/Ops/Block.lean` and `Wasm/Ops/Store.lean` so both read and
write the same encoding. -/

private def hexDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n && n ≤ 0x46 then some (n - 0x41 + 10)
  else none

private def bytesOfHexCharsGo? : List Char → List UInt8 → Option (List UInt8)
  | [], reversed => some reversed.reverse
  | [_], _ => none
  | hi :: lo :: rest, reversed => do
      let h ← hexDigitValue? hi
      let l ← hexDigitValue? lo
      bytesOfHexCharsGo? rest (UInt8.ofNat (h * 16 + l) :: reversed)

/-- Decode an even-length hexadecimal string.  `none` on an odd length or a
non-hexadecimal character. -/
def bytesOfHex? (s : String) : Option ByteArray :=
  (bytesOfHexCharsGo? s.toList []).map fun bytes => ByteArray.mk bytes.toArray

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

/-- Lowercase hexadecimal, two digits per byte. -/
def hexOfBytes (bytes : ByteArray) : String :=
  let reversed := bytes.data.toList.foldl (fun out byte =>
    hexChar (byte.toNat % 16) :: hexChar (byte.toNat / 16) :: out) []
  String.ofList reversed.reverse

/-- The members of a JSON object WITHOUT its enclosing braces, so a caller can
splice a pre-serialised JSON document in beside them (the `srj` member of the
`queryDataset` envelope is such a document).  `[]` gives the empty string. -/
def jsonMembers (fields : List (String × Json)) : String :=
  String.intercalate "," (fields.map fun (name, value) =>
    (Json.string name).toString ++ ":" ++ value.toString)

/-- Telemetry only — NOT part of a closure answer (the mirror of
`entry_jsoo.ml`'s `rho_df_rounds_to_fixpoint` /
`rdfs_plus_rounds_to_fixpoint`): count rounds to fixpoint by re-driving
the step function and comparing graph length round over round, capped
so a pathological input cannot spin. The graph this loop touches is
discarded once the round count is known; the closure answer always
comes from the closure function itself. -/
def roundsToFixpoint (stepF : Graph → Graph) : Nat → Graph → Nat
  | 0, _ => 0
  | cap + 1, g =>
      let g' := stepF g
      if g'.length != g.length then roundsToFixpoint stepF cap g' + 1 else 0

end L4Wasm.Ops
