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
