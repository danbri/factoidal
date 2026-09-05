/-
Wasm.ExtHost — the one call-out a caller-registered SPARQL 1.1 §17.6
extension function crosses.

  extCallHost (iri : String) (argsJson : String) : String

`argsJson` is a JSON ARRAY of SRJ binding-value objects (SPARQL 1.1
Query Results JSON §3.3, the encoding `SPARQL/ResultsJson.lean`
writes). The answer is one SRJ binding-value object, or the EMPTY
STRING for "no value" — which the caller reads as the §17.6 error.

Realisation: `ffi/l4_ext.c`. Under Emscripten it is an `EM_JS` thunk
onto `globalThis.__factoidalExtCall`, installed by the JavaScript host
(`npm/factoidal/bin/ext.mjs`). On every other target the C side has no
host and answers the empty string, so a native build behaves exactly as
it did before this module existed.

This is the same shape the tree already uses for HACL* crypto
(`L4Factoidal/Crypto/Ed25519.lean`) and for positioned reads
(`Harness/PosixRangeIO.lean`): an `opaque` declaration realised by C.
No `unsafe`, no `@[implemented_by]`, no user `axiom`.

WHY IT LIVES IN `Wasm/`, NOT IN `L4Factoidal/`
`L4Factoidal/*` is the spec tree and stays a total function of explicit
inputs. A host call-out is an ambient effect, so it belongs in the wasm
entry layer, beside the other state this layer is permitted to hold
(`Wasm/Ops/Handles.lean` states that rule). The evaluator still receives
its extension table as an ordinary `EvalEnv.ext` argument; the argument
this layer builds happens to reach the host.

Design: `docs/designissues/2026-09-04-lean-extension-functions.md`.
-/

namespace L4Wasm

/-- Ask the host for the value of one registered extension-function
call. Empty answer = no value = the §17.6 error. -/
@[extern "l4_ext_call"]
opaque extCallHost (iri : @& String) (argsJson : @& String) : String

end L4Wasm
