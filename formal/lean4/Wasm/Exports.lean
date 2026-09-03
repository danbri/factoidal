/-
Wasm.Exports — the C symbols the WebAssembly module exposes.

Each `@[export]` gives the Lean function a stable C name. Lean's calling
convention for these is: every argument and the result is a
`lean_object *`, and a Lean `String` argument/result is a Lean string
object, NOT a `char *`. The C shim (`Wasm/l4_shim.c`) is what converts
between `char *` and Lean strings and owns the refcount discipline; see
that file and `skills/lean4-wasm-export/SKILL.md` for the memory rules.

Generated C prototypes (as `lean.h` spells them):

  lean_object * l4_version    (lean_object * unit);
  lean_object * l4_bgp_query  (lean_object * dataJson, lean_object * bgpJson);

`l4_version` takes `Unit` rather than being a constant because an
exported nullary Lean definition compiles to a closed thunk that C
cannot call portably; a `Unit` parameter (passed as `lean_box(0)`) keeps
it an ordinary function.
-/
import Wasm.Abi
import Wasm.Dispatch

/-- C symbol `l4_version`. -/
@[export l4_version]
def l4VersionExport (_ : Unit) : String :=
  L4Wasm.version

/-- C symbol `l4_bgp_query`. Evaluates a Basic Graph Pattern over a
graph, both encoded as JSON, and returns SPARQL Query Results JSON.
Never throws: decoding failures come back as `{"error":"…"}`. -/
@[export l4_bgp_query]
def l4BgpQueryExport (dataJson : String) (bgpJson : String) : String :=
  L4Wasm.bgpQuery dataJson bgpJson

/-- C symbol `l4_call`. The pure dispatch entry (`Wasm/Dispatch.lean`):
`op` names the method, `argsJson` is a JSON array of strings (positional
arguments), and the result is one `{"ok":…}` envelope matching the F*
npm entry's for that op. Never throws: every failure comes back as
`{"ok":false,"error":"…"}`. Serves the STATELESS ops only; the
dataset-handle ops need `l4_call_io` below. The signature is pinned —
callers of the committed wasm bind it — so it stays pure and 2-arg. -/
@[export l4_call]
def l4CallExport (op : String) (argsJson : String) : String :=
  L4Wasm.call op argsJson

/-- C symbol `l4_call_blob`. The dispatch entry that also carries ONE
contiguous byte region, for the ops of `L4Wasm.blobOpNames` whose bytes are
too large for the string ABI (block artifacts: hexadecimal would double them
over the boundary and walk every character on the way in). The generated C
prototype is

  lean_object * l4_call_blob (lean_object * op, lean_object * argsJson,
                              lean_object * blob);

where `blob` is a Lean `ByteArray` (a scalar array of `UInt8`).
`Wasm/l4_shim.c`'s `l4_call_blob_c` builds it from a host pointer and length
with one `lean_alloc_sarray` plus one `memcpy` — it moves bytes and never
interprets them. Every op outside `blobOpNames` delegates to `L4Wasm.call`,
envelope for envelope. Never throws. -/
@[export l4_call_blob]
def l4CallBlobExport (op : String) (argsJson : String) (blob : ByteArray) : String :=
  L4Wasm.callBlob op argsJson blob

/-- C symbol `l4_call_io`. The full dispatch entry: every stateless op
(delegated to `L4Wasm.call`, envelope for envelope) PLUS the
dataset-handle ops of https://github.com/danbri/factoidal/issues/585,
whose `IO.Ref` store a pure export cannot reach. Because the result
type is `IO String`, the generated C differs from `l4_call`'s in the
RESULT only: the v4.33 code generator erases the IO world token, so
the symbol still takes two `lean_object *` arguments, but it returns
an IO RESULT object (tag 0 = ok, wrapping the string), not the string
object itself — unwrap with `lean_io_result_take_value` after
`lean_io_result_is_ok`. `Wasm/l4_shim.c`'s `l4_call_c` does exactly
that, so the `char *` wire surface is unchanged. Never throws: every
failure comes back as `{"ok":false,"error":"…"}`. -/
@[export l4_call_io]
def l4CallIOExport (op : String) (argsJson : String) : IO String :=
  L4Wasm.callIO op argsJson

/-- C symbol `l4_call_blob_io`. The dispatch entry that carries ONE
contiguous byte region IN and ONE contiguous byte region OUT
(`L4Wasm.blobIoOpNames`). Bytes leave the module raw: hexadecimal doubles
them over the boundary, and base64 was refused (owner, 2026-09-03).

The generated C prototype is

  lean_object * l4_call_blob_io (lean_object * op, lean_object * argsJson,
                                 lean_object * blob);

The result type is `IO (String × ByteArray)`, so the v4.33 code generator
ERASES the IO world token — three `lean_object *` arguments, as for
`l4_call_blob` — and returns an IO RESULT object (tag 0 = ok). Its value is
a `Prod` object, so the shim takes the value with
`lean_io_result_take_value` and then projects field 0 (the Lean string) and
field 1 (the ByteArray) with `lean_ctor_get`. `Wasm/l4_shim.c`'s
`l4_call_blob_io_c` does exactly that and copies both out, so the wire
surface stays a `char *` envelope plus a malloc'd byte buffer.

Never throws: every failure comes back as `{"ok":false,"error":"…"}` with
an empty out region. -/
@[export l4_call_blob_io]
def l4CallBlobIOExport (op : String) (argsJson : String) (blob : ByteArray) :
    IO (String × ByteArray) :=
  L4Wasm.callBlobIO op argsJson blob
