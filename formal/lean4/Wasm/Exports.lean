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
