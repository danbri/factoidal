/-
Wasm.Ops.Canon — canonicalizeToNQuads.

Envelope matches `bin/npm-entry/entry_jsoo.ml`:

  canonicalizeToNQuads(nquads)
    -> {"ok":true,"nquads":"…"} | {"ok":false,"error":"…"}

RDFC-1.0 canonical labels + code-point sort, via
`L4Factoidal.RDF.Canonical.canonicalize` (SHA-256, the default the
spec's §4.4 note 2 names). A run that hits the §4.4 excessive-calls
abort returns the error envelope — never the un-canonicalised
fallback dressed up as an answer.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.NQuadsFast

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- `canonicalizeToNQuads(nquads)`. -/
def canonicalizeToNQuads (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let r := L4Factoidal.RDF.Canonical.canonicalize ds
    if r.aborted then
      errJson "canonicalizeToNQuads: RDFC-1.0 §4.4 excessive-calls budget exceeded"
    else
      okWith [("nquads", .string r.nquads)]

end L4Wasm.Ops
