/-
Wasm.Ops.CL — clParse.

The Common Logic / IKL op (L4Factoidal/CL/, issue 580):

  clParse(cliftext)
    -> {"ok":true,"sentences":N,"pureCL":true|false,"normalized":"…"}
     | {"ok":false,"error":"…"}

`clParse` reads a whole CLIF text (zero or more sentences) and returns
the sentence count, whether the text is pure ISO/IEC 24707 CL (no IKL
`that`), and the canonical re-serialisation, newline-separated.

The `clToDataset` and `queryWithIklService` ops are REMOVED
(https://github.com/danbri/factoidal/issues/626). They served the
IKL-to-RDF projection built on content-addressed proposition graph
names, which is deleted. The committed
wasm artifact still carries both ops until it is rebuilt; see
https://github.com/danbri/factoidal/issues/627.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.CL.Clif

namespace L4Wasm.Ops

open L4Factoidal.JSON

/-- `clParse(cliftext)`. -/
def clParse (cliftext : String) : String :=
  match L4Factoidal.CL.parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      okWith
        [ ("sentences", .number (toString ss.length))
        , ("pureCL", .bool (L4Factoidal.CL.sentencesPureCL ss))
        , ("normalized", .string (String.intercalate "\n"
            (ss.map L4Factoidal.CL.Sentence.toClif))) ]

end L4Wasm.Ops
