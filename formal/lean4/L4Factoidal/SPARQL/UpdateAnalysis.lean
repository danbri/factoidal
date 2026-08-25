/-
L4Factoidal.SPARQL.UpdateAnalysis — structural predicates over UPDATE.

Port of `formal/fstar/SPARQL.Update.Analysis.fst` (31 lines). One
question per predicate, all pure and total.

Migrated in the F\* tree out of `factoidal_http.ml`: the HTTP layer uses
these to decide whether to reject a request or set up a sandbox. The
semantic question "what does this update contain?" belongs here per
iron rule #1; the HTTP wiring — status codes, error messages — stays
with the caller.
-/
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## `updateHasLoad`

`LOAD` fetches an external IRI over HTTP, which is outside what this
semantics evaluates. The HTTP layer rejects an update containing one
with 501 Not Implemented rather than running it silently and producing
a wrong result. This is the check it consults. -/

def isLoadOp : UpdateOp → Bool
  | .load _ _ _ => true
  | _           => false

def updateHasLoad (u : Update) : Bool := u.ops.any isLoadOp

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def ui (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

#guard isLoadOp (.load false (ui "d") none)
#guard isLoadOp (.load true (ui "d") (some (ui "g")))
#guard !isLoadOp (.create false (ui "g"))
#guard !isLoadOp (.drop false (.graph (ui "g")))

#guard updateHasLoad { ops := [.load false (ui "d") none] }
#guard updateHasLoad { ops := [.create false (ui "g"), .load false (ui "d") none] }
#guard !updateHasLoad { ops := [.create false (ui "g")] }

/-! An empty update contains no LOAD, so it is not rejected. Checked
    because "reject when the predicate is false" makes the empty case
    load-bearing. -/

#guard !updateHasLoad { ops := [] }

end L4Factoidal.SPARQL
