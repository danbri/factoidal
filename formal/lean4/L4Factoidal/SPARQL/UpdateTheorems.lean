/-
L4Factoidal.SPARQL.UpdateTheorems — structural laws of the SPARQL 1.1
Update semantics (`SPARQL/Update.lean`), stated for EVERY Graph Store
(the `#guard`s in `UpdateTests.lean` pin concrete cases).

Each theorem names the §3 clause it makes precise. The F* tree proves
nothing about `apply_update`; these are new.

No `sorry`, no `axiom`, no `native_decide`; the `#print axioms` lines
at the end are the audit.
-/
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Graph helpers -/

/-- Removing a triple the graph does not hold changes nothing. -/
theorem Graph.remove_of_not_mem (g : Graph) (t : Triple) (h : g.mem t = false) :
    g.remove t = g := by
  induction g with
  | nil => rfl
  | cons hd tl ih =>
      simp only [Graph.mem, Bool.or_eq_false_iff] at h
      have ih' : tl.filter (fun u => !u.eqb t) = tl := ih h.2
      simp only [Graph.remove]
      rw [List.filter_cons]
      simp only [h.1, Bool.not_false, ↓reduceIte]
      exact congrArg (hd :: ·) ih'

/-- `remove` undoes the `add` of a triple that was absent. -/
theorem Graph.remove_add_of_not_mem (g : Graph) (t : Triple) (h : g.mem t = false) :
    (g.add t).remove t = g := by
  simp only [Graph.add, h, Bool.false_eq_true, ↓reduceIte]
  simp only [Graph.remove, List.filter_append]
  rw [← Graph.remove, Graph.remove_of_not_mem g t h]
  simp [Triple.eqb_refl]

/-! ## The request -/

/-- §3: the empty request (the grammar's `Prologue` alone) leaves the
store unchanged. -/
theorem applyUpdate_nil (ds : Dataset) : applyUpdate ds { ops := [] } = .ok ds := rfl

/-- §3.1.1: `INSERT DATA {}` is the identity. -/
theorem applyUpdate_insertData_empty (ds : Dataset) :
    applyUpdate ds { ops := [.insertData .empty] } = .ok ds := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyInsertData, collectQuads,
        Dataset.insertQuads]

/-- §3.1.2: `DELETE DATA {}` is the identity. -/
theorem applyUpdate_deleteData_empty (ds : Dataset) :
    applyUpdate ds { ops := [.deleteData .empty] } = .ok ds := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyDeleteData, collectQuads,
        Dataset.deleteQuads]

/-- §3.1.1 then §3.1.2: inserting a ground IRI triple the default graph
does not hold, then deleting it, returns the original store exactly
(a round trip at the level of the list representation, not only up to
set equality). -/
theorem applyUpdate_insert_then_delete (ds : Dataset) (s p o : WfIri)
    (h : ds.default.mem { s := .iri s, p := p, o := .iri o } = false) :
    applyUpdate ds { ops := [.insertData (.bgp [{ s := .iri s, p := .iri p, o := .iri o }]),
                             .deleteData (.bgp [{ s := .iri s, p := .iri p, o := .iri o }])] }
      = .ok ds := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyInsertData, applyDeleteData,
        collectQuads, groundTriple, groundSubject, groundPredicate, groundObject,
        Dataset.insertQuads, Dataset.insertQuad, Dataset.deleteQuads, Dataset.deleteQuad,
        Quad.renameBnodes, Triple.renameBnodes, Subject.renameBnodes, Term.renameBnodes,
        Triple.hasBnode, Graph.remove_add_of_not_mem _ _ h]

/-- §3.1.5: `CLEAR ALL` empties every graph and keeps every named slot. -/
theorem applyUpdate_clearAll (ds : Dataset) (silent : Bool) :
    applyUpdate ds { ops := [.clear silent .all] }
      = .ok { default := [], named := ds.named.map (fun ng => { ng with graph := [] }) } := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyClear, Dataset.clearAllNamed]

/-- §3.2.2: `DROP ALL` yields the empty store. -/
theorem applyUpdate_dropAll (ds : Dataset) (silent : Bool) :
    applyUpdate ds { ops := [.drop silent .all] } = .ok Dataset.empty := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyDrop]

/-- §3.1.5: `CLEAR GRAPH <g>` of a graph the store does not hold is an
error … -/
theorem applyUpdate_clear_missing (ds : Dataset) (i : WfIri) (h : ds.hasGraph i = false) :
    applyUpdate ds { ops := [.clear false (.graph i)] } = .error (.graphMissing i) := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyClear, h]

/-- … and `CLEAR SILENT GRAPH <g>` of the same is the identity. -/
theorem applyUpdate_clear_missing_silent (ds : Dataset) (i : WfIri) (h : ds.hasGraph i = false) :
    applyUpdate ds { ops := [.clear true (.graph i)] } = .ok ds := by
  simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyClear, h]

/-- §3.2.1: `CREATE GRAPH <g>` of a graph the store holds is an error;
with `SILENT` it is the identity. -/
theorem applyUpdate_create_existing (ds : Dataset) (i : WfIri) (h : ds.hasGraph i = true) :
    applyUpdate ds { ops := [.create false i] } = .error (.graphExists i) ∧
    applyUpdate ds { ops := [.create true i] } = .ok ds := by
  constructor <;> simp [applyUpdate, applyUpdateIn, applyOps, applyOp, applyCreate, h]

/-- §3: the request is the operations in order — a two-operation
request is the second operation applied to the first's result. -/
theorem applyOps_cons (env : EvalEnv) (pre : String) (ix : Nat) (ds : Dataset)
    (op : UpdateOp) (rest : List UpdateOp) :
    applyOps env pre ix ds (op :: rest)
      = (applyOp env pre ix ds op).bind (fun ds' => applyOps env pre (ix + 1) ds' rest) := by
  simp only [applyOps]
  cases applyOp env pre ix ds op <;> rfl

/-! ## Axiom audit -/

#print axioms applyUpdate_nil
#print axioms applyUpdate_insertData_empty
#print axioms applyUpdate_insert_then_delete
#print axioms applyUpdate_clearAll
#print axioms applyUpdate_dropAll
#print axioms applyUpdate_clear_missing
#print axioms applyUpdate_clear_missing_silent
#print axioms applyUpdate_create_existing
#print axioms applyOps_cons

end L4Factoidal.SPARQL
