/-
L4Factoidal.SPARQL.Update — SPARQL 1.1 Update: the request AST and the
§3 operation semantics over a `Dataset` (the Graph Store).

Port of `formal/fstar/SPARQL11.Algebra.fst` Part 6b (`graph_ref`,
`update_op`, `sparql_update`) and Parts 19b–19e (`collect_quads`,
`apply_insert_data`, `apply_delete_data`, `apply_delete_where`,
`build_where_dataset`, `apply_modify`, `apply_create`, `apply_clear`,
`apply_drop`, `apply_copy`, `apply_move`, `apply_add`,
`apply_update_op`, `apply_update_ops`, `apply_update`,
`is_implemented_op` / `update_is_implemented_only`).

Spec: "SPARQL 1.1 Update" (W3C Recommendation 21 March 2013),
https://www.w3.org/TR/sparql11-update/ — §3.1 graph update
(INSERT DATA §3.1.1, DELETE DATA §3.1.2, DELETE/INSERT §3.1.3,
DELETE WHERE §3.1.3.3 shorthand, LOAD §3.1.4, CLEAR §3.1.5) and §3.2
graph management (CREATE §3.2.1, DROP §3.2.2, COPY §3.2.3, MOVE
§3.2.4, ADD §3.2.5). Every operation cites its section at its
definition.

TWO DEPARTURES FROM THE F* SOURCE, both recorded here:

  * An ERROR CHANNEL. The F* `apply_update : rdf_dataset ->
    sparql_update -> rdf_dataset` is total and treats SILENT as
    advisory ("errors do not exist; we no-op"). §3.2.1–§3.2.5 say
    CREATE of an existing graph, and CLEAR / DROP / COPY / MOVE / ADD
    naming a graph that does not exist, are errors UNLESS `SILENT` is
    given. This port returns `Except UpdateError Dataset` and raises
    exactly those errors; `SILENT` turns each into the identity.
    Non-silent LOAD is `UpdateError.loadUnavailable` — fetching a
    document is I/O, which this semantics does not perform; `LOAD
    SILENT` is the identity, which is the §3.1.4 "on failure, succeed
    silently with no effect" reading the F* also takes.
  * BLANK-NODE FRESHNESS BY CONSTRUCTION. The F* salts fresh labels
    with the dataset's triple COUNT, which can in principle collide
    with an existing label. Here `requestPrefix` is longer than every
    blank-node label already in the Graph Store, so every label it
    prefixes is new (`Dataset.maxBnodeLabelLength`). The scoping is
    the F*'s: one prefix per request for INSERT DATA (§19.6 — two
    INSERT DATA operations that share a label denote the same node;
    W3C `insert-data-same-bnode`), and one fresh node per (operation,
    solution, template label) for INSERT templates (§3.1.3.2; W3C
    `insert-where-same-bnode`).

WHERE-based operations (DELETE/INSERT … WHERE, DELETE WHERE) evaluate
their pattern with the query-side machinery unchanged —
`QueryPattern.rewriteBnodes` (§3.1.3.1: blank nodes in the WHERE
clause are non-distinguished variables), `QueryPattern.lower` and
`GraphPattern.evalIn` — then instantiate the templates per solution
(§3.1.3.2 / §3.1.3.3: a template triple with an unbound variable, a
literal or triple-term subject, or a non-IRI predicate is dropped),
and apply deletes BEFORE inserts within one operation (§3.1.3: "the
DELETE template is processed before the INSERT template").

No `sorry`, no `axiom`, no `native_decide`, no `partial`: every
recursion is structural (on the pattern, on the quad list, on the
operation list).
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The request AST — SPARQL 1.1 Update §3, grammar [29]–[52] -/

/-- [45] GraphRefAll ::= GraphRef | 'DEFAULT' | 'NAMED' | 'ALL';
[46] GraphRef ::= 'GRAPH' iri; [44] GraphOrDefault ::= 'DEFAULT' |
'GRAPH'? iri. One type serves all three productions, as in the F*
`graph_ref`; which constructors a production admits is the parser's
business. -/
inductive GraphRef where
  | default
  | named
  | all
  | graph (i : WfIri)
  deriving Repr, DecidableEq

/-- One update operation ([30] Update1). The `silent` flags carry the
`SILENT` keyword of [31] Load, [32] Clear, [33] Drop, [34] Create,
[35] Add, [36] Move, [37] Copy. The DATA forms ([38] InsertData,
[39] DeleteData) and [40] DeleteWhere carry their quad block as a
`QueryPattern` restricted to `bgp` / `join` / `graph` / `empty` — the
same representation the F* `update_op` uses, so `collectQuads` below
is the F* `collect_quads` arm for arm. -/
inductive UpdateOp where
  /-- [31] `LOAD SILENT? iri ( INTO GraphRef )?` — §3.1.4. -/
  | load   (silent : Bool) (source : WfIri) (into : Option WfIri)
  /-- [32] `CLEAR SILENT? GraphRefAll` — §3.1.5. -/
  | clear  (silent : Bool) (target : GraphRef)
  /-- [33] `DROP SILENT? GraphRefAll` — §3.2.2. -/
  | drop   (silent : Bool) (target : GraphRef)
  /-- [34] `CREATE SILENT? GraphRef` — §3.2.1. -/
  | create (silent : Bool) (name : WfIri)
  /-- [35] `ADD SILENT? GraphOrDefault TO GraphOrDefault` — §3.2.5. -/
  | add    (silent : Bool) (src dst : GraphRef)
  /-- [36] `MOVE SILENT? GraphOrDefault TO GraphOrDefault` — §3.2.4. -/
  | move   (silent : Bool) (src dst : GraphRef)
  /-- [37] `COPY SILENT? GraphOrDefault TO GraphOrDefault` — §3.2.3. -/
  | copy   (silent : Bool) (src dst : GraphRef)
  /-- [38] `INSERT DATA QuadData` — §3.1.1. -/
  | insertData  (quads : QueryPattern)
  /-- [39] `DELETE DATA QuadData` — §3.1.2. -/
  | deleteData  (quads : QueryPattern)
  /-- [40] `DELETE WHERE QuadPattern` — §3.1.3.3. -/
  | deleteWhere (pattern : QueryPattern)
  /-- [41] Modify ::= `( WITH iri )? ( DeleteClause InsertClause? |
  InsertClause ) UsingClause* WHERE GroupGraphPattern` — §3.1.3. -/
  | modify (withIri : Option WfIri)
           (deleteTemplate insertTemplate : Option QueryPattern)
           (usingClauses : List DatasetClause)
           (wherePattern : QueryPattern)

/-- [29] Update ::= Prologue ( Update1 ( ';' Update )? )? — the whole
request: the prologue in force at the end (port of `sparql_update`)
and the operations in request order. -/
structure Update where
  base     : Option String := none
  prefixes : List (String × String) := []
  ops      : List UpdateOp

/-- The failures §3 names. See the module header for which operation
raises which, and how `SILENT` suppresses each. -/
inductive UpdateError where
  /-- Non-silent `LOAD`: fetching `source` is I/O this semantics does
  not perform, so the operation cannot succeed (§3.1.4). -/
  | loadUnavailable (source : WfIri)
  /-- `CREATE GRAPH` of a graph the store already holds (§3.2.1). -/
  | graphExists (name : WfIri)
  /-- `CLEAR` / `DROP` / `COPY` / `MOVE` / `ADD` naming a graph the
  store does not hold (§3.1.5, §3.2.2–§3.2.5). -/
  | graphMissing (name : WfIri)
  deriving Repr, DecidableEq

instance : ToString UpdateError where
  toString
    | .loadUnavailable i => s!"LOAD <{i.val}> cannot be performed (no document fetch)"
    | .graphExists i     => s!"graph <{i.val}> already exists"
    | .graphMissing i    => s!"graph <{i.val}> does not exist"

/-- `is_implemented_op` negated: does the request contain a `LOAD`
without `SILENT`? Such a request cannot be evaluated by a pure
semantics; the harness reports it as a skip, as the F* runner does. -/
def Update.hasNonSilentLoad (u : Update) : Bool :=
  u.ops.any (fun op => match op with
    | .load silent _ _ => !silent
    | _                => false)

/-! ## Graph Store helpers — named-graph slots by IRI

RDF 1.1 Concepts §4 lets a graph name be a blank node, and
`NamedGraph.name` is a `Subject` accordingly; the Update grammar only
ever NAMES a graph by IRI ([46] GraphRef), so every helper here takes
a `WfIri`. -/

end L4Factoidal.SPARQL

namespace L4Factoidal.RDF

-- `Graph.remove` used to be defined here. It moved to
-- `RDF/Graph.lean`, beside `Graph.add` and `Graph.mem`, when the
-- delta-merge proof needed its membership characterisation: the F\*
-- tree keeps `graph_remove` in `RDF.Graph.Executable` with the other
-- two, and splitting it off here put a set operation in an update
-- module.

/-- Does the store hold a graph named `i` (possibly empty)? Port of
`has_named_graph`. -/
def Dataset.hasGraph (i : WfIri) (ds : Dataset) : Bool :=
  ds.named.any (fun ng => ng.name == .iri i)

/-- The triples of the graph named `i`; the empty graph when the store
holds none. Port of `find_named_graph_triples`. -/
def Dataset.graphOf (i : WfIri) (ds : Dataset) : Graph :=
  match ds.lookupNamed (.iri i) with
  | some g => g
  | none   => []

/-- Replace the triples of the graph named `i` (keeping its slot), or
append a new slot. Port of `replace_named_graph_triples`. -/
def replaceNamed (i : WfIri) (g : Graph) : List NamedGraph → List NamedGraph
  | []         => [{ name := .iri i, graph := g }]
  | ng :: rest =>
      if ng.name == .iri i then { ng with graph := g } :: rest
      else ng :: replaceNamed i g rest

def Dataset.setGraph (i : WfIri) (g : Graph) (ds : Dataset) : Dataset :=
  { ds with named := replaceNamed i g ds.named }

/-- Remove the slot of the graph named `i` entirely (port of
`drop_named_by_iri`). -/
def Dataset.dropGraph (i : WfIri) (ds : Dataset) : Dataset :=
  { ds with named := ds.named.filter (fun ng => !(ng.name == .iri i)) }

/-- Add an empty slot for `i` when the store has none (port of
`ensure_named_graph`). -/
def Dataset.ensureGraph (i : WfIri) (ds : Dataset) : Dataset :=
  if ds.hasGraph i then ds
  else { ds with named := ds.named ++ [{ name := .iri i, graph := [] }] }

/-- Every named graph emptied, slots kept (port of `empty_all_named`). -/
def Dataset.clearAllNamed (ds : Dataset) : Dataset :=
  { ds with named := ds.named.map (fun ng => { ng with graph := [] }) }

/-! ## Quads

A quad is a triple with its graph slot: `none` for the default graph
(the F* `option wf_iri * triple`). -/

abbrev Quad := Option WfIri × Triple

/-- Add one quad to the store; a named graph the store does not hold
is created (port of `insert_quad` / `upsert_named_graph`). -/
def Dataset.insertQuad (ds : Dataset) : Quad → Dataset
  | (none, t)   => { ds with default := ds.default.add t }
  | (some g, t) => ds.setGraph g ((ds.graphOf g).add t)

def Dataset.insertQuads (ds : Dataset) (qs : List Quad) : Dataset :=
  qs.foldl Dataset.insertQuad ds

/-- Remove one quad; removing from a graph the store does not hold is
a no-op and does NOT create the graph (port of `delete_quad` /
`remove_from_named_graph`). -/
def Dataset.deleteQuad (ds : Dataset) : Quad → Dataset
  | (none, t)   => { ds with default := ds.default.remove t }
  | (some g, t) =>
      if ds.hasGraph g then ds.setGraph g ((ds.graphOf g).remove t) else ds

def Dataset.deleteQuads (ds : Dataset) (qs : List Quad) : Dataset :=
  qs.foldl Dataset.deleteQuad ds

/-- §3.1.2 / §4.1.2: DELETE DATA may not mention blank nodes (they could
not denote an existing node). The parser rejects them; the semantics
drops any that reach it, as the F* `filter_no_bnode_quads` does. -/
def Triple.hasBnode (t : Triple) : Bool :=
  (match t.s with | .bnode _ => true | _ => false) ||
  (match t.o with | .bnode _ => true | _ => false)

/-- The longest blank-node label in the store (graph names included). -/
def Dataset.maxBnodeLabelLength (ds : Dataset) : Nat :=
  ds.bnodes.foldl (fun acc b => max acc b.length) 0

/-- Rename every blank node of a quad's triple. -/
def Quad.renameBnodes (f : BNodeId → BNodeId) : Quad → Quad
  | (g, t) => (g, t.renameBnodes f)

end L4Factoidal.RDF

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Ground quads — INSERT DATA / DELETE DATA (§3.1.1, §3.1.2)

The grammar forbids variables in QuadData ([48] QuadData uses
TriplesTemplate); the parser enforces it. The collectors below drop
any non-ground triple anyway, so the semantics is total on every
`QueryPattern` (port of `tp_to_triple_concrete` and friends). -/

def groundSubject : PatternSubject → Option Subject
  | .iri i            => some (.iri i)
  | .bnode b          => some (.bnode b)
  | .var _            => none
  | .tripleTerm _ _ _ => none

def groundPredicate : PatternTerm → Option WfIri
  | .iri i => some i
  | _      => none

/-- RDF 1.2: a ground triple-term object grounds position by position. -/
def groundObject : PatternTerm → Option Term
  | .iri i     => some (.iri i)
  | .bnode b   => some (.bnode b)
  | .literal l => some (.literal l)
  | .var _     => none
  | .tripleTerm s p o =>
      match groundObject s with
      | none => none
      | some st =>
          match st.toSubject? with
          | none => none
          | some ss =>
              match groundPredicate p with
              | none => none
              | some pi =>
                  match groundObject o with
                  | none => none
                  | some ot => some (.tripleTerm ss pi ot)

/-- Port of `tp_to_triple_concrete`. -/
def groundTriple (tp : TriplePattern) : Option Triple :=
  match groundSubject tp.s with
  | none   => none
  | some s =>
      match groundPredicate tp.p with
      | none   => none
      | some p =>
          match groundObject tp.o with
          | none   => none
          | some o => some { s := s, p := p, o := o }

/-- Walk a QuadData block: triples under `GRAPH <g> { … }` go to `g`,
the rest to `outer` (the default graph at the top). Port of
`collect_quads`; every other pattern form is outside QuadData and
contributes nothing. -/
def collectQuads (outer : Option WfIri) : QueryPattern → List Quad
  | .empty  => []
  | .bgp b  => (b.filterMap groundTriple).map (fun t => (outer, t))
  | .join a b => collectQuads outer a ++ collectQuads outer b
  | .graph (.iri g) inner => collectQuads (some g) inner
  | .graph _ inner        => collectQuads outer inner
  | _ => []

/-! ## Fresh blank nodes -/

/-- A label prefix strictly longer than every label in the store, so
any label it prefixes is not in the store. Computed once per request
(see the module header). -/
def requestPrefix (ds : Dataset) : String :=
  "b" ++ String.ofList (List.replicate ds.maxBnodeLabelLength '_') ++ "_"

/-- INSERT DATA labels are scoped to the REQUEST (§19.6). -/
def freshDataBnode (pre : String) (label : String) : BNodeId :=
  pre ++ "d_" ++ label

/-- INSERT template labels are fresh per (operation, solution) —
§3.1.3.2: "blank nodes in the INSERT template are instantiated afresh
for each solution". -/
def freshTemplateBnode (pre : String) (opIx solIx : Nat) (label : String) : BNodeId :=
  pre ++ "o" ++ toString opIx ++ "_" ++ toString solIx ++ "_" ++ label

/-- §3.1.1 INSERT DATA: the ground quads are added, their blank nodes
renamed request-fresh (port of `apply_insert_data`). -/
def applyInsertData (pre : String) (ds : Dataset) (quads : QueryPattern) : Dataset :=
  ds.insertQuads ((collectQuads none quads).map (Quad.renameBnodes (freshDataBnode pre)))

/-- §3.1.2 DELETE DATA: the ground, blank-node-free quads are removed
(port of `apply_delete_data`). A quad absent from the store is a
no-op, not an error. -/
def applyDeleteData (ds : Dataset) (quads : QueryPattern) : Dataset :=
  ds.deleteQuads ((collectQuads none quads).filter (fun q => !q.2.hasBnode))

/-! ## Template instantiation — §3.1.3.2 / §3.1.3.3

A template is instantiated under one solution mapping. A template
triple is dropped when a variable in it is unbound, when its subject
would be a literal or a triple term, or when its predicate would not
be an IRI ("ill-formed" in §3.1.3.3). Blank nodes written in the
template go through `fresh`; blank nodes a VARIABLE is bound to pass
through unchanged (they are existing nodes of the store — W3C
`insert-05a`). -/

def instSubject (fresh : String → BNodeId) (mu : Binding) : PatternSubject → Option Subject
  | .iri i            => some (.iri i)
  | .bnode b          => some (.bnode (fresh b))
  | .tripleTerm _ _ _ => none
  | .var v =>
      match mu.lookup v with
      | some (.iri i)   => some (.iri i)
      | some (.bnode b) => some (.bnode b)
      | _               => none

def instObject (fresh : String → BNodeId) (mu : Binding) : PatternTerm → Option Term
  | .iri i     => some (.iri i)
  | .bnode b   => some (.bnode (fresh b))
  | .literal l => some (.literal l)
  | .var v     => mu.lookup v
  | .tripleTerm s p o =>
      match instObject fresh mu s with
      | none => none
      | some st =>
          match st.toSubject? with
          | none => none
          | some ss =>
              match instObject fresh mu p with
              | some (.iri pi) =>
                  match instObject fresh mu o with
                  | none    => none
                  | some ot => some (.tripleTerm ss pi ot)
              | _ => none

def instTriple (fresh : String → BNodeId) (mu : Binding) (tp : TriplePattern) : Option Triple :=
  match instSubject fresh mu tp.s with
  | none   => none
  | some s =>
      match constructPredicate tp.p mu with
      | none   => none
      | some p =>
          match instObject fresh mu tp.o with
          | none   => none
          | some o => some { s := s, p := p, o := o }

/-- The quads one template yields under one solution. `GRAPH ?g { … }`
in a template targets the graph `?g` is bound to; an unbound or
non-IRI graph slot falls back to the enclosing scope, as the F*
`instantiate_ggp_quads` does. -/
def instQuads (fresh : String → BNodeId) (mu : Binding) (outer : Option WfIri) :
    QueryPattern → List Quad
  | .empty   => []
  | .bgp b   => (b.filterMap (instTriple fresh mu)).map (fun t => (outer, t))
  | .join a b => instQuads fresh mu outer a ++ instQuads fresh mu outer b
  | .graph name inner =>
      match constructPredicate name mu with
      | some g => instQuads fresh mu (some g) inner
      | none   => instQuads fresh mu outer inner
  | _ => []

/-- Evaluate a WHERE pattern against a Graph Store view, with the
query-side treatment of blank nodes (§3.1.3.1) and EXISTS seeing the
same view. -/
def evalWhere (env : EvalEnv) (ds : Dataset) (p : QueryPattern) : SolutionSeq :=
  let env := { env with dataset := some ds }
  (p.rewriteBnodes.lower env).evalIn ds ds.default

/-- §3.1.3.3 DELETE WHERE: the pattern is both the WHERE clause and the
DELETE template. Port of `apply_delete_where`. -/
def applyDeleteWhere (env : EvalEnv) (ds : Dataset) (p : QueryPattern) : Dataset :=
  let rewritten := p.rewriteBnodes
  let mus := evalWhere env ds p
  ds.deleteQuads (mus.flatMap (fun mu => instQuads id mu none rewritten))

/-! ## DELETE/INSERT — §3.1.3 -/

/-- The Graph Store view the WHERE clause is evaluated against
(§3.1.3): `USING` / `USING NAMED` build it exactly as `FROM` / `FROM
NAMED` would (and override `WITH`); with no `USING`, `WITH <g>` makes
`g` the default graph for matching; with neither, the store itself.
Port of `build_where_dataset`. -/
def whereDataset (ds : Dataset) (withIri : Option WfIri)
    (usingClauses : List DatasetClause) : Dataset :=
  match usingClauses with
  | [] =>
      match withIri with
      | none   => ds
      | some g => { ds with default := ds.graphOf g }
  | _ =>
      let defaults := usingClauses.filterMap (fun dc =>
        match dc with | .default i => some i | .named _ => none)
      let named := usingClauses.filterMap (fun dc =>
        match dc with | .named i => some i | .default _ => none)
      { default := defaults.foldl (fun acc i => acc.union (ds.graphOf i)) [],
        named   := named.map (fun i => { name := .iri i, graph := ds.graphOf i }) }

/-- §3.1.3: `WITH <g>` makes `g` the target of every template triple
not inside an explicit `GRAPH` block. Port of `redirect_default_quad`. -/
def redirectQuad (withIri : Option WfIri) : Quad → Quad
  | (none, t) =>
      match withIri with
      | some g => (some g, t)
      | none   => (none, t)
  | q => q

/-- One solution's INSERT quads, with template blank nodes fresh for
that solution. -/
def insertQuadsFor (pre : String) (opIx : Nat) (withIri : Option WfIri)
    (tmpl : QueryPattern) : SolutionSeq → Nat → List Quad
  | [],        _  => []
  | mu :: rest, ix =>
      (instQuads (freshTemplateBnode pre opIx ix) mu none tmpl).map (redirectQuad withIri) ++
      insertQuadsFor pre opIx withIri tmpl rest (ix + 1)

/-- §3.1.3 DELETE/INSERT: evaluate WHERE on the view, delete every
DELETE-template instance from the STORE, then insert every
INSERT-template instance into the store. Port of `apply_modify`. -/
def applyModify (env : EvalEnv) (pre : String) (opIx : Nat) (ds : Dataset)
    (withIri : Option WfIri) (deleteTmpl insertTmpl : Option QueryPattern)
    (usingClauses : List DatasetClause) (wherePat : QueryPattern) : Dataset :=
  let mus := evalWhere env (whereDataset ds withIri usingClauses) wherePat
  let delQuads := match deleteTmpl with
    | none    => []
    | some dt => (mus.flatMap (fun mu => instQuads id mu none dt)).map (redirectQuad withIri)
  let afterDelete := ds.deleteQuads delQuads
  match insertTmpl with
  | none    => afterDelete
  | some it => afterDelete.insertQuads (insertQuadsFor pre opIx withIri it mus 0)

/-! ## Graph management — §3.1.5, §3.2 -/

/-- The triples at a `GraphOrDefault` slot. -/
def readRef (ds : Dataset) : GraphRef → Graph
  | .default => ds.default
  | .graph i => ds.graphOf i
  | _        => []

/-- Does the slot exist? The default graph always does (§3.2.2: it
"cannot be removed"). -/
def refExists (ds : Dataset) : GraphRef → Bool
  | .default => true
  | .graph i => ds.hasGraph i
  | _        => false

/-- Write a graph into a slot, creating a named slot if absent. -/
def writeRef (ds : Dataset) (g : Graph) : GraphRef → Dataset
  | .default => { ds with default := g }
  | .graph i => ds.setGraph i g
  | _        => ds

/-- §3.2.3–§3.2.5: a source graph the store does not hold is an error
unless `SILENT`. -/
def sourceCheck (silent : Bool) (ds : Dataset) : GraphRef → Option UpdateError
  | .graph i => if ds.hasGraph i || silent then none else some (.graphMissing i)
  | _        => none

/-- §3.1.5 CLEAR: empty the target graphs, keeping their slots.
`CLEAR GRAPH <g>` on an absent graph is an error unless `SILENT`. -/
def applyClear (ds : Dataset) (silent : Bool) : GraphRef → Except UpdateError Dataset
  | .default => .ok { ds with default := [] }
  | .named   => .ok ds.clearAllNamed
  | .all     => .ok { ds.clearAllNamed with default := [] }
  | .graph i =>
      if ds.hasGraph i then .ok (ds.setGraph i [])
      else if silent then .ok ds
      else .error (.graphMissing i)

/-- §3.2.2 DROP: remove the target graphs. The default graph cannot be
removed, so `DROP DEFAULT` empties it; `DROP GRAPH <g>` on an absent
graph is an error unless `SILENT`. -/
def applyDrop (ds : Dataset) (silent : Bool) : GraphRef → Except UpdateError Dataset
  | .default => .ok { ds with default := [] }
  | .named   => .ok { ds with named := [] }
  | .all     => .ok Dataset.empty
  | .graph i =>
      if ds.hasGraph i then .ok (ds.dropGraph i)
      else if silent then .ok ds
      else .error (.graphMissing i)

/-- §3.2.1 CREATE: a new empty graph; an existing one is an error
unless `SILENT`. -/
def applyCreate (ds : Dataset) (silent : Bool) (i : WfIri) : Except UpdateError Dataset :=
  if ds.hasGraph i then (if silent then .ok ds else .error (.graphExists i))
  else .ok (ds.ensureGraph i)

/-- §3.2.3 COPY: the destination's content becomes a copy of the
source's; a no-op when both are the same graph. -/
def applyCopy (ds : Dataset) (silent : Bool) (src dst : GraphRef) : Except UpdateError Dataset :=
  if src == dst then .ok ds
  else match sourceCheck silent ds src with
    | some e => .error e
    | none   => if refExists ds src then .ok (writeRef ds (readRef ds src) dst) else .ok ds

/-- §3.2.4 MOVE: `COPY src TO dst` then `DROP src` (the default graph
is emptied rather than dropped). -/
def applyMove (ds : Dataset) (silent : Bool) (src dst : GraphRef) : Except UpdateError Dataset :=
  if src == dst then .ok ds
  else match sourceCheck silent ds src with
    | some e => .error e
    | none   =>
        if !refExists ds src then .ok ds
        else
          let copied := writeRef ds (readRef ds src) dst
          match src with
          | .default => .ok { copied with default := [] }
          | .graph i => .ok (copied.dropGraph i)
          | _        => .ok copied

/-- §3.2.5 ADD: the source's triples are added to the destination. -/
def applyAdd (ds : Dataset) (silent : Bool) (src dst : GraphRef) : Except UpdateError Dataset :=
  if src == dst then .ok ds
  else match sourceCheck silent ds src with
    | some e => .error e
    | none   =>
        if !refExists ds src then .ok ds
        else .ok (writeRef ds ((readRef ds dst).union (readRef ds src)) dst)

/-! ## The request -/

/-- One operation on the store (port of `apply_update_op`). `pre` is
the request's fresh-label prefix; `opIx` the operation's index in the
request. -/
def applyOp (env : EvalEnv) (pre : String) (opIx : Nat) (ds : Dataset) :
    UpdateOp → Except UpdateError Dataset
  | .load silent src _     => if silent then .ok ds else .error (.loadUnavailable src)
  | .clear silent gr       => applyClear ds silent gr
  | .drop silent gr        => applyDrop ds silent gr
  | .create silent i       => applyCreate ds silent i
  | .add silent src dst    => applyAdd ds silent src dst
  | .move silent src dst   => applyMove ds silent src dst
  | .copy silent src dst   => applyCopy ds silent src dst
  | .insertData q          => .ok (applyInsertData pre ds q)
  | .deleteData q          => .ok (applyDeleteData ds q)
  | .deleteWhere p         => .ok (applyDeleteWhere env ds p)
  | .modify w d i u p      => .ok (applyModify env pre opIx ds w d i u p)

/-- The operations in order; the first error stops the request
(§3: "the operations of a request are performed in order … an error
aborts the request"). Port of `apply_update_ops_aux`. -/
def applyOps (env : EvalEnv) (pre : String) : Nat → Dataset → List UpdateOp →
    Except UpdateError Dataset
  | _,  ds, []        => .ok ds
  | ix, ds, op :: rest =>
      match applyOp env pre ix ds op with
      | .error e => .error e
      | .ok ds'  => applyOps env pre (ix + 1) ds' rest

/-- Apply a request under an evaluation environment (NOW, SERVICE
endpoints, BASE for the WHERE clauses). Port of `apply_update`. -/
def applyUpdateIn (env : EvalEnv) (ds : Dataset) (u : Update) : Except UpdateError Dataset :=
  applyOps env (requestPrefix ds) 0 ds u.ops

/-- Apply a request with the empty environment. -/
def applyUpdate (ds : Dataset) (u : Update) : Except UpdateError Dataset :=
  applyUpdateIn {} ds u

end L4Factoidal.SPARQL
