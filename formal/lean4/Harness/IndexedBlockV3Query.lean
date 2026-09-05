/- Parsed SELECT over constant-predicate IBK3 fragments: physical bytes are
   admitted by the shared Merkle/paged materializer, then ordinary Lean SPARQL
   evaluates the parsed algebra. -/
import Harness.IndexedBlockV3Materialize
import Harness.ShardMerkleMaterialize
import Harness.GenerationPointer
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.SharedSubjectTriple
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.StoreFastPath
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Query

open Harness.IndexedBlockV3Materialize
open Harness.ShardMerkleMaterialize
open Harness.GenerationPointer
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.SharedSubjectTriple
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StoreFastPath
open L4Factoidal.Storage.ShardManifest

private def readOpsOf (triples : List Triple) : BackendReadOps :=
  { search := fun bound => tripleMatchesBound bound triples
    estimate := fun bound => (tripleMatchesBound bound triples).length
    predicatePresent := fun predicate => !(tripleMatchesBound { p := some predicate } triples).isEmpty }

/-- Build the already-proved in-memory indexed backend over the exact triples
    materialised from immutable storage. `igSearch` now widens object buckets
    whenever a structural key is not complete for SPARQL term equality. Delta
    overlays retain the established read-ops route until their own indexed
    materialisation contract is explicit. -/
private def backendFor (triples : List Triple) (delta : DeltaResolved) : GraphBackend :=
  if deltaResolvedIsEmpty delta then indexedGraphBackend triples
  else .hdt (readOpsOfDelta triples delta)

/-- A physically safe bounded-prefix shape. Subject/object must be distinct
    variables: constants or repeated variables could make early rows fail the
    SPARQL pattern and would need continued scanning. -/
private def prefixPredicate? (tp : TriplePattern) : Option WfIri :=
  match tp.s, tp.p, tp.o with
  | .var subject, .iri predicate, .var object =>
      if subject == object then none else some predicate
  | _, _, _ => none

/-- The physical count path is narrower than the already-conservative Lean
    detector: this store has only a default graph, no query dataset clauses,
    and must establish one constant predicate by reading its rows. -/
private def countPredicate? (query : Query) : Option (VarName × WfIri) := do
  if !query.dataset.isEmpty then none else
  let (alias, tp, scope) ← detectStreamingCountStar query
  if scope.isSome then none else do
  let predicate ← prefixPredicate? tp
  some (alias, predicate)

/-- The same physically established predicate cardinality decides this simple
    ASK form. Post-VALUES needs ordinary binding evaluation, so it falls back
    even though its underlying triple pattern may be predicate-local. -/
private def askPredicate? (query : Query) : Option WfIri :=
  if !query.dataset.isEmpty || query.postValues.isSome then none else
  match query.form, query.pattern with
  | .ask, .bgp [tp] => prefixPredicate? tp
  | _, _ => none

private def groupPredicate? (query : Query) : Option (VarName × VarName) := do
  if !query.dataset.isEmpty then none else
  let (predicateVar, countAlias, scope) ← detectStreamingCountGroupByPredicate query
  if scope.isSome then none else some (predicateVar, countAlias)

private def countForPredicate (counts : List (WfIri × Nat)) (predicate : WfIri) : Nat :=
  (counts.find? fun pair => pair.1 == predicate).map Prod.snd |>.getD 0

private def countAllPredicates (directory : System.FilePath) (manifest : Manifest) :
    List WfIri → List (WfIri × Nat) → Counters → IO (Option (List (WfIri × Nat) × Counters))
  | [], reversed, counters => pure (some (reversed.reverse, counters))
  | predicate :: rest, reversed, counters => do
      match ← Harness.IndexedBlockV3Materialize.countEntries directory predicate
          (selectAll manifest predicate) 0 {} with
      | none => pure none
      | some (count, current) =>
          countAllPredicates directory manifest rest ((predicate, count) :: reversed)
            (addCounters counters current)

private def finish (query : Query) (entries : List Entry) (predicates : List WfIri)
    (triples : List Triple) (counters : Counters) (delta : DeltaResolved)
    (mode : String := "ibk3-paged-merkle") : IO UInt32 := do
  let backend := backendFor triples delta
  let dataset : DatasetBackend := { default := backend, named := [] }
  -- §18.6: EXISTS / NOT EXISTS evaluate against the query's dataset, which
  -- the backend runners read from `env.dataset`; the reference evaluator
  -- sets it itself.  The dataset is the same base-plus-delta graph the
  -- backend answers from (the CONSTRUCT arm below already reads it this
  -- way), so an EXISTS sub-pattern sees exactly the materialised fragment.
  let env : EvalEnv := { emptyEnv with
    dataset := some { default := backendSearch backend patternBoundAll, named := [] } }
  let deltaMode := if deltaResolvedIsEmpty delta then "base" else "base-plus-delta"
  match query.form with
  | .select _ =>
      match runSelectQueryBackendDataset env query dataset with
      | none => IO.eprintln "l4block-id-v3-query failed: query was not evaluated as SELECT"; return 1
      | some rows =>
          IO.println s!"l4block-id-v3-query shards={entries.length} open-mode={mode}({predicates.length}) delta={deltaMode} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
          IO.println s!"l4block-id-v3-query sse={query.toSse}"
          IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
          return 0
  | .ask =>
      match runAskQueryBackendDataset emptyEnv query dataset with
      | none => IO.eprintln "l4block-id-v3-query failed: query was not evaluated as ASK"; return 1
      | some answer =>
          IO.println s!"l4block-id-v3-query shards={entries.length} open-mode={mode}({predicates.length}) delta={deltaMode} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
          IO.println s!"l4block-id-v3-query sse={query.toSse}"
          IO.println s!"l4block-id-v3-query boolean={answer}"
          return 0
  | .construct _ =>
      let graph : Graph := evalConstruct emptyEnv
        { default := backendSearch (backendFor triples delta) patternBoundAll, named := [] } query
      IO.println s!"l4block-id-v3-query shards={entries.length} open-mode={mode}({predicates.length}) delta={deltaMode} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
      IO.println s!"l4block-id-v3-query sse={query.toSse}"
      IO.println s!"l4block-id-v3-query triples={graph.length} preview={toString (repr (graph.take 10))}"
      return 0
  | .describe _ =>
      IO.eprintln "l4block-id-v3-query rejected: DESCRIBE needs an explicit description policy"; return 1

/-- The narrow OLI2→SRI2 physical join has already established the two BGP
    constraints: every target row has a driver subject, and the driver object
    is constant. For SELECT only, form those bindings directly, retaining the
    driver's multiplicity, then use the standard SELECT post-WHERE pipeline
    for projection, aggregates, ordering, DISTINCT and slicing. -/
private def objectSubjectSolutions (subjectVar objectVar : VarName)
    (drivers targets : List Triple) : SolutionSeq :=
  let multiplicities := drivers.foldl (fun counts triple =>
    counts.insert triple.s (counts.getD triple.s 0 + 1)) (∅ : Std.HashMap Subject Nat)
  targets.flatMap fun target =>
    List.replicate (multiplicities.getD target.s 0)
      [(objectVar, target.o), (subjectVar, target.s.toTerm)]

/-- Preserve first-seen RDF subjects while avoiding `List.eraseDups`'s
    quadratic repeated membership scan on a broad OLI2 driver. Subjects are
    IRI/blank-node keys, whose structural equality is the same identity used
    by the physical SRI2 sidecar. -/
private def distinctSubjectTerms (triples : List Triple) : List Term :=
  go triples (∅ : Std.HashSet Subject) []
where
  go : List Triple → Std.HashSet Subject → List Term → List Term
    | [], _, reversed => reversed.reverse
    | triple :: rest, seen, reversed =>
        if seen.contains triple.s then go rest seen reversed
        else go rest (seen.insert triple.s) (triple.s.toTerm :: reversed)

/-- This is a deliberately narrower physical finishing path than generic
    `DISTINCT`: a one-variable `SELECT DISTINCT ?subject ORDER BY ?subject`
    (ascending or descending) has already projected every relevant value.
    The input target rows are known to have driver subjects, so a structural
    subject set produces exactly its distinct solution mappings.  Ordering is
    retained in `selectPost`; disabling its generic quadratic DISTINCT is safe
    only after this pre-deduplication and only for this exact shape. -/
private def distinctSubjectOrderQuery? (query : Query) (subjectVar : VarName) : Option Query := do
  if query.groupBy.isSome || !query.having.isEmpty || !query.modifier.distinct then none else
  match query.form, query.modifier.orderBy with
  | .select (.vars [.var selected]), some [order] =>
      let orderedVar := match order with
        | .asc (.var v) => some v
        | .desc (.var v) => some v
        | _ => none
      if selected != subjectVar || orderedVar != some subjectVar then none else
      some (.mk query.form query.dataset query.pattern query.groupBy query.having
        { query.modifier with distinct := false } query.postValues query.base)
  | _, _ => none

private def objectSubjectDistinctSolutions (subjectVar : VarName)
    (targets : List Triple) : SolutionSeq :=
  (distinctSubjectTerms targets).map fun subject => [(subjectVar, subject)]

private def finishObjectSubjectSelect (query : Query) (entries : List Entry)
    (predicates : List WfIri) (subjectVar objectVar : VarName)
    (drivers targets : List Triple) (counters : Counters) : IO UInt32 := do
  let (executionQuery, inputRows, mode) :=
    match distinctSubjectOrderQuery? query subjectVar with
    | some q => (q, objectSubjectDistinctSolutions subjectVar targets,
        "ibk3-sri2-tli1-oli2-object-subject-direct-select-distinct-subject")
    | none => (query, objectSubjectSolutions subjectVar objectVar drivers targets,
        "ibk3-sri2-tli1-oli2-object-subject-direct-select")
  let rows := selectPost emptyEnv emptyEnv.activeGraph executionQuery inputRows
  IO.println s!"l4block-id-v3-query shards={entries.length} open-mode={mode}({predicates.length}) delta=base logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
  return 0

/-- The three-way direct path has already performed the BGP join using exact
    RDF subject identity.  Do not re-run generic algebra over the fragments:
    pass its equivalent solution sequence into the established SELECT post
    phase, which keeps projection, expressions, grouping, DISTINCT, ordering,
    OFFSET and LIMIT centralised. -/
private def finishSubjectTripleSelect (query : Query) (entries : List Entry)
    (predicates : List WfIri) (subjectVar driverVar leftVar rightVar : VarName)
    (drivers lefts rights : List Triple) (counters : Counters) : IO UInt32 := do
  let rows := selectPost emptyEnv emptyEnv.activeGraph query
    (subjectTripleSolutions subjectVar driverVar leftVar rightVar drivers lefts rights)
  IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-sri2-tli1-subject-triple-direct-select({predicates.length}) delta=base logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
  return 0

private def finishCount (query : Query) (entries : List Entry)
    (alias : VarName) (count : Nat) (counters : Counters) : IO UInt32 := do
  let rows := sliceSolutions query.modifier.offset query.modifier.limit (countStarSolution alias count)
  IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle-count(1) delta=base logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr rows)}"
  return 0

private def finishAsk (query : Query) (entries : List Entry) (predicates : List WfIri)
    (triples : List Triple) (counters : Counters) (delta : DeltaResolved) : IO UInt32 := do
  let dataset : DatasetBackend := { default := backendFor triples delta, named := [] }
  match runAskQueryBackendDataset emptyEnv query dataset with
  | none => IO.eprintln "l4block-id-v3-query failed: query was not evaluated as ASK"; return 1
  | some answer =>
      let deltaMode := if deltaResolvedIsEmpty delta then "base" else "base-plus-delta"
      IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle({predicates.length}) delta={deltaMode} logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
      IO.println s!"l4block-id-v3-query sse={query.toSse}"
      IO.println s!"l4block-id-v3-query boolean={answer}"
      return 0

private def finishAskCount (query : Query) (entries : List Entry) (count : Nat)
    (counters : Counters) : IO UInt32 := do
  IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle-ask(1) delta=base logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println s!"l4block-id-v3-query boolean={if count > 0 then "true" else "false"}"
  return 0

private def finishPredicateGroup (query : Query) (entries : List Entry) (predicates : List WfIri)
    (predicateVar countAlias : VarName) (counts : List (WfIri × Nat)) (counters : Counters) : IO UInt32 := do
  let backend : GraphBackend := .hdt
    { search := fun _ => []
      estimate := fun bound =>
        match bound.p with
        | none => counts.foldl (fun total pair => total + pair.2) 0
        | some predicate => countForPredicate counts predicate
      predicatePresent := fun predicate => countForPredicate counts predicate > 0 }
  let grouped := predicateGroupBySolutions predicateVar countAlias backend predicates
  let ordered := match query.modifier.orderBy with
    | none => grouped
    | some order => sortSolutions (compareOnConditions emptyEnv emptyEnv.activeGraph order) grouped
  let rows := sliceSolutions query.modifier.offset query.modifier.limit ordered
  IO.println s!"l4block-id-v3-query shards={entries.length} open-mode=ibk3-paged-merkle-predicate-group-count({predicates.length}) delta=base logical-read-bytes={counters.requestedBytes} fetched-bytes={counters.fetchedBytes}"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println s!"l4block-id-v3-query rows={rows.length} preview={toString (repr (rows.take 10))}"
  return 0

/-- A deliberately narrow first SRI1 join admission.  The two BGP patterns
    share one subject variable and have different constant predicates.  There
    are no dataset clauses or trailing VALUES.  We materialise the smaller
    side normally, then use its RDF subjects to select rows from the larger
    side. The ordinary parsed evaluator still performs the join, projection,
    ordering and bag semantics over the reduced exact graph. -/
private def sharedSubjectJoin? (query : Query) : Option (WfIri × WfIri) := do
  if !query.dataset.isEmpty || query.postValues.isSome then none else
  match query.pattern with
  | .bgp [left, right] =>
      match left.s, left.p, right.s, right.p with
      | .var subject, .iri leftPredicate, .var otherSubject, .iri rightPredicate =>
          if subject == otherSubject && leftPredicate != rightPredicate then
            some (leftPredicate, rightPredicate)
          else none
      | _, _, _, _ => none
  | _ => none

/-- Conservative three-way shared-subject BGP admission.  This is kept
separate from the two-way detector so an execution path can be introduced
without broadening existing plans. -/
private structure SharedSubjectTriplePlan where
  subject : VarName
  first : WfIri × VarName
  second : WfIri × VarName
  third : WfIri × VarName

private def sharedSubjectTriple? (query : Query) : Option SharedSubjectTriplePlan := do
  if !query.dataset.isEmpty || query.postValues.isSome then none else
  match query.pattern with
  | .bgp [a, b, c] =>
      match a.s, a.p, a.o, b.s, b.p, b.o, c.s, c.p, c.o with
      | .var s, .iri pa, .var oa, .var sb, .iri pb, .var ob, .var sc, .iri pc, .var oc =>
          if s == sb && s == sc && pa != pb && pa != pc && pb != pc &&
              s != oa && s != ob && s != oc && oa != ob && oa != oc && ob != oc then
            some { subject := s, first := (pa, oa), second := (pb, ob), third := (pc, oc) }
          else none
      | _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- The direct three-way binding sequence deliberately chooses the smallest
    physical driver, so it proves a BGP *bag* rather than the source BGP's
    incidental list order.  Keep the first executable admission to a basic
    modifier-free SELECT: ORDER BY tie order, DISTINCT's retained occurrence,
    grouping, and OFFSET/LIMIT can all observe list order.  Those forms stay
    on the established evaluator until their own refinement contracts are
    stated and proved. -/
private def directSubjectTripleSelect? (query : Query) : Bool :=
  match query.form with
  | .select _ =>
      query.groupBy.isNone && query.having.isEmpty && query.modifier.orderBy.isNone &&
        !query.modifier.distinct && !query.modifier.reduced &&
        query.modifier.offset.isNone && query.modifier.limit.isNone
  | _ => false

private def entryRows (entries : List Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.rows) 0

/-- TLI1 is currently ordered by the exact persisted term serialization,
    whereas SPARQL term matching is coarser for language-tag case and
    `rdf:XMLLiteral` canonical XML.  Such literals must therefore use the
    ordinary materialising route until the index represents every equivalent
    local ID; admitting them here could incorrectly turn a match into no
    rows. -/
private def exactObjectIndexKeySafe (term : Term) : Bool :=
  match term with
  | .iri _ => true
  | .literal literal =>
      literal.val.langTag.isNone && literal.val.datatype != rdfXMLLiteral
  | .bnode _ | .tripleTerm _ _ _ => false

/-- The OLI2-safe object-bound triple shape. Blank labels and RDF 1.2 triple
    terms deliberately wait for a separate scoped-identity admission; so do
    literals whose SPARQL equality is not byte-exact in the current TLI1. -/
private def objectBoundTriple? (tp : TriplePattern) : Option (WfIri × Term) :=
  match tp.p, tp.o with
  | .iri predicate, .iri object => some (predicate, .iri object)
  | .iri predicate, .literal object =>
      if exactObjectIndexKeySafe (.literal object) then some (predicate, .literal object) else none
  | _, _ => none

/-- The first object-bound physical admission stays deliberately small:
    default graph, one BGP triple, a constant IRI predicate, and an IRI or
    literal object.  The parsed evaluator still supplies all SPARQL result
    semantics over the exact, OLI2-selected fragment. -/
private def objectBoundPredicate? (query : Query) : Option (WfIri × Term) :=
  if !query.dataset.isEmpty || query.postValues.isSome then none else
  match query.pattern with
  | .bgp [tp] => objectBoundTriple? tp
  | _ => none

/-- Every selective access path below hands `finish` a PROPER SUBSET of the
    store's triples, and `finish` builds `env.dataset` from exactly that
    subset.  §18.6 evaluates an `EXISTS` / `NOT EXISTS` against the ACTIVE
    GRAPH, so a query carrying one in its projection, a GROUP BY key, a
    HAVING condition or an ORDER BY condition may not take a selective path;
    it falls through to the full-manifest read.
    `ShardManifest.queryNativeConstantPredicates?` carries the same guard for
    the pattern-driven opener below
    (https://github.com/danbri/factoidal/issues/638). -/
private def selectivePathAdmissible (query : Query) : Bool :=
  query.expressionsOutsidePatternExistsFree

private def tryObjectIndexScan (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
  if !selectivePathAdmissible query then pure none else
  match objectBoundPredicate? query, ← readDefaultDelta? directory with
  | some (predicate, object), some delta =>
      if manifest.version != 6 || !deltaResolvedIsEmpty delta then pure none else
      let entries := selectAll manifest predicate
      if entries.isEmpty then pure none else
      match ← scanEntriesForObjectsV2 directory predicate [object] entries [] {} 0 with
      | none => pure none
      | some (triples, counters, _) =>
          some <$> finish query entries [predicate] triples counters delta
            "ibk3-sri2-tli1-oli2-object-scan"
  | _, _ => pure none

/-- An object-selected triple can drive a second constant-predicate triple
    through its RDF subjects.  This is the reverse of the existing SRI2 join:
    OLI2/TLI1 first returns exact driver triples; their subjects then select
    exact rows from the other predicate via SRI2/TLI1.  Different predicates
    avoid duplicating one physical fragment in the evaluator's input. -/
private def tryObjectIndexJoin (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
  if !selectivePathAdmissible query then pure none else
  if !query.dataset.isEmpty || query.postValues.isSome || manifest.version != 6 then pure none else
  match query.pattern, ← readDefaultDelta? directory with
  | .bgp [left, right], some delta =>
      if !deltaResolvedIsEmpty delta then pure none else
      let plan :=
        match objectBoundTriple? left, prefixPredicate? right with
        | some (drivePredicate, object), some targetPredicate =>
            match left.s, right.s, right.o with
            | .var driveSubject, .var targetSubject, .var targetObject =>
                if driveSubject == targetSubject && drivePredicate != targetPredicate then
                  some (drivePredicate, object, targetPredicate, driveSubject, targetObject)
                else none
            | _, _, _ => none
        | _, _ =>
            match objectBoundTriple? right, prefixPredicate? left with
            | some (drivePredicate, object), some targetPredicate =>
                match right.s, left.s, left.o with
                | .var driveSubject, .var targetSubject, .var targetObject =>
                    if driveSubject == targetSubject && drivePredicate != targetPredicate then
                      some (drivePredicate, object, targetPredicate, driveSubject, targetObject)
                    else none
                | _, _, _ => none
            | _, _ => none
      match plan with
      | none => pure none
      | some (drivePredicate, object, targetPredicate, subjectVar, targetObjectVar) =>
          let driveEntries := selectAll manifest drivePredicate
          let targetEntries := selectAll manifest targetPredicate
          if driveEntries.isEmpty || targetEntries.isEmpty then pure none else
          match ← scanEntriesForObjectsV2 directory drivePredicate [object] driveEntries [] {} 0 with
          | none => pure none
          | some (driveTriples, driveCounters, _) =>
              let subjects := distinctSubjectTerms driveTriples
              match ← scanEntriesForSubjectsV2 directory targetPredicate subjects targetEntries [] {} 0 with
              | none => pure none
              | some (targetTriples, targetCounters, _) =>
                  let entries := driveEntries ++ targetEntries
                  let counters := addCounters driveCounters targetCounters
                  match query.form with
                  | .select _ =>
                      some <$> finishObjectSubjectSelect query entries
                        [drivePredicate, targetPredicate] subjectVar targetObjectVar
                        driveTriples targetTriples counters
                  | _ =>
                      some <$> finish query entries [drivePredicate, targetPredicate]
                        (driveTriples ++ targetTriples) counters delta
                        "ibk3-sri2-tli1-oli2-object-subject-join"
  | _, _ => pure none

private def trySubjectIndexJoin (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
  if !selectivePathAdmissible query then pure none else
  match sharedSubjectJoin? query, ← readDefaultDelta? directory with
  | some (leftPredicate, rightPredicate), some delta =>
      if !deltaResolvedIsEmpty delta then pure none else
      let leftEntries := selectAll manifest leftPredicate
      let rightEntries := selectAll manifest rightPredicate
      if leftEntries.isEmpty || rightEntries.isEmpty then pure none else
      let (drivePredicate, driveEntries, targetPredicate, targetEntries) :=
        if entryRows leftEntries <= entryRows rightEntries then
          (leftPredicate, leftEntries, rightPredicate, rightEntries)
        else (rightPredicate, rightEntries, leftPredicate, leftEntries)
      match ← materializeEntries directory driveEntries with
      | none => pure none
      | some (driveTriples, driveCounters) =>
          let subjects := distinctSubjectTerms driveTriples
          let targetScan ←
            if manifest.version >= 5 then
              scanEntriesForSubjectsV2 directory targetPredicate subjects targetEntries [] {} 0
            else
              scanEntriesForSubjects directory targetPredicate subjects targetEntries [] {} 0
          match targetScan with
          | none => pure none
          | some (targetTriples, targetCounters, _) =>
              let entries := driveEntries ++ targetEntries
              let counters := addCounters driveCounters targetCounters
              let code ← finish query entries [drivePredicate, targetPredicate]
                (driveTriples ++ targetTriples) counters delta
                  (if manifest.version >= 5 then "ibk3-sri2-tli1-subject-join" else "ibk3-sri1-tli1-subject-join")
              pure (some code)
  | _, _ => pure none

private def trySubjectTripleJoin (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
  if !selectivePathAdmissible query then pure none else
  match sharedSubjectTriple? query, ← readDefaultDelta? directory with
  | some plan, some delta =>
      if manifest.version < 5 || !deltaResolvedIsEmpty delta then pure none else
      let ea := selectAll manifest plan.first.1
      let eb := selectAll manifest plan.second.1
      let ec := selectAll manifest plan.third.1
      if ea.isEmpty || eb.isEmpty || ec.isEmpty then pure none else
      let (drive, driveVar, de, left, leftVar, le, right, rightVar, re) :=
        if entryRows ea <= entryRows eb && entryRows ea <= entryRows ec then
          (plan.first.1, plan.first.2, ea, plan.second.1, plan.second.2, eb,
            plan.third.1, plan.third.2, ec)
        else if entryRows eb <= entryRows ec then
          (plan.second.1, plan.second.2, eb, plan.first.1, plan.first.2, ea,
            plan.third.1, plan.third.2, ec)
        else
          (plan.third.1, plan.third.2, ec, plan.first.1, plan.first.2, ea,
            plan.second.1, plan.second.2, eb)
      match ← materializeEntries directory de with
      | none => pure none
      | some (drivers, dc) =>
          let subjects := distinctSubjectTerms drivers
          match ← scanEntriesForSubjectsV2 directory left subjects le [] {} 0,
                ← scanEntriesForSubjectsV2 directory right subjects re [] {} 0 with
          | some (ls, lc, _), some (rs, rc, _) =>
              let counters := addCounters dc (addCounters lc rc)
              let code ← match query.form with
                | .select _ =>
                    if directSubjectTripleSelect? query then
                      finishSubjectTripleSelect query (de ++ le ++ re) [drive, left, right]
                        plan.subject driveVar leftVar rightVar drivers ls rs counters
                    else
                      finish query (de ++ le ++ re) [drive, left, right]
                        (drivers ++ ls ++ rs) counters delta "ibk3-sri2-tli1-subject-triple-join"
                | _ =>
                    finish query (de ++ le ++ re) [drive, left, right]
                      (drivers ++ ls ++ rs) counters delta "ibk3-sri2-tli1-subject-triple-join"
              pure (some code)
          | _, _ => pure none
  | _, _ => pure none

/-- The subject-point shape: one BGP triple whose subject is a constant IRI
    and whose predicate is a variable.  A blank-node subject is refused: a
    blank node label is a scoped identity, not a global name, so it cannot be
    resolved against a persisted term index.  The object position is
    unconstrained — the parsed evaluator still applies the whole triple
    pattern to the exact fragment this path returns, so a constant object or a
    repeated variable simply filters it. -/
private def subjectPointSubject? (query : Query) : Option WfIri :=
  if !query.dataset.isEmpty || query.postValues.isSome then none else
  match query.pattern with
  | .bgp [tp] =>
      match tp.s, tp.p with
      | .iri subject, .var _ => some subject
      | _, _ => none
  | _ => none

/-- Read every predicate-local block's SRI2 postings for one RDF subject.
    Each entry is scanned under its OWN predicate, which is how the manifest
    labels it; a malformed or unavailable artifact propagates `none` so the
    caller falls through to the complete path. -/
private def scanAllEntriesForSubject (directory : System.FilePath) (subject : Term) :
    List Entry → List Triple → Counters → IO (Option (List Triple × Counters))
  | [], triples, counters => pure (some (triples, counters))
  | entry :: rest, triples, counters => do
      match ← scanEntriesForSubjectsV2 directory entry.predicate [subject] [entry] [] {} 0 with
      | none => pure none
      | some (current, currentCounters, _) =>
          scanAllEntriesForSubject directory subject rest (triples ++ current)
            (addCounters counters currentCounters)

/-- A constant-subject triple pattern with an unbound predicate has a
    selective physical access path even though no predicate is named: every
    triple with that subject lives in exactly one predicate-local block, and
    every block's TLI1 term index and SRI2 subject postings were recomputed
    and validated against its rows at activation (Shardborough §6.3).  The
    union of the SRI2-selected rows over ALL manifest entries is therefore the
    exact subject fragment, and only the pages those postings need are read.
    The ordinary parsed evaluator supplies every SPARQL result semantic over
    that fragment. -/
private def trySubjectPointLookup (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
  if !selectivePathAdmissible query then pure none else
  match subjectPointSubject? query, ← readDefaultDelta? directory with
  | some subject, some delta =>
      if manifest.version < 5 || !deltaResolvedIsEmpty delta then pure none else
      if manifest.entries.isEmpty then pure none else
      match ← scanAllEntriesForSubject directory (.iri subject) manifest.entries [] {} with
      | none => pure none
      | some (triples, counters) =>
          some <$> finish query manifest.entries (predicateOrder manifest.entries)
            triples counters delta "ibk3-sri2-tli1-subject-point"
  | _, _ => pure none

/-- `LIMIT 0` is the one bounded SELECT case whose result is independent of
    physical BGP order, delta contents, grouping, ordering and expression
    evaluation: `sliceSolutions` necessarily returns `[]`.  Handle it after
    query/manifest/activation admission but before opening any artifact. -/
private def finishSelectLimitZero (query : Query) : IO UInt32 := do
  IO.println "l4block-id-v3-query shards=0 open-mode=ibk3-limit-zero(0) delta=not-read logical-read-bytes=0 fetched-bytes=0"
  IO.println s!"l4block-id-v3-query sse={query.toSse}"
  IO.println "l4block-id-v3-query rows=0 preview=[]"
  return 0

private def run (directoryText queryText : String) : IO UInt32 := do
  try
    let root := System.FilePath.mk directoryText
    let directory ← resolveStoreDirectory root
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-id-v3-query rejected: malformed SBM2 manifest"; return 1
    | _, .error error => IO.eprintln s!"l4block-id-v3-query query parse error at {error.pos}: {error.msg}"; return 1
    | some manifest, .ok query =>
        if isIbk4Layout manifest.layout || manifest.version == 7 || manifest.version == 8 then
          IO.eprintln "l4block-id-v3-query rejected: this generation is SBM7 or SBM8 with IBK4 quad blocks; the quad-aware query path is not implemented, and an IBK3 reader would misread its rows"
          return 1
        if !rangeCommitted manifest || !isIbk3Layout manifest.layout then
          IO.eprintln "l4block-id-v3-query rejected: not an IBK3 range-committed manifest"; return 1
        if manifest.version >= 5 && !(← (root / currentName).pathExists) then
          IO.eprintln "l4block-id-v3-query rejected: SBM5 and later require an activated collection root (CURRENT)"; return 1
        match query.form, query.modifier.limit with
        | .select _, some 0 => finishSelectLimitZero query
        | _, _ => match ← tryObjectIndexScan directory manifest query with
        | some code => return code
        | none => match ← tryObjectIndexJoin directory manifest query with
        | some code => return code
        | none => match ← trySubjectIndexJoin directory manifest query with
        | some code => return code
        | none => match ← trySubjectTripleJoin directory manifest query with
        | some code => return code
        | none => match ← trySubjectPointLookup directory manifest query with
        | some code => return code
        | none => match queryNativeConstantPredicates? query with
        | none =>
            match groupPredicate? query with
            | none =>
                /- A query with an unbound predicate is still a valid
                   persistent query.  It has no selective access path yet,
                   so make the cost explicit in the mode rather than
                   rejecting it or accidentally treating one predicate as
                   the whole graph. -/
                match ← readDefaultDelta? directory with
                | none => IO.eprintln "l4block-id-v3-query rejected: malformed DLOG sidecar"; return 1
                | some delta =>
                    match ← materializeEntries directory manifest.entries with
                    | some (triples, counters) =>
                        finish query manifest.entries (predicateOrder manifest.entries) triples counters delta
                          "ibk3-paged-merkle-full-manifest"
                    | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
            | some (predicateVar, countAlias) =>
                match ← readDefaultDelta? directory with
                | none => IO.eprintln "l4block-id-v3-query rejected: malformed DLOG sidecar"; return 1
                | some delta =>
                    if !deltaResolvedIsEmpty delta then
                      match ← materializeEntries directory manifest.entries with
                      | some (triples, counters) => finish query manifest.entries [] triples counters delta
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                    else
                      let predicates := predicateOrder manifest.entries
                      match ← countAllPredicates directory manifest predicates [] {} with
                      | some (counts, counters) =>
                          finishPredicateGroup query manifest.entries predicates predicateVar countAlias counts counters
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
        | some predicates =>
            let entries := entriesForPredicates manifest predicates
            match ← readDefaultDelta? directory with
            | none => IO.eprintln "l4block-id-v3-query rejected: malformed DLOG sidecar"; return 1
            | some delta =>
                match countPredicate? query with
                | some (alias, predicate) =>
                    if !deltaResolvedIsEmpty delta then
                      match ← materializeEntries directory entries with
                      | some (triples, counters) => finish query entries predicates triples counters delta
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                    else
                      let countEntries := selectAll manifest predicate
                      match ← Harness.IndexedBlockV3Materialize.countEntries directory predicate countEntries 0 {} with
                      | some (count, counters) => finishCount query countEntries alias count counters
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                | none => match askPredicate? query with
                | some predicate =>
                    if !deltaResolvedIsEmpty delta then
                      match ← materializeEntries directory entries with
                      | some (triples, counters) => finishAsk query entries predicates triples counters delta
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                    else
                      let askEntries := selectAll manifest predicate
                      match ← Harness.IndexedBlockV3Materialize.countEntries directory predicate askEntries 0 {} with
                      | some (count, counters) => finishAskCount query askEntries count counters
                      | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                | none => match detectLimitSingleTp query with
                | some (tp, limit) =>
                    match prefixPredicate? tp with
                    | some predicate =>
                        if !deltaResolvedIsEmpty delta then
                          match ← materializeEntries directory entries with
                          | some (triples, counters) => finish query entries predicates triples counters delta
                          | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                        else
                          let prefixEntries := selectAll manifest predicate
                          match ← scanEntries directory predicate limit prefixEntries [] {} 0 with
                          | some (triples, counters, _) => finish query prefixEntries predicates triples counters delta
                          | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                    | none =>
                        match ← materializeEntries directory entries with
                        | some (triples, counters) => finish query entries predicates triples counters delta
                        | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
                | none =>
                    match ← materializeEntries directory entries with
                    | some (triples, counters) => finish query entries predicates triples counters delta
                    | none => IO.eprintln "l4block-id-v3-query rejected: malformed or unavailable committed artifact"; return 1
  catch error => IO.eprintln s!"l4block-id-v3-query failure: {error}"; return 1

/-- Benchmark-only repeated fresh evaluation inside one native process. Each
    iteration still opens the immutable generation and validates its requested
    ranges; this mode exists so a profiler can observe an otherwise sub-second
    physical query without changing query semantics. -/
private def repeatRun (remaining : Nat) (directoryText queryText : String) : IO UInt32 :=
  match remaining with
  | 0 => pure 0
  | count + 1 => do
      let code ← run directoryText queryText
      if code == 0 then repeatRun count directoryText queryText else pure code

def main (args : List String) : IO UInt32 := do
  match args with
  | directory :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-id-v3-query requires a query"; return 2
      else run directory (String.intercalate " " queryParts)
  | directory :: "--repeat" :: countText :: "--query" :: queryParts =>
      if queryParts.isEmpty then IO.eprintln "l4block-id-v3-query requires a query"; return 2
      else match countText.toNat? with
      | some count => repeatRun count directory (String.intercalate " " queryParts)
      | none => IO.eprintln "l4block-id-v3-query --repeat requires a natural number"; return 2
  | _ => IO.eprintln "usage: l4block-id-v3-query SHARD-DIR [--repeat N] --query SELECT..."; return 2

end Harness.IndexedBlockV3Query

def main (args : List String) : IO UInt32 := Harness.IndexedBlockV3Query.main args
