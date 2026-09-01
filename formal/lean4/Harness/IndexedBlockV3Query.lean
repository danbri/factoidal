/- Parsed SELECT over constant-predicate IBK3 fragments: physical bytes are
   admitted by the shared Merkle/paged materializer, then ordinary Lean SPARQL
   evaluates the parsed algebra. -/
import Harness.IndexedBlockV3Materialize
import Harness.ShardMerkleMaterialize
import Harness.GenerationPointer
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.StoreFastPath
import L4Factoidal.Storage.ShardManifest

namespace Harness.IndexedBlockV3Query

open Harness.IndexedBlockV3Materialize
open Harness.ShardMerkleMaterialize
open Harness.GenerationPointer
open L4Factoidal.RDF
open L4Factoidal.SPARQL
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

private def isIbk3Layout (layout : String) : Bool :=
    layout == "predicate-ibk3-ptd1-merkle-v0" ||
    layout == "predicate-ibk3-ptd1-sri1-merkle-v0" ||
    layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0" ||
    layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0" ||
    layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0" ||
    layout == "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1" ||
    layout == "predicate-ibk3-ptd1-sri1-merkle-v0-compacted-default-dlog-v1" ||
    layout == "predicate-ibk3-ptd1-sri1-tli1-merkle-v0-compacted-default-dlog-v1" ||
    layout == "predicate-ibk3-ptd1-sri2-tli1-merkle-v0-compacted-default-dlog-v1" ||
    layout == "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0-compacted-default-dlog-v1"

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

private def predicateOrder (entries : List Entry) : List WfIri :=
  entries.foldl (fun seen entry =>
    if seen.contains entry.predicate then seen else seen ++ [entry.predicate]) []

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
  let dataset : DatasetBackend := { default := backendFor triples delta, named := [] }
  let deltaMode := if deltaResolvedIsEmpty delta then "base" else "base-plus-delta"
  match query.form with
  | .select _ =>
      match runSelectQueryBackendDataset emptyEnv query dataset with
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
    | some order => sortSolutions (compareOnConditions emptyEnv order) grouped
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

private def tryObjectIndexScan (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
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
  if !query.dataset.isEmpty || query.postValues.isSome || manifest.version != 6 then pure none else
  match query.pattern, ← readDefaultDelta? directory with
  | .bgp [left, right], some delta =>
      if !deltaResolvedIsEmpty delta then pure none else
      let plan :=
        match objectBoundTriple? left, prefixPredicate? right with
        | some (drivePredicate, object), some targetPredicate =>
            match left.s, right.s with
            | .var driveSubject, .var targetSubject =>
                if driveSubject == targetSubject && drivePredicate != targetPredicate then
                  some (drivePredicate, object, targetPredicate)
                else none
            | _, _ => none
        | _, _ =>
            match objectBoundTriple? right, prefixPredicate? left with
            | some (drivePredicate, object), some targetPredicate =>
                match right.s, left.s with
                | .var driveSubject, .var targetSubject =>
                    if driveSubject == targetSubject && drivePredicate != targetPredicate then
                      some (drivePredicate, object, targetPredicate)
                    else none
                | _, _ => none
            | _, _ => none
      match plan with
      | none => pure none
      | some (drivePredicate, object, targetPredicate) =>
          let driveEntries := selectAll manifest drivePredicate
          let targetEntries := selectAll manifest targetPredicate
          if driveEntries.isEmpty || targetEntries.isEmpty then pure none else
          match ← scanEntriesForObjectsV2 directory drivePredicate [object] driveEntries [] {} 0 with
          | none => pure none
          | some (driveTriples, driveCounters, _) =>
              let subjects := driveTriples.map (fun triple => triple.s.toTerm) |>.eraseDups
              match ← scanEntriesForSubjectsV2 directory targetPredicate subjects targetEntries [] {} 0 with
              | none => pure none
              | some (targetTriples, targetCounters, _) =>
                  let entries := driveEntries ++ targetEntries
                  let counters := addCounters driveCounters targetCounters
                  some <$> finish query entries [drivePredicate, targetPredicate]
                    (driveTriples ++ targetTriples) counters delta
                    "ibk3-sri2-tli1-oli2-object-subject-join"
  | _, _ => pure none

private def trySubjectIndexJoin (directory : System.FilePath) (manifest : Manifest) (query : Query) :
    IO (Option UInt32) := do
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
          let subjects := driveTriples.map (fun triple => triple.s.toTerm) |>.eraseDups
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

private def run (directoryText queryText : String) : IO UInt32 := do
  try
    let root := System.FilePath.mk directoryText
    let directory ← resolveStoreDirectory root
    let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
    match decode? manifestBytes, parseSparql queryText with
    | none, _ => IO.eprintln "l4block-id-v3-query rejected: malformed SBM2 manifest"; return 1
    | _, .error error => IO.eprintln s!"l4block-id-v3-query query parse error at {error.pos}: {error.msg}"; return 1
    | some manifest, .ok query =>
        if !rangeCommitted manifest || !isIbk3Layout manifest.layout then
          IO.eprintln "l4block-id-v3-query rejected: not an IBK3 range-committed manifest"; return 1
        if manifest.version >= 5 && !(← (root / currentName).pathExists) then
          IO.eprintln "l4block-id-v3-query rejected: SBM5 and later require an activated collection root (CURRENT)"; return 1
        match ← tryObjectIndexScan directory manifest query with
        | some code => return code
        | none => match ← tryObjectIndexJoin directory manifest query with
        | some code => return code
        | none => match ← trySubjectIndexJoin directory manifest query with
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
