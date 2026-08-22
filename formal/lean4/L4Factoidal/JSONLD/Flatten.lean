/-
L4Factoidal.JSONLD.Flatten — JSON-LD 1.1 Flattening.

Port of `formal/fstar/JSONLD.Flatten.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §7.1 Node Map Generation — `nmg`: walk the EXPANDED document,
    collecting every node's properties into a per-graph node map keyed
    by node identifier, relabelling every blank node identifier through
    the §7.2 issuer (`_:b0`, `_:b1`, … in first-issue order — the
    fixtures pin the exact labels, so issue order follows the spec's
    step order: `@type` items first, then `@id`, then `@reverse` /
    `@graph` / `@included` / the remaining properties in code-point key
    order);
  * §7.2 Generate Blank Node Identifier — `issueKeyed` / `issueFresh`;
  * §6.1's flattening fold (`flattenExpanded`): fold each named graph's
    nodes (ordered by id) under a `@graph` entry of that graph's
    name-node in the default graph (graph names ordered
    lexicographically), then emit the default graph's nodes ordered by
    id, dropping nodes that consist ONLY of an `@id`;
  * the `JsonLdProcessor.flatten()` entry point (`flattenDocument`):
    expand, flatten, and — when the caller supplies a context — compact
    the flattened array with `JSONLD.Compact`, keeping a top-level
    `@graph` (or its alias) and re-attaching the original context.

All map lookups here are on EXPANDED-form JSON (literal `@id` / `@value`
keys — expansion has already resolved aliases); aliases matter only for
the OUTPUT `@graph` key of the compaction step.

## Error model

`Res` (`Except JsonLdError`). The flatten manifest's single negative
test expects `conflicting indexes`, raised at Node Map Generation step
6.8 when two different `@index` values reach one node id; this port
produces exactly that code. Fuel exhaustion is `contextOverflow` — an
honest failure, never a wrong answer.

## Termination

Node Map Generation recurses over the document tree through a mutual
group; every function in it carries an explicit fuel `Nat` derived from
`Json.size`, exactly as the F* source does.
-/
import L4Factoidal.JSONLD.Compact

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Node-map representation

A node's collected entries: `@id` first (always present), then `@type` /
`@index` / properties in first-seen order. Emitted verbatim as an
object — member order is insignificant under the suite's JCS-canonical
comparison, but ARRAY order inside each property's value IS significant
and follows the spec's append order. -/

abbrev NmNode := List (String × Json)

/-- One graph's node map: node id → node, in first-creation order
(re-sorted by id at emission time — the spec's "ordered by id"). -/
abbrev NmGraph := List (String × NmNode)

/-- Whole-algorithm state: graph name → graph (`"@default"` plus named
graphs), the blank-node relabelling map (old label → issued label), and
the issuer counter. -/
structure NmState where
  graphs : List (String × NmGraph)
  idmap  : List (String × String)
  ctr    : Nat
  deriving Repr

/-! ## Association-list helpers -/

def flLookup {α : Type} (xs : List (String × α)) (k : String) : Option α :=
  (xs.find? (fun kv => kv.1 == k)).map Prod.snd

/-- Replace `k`'s value in place (preserving position) or append at the
end. -/
def flUpd {α : Type} : List (String × α) → String → α → List (String × α)
  | [],               k, v => [(k, v)]
  | (k2, v2) :: rest, k, v => if k2 == k then (k2, v) :: rest else (k2, v2) :: flUpd rest k v

def flRemove {α : Type} : List (String × α) → String → List (String × α)
  | [],               _ => []
  | (k2, v2) :: rest, k => if k2 == k then rest else (k2, v2) :: flRemove rest k

/-- Insertion sort by key, code-point order — the spec's "ordered
lexicographically". Stable for equal keys. -/
def flInsertByKey {α : Type} (kv : String × α) : List (String × α) → List (String × α)
  | []      => [kv]
  | y :: rest => if strLt kv.1 y.1 then kv :: y :: rest else y :: flInsertByKey kv rest

def flSortByKey {α : Type} : List (String × α) → List (String × α)
  | []        => []
  | kv :: rest => flInsertByKey kv (flSortByKey rest)

/-- "the value is already in the array" — the spec's duplicate check
compares maps structurally; `expandedEqual` (JCS canonical form) is that
comparison: member order insignificant, array order significant, numbers
by canonical value. -/
def flArrContains (items : List Json) (v : Json) : Bool :=
  items.any (fun it => expandedEqual it v)

/-! ## Node-level operations -/

/-- Append `v` to the node's property array (creating the entry),
skipping the append when `dedup` is set and an equal value is already
present. -/
def nodeAppendProp (n : NmNode) (prop : String) (v : Json) (dedup : Bool) : NmNode :=
  match flLookup n prop with
  | some (.array items) =>
    if dedup && flArrContains items v then n else flUpd n prop (.array (items ++ [v]))
  | some other => flUpd n prop (.array [other, v])  -- non-array: defensive, never built here
  | none       => n ++ [(prop, .array [v])]

/-- §7.1 step 6.12.2: the property entry exists even if no value
survives recursion. -/
def nodeEnsureProp (n : NmNode) (prop : String) : NmNode :=
  match flLookup n prop with
  | some _ => n
  | none   => n ++ [(prop, .array [])]

/-- Merge `@type` items into the node's `@type` array, skipping
duplicates (step 6.7's "unless it already exists"). -/
def flMergeTypeItems : List Json → List Json → List Json
  | existing, []        => existing
  | existing, hd :: tl  =>
    if flArrContains existing hd then flMergeTypeItems existing tl
    else flMergeTypeItems (existing ++ [hd]) tl

def nodeMergeTypes (n : NmNode) (items : List Json) : NmNode :=
  match flLookup n "@type" with
  | some (.array existing) => flUpd n "@type" (.array (flMergeTypeItems existing items))
  | some other             => flUpd n "@type" (.array (flMergeTypeItems [other] items))
  | none                   => n ++ [("@type", .array (flMergeTypeItems [] items))]

/-- Step 6.8: a second, DIFFERENT `@index` for the same node id is the
spec's "conflicting indexes" error (fixture e001). -/
def nodeSetIndex (n : NmNode) (idx : Json) : Option NmNode :=
  match flLookup n "@index" with
  | some old => if expandedEqual old idx then some n else none
  | none     => some (n ++ [("@index", idx)])

def nodeHasOnlyId : NmNode → Bool
  | [(k, _)] => k == "@id"
  | _        => false

/-! ## State-level operations -/

def stGraph (st : NmState) (g : String) : NmGraph :=
  (flLookup st.graphs g).getD []

def stPutGraph (st : NmState) (g : String) (gr : NmGraph) : NmState :=
  { st with graphs := flUpd st.graphs g gr }

/-- Step 6.3: create `graph[id] = { "@id": id }` when absent (also
registers the graph itself on first touch). -/
def stEnsureNode (st : NmState) (g id : String) : NmState :=
  let gr := stGraph st g
  match flLookup gr id with
  | some _ => stPutGraph st g gr
  | none   => stPutGraph st g (gr ++ [(id, [("@id", .string id)])])

/-- Apply `f` to `graph[id]`, creating the node first if needed. -/
def stNodeUpdate (st : NmState) (g id : String) (f : NmNode → NmNode) : NmState :=
  let gr := stGraph st g
  match flLookup gr id with
  | some n => stPutGraph st g (flUpd gr id (f n))
  | none   => stPutGraph st g (gr ++ [(id, f [("@id", .string id)])])

/-- Add `v` to `subject-node[aprop]` when both an active subject (an
IRI/bnode string) and an active property are in scope. A free-floating
value with no subject is silently dropped — expansion has already
removed the ones the spec drops, so this is pure defence. -/
def stAddValue (st : NmState) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (v : Json) (dedup : Bool) : NmState :=
  match asubj, aprop with
  | some (.string sid), some p =>
    stNodeUpdate st agraph sid (fun n => nodeAppendProp n p v dedup)
  | _, _ => st

/-! ## Generate Blank Node Identifier — API §7.2 -/

/-- Relabel a specific existing blank node identifier: return its issued
label if seen before, else issue `_:b<counter>` and record the
mapping. -/
def issueKeyed (st : NmState) (old : String) : String × NmState :=
  match flLookup st.idmap old with
  | some nid => (nid, st)
  | none =>
    let nid := "_:b" ++ toString st.ctr
    (nid, { st with idmap := st.idmap ++ [(old, nid)], ctr := st.ctr + 1 })

/-- Issue a fresh label — the spec's issuer called with a null
identifier (an anonymous node object with no `@id`). -/
def issueFresh (st : NmState) : String × NmState :=
  ("_:b" ++ toString st.ctr, { st with ctr := st.ctr + 1 })

/-- §7.1 step 3: relabel blank node identifiers among the element's
`@type` items. This runs BEFORE `@id` issuance — the fixtures pin the
resulting label order. -/
def flRelabelTypeItems (st : NmState) : List Json → NmState × List Json
  | []               => (st, [])
  | .string s :: tl  =>
    if isBnodeId s then
      let (nid, st1) := issueKeyed st s
      let (st2, tl') := flRelabelTypeItems st1 tl
      (st2, .string nid :: tl')
    else
      let (st1, tl') := flRelabelTypeItems st tl
      (st1, .string s :: tl')
  | hd :: tl =>
    let (st1, tl') := flRelabelTypeItems st tl
    (st1, hd :: tl')

/-- Shape-preserving: a node object's `@type` is an array in expanded
form, but a VALUE object's `@type` is a bare string — step 3 only
substitutes blank node identifiers, it never re-shapes (flatten/0002
pins the value-object scalar staying scalar). -/
def flRelabelTypes (st : NmState) (fields : List (String × Json))
    : NmState × List (String × Json) :=
  match flLookup fields "@type" with
  | some (.array items) =>
    let (st1, items') := flRelabelTypeItems st items
    (st1, flUpd fields "@type" (.array items'))
  | some (.string s) =>
    if isBnodeId s then
      let (nid, st1) := issueKeyed st s
      (st1, flUpd fields "@type" (.string nid))
    else (st, fields)
  | _ => (st, fields)

/-! ## Node Map Generation — API §7.1

`nmg`'s parameters mirror the spec's: the node map (inside `NmState`),
the active graph (a graph name), the active subject (`none`, a
`.string id`, or — for the `@reverse` case — an object node reference),
the active property, and `acc`, the in-progress `@list` array (`none` is
the spec's "list is null"). -/

mutual

def nmg (st : NmState) (element : Json) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match element with
    -- Step 1: arrays — process each item in order.
    | .array items => nmgItems st items agraph asubj aprop acc fuel
    | .object fields0 =>
      -- Step 3: relabel blank node identifiers among @type items.
      let (st, fields) := flRelabelTypes st fields0
      if hasField "@value" fields then
        -- Step 4: value object.
        match acc with
        | none    => .ok (stAddValue st agraph asubj aprop (.object fields) true, none)
        | some xs => .ok (st, some (xs ++ [.object fields]))
      else if hasField "@list" fields then
        -- Step 5: list object — collect the nested items into a fresh
        -- accumulator, then attach {"@list": [...]} where the spec says.
        match flLookup fields "@list" with
        | none      => .error .notJsonLd  -- unreachable: hasField just held
        | some lval =>
          match nmg st lval agraph asubj aprop (some []) fuel with
          | .ok (st1, some litems) =>
            let result := Json.object [("@list", .array litems)]
            (match acc with
             | none    => .ok (stAddValue st1 agraph asubj aprop result false, none)
             | some xs => .ok (st1, some (xs ++ [result])))
          | .ok (_, none) => .error .notJsonLd
          | .error e      => .error e
      else
        -- Step 6: node object.
        nmgNode st fields agraph asubj aprop acc fuel
    -- Scalars never appear in expanded form (expansion wraps every value
    -- in a value object); drop defensively rather than error.
    | _ => .ok (st, acc)
termination_by fuel

def nmgItems (st : NmState) (items : List Json) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | []       => .ok (st, acc)
    | hd :: tl =>
      match nmg st hd agraph asubj aprop acc fuel with
      | .error e         => .error e
      | .ok (st1, acc1)  => nmgItems st1 tl agraph asubj aprop acc1 fuel
termination_by fuel

/-- Step 6's body. `fields` arrives with `@type` already relabelled. -/
def nmgNode (st : NmState) (fields : List (String × Json)) (agraph : String)
    (asubj : Option Json) (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    -- Steps 6.1-6.2: determine the id (relabelling blank node
    -- identifiers), removing @id from the element.
    let idRes : Option (NmState × String × List (String × Json)) :=
      match flLookup fields "@id" with
      | some (.string s) =>
        if isBnodeId s then
          let (nid, st1) := issueKeyed st s
          some (st1, nid, flRemove fields "@id")
        else some (st, s, flRemove fields "@id")
      | some _ => none  -- a non-string @id cannot survive expansion
      | none =>
        let (nid, st1) := issueFresh st
        some (st1, nid, fields)
    match idRes with
    | none => .error .invalidIdValue
    | some (st, id, fields) =>
      -- Steps 6.3-6.4: ensure graph[id] exists.
      let st := stEnsureNode st agraph id
      -- Steps 6.5-6.6: link this node from where we came from.
      let (st, acc) :=
        match asubj with
        | some (.object reffields) =>
          -- 6.5: reverse relationship — append the REFERENCING node's
          -- reference to THIS node's active-property array (dedup).
          (match aprop with
           | some p =>
             (stNodeUpdate st agraph id
                (fun n => nodeAppendProp n p (.object reffields) true), acc)
           | none => (st, acc))
        | _ =>
          match aprop with
          | none => (st, acc)
          | some p =>
            let reference := Json.object [("@id", .string id)]
            match acc with
            | some xs => (st, some (xs ++ [reference]))
            | none    => (stAddValue st agraph asubj (some p) reference true, none)
      -- Step 6.7: merge @type into the node.
      let st :=
        match flLookup fields "@type" with
        | some (.array items) => stNodeUpdate st agraph id (fun n => nodeMergeTypes n items)
        | some (.string s)    => stNodeUpdate st agraph id (fun n => nodeMergeTypes n [.string s])
        | _                   => st
      let fields := flRemove fields "@type"
      -- Step 6.8: @index (the conflicting-indexes error surfaces here).
      let idxRes : Option (NmState × List (String × Json)) :=
        match flLookup fields "@index" with
        | some idx =>
          let gr := stGraph st agraph
          (match flLookup gr id with
           | some n =>
             (match nodeSetIndex n idx with
              | none    => none
              | some n1 => some (stPutGraph st agraph (flUpd gr id n1), flRemove fields "@index"))
           | none => some (st, flRemove fields "@index"))
        | none => some (st, fields)
      match idxRes with
      | none => .error .conflictingIndexes
      | some (st, fields) =>
        -- Step 6.9: @reverse — recurse into each reverse value with THIS
        -- node's reference as the active subject (map form triggers 6.5).
        let revRes : Res NmState :=
          match flLookup fields "@reverse" with
          | some (.object rentries) =>
            nmgReverseEntries st (sortMapEntries rentries) agraph id fuel
          | some _ => .error .invalidReversePropertyMap
          | none   => .ok st
        match revRes with
        | .error e => .error e
        | .ok st =>
          let fields := flRemove fields "@reverse"
          -- Step 6.10: @graph — recurse with id as the active graph.
          let graphRes : Res NmState :=
            match flLookup fields "@graph" with
            | some gval =>
              (match nmg st gval id none none none fuel with
               | .ok (st1, _) => .ok st1
               | .error e     => .error e)
            | none => .ok st
          match graphRes with
          | .error e => .error e
          | .ok st =>
            let fields := flRemove fields "@graph"
            -- Step 6.11: @included — recurse in the SAME active graph,
            -- with no active subject or property.
            let inclRes : Res NmState :=
              match flLookup fields "@included" with
              | some ival =>
                (match nmg st ival agraph none none none fuel with
                 | .ok (st1, _) => .ok st1
                 | .error e     => .error e)
              | none => .ok st
            match inclRes with
            | .error e => .error e
            | .ok st =>
              let fields := flRemove fields "@included"
              -- Step 6.12: the remaining properties, in code-point key order.
              match nmgProps st (sortMapEntries fields) agraph id fuel with
              | .error e => .error e
              | .ok st   => .ok (st, acc)
termination_by fuel

def nmgProps (st : NmState) (props : List (String × Json)) (agraph id : String) (fuel : Nat)
    : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match props with
    | []            => .ok st
    | (p, v) :: tl =>
      -- 6.12.1: a property that is itself a blank node identifier gets
      -- relabelled through the same issuer (generalized RDF).
      let (p', st) := if isBnodeId p then issueKeyed st p else (p, st)
      -- 6.12.2: the property entry exists even if no value survives.
      let st := stNodeUpdate st agraph id (fun n => nodeEnsureProp n p')
      -- 6.12.3: recurse with id as the active subject.
      match nmg st v agraph (some (.string id)) (some p') none fuel with
      | .error e     => .error e
      | .ok (st1, _) => nmgProps st1 tl agraph id fuel
termination_by fuel

def nmgReverseEntries (st : NmState) (entries : List (String × Json)) (agraph id : String)
    (fuel : Nat) : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | []              => .ok st
    | (p, vals) :: tl =>
      match nmgReverseValues st (asArray vals) p agraph id fuel with
      | .error e => .error e
      | .ok st1  => nmgReverseEntries st1 tl agraph id fuel
termination_by fuel

def nmgReverseValues (st : NmState) (vals : List Json) (p agraph id : String) (fuel : Nat)
    : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match vals with
    | []      => .ok st
    | v :: tl =>
      match nmg st v agraph (some (.object [("@id", .string id)])) (some p) none fuel with
      | .error e     => .error e
      | .ok (st1, _) => nmgReverseValues st1 tl p agraph id fuel
termination_by fuel

end

/-! ## The Flattening Algorithm — API §6.1 -/

/-- Emit a sorted graph's nodes, dropping any that consist only of `@id`
(the spec's "unless node consists only of `@id`"). -/
def flEmitNodes : List (String × NmNode) → List Json
  | []            => []
  | (_, n) :: tl  => if nodeHasOnlyId n then flEmitNodes tl else .object n :: flEmitNodes tl

def flFilterNamed : List (String × NmGraph) → List (String × NmGraph)
  | []            => []
  | (g, gr) :: tl => if g == "@default" then flFilterNamed tl else (g, gr) :: flFilterNamed tl

/-- Step 3: fold each named graph (ordered by name) under a `@graph`
entry of its name-node in the default graph. -/
def flFoldNamed : NmGraph → List (String × NmGraph) → NmGraph
  | dflt, []                => dflt
  | dflt, (gname, gr) :: tl =>
    let gnodes := flEmitNodes (flSortByKey gr)
    let dflt1 := match flLookup dflt gname with
                 | some n => flUpd dflt gname (n ++ [("@graph", .array gnodes)])
                 | none   => dflt ++ [(gname, [("@id", .string gname),
                                               ("@graph", .array gnodes)])]
    flFoldNamed dflt1 tl

/-- Flatten an EXPANDED document (normally an array of node objects) to
the ordered node array the flatten suite's context-free fixtures
expect. -/
def flattenExpanded (expanded : Json) : Res (List Json) :=
  let fuel := 16 * Json.size expanded + 128
  let st0 : NmState := { graphs := [("@default", [])], idmap := [], ctr := 0 }
  match nmg st0 expanded "@default" none none none fuel with
  | .error e => .error e
  | .ok (st, _) =>
    let dflt := stGraph st "@default"
    let named := flSortByKey (flFilterNamed st.graphs)
    let dflt1 := flFoldNamed dflt named
    .ok (flEmitNodes (flSortByKey dflt1))

/-! ## `JsonLdProcessor.flatten()` -/

/-- Flatten a JSON-LD document.

  * `input`         — the document text (expanded by §5.1 first);
  * `ctxDoc`        — the OPTIONAL compaction context DOCUMENT text (the
    manifest's `context` file; most flatten tests have none and expect
    the bare flattened array);
  * `base`          — the input document's base IRI;
  * `ctxUrl`        — the context document's own URL;
  * `compactArrays` — the API option, consulted only when `ctxDoc` is
    supplied;
  * `processingMode` — `"json-ld-1.0"` selects 1.0 mode. -/
def flattenDocument (loader : Loader) (input : String) (ctxDoc : Option String)
    (base ctxUrl : Option String) (compactArrays : Bool) (processingMode : Option String)
    : Res Json :=
  match expandDocument loader input base none processingMode with
  | .error e => .error e
  | .ok expanded =>
    match flattenExpanded expanded with
    | .error e => .error e
    | .ok flattened =>
      match ctxDoc with
      | none => .ok (.array flattened)
      | some ctxText =>
        -- §6.1 step 6: compact the flattened array, ENSURING the result
        -- keeps @graph (or its alias) at the top level, then re-attach
        -- the original context — the same tail as `compactDocument`,
        -- minus its singleton unwrapping (flatten's output shape is
        -- pinned to @graph).
        match parseJson ctxText with
        | .error _ => .error .invalidLocalContext
        | .ok ctxRoot =>
          let ctxVal := match ctxRoot with
                        | .object cf => (match cmpField cf "@context" with
                                         | some c => c | none => ctxRoot)
                        | _ => ctxRoot
          let mode10 := processingMode == some "json-ld-1.0"
          let acSeed : ActiveContext :=
            { cur := { emptyContextCore with
                       base := base, mode10 := mode10,
                       docUrl := (match ctxUrl with | some u => some u | none => base),
                       originalBase := base },
              prev := [] }
          match contextProcess loader acSeed ctxVal false contextFuel remoteContextFuel [] with
          | .error e => .error e
          | .ok ac =>
            let co : CmpOpts := { arrays := compactArrays, rel := true }
            let farr := Json.array flattened
            let fuel := 16 * Json.size farr + 128
            match compactElem loader ac none farr co fuel with
            | .error e => .error e
            | .ok compacted0 =>
              let garr := match compacted0 with
                          | .array xs => Json.array xs
                          | other     => Json.array [other]
              let gkey := aliasKw ac co "@graph"
              if cmpCtxIsEmpty ctxVal then .ok (.object [(gkey, garr)])
              else .ok (.object [("@context", ctxVal), (gkey, garr)])

end L4Factoidal.JSONLD
