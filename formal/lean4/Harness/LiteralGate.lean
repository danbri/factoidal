/-
Harness.LiteralGate — the row-identity gate for the LGI1 literal search
index, driven through the SHIPPED query path.

    l4block-literal-gate <collection-root-or-generation-dir> <predicate-iri> <needle> [...]

For each needle this answers

    SELECT ?s ?o WHERE { ?s <P> ?o FILTER(CONTAINS(LCASE(STR(?o)), "needle")) }

TWICE, through `L4Wasm.Ops.storeHandleQuery` both times:

* through a handle opened WITH the LGI1 sidecars, which takes the index path
  (`LiteralIndexPlan.plan?` admits the shape, so the handle materialises the
  candidate rows and re-evaluates the same query text on them), and
* through a handle opened WITHOUT them, which scans.

The two answer envelopes are compared BYTE FOR BYTE. That compares the rows
themselves and their order, not their count (anti-pattern 34): an index that
returned a superset whose filter was not re-applied would add rows, and an
index that dropped a match would remove one. Either shows here.

`Harness/LiteralGramProbe.lean` measures the same mechanism against a block
in isolation. This is the gate through the operation a host actually calls.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Wasm.Ops.StoreHandles

namespace Harness.LiteralGate

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.Storage.ShardManifest
open L4Wasm.Ops

/-- The generation a collection root points at, or the directory itself when
it holds a manifest. -/
def resolveGeneration (root : System.FilePath) : IO System.FilePath := do
  if ← (root / "manifest.sbm2").pathExists then pure root
  else do
    let current := root / "CURRENT"
    if ← current.pathExists then do
      let name := (← IO.FS.readFile current).trim
      pure (root / name)
    else throw (IO.userError s!"no manifest.sbm2 and no CURRENT under {root}")

/-- The plan envelope's string members, decoded once. -/
def stringsAt (json : Json) (field : String) : List String :=
  match json with
  | .object members =>
      match members.find? (fun m => m.1 == field) with
      | some (_, .array items) =>
          items.filterMap fun item => match item with | .string s => some s | _ => none
      | _ => []
  | _ => []

def envelopeOf (text : String) : IO Json :=
  match parseJson text with
  | .error e => throw (IO.userError s!"could not parse an engine envelope: {e}")
  | .ok json => do
      match json with
      | .object members =>
          match members.find? (fun m => m.1 == "ok") with
          | some (_, .bool false) => throw (IO.userError s!"engine refused: {text}")
          | _ => pure json
      | _ => pure json

/-- How many result rows an answer envelope carries. Reported beside the
identity verdict; the verdict itself compares the whole envelope. -/
def rowCount (text : String) : Option Nat :=
  match parseJson text with
  | .error _ => none
  | .ok (.object members) => do
      let (_, srj) ← members.find? (fun m => m.1 == "srj")
      let inner ← match srj with
        | .string raw => (parseJson raw).toOption
        | other => some other
      match inner with
      | .object outer => do
          let (_, results) ← outer.find? (fun m => m.1 == "results")
          match results with
          | .object fields => do
              let (_, bindings) ← fields.find? (fun m => m.1 == "bindings")
              match bindings with
              | .array rows => some rows.length
              | _ => none
          | _ => none
      | _ => none
  | .ok _ => none

/-- Read the named artifacts and lay them out back to back in one region,
with the `{"key","offset","len"}` descriptor document the engine reads. This
is the same shape `npm/factoidal/bin/store.mjs` builds. -/
def regionOf (directory : System.FilePath) (keys : List String) :
    IO (ByteArray × String) := do
  let mut blob : ByteArray := ByteArray.empty
  let mut descriptors : List Json := []
  for key in keys do
    let bytes ← IO.FS.readBinFile (directory / key)
    descriptors := descriptors ++
      [Json.object [("key", .string key), ("offset", .number (toString blob.size)),
                    ("len", .number (toString bytes.size))]]
    blob := blob ++ bytes
  pure (blob, (Json.array descriptors).toString)

/-- The two pattern shapes a generation can answer this in. A store whose
quads are all in NAMED graphs answers nothing to a default-graph pattern, and
the reverse, so the gate tries the `GRAPH ?g` form first and falls back to the
bare form when the plan selects no block. `LiteralIndexPlan` admits both. -/
inductive Shape where
  | named
  | bare

def queryFor (shape : Shape) (predicate needle : String) : String :=
  match shape with
  | .named =>
      s!"SELECT ?g ?s ?o WHERE \{ GRAPH ?g \{ ?s <{predicate}> ?o FILTER(CONTAINS(LCASE(STR(?o)), \"{needle}\")) } } ORDER BY ?g ?s ?o"
  | .bare =>
      s!"SELECT ?s ?o WHERE \{ ?s <{predicate}> ?o FILTER(CONTAINS(LCASE(STR(?o)), \"{needle}\")) } ORDER BY ?s ?o"

/-- Best of `repeats`, in microseconds. The measurement machine is shared, so
one reading measures the load as much as the code. -/
def bestOf (repeats : Nat) (act : IO String) : IO (Nat × String) := do
  let mut best : Nat := 0
  let mut answer := ""
  for _ in [0 : repeats] do
    let t0 ← IO.monoNanosNow
    let got ← act
    -- Force the answer: a timing that does not touch its result measures a thunk.
    if got.length == 0 then IO.eprint "" else IO.eprint ""
    let t1 ← IO.monoNanosNow
    answer := got
    if best == 0 || t1 - t0 < best then best := t1 - t0
  pure (best / 1000, answer)

def usage : String :=
  "usage: l4block-literal-gate COLLECTION-ROOT PREDICATE-IRI NEEDLE [NEEDLE ...]"

def run (args : List String) : IO UInt32 := do
  match args with
  | root :: predicate :: needles =>
      if needles.isEmpty then do IO.eprintln usage; pure 2 else do
      let directory ← resolveGeneration (System.FilePath.mk root)
      let manifestBytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
      let manifestHex := hexOfBytes manifestBytes
      let probe := needles.headD ""
      let namedPlan ← envelopeOf (storeQueryPlan manifestHex (queryFor .named predicate probe))
      let (shape, plan) ←
        if (stringsAt namedPlan "keys").isEmpty then do
          let barePlan ← envelopeOf (storeQueryPlan manifestHex (queryFor .bare predicate probe))
          pure (Shape.bare, barePlan)
        else pure (Shape.named, namedPlan)
      let blockKeys := stringsAt plan "keys"
      let sidecarKeys := stringsAt plan "sidecarKeys"
      let shapeName := match shape with | .named => "GRAPH ?g" | .bare => "default graph"
      IO.println s!"generation {directory} shape {shapeName} blocks {blockKeys.length} sidecars {sidecarKeys.length}"
      if blockKeys.isEmpty then do
        IO.eprintln "l4block-literal-gate: the plan selects no block for that predicate"
        pure 1
      else do
        let (withBlob, withJson) ← regionOf directory (blockKeys ++ sidecarKeys)
        let (scanBlob, scanJson) ← regionOf directory blockKeys
        let indexHandle ← envelopeOf (← storeOpen manifestHex withJson withBlob)
        let scanHandle ← envelopeOf (← storeOpen manifestHex scanJson scanBlob)
        let handleId (json : Json) : IO String :=
          match json with
          | .object members =>
              match members.find? (fun m => m.1 == "handle") with
              | some (_, .string h) => pure h
              | _ => throw (IO.userError "storeOpen answered no handle")
          | _ => throw (IO.userError "storeOpen answered no handle")
        let indexId ← handleId indexHandle
        let scanId ← handleId scanHandle
        IO.println s!"handles index={indexId} scan={scanId} bytes-with-sidecars {withBlob.size} bytes-without {scanBlob.size}"
        let mut failures := 0
        for needle in needles do
          let sparql := queryFor shape predicate needle
          let (scanUs, scanAnswer) ← bestOf 5 (storeHandleQuery scanId sparql)
          let (indexUs, indexAnswer) ← bestOf 5 (storeHandleQuery indexId sparql)
          let identical := scanAnswer == indexAnswer
          if !identical then failures := failures + 1
          let rows := (rowCount scanAnswer).map toString |>.getD "?"
          IO.println s!"needle \"{needle}\": rows {rows}, scan {scanUs} us, index {indexUs} us, identical {identical}"
        let _ ← storeHandleClose indexId
        let _ ← storeHandleClose scanId
        if failures == 0 then do
          IO.println s!"row identity: {needles.length} pass, 0 fail (out of {needles.length})"
          pure 0
        else do
          IO.eprintln s!"row identity: {needles.length - failures} pass, {failures} fail (out of {needles.length})"
          pure 1
  | _ => do IO.eprintln usage; pure 2

end Harness.LiteralGate

def main (args : List String) : IO UInt32 := Harness.LiteralGate.run args
