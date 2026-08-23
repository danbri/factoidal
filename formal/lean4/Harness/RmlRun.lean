/-
Harness/RmlRun — the RML-Core test cases, run end to end.

Each case is a directory holding `mapping.ttl`, its source document,
and `output.nq`. The runner reads the mapping AS RDF (the Lean Turtle
parser), runs it with `RML.Eval`, and compares the result with the
expected N-Quads.

## The comparison is one graph isomorphism over the whole DATASET

A dataset is not a bag of graphs that can be compared one at a time: a
blank node may appear in the default graph and in a named one, and
comparing each graph on its own would let two different datasets
match. Every quad is encoded as a TRIPLE whose predicate carries the
graph name — `urn:x-rml-quad:<graph>:<predicate>`, both parts
percent-encoded so the encoding is injective — and the two encoded
graphs are compared once. Blank nodes then have to line up ACROSS
graphs, which is what dataset isomorphism means.

## Three outcomes

  * **pass / fail** — the datasets matched, or they did not;
  * **comparison gave up** — the isomorphism search hit its budget.
    Counted apart from a failure, because it is not evidence the two
    differ.

## Scope

RML-CORE only. `rml-io`, `rml-cc`, `rml-fnml` and `rml-star` are laid
out differently and need modules this port does not have (function
maps, RDF-star terms, collections and containers, non-file sources).
Pointing the runner at them reports almost everything NOT READ, which
is the truth about them and not a score.

Usage: `lake exe l4rml [test-cases-dir]`
-/
import L4Factoidal.RML.Eval
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.JSON.Parser
import L4Factoidal.CSVW.Dialect

open L4Factoidal.RML
open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Percent-encode everything but the RFC 3986 unreserved set, so the
    encoding of a (graph, predicate) pair is injective. -/
def enc (s : String) : String :=
  let hex := fun (n : Nat) =>
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)
  s.toList.foldl (fun acc c =>
    if ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
       || c == '-' || c == '.' || c == '_' || c == '~'
    then acc ++ String.mk [c]
    else acc ++ String.ofList ((String.mk [c]).toUTF8.toList.flatMap (fun b =>
           ['%', hex (b.toNat / 16), hex (b.toNat % 16)]))) ""

def quadPred (g : Option String) (p : String) : Option WfIri :=
  let raw := "urn:x-rml-quad:" ++ (match g with | none => "" | some x => enc x) ++ ":" ++ enc p
  if h : isIri raw then some ⟨raw, h⟩ else none

/-- A dataset as ONE graph, with the graph name folded into each
    predicate. -/
def flattenDataset (ds : Dataset) : Graph :=
  let dflt := ds.default.filterMap (fun t =>
    (quadPred none t.p.val).map (fun p => ({ s := t.s, p := p, o := t.o } : Triple)))
  let named := ds.named.flatMap (fun ng =>
    let n := match ng.name with
      | .iri i   => i.val
      | .bnode b => "_:" ++ b
    ng.graph.filterMap (fun t =>
      (quadPred (some n) t.p.val).map (fun p => ({ s := t.s, p := p, o := t.o } : Triple))))
  dflt ++ named

def flattenQuads (qs : List QuadOut) : Graph :=
  qs.filterMap (fun q =>
    let n := q.g.map (fun t => match t with
      | .iri i   => i.val
      | .bnode b => "_:" ++ b
      | _        => "")
    (quadPred n q.p.val).map (fun p => ({ s := q.s, p := p, o := q.o } : Triple)))

/-- One row of the corpus's own `metadata.csv`: the base IRI a case
    runs under, and whether it is a NEGATIVE case.

    A negative case has no `output.nq`, and reading that absence as
    "the file is missing" would report a deliberate part of the suite
    as a broken fixture. -/
structure CaseMeta where
  id      : String
  baseIri : String
  isError : Bool
deriving Inhabited

def readMetadata (src : String) : List CaseMeta :=
  let t := L4Factoidal.CSVW.read (({} : L4Factoidal.CSVW.Dialect).resolve) src
  let hdr := (t.header.head?.map (·.cells)).getD []
  let idx := fun (n : String) => hdr.findIdx? (· == n)
  match idx "ID", idx "base_iri", idx "error" with
  | some i, some b, some e =>
      t.rows.map (fun r =>
        { id := (r.cells.getD i ""), baseIri := (r.cells.getD b ""),
          isError := (r.cells.getD e "") == "true" })
  | _, _, _ => []

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  gaveUp  : Nat := 0
  notRead : Nat := 0
  negative : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/rml-modules/rml-core/test-cases"
  let dump := (args.find? (fun a => a.startsWith "--dump=")).map
    (fun a => String.ofList (a.toList.drop 7))
  if !(← System.FilePath.isDir dir) then
    IO.println s!"rml runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let metaPath := dir ++ "/metadata.csv"
  let metaRows : List CaseMeta ← if ← System.FilePath.pathExists metaPath
             then do let src ← IO.FS.readFile metaPath; pure (readMetadata src)
             else pure []
  let mut t : Tally := {}
  let mut names : List String := []
  for entry in (← System.FilePath.readDir dir) do
    if ← System.FilePath.isDir entry.path then
      names := names ++ [entry.fileName]
  for name in names.mergeSort (· ≤ ·) do
    let caseDir := dir ++ "/" ++ name
    let mp := caseDir ++ "/mapping.ttl"
    let op := caseDir ++ "/output.nq"
    let m? := metaRows.find? (fun c => c.id == name)
    if !(← System.FilePath.pathExists mp) then pure ()
    else if (m?.map (·.isError)).getD false then
      -- A NEGATIVE case: the corpus's own metadata says the mapping
      -- is invalid, and there is no expected output because the
      -- correct outcome is an ERROR. This slice has no mapping
      -- validator, so it does not attempt them — counted and named
      -- rather than folded into either column.
      t := { t with negative := t.negative + 1 }
    else if !(← System.FilePath.pathExists op) then
      t := { t with notRead := t.notRead + 1 }
      IO.println s!"no expected output and the metadata does not call it an error: {name}"
    else
      let msrc ← IO.FS.readFile mp
      let osrc ← IO.FS.readFile op
      match parseTurtle msrc none, parseNQuads osrc with
      | .error e, _ =>
          t := { t with notRead := t.notRead + 1 }
          IO.println s!"NOT READ {name}: the mapping did not parse ({e.msg})"
      | _, .error _ =>
          t := { t with notRead := t.notRead + 1 }
          IO.println (s!"NOT READ {name}: the expected N-Quads did not parse. " ++
            "Check the fixture before the parser: RMLTC0027b's output.nq writes " ++
            "<http://example.com/Person/Emily Smith>, and an IRIREF may not contain a space.")
      | .ok mg, .ok want =>
          -- Every JSON document in the case directory, by file name:
          -- `rml:path` is relative to the mapping, and reading them
          -- all keeps the evaluator a pure function of its inputs.
          let mut docs : List (String × Json) := []
          for e in (← System.FilePath.readDir caseDir) do
            if e.fileName.endsWith ".json" then
              let src ← IO.FS.readFile e.path.toString
              match parseJson? src with
              | none   => pure ()
              | some j => docs := docs ++ [(e.fileName, j)]
          let docFor : String → Option Json := fun p =>
            let base := ((p.splitOn "/").getLast?).getD p
            (docs.find? (fun (n, _) => n == base)).map (·.2)
          let m := mappingOf mg
          let defaultBase := (m?.map (·.baseIri)).filter (fun b => b != "")
          let got := flattenQuads (evalMapping defaultBase m docFor)
          let wantG := flattenDataset want
          if dump == some name then
            IO.println s!"--- {name} PRODUCED {got.length} ---"
            for l in ((got.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
              IO.println l.trim
            IO.println s!"--- {name} EXPECTED {wantG.length} ---"
            for l in ((wantG.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
              IO.println l.trim
          match Graph.isomorphicOutcome got wantG with
          | .equal          => t := { t with pass := t.pass + 1 }
          | .budgetExceeded =>
              t := { t with gaveUp := t.gaveUp + 1 }
              IO.println s!"GAVE UP {name}: the isomorphism search hit its budget"
          | .notEqual =>
              t := { t with fail := t.fail + 1 }
              IO.println s!"FAIL {name}: produced {got.length}, expected {wantG.length}"
  IO.println ""
  IO.println s!"{dir}: {t.pass} pass, {t.fail} fail, {t.gaveUp} comparison-gave-up (out of {t.pass + t.fail + t.gaveUp} compared)"
  IO.println s!"NOT READ: {t.notRead} cases"
  IO.println s!"NEGATIVE (the mapping must be rejected): {t.negative} cases, not attempted —"
  IO.println "  this slice has no mapping validator, so it makes no claim about them"
  IO.println ""
  IO.println "Comparison is DATASET isomorphism: every quad is encoded as a"
  IO.println "triple carrying its graph name, so blank nodes must line up"
  IO.println "across graphs. A comparison that gives up is counted apart from"
  IO.println "a failure -- it is not evidence the two datasets differ."
  return 0
