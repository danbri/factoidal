/-
Harness.LiteralGramProbe — measure the LGI1 candidate filter against a real
IBK4 block, and gate its rows against the scan.

    l4block-literal-gram <block.ibk4> <needle> [<needle> ...]

For each needle the probe answers the SPARQL shape

    SELECT ?s ?o WHERE { ?s <P> ?o FILTER(CONTAINS(LCASE(STR(?o)), "needle")) }

twice: once by scanning every row and evaluating the filter, and once by
taking the LGI candidate local IDs, reaching their rows through the object
index, and evaluating the SAME filter on those rows. It prints both timings
and whether the two ROW LISTS are equal (anti-pattern 34: rows, not counts).

The object index built here is the OLI2 role — object local ID to row
positions — and its build time is reported separately, because in the shipped
form it is a sidecar the packer writes, not work a query pays for.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.LiteralGramIndex

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open L4Factoidal.Storage.LiteralGramIndex

namespace Harness.LiteralGramProbe

/-- The value the filter tests: `LCASE(STR(?o))` of a literal, as characters.
A non-literal object has no `STR` a `CONTAINS` can match here. -/
def objectFolded (dict : Array Term) (o : Nat) : List Char :=
  match dict[o]? with
  | some t => foldedOfTerm t
  | none => []

/-- The filter itself, evaluated exactly as `Expr` evaluates it. -/
def rowMatches (dict : Array Term) (needle : List Char) (o : Nat) : Bool :=
  listContainsSublist needle (objectFolded dict o)

/-- The scan: every row, in row order. -/
def scanRows (block : IndexedBlockWireV4.QuadBlock) (needle : List Char) :
    Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for h : i in [0 : block.rows.size] do
    let row := block.rows[i]
    if rowMatches block.dict needle row.o then
      out := out.push i
  pure out

/-- Object local ID to the row positions carrying it. This is the OLI2 role. -/
def objectRows (block : IndexedBlockWireV4.QuadBlock) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.replicate block.dict.size #[]
  for h : i in [0 : block.rows.size] do
    let row := block.rows[i]
    if row.o < out.size then
      out := out.set! row.o ((out[row.o]!).push i)
  pure out

/-- The index path: candidates, then their rows, then the SAME filter. -/
def indexRows (block : IndexedBlockWireV4.QuadBlock) (oli : Array (Array Nat))
    (idx : Index) (needleStr : String) (needle : List Char) : Option (Array Nat) :=
  match candidates? idx needleStr with
  | none => none
  | some ids => Id.run do
      let mut rows : Array Nat := #[]
      for id in ids do
        if rowMatches block.dict needle id then
          if h : id < oli.size then
            rows := rows ++ oli[id]
      pure (some (rows.qsort (fun a b => decide (a < b))))

def postingCount (idx : Index) : Nat :=
  idx.postings.foldl (fun total posting => total + posting.ids.length) 0

/-- The LGI1 encoded size of this index, computed from the layout in
`docs/designissues/2026-09-04-literal-token-index.md` section 3. -/
def encodedBytes (idx : Index) : Nat :=
  let directory := idx.postings.foldl
    (fun total posting => total + 4 + (String.mk posting.gram).utf8ByteSize + 12) 0
  61 + directory + 4 * postingCount idx + 4

/-- Force a `Nat` to weak head normal form inside `IO`. Lean is lazy: a timing
that does not force its result measures the allocation of a thunk. The first
run of this probe reported 0 ms for every step for exactly that reason, and
the second still did, because an `if` whose two branches are the same value is
removed with its scrutinee. The branches below have DIFFERENT effects, so the
`Nat` has to be decided. -/
def forceNat (n : Nat) : IO Unit :=
  if n == 0 then IO.eprint " " else IO.eprint ""

/-- Force every element of a row list. -/
def forceRows (rows : Array Nat) : IO Unit :=
  forceNat (rows.foldl (fun total row => total + row + 1) 0)

/-- Force the whole index: every gram and every posting. -/
def forceIndex (idx : Index) : IO Unit :=
  forceNat (idx.postings.foldl
    (fun total posting => total + posting.gram.length + posting.ids.length) idx.literalCount)

def usage : String :=
  "usage: l4block-literal-gram <block.ibk4> <needle> [<needle> ...]"

def run (args : List String) : IO UInt32 := do
  match args with
  | path :: needles =>
      if needles.isEmpty then
        IO.eprintln usage
        pure 2
      else do
        let bytes ← IO.FS.readBinFile path
        IO.println s!"block {path} bytes {bytes.size}"
        match IndexedBlockWireV4.decode bytes with
        | none => IO.eprintln s!"could not decode {path} as IBK4"; pure 1
        | some block => do
            IO.println s!"rows {block.rows.size} dictionary {block.dict.size}"
            let t0 ← IO.monoMsNow
            let idx := build block.dict
            forceIndex idx
            let postings := postingCount idx
            forceNat postings
            let t1 ← IO.monoMsNow
            let oli := objectRows block
            forceNat (oli.foldl (fun total rows => total + rows.size + 1) 0)
            let t2 ← IO.monoMsNow
            IO.println s!"lgi build {t1 - t0} ms, grams {idx.postings.size}, postings {postings}, literals {idx.literalCount}"
            IO.println s!"lgi encoded bytes {encodedBytes idx} ({(encodedBytes idx) * 100 / bytes.size}% of the block)"
            IO.println s!"object index build {t2 - t1} ms"
            let mut failures := 0
            /- Best of five. The measurement machine is shared, so a single
               reading measures the load as much as the code. -/
            let repeats := 5
            for needle in needles do
              let folded := foldString needle
              let mut scanBest : Nat := 0
              let mut indexBest : Nat := 0
              let mut scanned : Array Nat := #[]
              let mut served := true
              for _ in [0 : repeats] do
                let a0 ← IO.monoNanosNow
                let rows := scanRows block folded
                forceRows rows
                let a1 ← IO.monoNanosNow
                let viaIndex := indexRows block oli idx needle folded
                match viaIndex with
                | none => served := false
                | some got => forceRows got
                let a2 ← IO.monoNanosNow
                scanned := rows
                if scanBest == 0 || a1 - a0 < scanBest then scanBest := a1 - a0
                if indexBest == 0 || a2 - a1 < indexBest then indexBest := a2 - a1
              if !served then
                IO.println s!"needle \"{needle}\": scan {scanBest / 1000} us, {scanned.size} rows; index NOT USED (needle shorter than {gramLength}), falls back"
              else
                match indexRows block oli idx needle folded with
                | none => failures := failures + 1
                | some rows =>
                    let same := rows == scanned
                    if !same then failures := failures + 1
                    IO.println s!"needle \"{needle}\": scan {scanBest / 1000} us, index {indexBest / 1000} us, rows {scanned.size}, identical {same}"
            if failures == 0 then
              IO.println "row identity: every needle identical"
              pure 0
            else do
              IO.eprintln s!"row identity: {failures} needle(s) differ"
              pure 1
  | _ => IO.eprintln usage; pure 2

end Harness.LiteralGramProbe

def main (args : List String) : IO UInt32 := Harness.LiteralGramProbe.run args
