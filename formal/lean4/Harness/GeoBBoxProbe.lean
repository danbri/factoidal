/-
Harness.GeoBBoxProbe — measure the GBI1 candidate filter against a real IBK4
block, and gate its rows against the scan.

    l4block-geo-bbox <block.ibk4> <op> <query WKT> [<op> <query WKT> ...]

`op` is one of `sfEquals`, `sfWithin`, `sfContains`, `sfIntersects`,
`sfTouches`, `sfDisjoint`.

For each pair the probe answers the SPARQL shape

    SELECT ?s ?o WHERE { ?s <P> ?o FILTER(geof:sfWithin(?o, "<query>"^^geo:wktLiteral)) }

twice: once by scanning every row and evaluating the filter, and once by
taking the GBI1 candidate local IDs, reaching their rows through the object
index, and evaluating the SAME filter on those rows. It prints both timings
and whether the two ROW LISTS are equal (anti-pattern 34: rows, not counts).

The object index built here is the OLI2 role — object local ID to row
positions — and its build time is reported separately, because in the shipped
form it is a sidecar the packer writes, not work a query pays for.

The MISS is the reading that matters: a query polygon over empty space must
be answered without touching a row.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.GeoBBoxIndexWire

open L4Factoidal.RDF
open L4Factoidal.Geo
open L4Factoidal.Storage
open L4Factoidal.Storage.GeoBBoxIndex

namespace Harness.GeoBBoxProbe

def opOfName : String → Option GeoOp
  | "sfEquals" => some .equals
  | "sfWithin" => some .within
  | "sfContains" => some .contains
  | "sfIntersects" => some .intersects
  | "sfTouches" => some .touches
  | "sfDisjoint" => some .disjoint
  | _ => none

/-- The filter itself, evaluated exactly as the evaluator evaluates it:
`Geo.wktArg`'s datatype gate, `Geo.sameCrs`, then the topology function. -/
def rowMatches (dict : Array Term) (op : GeoOp) (query : WktValue) (o : Nat) : Bool :=
  match dict[o]? with
  | some t => evalTerm op t query == some true
  | none => false

/-- The scan: every row, in row order. -/
def scanRows (block : IndexedBlockWireV4.QuadBlock) (op : GeoOp) (query : WktValue) :
    Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for h : i in [0 : block.rows.size] do
    let row := block.rows[i]
    if rowMatches block.dict op query row.o then
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
    (idx : Index) (op : GeoOp) (query : WktValue) : Option (Array Nat) :=
  match candidates? idx op query with
  | none => none
  | some ids => Id.run do
      let mut rows : Array Nat := #[]
      for id in ids do
        if rowMatches block.dict op query id then
          if h : id < oli.size then
            rows := rows ++ oli[id]
      pure (some (rows.qsort (fun a b => decide (a < b))))

/-- The GBI1 encoded size of this index, from the layout in
`docs/designissues/2026-09-05-geometry-bounding-box-index.md` section 6. -/
def encodedBytes (idx : Index) : Nat :=
  let crs := idx.crsTable.foldl (fun total c => total + 4 + c.utf8ByteSize) 0
  GeoBBoxIndexWire.prefixBytes + crs +
    GeoBBoxIndexWire.entryBytes * idx.entries.size + 4 * idx.opaqueIds.size + 4

/-- Force a `Nat` to weak head normal form inside `IO`. Lean is lazy: a timing
that does not force its result measures the allocation of a thunk. The two
branches below have DIFFERENT effects, so the `Nat` has to be decided. -/
def forceNat (n : Nat) : IO Unit :=
  if n == 0 then IO.eprint " " else IO.eprint ""

def forceRows (rows : Array Nat) : IO Unit :=
  forceNat (rows.foldl (fun total row => total + row + 1) 0)

/-- Force the whole index: every entry, every opaque ID, every CRS. -/
def forceIndex (idx : Index) : IO Unit :=
  forceNat (idx.entries.foldl
    (fun total e => total + e.id + e.crsIndex + e.box.xmin.scale + e.box.ymax.scale) 0
    + idx.opaqueIds.foldl (fun total i => total + i + 1) 0
    + idx.crsTable.foldl (fun total c => total + c.length) idx.dictCount)

def usage : String :=
  "usage: l4block-geo-bbox <block.ibk4> <op> <query WKT> [<op> <query WKT> ...]"

/-- Read the argument list as `op`, `wkt` pairs. -/
def pairs : List String → Option (List (String × String))
  | [] => some []
  | [_] => none
  | a :: b :: rest => (pairs rest).map (fun t => (a, b) :: t)

def run (args : List String) : IO UInt32 := do
  match args with
  | path :: rest =>
      match pairs rest with
      | none => IO.eprintln usage; pure 2
      | some [] => IO.eprintln usage; pure 2
      | some queries => do
        let bytes ← IO.FS.readBinFile path
        IO.println s!"block {path} bytes {bytes.size}"
        match IndexedBlockWireV4.decode bytes with
        | none => IO.eprintln s!"could not decode {path} as IBK4"; pure 1
        | some block => do
            IO.println s!"rows {block.rows.size} dictionary {block.dict.size}"
            let t0 ← IO.monoMsNow
            let idx := build block.dict
            forceIndex idx
            let t1 ← IO.monoMsNow
            let oli := objectRows block
            forceNat (oli.foldl (fun total rows => total + rows.size + 1) 0)
            let t2 ← IO.monoMsNow
            IO.println s!"gbi build {t1 - t0} ms, boxed {idx.entries.size}, opaque {idx.opaqueIds.size}, crs {idx.crsTable.size}"
            IO.println s!"gbi encoded bytes {encodedBytes idx} ({(encodedBytes idx) * 100 / bytes.size}% of the block)"
            IO.println s!"object index build {t2 - t1} ms"
            -- The sidecar the packer would write, and the reader that reads
            -- it back. Row identity below runs against the DECODED index, so
            -- the measurement is of the artifact and not only of `build`.
            let artifact : GeoBBoxIndexWire.Artifact :=
              { targetIBKSha256 := ByteArray.mk (Array.replicate 32 0), index := idx }
            let roundTrip : Option Index :=
              match GeoBBoxIndexWire.encode? artifact with
              | none => none
              | some wire => (GeoBBoxIndexWire.decode? wire).map (fun a => a.index)
            match roundTrip with
            | none => IO.eprintln "gbi round trip: encode or decode refused the index"; pure 1
            | some decoded => do
              if decoded != idx then
                IO.eprintln "gbi round trip: the decoded index differs from the built one"
                pure 1
              else do
                IO.println "gbi round trip: decoded index equals the built one"
                let mut failures := 0
                let repeats := 5
                for (opName, queryWkt) in queries do
                  match opOfName opName, Wkt.parseLiteral queryWkt with
                  | none, _ => IO.eprintln s!"unknown op {opName}"; failures := failures + 1
                  | _, none => IO.eprintln s!"could not parse {queryWkt}"; failures := failures + 1
                  | some op, some query => do
                      let mut scanBest : Nat := 0
                      let mut indexBest : Nat := 0
                      let mut scanned : Array Nat := #[]
                      let mut served := true
                      for _ in [0 : repeats] do
                        let a0 ← IO.monoNanosNow
                        let rows := scanRows block op query
                        forceRows rows
                        let a1 ← IO.monoNanosNow
                        match indexRows block oli decoded op query with
                        | none => served := false
                        | some got => forceRows got
                        let a2 ← IO.monoNanosNow
                        scanned := rows
                        if scanBest == 0 || a1 - a0 < scanBest then scanBest := a1 - a0
                        if indexBest == 0 || a2 - a1 < indexBest then indexBest := a2 - a1
                      if !served then
                        IO.println s!"{opName} \"{queryWkt}\": scan {scanBest / 1000} us, {scanned.size} rows; index NOT USED, falls back"
                      else
                        match indexRows block oli decoded op query with
                        | none => failures := failures + 1
                        | some rows =>
                            let same := rows == scanned
                            if !same then failures := failures + 1
                            IO.println s!"{opName} \"{queryWkt}\": scan {scanBest / 1000} us, index {indexBest / 1000} us, rows {scanned.size}, identical {same}"
                if failures == 0 then
                  IO.println "row identity: every query identical"
                  pure 0
                else do
                  IO.eprintln s!"row identity: {failures} query/queries differ"
                  pure 1
  | _ => IO.eprintln usage; pure 2

end Harness.GeoBBoxProbe

def main (args : List String) : IO UInt32 := Harness.GeoBBoxProbe.run args
