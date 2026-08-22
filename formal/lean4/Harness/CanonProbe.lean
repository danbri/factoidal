/-
Harness/CanonProbe — run `L4Factoidal.RDF.Canonical` against the real
W3C `rdf-canon` corpus vendored at
`third_party/testing/rdf-canon/tests/rdfc10/`.

This is a HARNESS, not part of the verified library: it does file I/O
and prints. It reads the corpus the same way the F* tree's runner does
— real `.nq` files off disk, byte-compared against the suite's own
expected output — never synthetic inputs "inspired by" the suite.

Pair discovery needs no manifest: every `testNNN-in.nq` with a
matching `testNNN-rdfc10.nq` is an RDFC10EvalTest. The manifest IS
consulted for one thing only, because the file layout does not encode
it: which entries declare `rdfc:hashAlgorithm "SHA384"` instead of the
§4.4 default SHA-256. Entries with no declaration run under SHA-256.

Usage: `lake exe l4rdfc-probe [path-to-rdfc10-dir] [path-to-manifest]`
Defaults are the vendored corpus, relative to the repository root.
-/
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.NQuads

open L4Factoidal.RDF
open L4Factoidal.RDF.Canonical
open L4Factoidal.Syntax
open L4Factoidal.Crypto

namespace CanonProbe

/-- Trim trailing newlines so a missing/extra final EOL is not a
failure (the only normalisation applied; everything else is a
byte-for-byte comparison). -/
def trimTrailingNewlines (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

/-- Test ids the manifest declares as SHA-384. Scans line by line:
a line starting with `:test` opens a block; `rdfc:hashAlgorithm
"SHA384"` inside that block records the block's base id. -/
def sha384Ids (manifest : String) : List String :=
  let step : (String × List String) → String → (String × List String) :=
    fun (cur, acc) line =>
      let l := line.trim
      if l.startsWith ":test" then
        -- `:test075c a rdfc:RDFC10EvalTest;` → base id `test075`
        ("test" ++ String.ofList ((l.toList.drop 5).takeWhile Char.isDigit), acc)
      else if l.startsWith "rdfc:hashAlgorithm" && (l.splitOn "SHA384").length > 1 then
        (cur, cur :: acc)
      else (cur, acc)
  ((manifest.splitOn "\n").foldl step ("", [])).2

/-- Budget for the negative (excessive-calls) test. Far below
`defaultHndqBudget` so a pathological input aborts promptly instead of
burning a million bounded-but-expensive Hash-N-Degree-Quads calls
first. -/
def negativeBudget : Nat := 1000

/-- Collect the double-quoted tokens of a string, in order. The
suite's `*-rdfc10map.json` files are flat `{"orig": "c14nN", …}`
objects whose keys and values are blank-node labels, so pairing the
quoted tokens reconstructs the map without a JSON parser. -/
def oddIndexed : List String → List String
  | _ :: b :: rest => b :: oddIndexed rest
  | _              => []

def quotedTokens (s : String) : List String := oddIndexed (s.splitOn "\"")

def pairUp : List String → List (String × String)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _              => []

/-- An RDFC10MapTest: the issued identifier map must equal the
suite's, as a set of pairs. -/
def runMapTest (dir : System.FilePath) (id : String) (alg : HashAlgorithm) :
    IO (Bool × String) := do
  let inTxt ← IO.FS.readFile (dir / (id ++ "-in.nq"))
  let expTxt ← IO.FS.readFile (dir / (id ++ "-rdfc10map.json"))
  let expected := pairUp (quotedTokens expTxt)
  match parseNQuads inTxt .rdf11 with
  | .error e => return (false, s!"{id} (map): parse error at offset {e.pos}: {e.msg}")
  | .ok ds =>
      let got := (canonicalize ds alg).issued
      if got.length == expected.length && expected.all (fun p => got.contains p) then
        return (true, "")
      else
        return (false, s!"{id} (map): issued map differs (got {got.length} entries, expected {expected.length})")

/-- One evaluation: parse, canonicalise, byte-compare. -/
def runOne (dir : System.FilePath) (id : String) (alg : HashAlgorithm) :
    IO (Bool × String) := do
  let inTxt ← IO.FS.readFile (dir / (id ++ "-in.nq"))
  let expected ← IO.FS.readFile (dir / (id ++ "-rdfc10.nq"))
  match parseNQuads inTxt .rdf11 with
  | .error e => return (false, s!"{id}: parse error at offset {e.pos}: {e.msg}")
  | .ok ds =>
      let got := ds.canonicalNQuads alg
      if trimTrailingNewlines got == trimTrailingNewlines expected then
        return (true, "")
      else
        return (false, s!"{id}: output differs")

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath :=
    match args with
    | d :: _ => d
    | []     => "../../third_party/testing/rdf-canon/tests/rdfc10"
  let manifestPath : System.FilePath :=
    match args with
    | _ :: m :: _ => m
    | _           => dir / ".." / "manifest.ttl"
  if !(← dir.pathExists) then
    IO.eprintln s!"rdfc10 probe: corpus directory not found: {dir}"
    IO.eprintln "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let manifest ← if ← manifestPath.pathExists then IO.FS.readFile manifestPath
                 else pure ""
  let sha384 := sha384Ids manifest
  if manifest.isEmpty then
    IO.println "rdfc10 probe: manifest not found — every pair runs under SHA-256"
  let entries ← dir.readDir
  let ids := (entries.toList.map (fun e => e.fileName)).filterMap (fun n =>
    if n.endsWith "-in.nq" then
      some (String.ofList (n.toList.take (n.length - "-in.nq".length)))
    else none)
  let ids := ids.toArray.qsort (fun a b => decide (a < b)) |>.toList
  let mut n256 := 0; let mut d256 := 0
  let mut n384 := 0; let mut d384 := 0
  let mut skipped : List String := []
  let mut failures : List String := []
  let mut negPass := 0; let mut negTotal := 0
  let mut nMap := 0; let mut dMap := 0
  for id in ids do
    if !(← (dir / (id ++ "-rdfc10.nq")).pathExists) then
      -- No expected output file: the suite's negative eval test. It
      -- passes when the implementation reports an error for excessive
      -- calls to Hash N-Degree Quads (RDFC-1.0 §4.4).
      negTotal := negTotal + 1
      let inTxt ← IO.FS.readFile (dir / (id ++ "-in.nq"))
      match parseNQuads inTxt .rdf11 with
      | .error _ => skipped := id :: skipped
      | .ok ds =>
          if canonicalizeExceedsBudget .sha256 negativeBudget ds then
            negPass := negPass + 1
          else
            failures := s!"{id}: expected an excessive-calls abort, got a result" :: failures
    else
      let alg := if sha384.contains id then HashAlgorithm.sha384 else HashAlgorithm.sha256
      let (ok, msg) ← runOne dir id alg
      if alg == .sha384 then
        d384 := d384 + 1
        if ok then n384 := n384 + 1 else failures := msg :: failures
      else
        d256 := d256 + 1
        if ok then n256 := n256 + 1 else failures := msg :: failures
      if ← (dir / (id ++ "-rdfc10map.json")).pathExists then
        dMap := dMap + 1
        let (okM, msgM) ← runMapTest dir id alg
        if okM then nMap := nMap + 1 else failures := msgM :: failures
  IO.println s!"rdfc10 eval: {n256} of {d256}"
  IO.println s!"sha384 eval: {n384} of {d384}"
  IO.println s!"rdfc10 map eval: {nMap} of {dMap}"
  IO.println s!"negative eval (excessive-calls abort): {negPass} of {negTotal}"
  for f in failures.reverse do IO.println s!"  FAIL {f}"
  for s in skipped.reverse do
    IO.println s!"  no expected output (not an eval test): {s}"
  return (if failures.isEmpty then 0 else 1)

end CanonProbe

def main (args : List String) : IO UInt32 := CanonProbe.main args
