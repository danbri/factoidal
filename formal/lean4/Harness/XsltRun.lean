/-
Harness/XsltRun — an XSLT 1.0 conformance runner over the vendored
subset of the W3C `xslt30-test` suite.

It reads `third_party/testing/xslt/manifest.json`, parses each case's
stylesheet and source document with the project's own XML parser,
runs `XSLT.Transform.transform`, and compares the serialised result
tree against the suite's own `assert-xml` expected file.

## What the score means

Four outcomes, not two:

  * **pass** — the produced text equals the expected text exactly,
    after stripping each side's XML declaration;
  * **pass-loose** — they differ only by insignificant whitespace.
    The same collapse is applied to BOTH sides, so it can never turn
    a structural difference into a pass; it separates a real defect
    from a serialisation-only one;
  * **fail** — a real difference. This is the number that means
    something is broken;
  * **refused** — the engine declined: an XSLT element it does not
    implement, a match pattern it could not parse, or an XPath
    expression it could not evaluate. The reason is printed. A
    refusal is NEVER scored as a pass and never as a fail, because
    an engine that guesses produces a document of the right shape
    with the wrong content, and that reads as a near miss.

Usage: `lake exe l4xslt [tests-dir]`
-/
import L4Factoidal.XSLT.Transform
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.XML
open L4Factoidal.XSLT

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- XML §2.11 line-end normalisation: a CRLF pair and a lone CR both
    become a single LF.

    This is NOT a loosening of the comparison. The vendored expected
    files carry CRLF line endings, and every XML processor — this
    project's parser included — normalises them on input, so the
    source document's text nodes hold LF. Comparing the engine's
    output against the RAW bytes of the expected file therefore
    differed on every line of every document that has one, and 49 of
    the 84 decided cases landed in the whitespace bucket for that one
    reason. Applying §2.11 to the expected text is reading it as XML
    rather than as bytes. -/
def normalizeEol (s : String) : String :=
  String.ofList (s.toList.foldr (fun c acc =>
    match c, acc with
    | '\r', '\n' :: r => '\n' :: r
    | '\r', r         => '\n' :: r
    | _, r            => c :: acc) [])

/-- Drop a leading `<?xml … ?>` declaration and any whitespace around
    the document. The expected files carry one and the engine does not
    emit one; comparing them with it in place would fail every case
    for a reason that is not about the transform. -/
def stripDecl (s : String) : String :=
  let t := s.trim
  if t.startsWith "<?xml" then
    match (t.toList.drop 5) |>.findIdx? (· == '>') with
    | some i => String.ofList (t.toList.drop (5 + i + 1)) |>.trim
    | none   => t
  else t

private def isWsC (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Collapse every run of whitespace to one space and drop whitespace
    that sits between two tags. Applied IDENTICALLY to both sides. -/
def looseForm (s : String) : String :=
  let collapsed := (s.toList.foldr (fun c acc =>
    if isWsC c then
      match acc with
      | ' ' :: _ => acc
      | _        => ' ' :: acc
    else c :: acc) [])
  -- `> <` between tags carries no information in these documents.
  let dropped := collapsed.foldr (fun c acc =>
    match c, acc with
    | '>', ' ' :: '<' :: r => '>' :: '<' :: r
    | _, _                 => c :: acc) []
  (String.ofList dropped).trim

structure Tally where
  pass    : Nat := 0
  loose   : Nat := 0
  fail    : Nat := 0
  refused : Nat := 0
  errors  : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/xslt"
  let manifestPath := dir ++ "/manifest.json"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"xslt runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  -- `XSLT_DUMP=<dir>` writes the produced and expected text of every
  -- non-exact case to `<dir>/<name>.got` and `.want`. A diff that
  -- spans lines cannot be read out of a one-line report, and reading
  -- it wrongly is how a whitespace-only mismatch gets filed as a
  -- structural one.
  let dump ← IO.getEnv "XSLT_DUMP"
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "xslt runner: manifest did not parse"
      return 1
  | some (.array cases) =>
      let mut t : Tally := {}
      let mut reasons : List String := []
      for c in cases do
        let name := (str? "name" c).getD "<unnamed>"
        let cat := (str? "category" c).getD "?"
        match str? "stylesheet" c, str? "source" c, str? "expected" c with
        | some sp, some src, some exp => do
            let styleSrc ← IO.FS.readFile (dir ++ "/" ++ sp)
            let srcSrc ← IO.FS.readFile (dir ++ "/" ++ src)
            let expSrc ← IO.FS.readFile (dir ++ "/" ++ exp)
            match parseXML styleSrc, parseXML srcSrc with
            | .error e, _ =>
                IO.println s!"ERROR {cat}/{name}: the stylesheet is not well-formed XML: {e.message} at {e.position}"
                t := { t with errors := t.errors + 1 }
            | _, .error e =>
                IO.println s!"ERROR {cat}/{name}: the source is not well-formed XML: {e.message} at {e.position}"
                t := { t with errors := t.errors + 1 }
            | .ok style, .ok source =>
                match transform style source with
                | .refused why =>
                    t := { t with refused := t.refused + 1 }
                    reasons := reasons ++ [why]
                    IO.println s!"REFUSED {cat}/{name}: {why}"
                | .produced got =>
                    let a := stripDecl got
                    let b := stripDecl (normalizeEol expSrc)
                    if a != b then
                      match dump with
                      | some dd => do
                          IO.FS.createDirAll dd
                          IO.FS.writeFile (dd ++ "/" ++ cat ++ "__" ++ name ++ ".got") a
                          IO.FS.writeFile (dd ++ "/" ++ cat ++ "__" ++ name ++ ".want") b
                      | none => pure ()
                    else pure ()
                    if a == b then t := { t with pass := t.pass + 1 }
                    else if looseForm a == looseForm b then
                      t := { t with loose := t.loose + 1 }
                      IO.println s!"LOOSE {cat}/{name}"
                    else
                      t := { t with fail := t.fail + 1 }
                      IO.println s!"FAIL {cat}/{name}"
                      IO.println s!"    produced: {a}"
                      IO.println s!"    expected: {b}"
        | _, _, _ =>
            IO.println s!"ERROR {name}: the manifest entry is incomplete"
            t := { t with errors := t.errors + 1 }
      let decided := t.pass + t.loose + t.fail
      IO.println ""
      IO.println s!"xslt EXACT: {t.pass} pass (out of {decided} decided)"
      IO.println s!"xslt EXACT-or-WHITESPACE: {t.pass + t.loose} pass, {t.fail} fail (out of {decided} decided)"
      IO.println s!"REFUSED: {t.refused} cases the engine declined to transform"
      if t.errors > 0 then
        IO.println s!"ERRORS: {t.errors} cases could not be read at all"
      IO.println s!"  (out of {cases.length} cases in the manifest)"
      -- Which refusals, and how many of each: a list of one-off
      -- reasons and a single reason repeated fifty times call for
      -- very different next pieces of work.
      let uniq := reasons.eraseDups
      if !uniq.isEmpty then
        IO.println ""
        IO.println "Refusal reasons, by frequency:"
        for r in uniq do
          IO.println s!"  {(reasons.filter (· == r)).length}x  {r}"
      IO.println ""
      IO.println "A REFUSED case is counted apart, never as a pass and never as a"
      IO.println "failure: an engine that guesses at an instruction it does not have"
      IO.println "produces a document of the right shape with the wrong content."
      return (if t.fail > 0 || t.errors > 0 then 1 else 0)
  | some _ =>
      IO.println "xslt runner: the manifest is not an array of cases"
      return 1
