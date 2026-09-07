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

## Where the corpus is found

The runner takes a corpus directory, either positionally or as
`--base DIR`. A RELATIVE directory is tried first against the process's
working directory (the repository root, as `lake -d formal/lean4 exe
l4xslt` runs it) and then against `../../` (the working directory when
a command runs inside `formal/lean4`). Both invocations therefore work
and neither needs the caller to know which one the harness used.

`--verbose` prints the produced and expected text of every failing
case. Without it a failing case prints only its name, because a
1690-case corpus prints megabytes otherwise.

Usage: `lake exe l4xslt [--base DIR] [--verbose] [tests-dir]`
       default corpus: `third_party/testing/xslt`
       Apache Xalan mirror: `--base third_party/testing/xslt1-xalan`
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

/-- Every `document('literal')` URI a stylesheet mentions.

    `XPath.Eval` does no I/O: the caller decides which documents
    exist. The runner scans the stylesheet TEXT for the literal
    argument of each `document(...)` call and loads the file beside
    the stylesheet, so `document('select-59.xml')` resolves and
    `document($computed)` does not — which is the truth, and shows up
    as a refusal rather than as an empty tree. -/
partial def documentUris (cs : List Char) : List String :=
  match cs with
  | [] => []
  | _ =>
      if (cs.take 9) == "document(".toList then
        let r := (cs.drop 9).dropWhile (fun c => c == ' ')
        match r with
        | q :: rest =>
            if q == '\'' || q == '"' then
              let body := rest.takeWhile (· != q)
              String.ofList body :: documentUris (rest.dropWhile (· != q))
            else documentUris (cs.drop 9)
        | [] => []
      else documentUris cs.tail!

/-- Resolve a corpus directory that may be written relative to the
    repository root or relative to `formal/lean4`. Some probes are run
    as `lake -d formal/lean4 exe NAME` from the root and some from
    inside `formal/lean4`; trying the root-relative path first and the
    `../../` path second makes one spelling work for both. -/
def resolveBase (d : String) : IO String := do
  if ← System.FilePath.pathExists (d ++ "/manifest.json") then return d
  let up := "../../" ++ d
  if ← System.FilePath.pathExists (up ++ "/manifest.json") then return up
  return d

/-- Read a corpus file as text, or `none` when it is not UTF-8.

    The Xalan mirror carries Latin-1 and UTF-16 source documents.
    `IO.FS.readFile` raises on those and killed the run at case 60 of
    1690. A file this parser cannot decode is counted apart as
    NOT-UTF-8, exactly as the XML conformance runner counts one: the
    profile is UTF-8, and a transcoding gap is not a transform defect. -/
def readUtf8? (path : String) : IO (Option String) := do
  if !(← System.FilePath.pathExists path) then return none
  let bytes ← IO.FS.readBinFile path
  return String.fromUTF8? bytes

structure Tally where
  pass    : Nat := 0
  loose   : Nat := 0
  fail    : Nat := 0
  refused : Nat := 0
  errors  : Nat := 0
  /-- Files this parser cannot decode: the profile is UTF-8. -/
  notUtf8 : Nat := 0
deriving Inhabited

/-- Add one decided case, failing or not, to the per-category counts. -/
def bump (l : List (String × Nat × Nat)) (cat : String) (failed : Bool)
    : List (String × Nat × Nat) :=
  if l.any (fun e => e.1 == cat) then
    l.map (fun e => if e.1 == cat then (e.1, e.2.1 + (if failed then 1 else 0), e.2.2 + 1) else e)
  else l ++ [(cat, (if failed then 1 else 0), 1)]

/-- `--base DIR` or a bare positional directory; the two spellings mean
    the same thing. -/
def baseArg (args : List String) : String :=
  let rec go : List String → Option String
    | "--base" :: d :: _ => some d
    | _ :: rest          => go rest
    | []                 => none
  match go args with
  | some d => d
  | none   => ((args.filter (fun a => !a.startsWith "--")).head?).getD
                "third_party/testing/xslt"

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let dir ← resolveBase (baseArg args)
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
      -- Per-category (fail, decided) counts. A 1690-case corpus is
      -- only actionable as clusters: one category at 44 of 44 names a
      -- missing instruction, forty singletons name forty bugs.
      let mut byCat : List (String × Nat × Nat) := []
      for c in cases do
        let name := (str? "name" c).getD "<unnamed>"
        let cat := (str? "category" c).getD "?"
        match str? "stylesheet" c, str? "source" c, str? "expected" c with
        | some sp, some src, some exp => do
            match (← readUtf8? (dir ++ "/" ++ sp)),
                  (← readUtf8? (dir ++ "/" ++ src)),
                  (← readUtf8? (dir ++ "/" ++ exp)) with
            | none, _, _ | _, none, _ | _, _, none =>
                t := { t with notUtf8 := t.notUtf8 + 1 }
                IO.println s!"NOT-UTF-8 {cat}/{name}: a file of this case is missing or is not UTF-8"
            | some styleSrc, some srcSrc, some expSrc => do
                -- The stylesheet's own directory is the base for a
                -- relative `document()` URI.
                let sdir := (sp.splitOn "/").dropLast
                let mut extra : List (String × List Node) := []
                let mut absent : List String := []
                for u in (documentUris styleSrc.toList).eraseDups do
                  if u != "" then
                    let path := dir ++ "/" ++ String.intercalate "/" (sdir ++ [u])
                    if ← System.FilePath.pathExists path then
                      let dtext ← IO.FS.readFile path
                      match parseXML dtext with
                      | .ok dd => extra := extra ++ [(u, dd.prolog ++ (dd.root :: dd.epilog))]
                      | .error _ => absent := absent ++ [u]
                    else absent := absent ++ [u]
                match parseXML styleSrc, parseXML srcSrc with
                | .error e, _ =>
                    IO.println s!"ERROR {cat}/{name}: the stylesheet is not well-formed XML: {e.message} at {e.position}"
                    t := { t with errors := t.errors + 1 }
                | _, .error e =>
                    IO.println s!"ERROR {cat}/{name}: the source is not well-formed XML: {e.message} at {e.position}"
                    t := { t with errors := t.errors + 1 }
                | .ok style, .ok source =>
                    match transform style source extra with
                    | .refused why =>
                        -- A refusal that names nothing is hard to act on.
                        -- When the stylesheet asks for a document the
                        -- corpus does not carry, say WHICH: the vendoring
                        -- renamed each environment's source file, so a
                        -- stylesheet naming it by its upstream filename
                        -- cannot find it, and that is a corpus fact
                        -- rather than an engine gap.
                        let why := if absent.isEmpty then why
                          else why ++ " (no such document in the corpus: "
                                    ++ String.intercalate ", " absent ++ ")"
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
                        let failed := a != b && looseForm a != looseForm b
                        if a == b then t := { t with pass := t.pass + 1 }
                        else if !failed then
                          t := { t with loose := t.loose + 1 }
                          IO.println s!"LOOSE {cat}/{name}"
                        else
                          t := { t with fail := t.fail + 1 }
                          IO.println s!"FAIL {cat}/{name}"
                          -- The whole produced and expected text of
                          -- every failure is megabytes over the Xalan
                          -- mirror, so it is behind `--verbose`.
                          if verbose then
                            IO.println s!"    produced: {a}"
                            IO.println s!"    expected: {b}"
                        byCat := bump byCat cat failed
        | _, _, _ =>
            IO.println s!"ERROR {name}: the manifest entry is incomplete"
            t := { t with errors := t.errors + 1 }
      let decided := t.pass + t.loose + t.fail
      IO.println ""
      IO.println s!"xslt EXACT: {t.pass} pass (out of {decided} decided)"
      IO.println s!"xslt EXACT-or-WHITESPACE: {t.pass + t.loose} pass, {t.fail} fail (out of {decided} decided)"
      IO.println s!"REFUSED: {t.refused} cases the engine declined to transform"
      if t.notUtf8 > 0 then
        IO.println s!"NOT UTF-8 or missing: {t.notUtf8} cases (out of profile, not scored)"
      if t.errors > 0 then
        IO.println s!"ERRORS: {t.errors} cases could not be read at all"
      IO.println s!"  (out of {cases.length} cases in the manifest)"
      -- Which refusals, and how many of each: a list of one-off
      -- reasons and a single reason repeated fifty times call for
      -- very different next pieces of work.
      -- Clusters first: which categories the failures sit in.
      let hot := (byCat.filter (fun e => e.2.1 > 0)).toArray.qsort
                   (fun a b => a.2.1 > b.2.1) |>.toList
      if !hot.isEmpty then
        IO.println ""
        IO.println "Failures by category (fail / decided):"
        for (c, f, d) in hot do
          IO.println s!"  {f} / {d}   {c}"
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
