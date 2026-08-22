/-
L4Factoidal.XML.ConfProbe — run the Lean XML parser over real files
from the W3C XML Conformance Test Suite.

Reads a list of file paths from standard input, one per line, and
prints one verdict line per file:

    WF   <path>
    NWF  <path>  <reason>

then a labelled summary on standard error. It never writes to the
corpus and never follows an external DTD reference — the parser reads
no external resource at all.

Iron rule #6 (run the real W3C test files) is why this exists: the
`#guard`s in `Tests.lean` are hand-written fixtures and are NOT a
conformance claim. This binary reads the vendored corpus from disk.

## What a verdict does and does not mean

`WF` means this parser accepted the document under the profile
`Parser.lean`'s header states: XML 1.0, NON-VALIDATING, NON-NAMESPACE.
A conformance case is only genuinely scored when the construct it tests
falls inside that profile. In particular a `not-wf` case that this
parser rejects for a DIFFERENT reason than the one under test is a
right verdict for the wrong reason, and a `valid` case that turns on
DTD validation is outside the profile entirely. Read the raw counts
accordingly, and label them.

## Encoding

Each file is read as BYTES and decoded as UTF-8. A file that is not
valid UTF-8 is reported `NWF` with the reason `not valid UTF-8`. That
covers two different things and the distinction matters:

  * a document whose bytes really are malformed Unicode — the right
    verdict, and the Lean counterpart of the F*'s
    `is_valid_decoded_char` rejection; and
  * a document in a DIFFERENT declared encoding (UTF-16, EBCDIC,
    Shift-JIS), which this probe does not transcode. Those are a
    LIMITATION of the probe, not a verdict about the document.

`[81] EncName` is parsed and recorded; acting on it (transcoding the
entity before parsing) is not implemented here, exactly as it is not in
the F* module this ports.
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XML.ConfProbe

open L4Factoidal.XML

/-- The verdict for one file, plus whether it was decodable at all. -/
structure Verdict where
  /-- The path as it was read from standard input. -/
  path : String
  /-- True when `parseXML` accepted the document. -/
  wellFormed : Bool
  /-- Why it was rejected, or why it could not be read. -/
  reason : String
deriving Repr, Inhabited

/-- Strip ASCII whitespace from both ends of a line — chiefly the `\r`
of a CRLF-terminated path list. -/
def trimWs (p : String) : String :=
  let ws (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'
  String.ofList (((p.toList.dropWhile ws).reverse.dropWhile ws).reverse)

/-- Read one file and decide well-formedness on its contents. -/
def probeFile (path : String) : IO Verdict := do
  let bytes ← try
      IO.FS.readBinFile path
    catch e =>
      return { path := path, wellFormed := false, reason := s!"unreadable: {e}" }
  match String.fromUTF8? bytes with
  | none =>
      return { path := path, wellFormed := false, reason := "not valid UTF-8" }
  | some text =>
      match parseXML text with
      | .ok _ => return { path := path, wellFormed := true, reason := "" }
      | .error e =>
          return { path := path, wellFormed := false,
                   reason := s!"{e.message} @ {e.position}" }

/-- Read paths from standard input, print one verdict per line, and
finish with a labelled summary on standard error.

The whole of standard input is read at once and split, rather than
looped over line by line: an unbounded read loop would need `partial`,
which this project does not permit anywhere. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let content ← stdin.readToEnd
  let paths := (content.splitOn "\n").map trimWs
                 |>.filter (fun p => !p.isEmpty)
  let verdicts ← paths.mapM probeFile
  for v in verdicts do
    if v.wellFormed then
      IO.println s!"WF   {v.path}"
    else
      IO.println s!"NWF  {v.path}  {v.reason}"
  let wf := (verdicts.filter (·.wellFormed)).length
  let nwf := verdicts.length - wf
  let undecodable := (verdicts.filter (fun v => v.reason == "not valid UTF-8")).length
  IO.eprintln s!"summary: {wf} accepted as well-formed, {nwf} rejected as malformed (out of {verdicts.length} files); {undecodable} of the rejections were undecodable as UTF-8"

end L4Factoidal.XML.ConfProbe

/-- Entry point for the `xmlconf-probe` executable. -/
def main : IO Unit := L4Factoidal.XML.ConfProbe.main
