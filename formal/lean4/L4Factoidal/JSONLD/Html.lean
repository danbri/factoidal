/-
L4Factoidal.JSONLD.Html — JSON-LD embedded in HTML.

Port of `formal/fstar/Parser.JSONLD.Html.fst`.

Specification implemented: JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/#html-content-algorithms.

This is NOT an HTML parser. Per the spec a
`<script type="application/ld+json">` element's content is raw text
(CDATA-like — no HTML entity decoding), so the document is scanned for
such elements and their content sliced out verbatim, then handed to the
ordinary expand / compact / flatten / toRdf algorithms. Script SELECTION
follows the API's "Load document" step:

  * `fragment = some id` — the script whose `id` attribute equals it;
  * `extractAll = true`  — every `ld+json` script, combined into a single
    JSON array;
  * otherwise            — the FIRST `ld+json` script's content.

`none` means "no matching script", which drives the suite's negative
"no script at the target" cases; malformed JSON is caught downstream
when the extracted text fails to parse.

## Termination

Every scan is fuel-bounded by the document length, which is more than
enough for any single left-to-right pass — the same discipline the F*
source uses, so each recursion decreases on `fuel` and no `partial` is
needed.

## Character units, not bytes

The F* source scans BYTES (`Parser.FastString`); this port scans
`Char`s, as every other Lean module in this tree does. The literals
being matched (`<script`, `</script`, `application/ld+json`, `id=`,
`href=`, quotes, whitespace) are ASCII, and a UTF-8 multi-byte sequence
never contains an ASCII byte, so the two scans select the same
substrings.
-/
import L4Factoidal.JSONLD.Context

namespace L4Factoidal.JSONLD.Html

open L4Factoidal.JSON

/-! ## Case-insensitive scanning -/

/-- Case-insensitive match of the lowercase-ASCII literal `pat` at
`cs.drop pos`. -/
def ciMatchAt (pat : List Char) (cs : List Char) (pos : Nat) : Bool :=
  let seg := (cs.drop pos).take pat.length
  seg.length == pat.length && (seg.map Char.toLower) == pat

/-- First index at or after `pos` at which the case-insensitive literal
`pat` occurs. -/
def ciFind (pat : List Char) (cs : List Char) : Nat → Nat → Option Nat
  | _,   0        => none
  | pos, fuel + 1 =>
    if pos ≥ cs.length then none
    else if ciMatchAt pat cs pos then some pos
    else ciFind pat cs (pos + 1) fuel

/-- First index at or after `pos` of the character `c`. -/
def findChar (c : Char) (cs : List Char) (pos : Nat) : Option Nat :=
  match (cs.drop pos).findIdx? (· == c) with
  | some i => some (pos + i)
  | none   => none

def sliceStr (cs : List Char) (start len : Nat) : String :=
  String.ofList ((cs.drop start).take len)

def satSub (a b : Nat) : Nat := if a ≥ b then a - b else 0

/-! ## Attributes -/

/-- The value of a quoted attribute `name="…"` / `name='…'` in an
open-tag slice. `name` includes the trailing `=` (e.g. `"id="`). -/
def extractAttr (opentag : String) (name : String) : Option String :=
  let cs := opentag.toList
  let pat := name.toList.map Char.toLower
  match ciFind pat cs 0 (cs.length + 1) with
  | none   => none
  | some p =>
    let qpos := p + pat.length
    match cs[qpos]? with
    | some q =>
      if q == '"' || q == '\'' then
        match findChar q cs (qpos + 1) with
        | none    => none
        | some ep => some (sliceStr cs (qpos + 1) (satSub ep (qpos + 1)))
      else none
    | none => none

def extractId (opentag : String) : Option String := extractAttr opentag "id="

/-- The `href` of the document's first `<base … href="…">` element.
Returned verbatim — the caller resolves a relative href against the
document URL. -/
def extractHtmlBase (html : String) : Option String :=
  let cs := html.toList
  match ciFind "<base".toList cs 0 (cs.length + 1) with
  | none    => none
  | some bp =>
    match findChar '>' cs (bp + 5) with
    | none    => none
    | some gt => extractAttr (sliceStr cs bp (satSub gt bp + 1)) "href="

/-! ## Script collection -/

/-- Collect `(id?, content)` for every
`<script … application/ld+json …>` element, in document order. -/
def collectScripts (cs : List Char) : Nat → Nat → List (Option String × String)
    → List (Option String × String)
  | _,   0,        acc => acc.reverse
  | pos, fuel + 1, acc =>
    match ciFind "<script".toList cs pos (cs.length + 1) with
    | none    => acc.reverse
    | some sp =>
      match findChar '>' cs (sp + 7) with
      | none    => acc.reverse
      | some gt =>
        let opentag := sliceStr cs sp (satSub gt sp + 1)
        let cstart := gt + 1
        match ciFind "</script".toList cs cstart (cs.length + 1) with
        | none    => acc.reverse
        | some ep =>
          let content := sliceStr cs cstart (satSub ep cstart)
          let otcs := opentag.toList
          let isLd := (ciFind "application/ld+json".toList otcs 0 (otcs.length + 1)).isSome
          let acc' := if isLd then (extractId opentag, content) :: acc else acc
          collectScripts cs (ep + 8) fuel acc'

def findScriptById : List (Option String × String) → String → Option String
  | [],                _   => none
  | (some i, c) :: rest, fid => if i == fid then some c else findScriptById rest fid
  | (none,   _) :: rest, fid => findScriptById rest fid

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- When an `extractAllScripts` member is itself a top-level JSON array,
its ELEMENTS are appended to the combined array (spliced), not nested —
so strip the outer `[ … ]`. A non-array (object) member is kept
whole. -/
def spliceIfArray (c : String) : String :=
  let cs := c.toList
  let trimmed := (cs.dropWhile isWs).reverse.dropWhile isWs |>.reverse
  match trimmed with
  | [] => c
  | first :: _ =>
    let lastC := trimmed.getLast? |>.getD ' '
    if first == '[' && lastC == ']' && trimmed.length > 2 then
      String.ofList ((trimmed.drop 1).take (trimmed.length - 2))
    else c

def joinContents : List (Option String × String) → String
  | []           => ""
  | [(_, c)]     => spliceIfArray c
  | (_, c) :: rest => spliceIfArray c ++ "," ++ joinContents rest

def jsonArrayOf (scripts : List (Option String × String)) : String :=
  "[" ++ joinContents scripts ++ "]"

/-- Split `"html/e003-in.html#second"` into
`("html/e003-in.html", some "second")`. -/
def splitFragment (s : String) : String × Option String :=
  match s.toList.findIdx? (· == '#') with
  | none   => (s, none)
  | some i => (String.ofList (s.toList.take i),
               some (String.ofList (s.toList.drop (i + 1))))

/-- The fragment part of a manifest `input` value, if any. -/
def fragmentOf (s : String) : Option String := (splitFragment s).2

/-- The path part of a manifest `input` value. -/
def pathOf (s : String) : String := (splitFragment s).1

/-- Extract the JSON-LD source text from an HTML document. -/
def extractJsonLdFromHtml (html : String) (fragment : Option String) (extractAll : Bool)
    : Option String :=
  let cs := html.toList
  let scripts := collectScripts cs 0 (cs.length + 1) []
  match fragment with
  | some fid => findScriptById scripts fid
  | none =>
    match scripts with
    -- No fragment and no script. With extractAllScripts this is the empty
    -- document `[]` (which expands to `[]`); WITHOUT it, loading a
    -- document that carries no JSON-LD is an error. The suite
    -- distinguishes the two. (A missing FRAGMENT target above is always
    -- the error case.)
    | []        => if extractAll then some "[]" else none
    | first :: _ => if extractAll then some (jsonArrayOf scripts) else some first.2

/-- The API's "Load document" step for an HTML source, with its two
error conditions spelled out instead of collapsed into `none`:

  * no element at the fragment target, or no `ld+json` script at all —
    `loading document failed` (html fixtures e006, e011-e013,
    r011-r013);
  * a script element whose content is not the JSON it must be —
    `invalid script element` (e014-e017, r014-r017: an uncommented
    script carrying an HTML comment, a missing start or end comment
    marker, or plain invalid JSON).

`.ok none` is the one remaining benign case: no script AND no fragment
target under a POSITIVE test, where the API says the document is simply
empty and the caller feeds `[]` onward. -/
def loadHtmlJsonLd (html : String) (fragment : Option String) (extractAll : Bool)
    : Res (Option String) :=
  match extractJsonLdFromHtml html fragment extractAll with
  | none      => .ok none
  | some text =>
    match parseJson text with
    | .ok _    => .ok (some text)
    | .error _ => .error .invalidScriptElement

end L4Factoidal.JSONLD.Html
