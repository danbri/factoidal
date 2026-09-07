import L4Factoidal.XML.Document
import L4Factoidal.XML.Parser

/-!
XMPP wire-format glue on top of `L4Factoidal.XML` — the real, W3C-XML-1.0-
conformant, F*-ported parser (`L4Factoidal/XML/Parser.lean`,
`Document.lean`). This module does NOT reimplement XML parsing: per Iron
Rule #7 ("no hand-written reimplementations of what the formal tree
defines"), a complete element (a stanza, `<stream:features>`, a SASL
payload wrapper, etc.) is parsed via `L4Factoidal.XML.parseXML` and its
`.root`.

Two things this module DOES add, because `L4Factoidal.XML` doesn't cover
them (it's a document-oriented — prolog+root+epilog — non-validating
parser, per its own module header) and XMPP genuinely needs them:

1. `render` — serialization. `L4Factoidal.XML` is parse-only (built for
   W3C conformance testing, not round-tripping), so there's nothing to
   reuse here; this is a new concern, not a duplicate.
2. `parseOpenTag` — an XMPP stream's `<stream:stream ...>` is never
   closed until the connection ends, so it can never be a complete
   `Node` the way `parseXML` expects. This is a narrow, stated gap: the
   right long-term fix is probably a small addition to `L4Factoidal.XML`
   itself (a generic "parse one start-tag, don't require a matching
   close" mode other streaming XML protocols could reuse too), not an
   XMPP-local parser. Filed as future work, not silently worked around.
-/

namespace L4Factoidal.XMPP.Wire

open L4Factoidal.XML (Node Attribute)

/-- Replace every occurrence of `old` in `s` with `new`. `old` must be
non-empty. -/
def replaceAll (s old new : String) : String :=
  if old.isEmpty then s else String.intercalate new (s.splitOn old)

def escapeText (s : String) : String :=
  let s := replaceAll s "&" "&amp;"
  let s := replaceAll s "<" "&lt;"
  let s := replaceAll s ">" "&gt;"
  s

def escapeAttr (s : String) : String :=
  let s := escapeText s
  replaceAll s "\"" "&quot;"

mutual

/-- Render a `Node` back to XML text. `comment`/`cdata`/`pi` nodes (which
`L4Factoidal.XML` can parse but XMPP stanzas never contain) render to
their literal XML forms too, for completeness. -/
def render : Node → String
  | .text s => escapeText s
  | .comment body => s!"<!--{body}-->"
  | .cdata content => s!"<![CDATA[{content}]]>"
  | .pi target data => s!"<?{target} {data}?>"
  | .element tag attrs children =>
    let attrStr := String.join (attrs.map (fun a => s! " {a.name}=\"{escapeAttr a.value}\""))
    match children with
    | [] => s!"<{tag}{attrStr}/>"
    | _ => s!"<{tag}{attrStr}>" ++ renderList children ++ s!"</{tag}>"

def renderList : List Node → String
  | [] => ""
  | n :: ns => render n ++ renderList ns

end

/-- Parse a complete element (a stanza, `<stream:features>`, ...) via the
real XML parser. `L4Factoidal.XML.parseXML` accepts a document with no
XML declaration, so a bare `<message>...</message>` string parses fine —
its `.root` is exactly the element. -/
def parseElement (s : String) : Option Node :=
  match L4Factoidal.XML.parseXML s with
  | .ok doc => some doc.root
  | .error _ => none

-- ## The one thing `L4Factoidal.XML` doesn't cover: an unclosed root.
-- Minimal fuel-bounded helpers, narrowly scoped to "one opening tag,"
-- not a competing element/document parser.

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == ':'

private def dropSpaces : List Char → List Char
  | [] => []
  | c :: cs => if isSpace c then dropSpaces cs else c :: cs

private def spanNameGo (acc : List Char) : List Char → (List Char × List Char)
  | [] => (acc.reverse, [])
  | c :: rest => if isNameChar c then spanNameGo (c :: acc) rest else (acc.reverse, c :: rest)

private def spanName (cs : List Char) : (String × List Char) :=
  let (nameChars, rest) := spanNameGo [] cs
  (String.ofList nameChars, rest)

private def spanUntilGo (acc : List Char) (delim : Char) : List Char → (List Char × List Char)
  | [] => (acc.reverse, [])
  | c :: rest => if c == delim then (acc.reverse, c :: rest) else spanUntilGo (c :: acc) delim rest

private def spanUntil (delim : Char) (cs : List Char) : (String × List Char) :=
  let (chars, rest) := spanUntilGo [] delim cs
  (String.ofList chars, rest)

/-- Decode the five predefined entities in an attribute value. `&amp;`
decoded last, so `&amp;lt;` (the four characters `&lt;`) doesn't
double-decode into `<`. Real entity handling (numeric refs, custom
entities) belongs to `L4Factoidal.XML`; opening tags only ever carry the
five predefined ones in practice. -/
private def unescapeAttr (s : String) : String :=
  let s := replaceAll s "&lt;" "<"
  let s := replaceAll s "&gt;" ">"
  let s := replaceAll s "&apos;" "'"
  let s := replaceAll s "&quot;" "\""
  replaceAll s "&amp;" "&"

private def parseAttrs (fuel : Nat) (acc : List Attribute) (cs : List Char) :
    Option (List Attribute × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let cs := dropSpaces cs
    match cs with
    | [] => none
    | '>' :: _ => some (acc.reverse, cs)
    | '/' :: _ => some (acc.reverse, cs)
    | c :: _ =>
      if !isNameChar c then none else
      let (name, rest) := spanName cs
      let rest := dropSpaces rest
      match rest with
      | '=' :: rest =>
        let rest := dropSpaces rest
        match rest with
        | q :: rest =>
          if q == '"' || q == '\'' then
            let (rawValue, rest) := spanUntil q rest
            match rest with
            | _ :: rest => parseAttrs fuel (⟨name, unescapeAttr rawValue⟩ :: acc) rest
            | [] => none
          else none
        | [] => none
      | _ => none

/-- Skip an optional leading XML declaration (`<?xml ... ?>`) — real
servers (confirmed against a live ejabberd instance, 2026-09-07) send one
before `<stream:stream>`, and a naive `parseOpenTag` that doesn't expect
it fails on every real-world capture despite passing on hand-written test
strings that omitted it. Skips at most one `<? ... ?>`, XML-declaration or
not; doesn't validate its contents (that's `L4Factoidal.XML`'s job for a
document that has one as part of a full parse). -/
private def skipXmlDecl (cs : List Char) : List Char :=
  match dropSpaces cs with
  | '<' :: '?' :: rest =>
    let (_, rest) := spanUntilGo [] '>' rest
    match rest with
    | _ :: rest => rest  -- consume the '>'
    | [] => []
  | cs => cs

/-- Parse just an element's OPENING tag (name + attributes), stopping
right after `>` or `/>` — does not require or consume a matching close
tag. Returns the tag name, its attributes, whether it was self-closing,
and the unconsumed remainder. Tolerates one leading `<?xml ... ?>`. -/
def parseOpenTag (s : String) : Option (String × List Attribute × Bool × String) :=
  match dropSpaces (skipXmlDecl s.toList) with
  | '<' :: rest =>
    let rest := dropSpaces rest
    match rest with
    | [] => none
    | c :: _ =>
      if !isNameChar c then none else
      let (tag, rest) := spanName rest
      match parseAttrs (2 * rest.length + 4) [] rest with
      | none => none
      | some (attrs, rest) =>
        match dropSpaces rest with
        | '/' :: '>' :: rest' => some (tag, attrs, true, String.ofList rest')
        | '>' :: rest' => some (tag, attrs, false, String.ofList rest')
        | _ => none
  | _ => none

end L4Factoidal.XMPP.Wire
