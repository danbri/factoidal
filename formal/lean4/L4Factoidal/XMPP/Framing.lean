/-
L4Factoidal.XMPP.Framing — cut an XMPP byte stream into the units a
server acts on.

RFC 6120 section 4.1 makes an XMPP stream an XML document whose ROOT
element (`<stream:stream>`) stays open for the life of the connection and
whose direct children (stanzas, `<stream:features>`, SASL elements) are
complete elements arriving one at a time. `L4Factoidal.XML.parseXML`
parses a COMPLETE document, so it cannot be handed the stream: it would
wait forever for the root's close tag. This module supplies exactly the
missing step — "where does the next top-level unit end" — and hands each
complete unit to `Wire.parseElement`, which is the real parser. It does
NOT interpret the unit: no attribute decoding, no entity expansion, no
namespace handling happens here.

Four unit kinds, per RFC 6120 section 4:
  * `.decl` — a leading `<?xml ...?>` declaration (section 11.5).
  * `.streamOpen` — the never-closed `<stream:stream ...>` root tag
    (section 4.2).
  * `.streamClose` — `</stream:stream>` (section 4.4).
  * `.element` — one complete top-level child element.

Bounded by construction: every scan is an index walk with an explicit
`Nat` fuel equal to the remaining input, so no input can make it loop.
No `partial`, no `sorry`, no `axiom`, no `native_decide`.
-/

namespace L4Factoidal.XMPP.Framing

/-- One top-level unit of a stream. -/
inductive Unit where
  /-- `<?xml version='1.0'?>` and any other processing instruction that
  arrives at the top level. -/
  | decl (text : String)
  /-- The stream root's opening tag, with its full text so
  `Core.StreamHeader.parse` can read its attributes. -/
  | streamOpen (text : String)
  /-- `</stream:stream>`. -/
  | streamClose
  /-- A complete top-level element, as its exact wire text. -/
  | element (text : String)
  deriving Repr, DecidableEq, Inhabited

def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The first index at or after `start` at which `pat` occurs. -/
def indexOfFrom (s : Array Char) (pat : List Char) (start : Nat) : Option Nat :=
  let n := pat.length
  let rec go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if i + n > s.size then none
      else if (List.range n).all (fun k => s[i + k]! == pat[k]!) then some i
      else go (i + 1) fuel
  if n == 0 then some start else go start (s.size + 1)

/-- Skip past a `<!-- ... -->` comment, a `<![CDATA[ ... ]]>` section or a
`<? ... ?>` processing instruction that begins at `i`. Returns the index
after its terminator, or `none` when the terminator has not arrived yet
(the caller then waits for more bytes). -/
def skipSpecial (s : Array Char) (i : Nat) : Option (Nat × Bool) :=
  -- `i` points at `<`. The Bool says whether this was a `<? ... ?>`.
  if i + 1 ≥ s.size then none
  else if s[i + 1]! == '?' then
    (indexOfFrom s ['?', '>'] (i + 2)).map (fun j => (j + 2, true))
  else if i + 3 < s.size && s[i + 1]! == '!' && s[i + 2]! == '-' && s[i + 3]! == '-' then
    (indexOfFrom s ['-', '-', '>'] (i + 4)).map (fun j => (j + 3, false))
  else if i + 8 < s.size && s[i + 1]! == '!' && s[i + 2]! == '[' then
    (indexOfFrom s [']', ']', '>'] (i + 3)).map (fun j => (j + 3, false))
  else none

/-- The name of the element whose `<` sits at `i` (after an optional
`/`). Stops at whitespace, `/` or `>`. -/
def tagNameAt (s : Array Char) (i : Nat) : String :=
  let start := if i + 1 < s.size && s[i + 1]! == '/' then i + 2 else i + 1
  let rec go (j : Nat) (acc : List Char) : Nat → List Char
    | 0 => acc.reverse
    | fuel + 1 =>
      if j ≥ s.size then acc.reverse
      else
        let c := s[j]!
        if isSpace c || c == '/' || c == '>' then acc.reverse
        else go (j + 1) (c :: acc) fuel
  String.ofList (go start [] (s.size + 1))

/-- Walk to the `>` that closes the tag starting at `i`, respecting
quoted attribute values (a `>` inside `"..."` or `'...'` does not end the
tag). Returns the index AFTER the `>` and whether the tag was
self-closing. `none` means the tag is not complete yet. -/
def scanTagEnd (s : Array Char) (i : Nat) : Option (Nat × Bool) :=
  let rec go (j : Nat) (quote : Option Char) (prevSlash : Bool) : Nat → Option (Nat × Bool)
    | 0 => none
    | fuel + 1 =>
      if j ≥ s.size then none
      else
        let c := s[j]!
        match quote with
        | some q => if c == q then go (j + 1) none false fuel else go (j + 1) quote false fuel
        | none =>
          if c == '"' || c == '\'' then go (j + 1) (some c) false fuel
          else if c == '>' then some (j + 1, prevSlash)
          else go (j + 1) none (c == '/') fuel
  go (i + 1) none false (s.size + 1)

/-- The end index of the complete element that starts at `i`, or `none`
when the element has not fully arrived. Nested elements are counted; text
between them is skipped; comments and CDATA are stepped over so a `<`
inside them cannot change the depth. -/
def scanElementEnd (s : Array Char) (i : Nat) : Option Nat :=
  let rec go (j depth : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if j ≥ s.size then none
      else if s[j]! != '<' then go (j + 1) depth fuel
      else if j + 1 < s.size && (s[j + 1]! == '?' || s[j + 1]! == '!') then
        match skipSpecial s j with
        | none => none
        | some (j', _) => go j' depth fuel
      else
        let closing := j + 1 < s.size && s[j + 1]! == '/'
        match scanTagEnd s j with
        | none => none
        | some (j', selfClosing) =>
          if closing then
            if depth ≤ 1 then some j' else go j' (depth - 1) fuel
          else if selfClosing then
            if depth == 0 then some j' else go j' depth fuel
          else go j' (depth + 1) fuel
  go i 0 (s.size + 1)

/-- Take the next top-level unit from `buf`, returning it with the
unconsumed remainder. `none` means "not enough bytes yet" — the caller
reads more and asks again; it is never an error verdict.

`inStream` says whether the stream root has already been opened. Before
it, a `<stream:stream ...>` opening tag is a unit in itself, because it
never closes. After it, the same tag would be an ordinary (and
ill-formed) child, and the server rejects it as a stream error rather
than this function guessing. -/
def nextUnit (inStream : Bool) (buf : String) : Option (Unit × String) :=
  let s := buf.toList.toArray
  let rec skipWs (j : Nat) : Nat → Nat
    | 0 => j
    | fuel + 1 => if j < s.size && isSpace s[j]! then skipWs (j + 1) fuel else j
  let i := skipWs 0 (s.size + 1)
  if i ≥ s.size then none
  else if s[i]! != '<' then none
  else
    let rest (j : Nat) : String := String.ofList (s.toList.drop j)
    let text (j k : Nat) : String := String.ofList ((s.toList.drop j).take (k - j))
    if i + 1 < s.size && s[i + 1]! == '?' then
      match skipSpecial s i with
      | none => none
      | some (j, _) => some (.decl (text i j), rest j)
    else if i + 1 < s.size && s[i + 1]! == '!' then
      match skipSpecial s i with
      | none => none
      | some (j, _) => some (.element (text i j), rest j)
    else
      let name := tagNameAt s i
      let closing := i + 1 < s.size && s[i + 1]! == '/'
      if closing && name == "stream:stream" then
        match scanTagEnd s i with
        | none => none
        | some (j, _) => some (.streamClose, rest j)
      else if !inStream && !closing && name == "stream:stream" then
        match scanTagEnd s i with
        | none => none
        | some (j, selfClosing) =>
          if selfClosing then some (.element (text i j), rest j)
          else some (.streamOpen (text i j), rest j)
      else
        match scanElementEnd s i with
        | none => none
        | some j => some (.element (text i j), rest j)

/-! ## Checks

Each `#guard` is one framing decision the server depends on. -/

#guard nextUnit false "<?xml version='1.0'?><stream:stream to='x'>"
  == some (.decl "<?xml version='1.0'?>", "<stream:stream to='x'>")

#guard nextUnit false "<stream:stream to='x' version='1.0'><auth/>"
  == some (.streamOpen "<stream:stream to='x' version='1.0'>", "<auth/>")

#guard nextUnit true "</stream:stream>" == some (.streamClose, "")

#guard nextUnit true "<iq type='set'><bind><resource>r</resource></bind></iq>rest"
  == some (.element "<iq type='set'><bind><resource>r</resource></bind></iq>", "rest")

#guard nextUnit true "<presence/><message/>"
  == some (.element "<presence/>", "<message/>")

-- A `>` inside an attribute value does not end the tag.
#guard nextUnit true "<message body='a &gt; b' to='x'/>"
  == some (.element "<message body='a &gt; b' to='x'/>", "")

-- A `<` inside a comment does not open an element.
#guard nextUnit true "<message><!-- <fake> --></message>"
  == some (.element "<message><!-- <fake> --></message>", "")

-- A `<` inside CDATA does not open an element either.
#guard nextUnit true "<message><![CDATA[<not a tag>]]></message>"
  == some (.element "<message><![CDATA[<not a tag>]]></message>", "")

-- An element with the same tag name nested inside itself closes at the
-- OUTER close tag, not the inner one.
#guard nextUnit true "<x><x/></x>tail" == some (.element "<x><x/></x>", "tail")

-- Incomplete input is "wait for more", never a frame.
#guard nextUnit true "<message><body>hi" == none
#guard nextUnit false "<stream:stream to=" == none
#guard nextUnit true "" == none

-- Leading whitespace between stanzas is skipped.
#guard nextUnit true "\n  <presence/>" == some (.element "<presence/>", "")

end L4Factoidal.XMPP.Framing
