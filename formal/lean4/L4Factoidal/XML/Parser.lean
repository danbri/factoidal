/-
L4Factoidal.XML.Parser — the XML 1.0 parser, and with it the
well-formedness decision.

Port of `formal/fstar/Parser.XML.fst` (F*) to Lean 4. Production
numbers cite **XML 1.0 (Fifth Edition)**, W3C Recommendation
26 November 2008, https://www.w3.org/TR/xml/ .

In XML there is no separate "validator pass" for well-formedness: a
document is well-formed exactly when the parser accepts its character
string. `parseXML` IS the well-formedness decision, and it is the same
decision the F* tree's `bin/xml-runner` scores against the W3C XML
Conformance Test Suite.

## Well-formedness constraints this parser enforces

Mirrors the scope of `Parser.XML.fst` exactly — no more, no less.

Structure and characters:
  1. `[2] Char` — every character of text, attribute values, comments,
     CDATA sections and PI data must be in the Char production, and so
     must every character a reference resolves to. Rejects #x0-#x8,
     #xB, #xC, #xE-#x1F, #xFFFE, #xFFFF.
  2. `[3] S` / `[5] Name` / `[4] NameStartChar` / `[4a] NameChar` —
     names are scanned against the codepoint tables in `Document.lean`.
  3. §2.11 line-ending normalisation — every `#xD #xA` pair and every
     lone `#xD` becomes a single `#xA`, unconditionally, before any
     other parsing step.
  4. §4.3.3 — a leading byte-order mark is consumed at position 0 only.

Element structure:
  5. **WFC: Element Type Match** (`[39] element`) — the `[42] ETag`
     name must equal the `[40] STag` name.
  6. **WFC: Unique Att Spec** (`[40]`/`[44]`) — no two attributes of one
     element may share a name.
  7. `[1] document ::= prolog element Misc*` — exactly one document
     element; after it only `[27] Misc` (S / Comment / PI) may appear.
     Trailing content, a second root, stray text, a CDATA section or a
     character reference in the epilog all reject.

Content productions:
  8. `[14] CharData` excludes the literal `]]>` sequence.
  9. `[15] Comment` — the body may not contain `--` and may not end
     in `-`.
 10. `[16] PI` — a `[17] PITarget` is required; the target `xml` in any
     case combination is reserved and rejected as a generic PI target;
     `S` is required between target and data unless `?>` follows the
     target immediately.
 11. `[18] CDSect` — `<![CDATA[` … `]]>`; an unterminated section
     rejects.
 12. `[10] AttValue` excludes `<` unconditionally.
 13. §3.3.3 attribute-value normalisation — a LITERAL tab / CR / LF in
     an attribute value becomes a single space; a CHARACTER REFERENCE
     to one of those codepoints is left alone, exactly as the spec
     carves out.

References:
 14. `[66] CharRef ::= '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'` — at
     least one digit, every digit of the right radix, and the resolved
     codepoint must satisfy `[2] Char`. Only lowercase `x` introduces
     the hexadecimal form.
 15. `[68] EntityRef` — the five predefined entities `amp lt gt quot
     apos`, then the general internal entities declared in the internal
     subset. A reference not terminated by `;` rejects.
 16. **WFC: Entity Declared** — a reference to an undeclared entity
     rejects.
 17. **WFC: No Recursion** — a directly or indirectly self-referential
     entity rejects.
 18. Stage-A entity boundary: replacement text containing literal
     markup (`<`) is REJECTED rather than spliced in as elements. This
     parser does not reparse replacement text as content, so a
     markup-bearing entity is an acknowledged unsupported case —
     rejected, never wrongly accepted. (This is the F* module's own
     documented boundary, ported unchanged.)

Prolog:
 19. `[23] XMLDecl` — a strict ordered walk: `[24] VersionInfo` is
     mandatory and first, `[80] EncodingDecl` and `[32] SDDecl` are each
     optional and each attempted exactly once, in that relative order.
     Anything left over before `?>` rejects the whole declaration, so an
     unknown fourth pseudo-attribute, a duplicate, or an out-of-order
     one all fail. Value lexicons are checked: `[26] VersionNum ::=
     '1.' [0-9]+`, `[81] EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')*`,
     and the SDDecl value is lowercase `yes` or `no` only.
     No whitespace may precede the declaration.
 20. `[28] doctypedecl` — recognised and parsed structurally.
     `[71] GEDecl` general internal entities are collected (first
     declaration wins, §4.2); `[52] AttlistDecl` is scanned for
     `[54] AttType` = `ID` pairs; `[45] elementdecl`,
     `[82] NotationDecl`, parameter entities, external entities,
     comments, PIs, PEReferences and whitespace are skipped
     structurally. An unterminated internal subset rejects.

## Deliberately NOT enforced — the F* module's own scope cuts

  * **Validity constraints.** This is a NON-VALIDATING processor.
    Content models, ATTLIST defaulting/enforcement, and ID/IDREF
    uniqueness are recognised but never checked.
  * **The external DTD subset** is never loaded — no external resource
    is read at all — and neither are conditional sections or general
    parameter-entity expansion.
  * **Namespaces in XML.** Plain XML 1.0 allows `:` anywhere in a Name,
    and `xmltest/` exercises that on purpose. The namespace layer is
    separate: `L4Factoidal.XML.Namespaces`.
  * **XML 1.1.** The declared version is recorded, never acted on
    (beyond handing it to the namespace layer, whose undeclaring rule
    differs between 1.0 and 1.1).
  * **The RDF/XML-specific checks** of `XML.Wellformedness.fst` live in
    `L4Factoidal.XML.Wellformedness`, not here.

## Byte semantics vs codepoint semantics

The F* parser indexes raw UTF-8 BYTES. Its `fs_cp_at`,
`is_utf8_continuation_byte`, `is_valid_decoded_char` and
`codepoint_to_string` exist only to rebuild codepoints from bytes, to
reject byte sequences that are not valid UTF-8, and to re-encode a
resolved character reference. Lean `String`/`Char` are codepoint types
and every `Char` is a valid Unicode scalar value by construction, so
that machinery has no counterpart here: the invalid-UTF-8 rejection is
discharged by Lean's type. Everything stated over CODEPOINTS is ported
in full. Positions in `XmlError` are therefore CHARACTER offsets into
the line-ending-normalised document, where the F* reports byte offsets.

## Totality

No `partial`, no `sorry`. Every scan is structurally recursive on an
explicit `Nat` fuel, exactly where the F* uses `decreases fuel`; entity
expansion uses the F*'s own lexicographic `(depth, budget)` measure via
`termination_by`.
-/
import L4Factoidal.XML.Document

namespace L4Factoidal.XML

/-! ## Errors and the internal parse result -/

/-- A parse failure: what went wrong, and the character offset into the
line-ending-normalised document where it was detected. -/
structure XmlError where
  /-- Human-readable description of the violated production or
  well-formedness constraint. -/
  message : String
  /-- Character offset into the normalised document. -/
  position : Nat
deriving DecidableEq, Repr, Inhabited

instance : ToString XmlError where
  toString e := s!"{e.message} (at character {e.position})"

/-- The internal result of one parsing step: a value and the position
after it, or a message and the position at which it failed. Port of F*
`Parser.Combinators.parse_result`. -/
inductive PResult (α : Type) where
  /-- Success: the value, and the position just after what was consumed. -/
  | ok (value : α) (pos : Nat) : PResult α
  /-- Failure: the message, and the position at which it was detected. -/
  | err (message : String) (pos : Nat) : PResult α
deriving Repr

/-- The document under the cursor, as a codepoint array. The F* indexes
bytes of a `string`; this is the codepoint-level counterpart. -/
abbrev Chars := Array Char

/-- The character at `i`, or NUL when `i` is out of range. NUL is not in
`[2] Char` and is not a delimiter of any production, so an out-of-range
read can never be mistaken for content — and every caller guards with
an explicit bound anyway, mirroring the F*. Port of F* `fs_byte_index`. -/
def charAt (s : Chars) (i : Nat) : Char := s.getD i (Char.ofNat 0)

/-- The substring `[start, stop)` as a `String`. Port of F*
`fs_byte_sub` (whose length argument becomes an end offset here). -/
def sub (s : Chars) (start stop : Nat) : String :=
  String.ofList (s.extract start stop).toList

/-! ## Primitive scanners

Counterparts of `Parser.Combinators`' `pchar` / `pstring` /
`ptake_while_pos` / `ptake_while1_pos`. -/

/-- True when the characters of `lit` occur at `pos`. -/
def matchLit : List Char → Chars → Nat → Bool
  | [], _, _ => true
  | c :: rest, s, pos => pos < s.size && charAt s pos == c && matchLit rest s (pos + 1)

/-- Require the literal `lit` at `pos`. Port of F* `pstring`. -/
def pstring (lit : String) (s : Chars) (pos : Nat) : PResult Unit :=
  if matchLit lit.toList s pos then .ok () (pos + lit.length)
  else .err s!"expected '{lit}'" pos

/-- True when the literal `lit` occurs at `pos`, without consuming. -/
def peekLit (lit : String) (s : Chars) (pos : Nat) : Bool :=
  matchLit lit.toList s pos

/-- Require the single character `c` at `pos`. Port of F* `pchar`. -/
def pchar (c : Char) (s : Chars) (pos : Nat) : PResult Unit :=
  if pos < s.size && charAt s pos == c then .ok () (pos + 1)
  else .err s!"expected '{c}'" pos

/-- Scan forward while `p` holds; returns the first position where it
does not. Port of F* `ptake_while_pos`. -/
def scanWhile (p : Char → Bool) (s : Chars) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    if pos < s.size && p (charAt s pos) then scanWhile p s (pos + 1) fuel else pos

/-- `[3] S?` — skip a possibly-empty run of whitespace.
Port of F* `skip_xml_space`. -/
def skipSpace (s : Chars) (pos : Nat) : Nat :=
  scanWhile isXmlSpace s pos (s.size - pos)

/-- `[3] S` — require at least one whitespace character.
Port of F* `ptake_while1_pos is_xml_space`. -/
def skipSpace1 (s : Chars) (pos : Nat) : PResult Unit :=
  let p := skipSpace s pos
  if p > pos then .ok () p else .err "expected whitespace" pos

/-- True when every character in `[start, stop)` satisfies `[2] Char`.
Port of F* `scan_chars_valid` (whose UTF-8 decoding half is discharged
by Lean's `Char` type). -/
def charsValid (s : Chars) (start stop : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if start ≥ stop || start ≥ s.size then true
    else if isXmlChar (charAt s start) then charsValid s (start + 1) stop fuel
    else false

/-- `[2] Char` over a whole half-open range. -/
def rangeCharsValid (s : Chars) (start stop : Nat) : Bool :=
  charsValid s start stop (stop - start)

/-! ## `[5] Name` -/

/-- Scan the body of a Name from `pos`, returning the first position
that is not a `[4a] NameChar`. Port of F* `scan_name_body_end`. -/
def scanNameEnd (s : Chars) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    if pos < s.size && isNameChar (charAt s pos) then scanNameEnd s (pos + 1) fuel else pos

/-- `[5] Name ::= NameStartChar (NameChar)*`. Port of F*
`parse_xml_name`. -/
def parseName (s : Chars) (pos : Nat) : PResult String :=
  if pos ≥ s.size then .err "expected XML name" pos
  else if isNameStartChar (charAt s pos) then
    let e := scanNameEnd s (pos + 1) (s.size - pos)
    .ok (sub s pos e) e
  else .err "expected XML name start character" pos

/-! ## `[66] CharRef` and `[68] EntityRef` -/

/-- `[0-9]`. -/
def isDecDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `[0-9a-fA-F]`. -/
def isHexDigit (c : Char) : Bool :=
  isDecDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The numeric value of one hexadecimal digit. Port of F*
`hex_digit_value`. -/
def hexDigitValue (c : Char) : Nat :=
  let cp := c.toNat
  if 0x30 ≤ cp && cp ≤ 0x39 then cp - 0x30
  else if 0x41 ≤ cp && cp ≤ 0x46 then cp - 0x41 + 10
  else if 0x61 ≤ cp && cp ≤ 0x66 then cp - 0x61 + 10
  else 0

/-- The value of a decimal digit string. Port of F* `chars_to_dec`
(whose `pow10`-weighted sum is the same number as this fold). -/
def decValue (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - 0x30)) 0

/-- The value of a hexadecimal digit string. Port of F*
`chars_to_hex`. -/
def hexValue (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 16 + hexDigitValue c) 0

/-- Collect the digits of a `[66] CharRef` up to its `;`. Every digit
must satisfy `validDigit` and at least one is required — so `&# 65;`,
`&#A;`, `&#x4G;` and `&#RE;` all reject on the first offending
character rather than accumulating it. Port of F* `parse_ref_digits`. -/
def parseRefDigits (validDigit : Char → Bool) (s : Chars) (pos : Nat)
    (acc : List Char) : Nat → PResult (List Char)
  | 0 => .err "character reference too long" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated character reference" pos
    else
      let ch := charAt s pos
      if ch == ';' then
        if acc.isEmpty then .err "empty character reference" pos
        else .ok acc.reverse (pos + 1)
      else if validDigit ch then parseRefDigits validDigit s (pos + 1) (ch :: acc) fuel
      else .err "invalid character reference digit" pos

/-- The character a resolved `[66] CharRef` denotes. Only ever applied
to a codepoint that has already passed `[2] Char`, so `Char.ofNat` is
exact. The F* needs a hand-written UTF-8 encoder here
(`codepoint_to_string`); Lean strings are codepoint sequences, so this
is one character. -/
def codepointToString (cp : Nat) : String := String.singleton (Char.ofNat cp)

/-- The general internal entities declared by the internal subset:
name ↦ raw, unexpanded replacement text. Port of F*
`dtd_entity_table`. -/
abbrev EntityTable := List (String × String)

/-- Look a declared general entity up by name. Port of F*
`lookup_entity`. -/
def lookupEntity (name : String) (ents : EntityTable) : Option String :=
  (ents.find? (fun p => p.1 == name)).map (·.2)

/-- The five entities §4.6 says every processor must recognise whether
or not they are declared. -/
def isPredefinedEntity (name : String) : Bool :=
  name == "amp" || name == "lt" || name == "gt" || name == "quot" || name == "apos"

/-- The replacement text of a predefined entity. -/
def predefinedValue (name : String) : String :=
  if name == "amp" then "&"
  else if name == "lt" then "<"
  else if name == "gt" then ">"
  else if name == "quot" then "\""
  else "'"

/-- Expand a raw entity replacement text into decoded characters.

`visited` holds the names currently being expanded, so a direct or
indirect cycle rejects (**WFC: No Recursion**). `depth` bounds how many
nested declared-entity dives may still happen; `budget` bounds the scan
of the current string. The lexicographic measure `(depth, budget)` is
the F*'s own `%[depth; budget]`: diving into a nested entity decrements
`depth`, scanning forward decrements `budget`.

Port of F* `expand_entity_value`. -/
def expandEntityValue (ents : EntityTable) (visited : List String)
    (s : Chars) (pos : Nat) (depth : Nat) (budget : Nat)
    (acc : List String) : PResult String :=
  match budget with
  | 0 => .err "entity replacement text too long" pos
  | budget' + 1 =>
    if pos ≥ s.size then .ok (String.join acc.reverse) pos
    else
      let ch := charAt s pos
      if ch == '<' then
        -- Stage-A boundary: replacement text carrying literal markup
        -- would have to be reparsed as content, which this slice does
        -- not do. Reject rather than accept it as text.
        .err "entity replacement text contains markup ('<'); unsupported" pos
      else if ch == '&' then
        if pos + 1 < s.size && charAt s (pos + 1) == '#' then
          if pos + 2 ≥ s.size then .err "unterminated character reference in entity" pos
          else if charAt s (pos + 2) == 'x' then
            match parseRefDigits isHexDigit s (pos + 3) [] (s.size + 1) with
            | .err m p => .err m p
            | .ok digits pos' =>
              let cp := hexValue digits
              if isXmlCharCode cp then
                expandEntityValue ents visited s pos' depth budget'
                  (codepointToString cp :: acc)
              else .err "character reference to a non-Char codepoint" pos'
          else
            match parseRefDigits isDecDigit s (pos + 2) [] (s.size + 1) with
            | .err m p => .err m p
            | .ok digits pos' =>
              let cp := decValue digits
              if isXmlCharCode cp then
                expandEntityValue ents visited s pos' depth budget'
                  (codepointToString cp :: acc)
              else .err "character reference to a non-Char codepoint" pos'
        else
          match parseName s (pos + 1) with
          | .err m p => .err m p
          | .ok name posN =>
            if posN ≥ s.size || charAt s posN != ';' then
              .err "entity reference not terminated by ';'" posN
            else
              let pos' := posN + 1
              if isPredefinedEntity name then
                expandEntityValue ents visited s pos' depth budget'
                  (predefinedValue name :: acc)
              else if visited.contains name then
                .err "recursive entity reference (WFC: No Recursion)" pos
              else
                match lookupEntity name ents with
                | none => .err "reference to undeclared entity (WFC: Entity Declared)" pos
                | some subval =>
                  match depth with
                  | 0 => .err "entity nesting too deep" pos
                  | depth' + 1 =>
                    let subArr : Chars := subval.toList.toArray
                    match expandEntityValue ents (name :: visited) subArr 0 depth'
                            (subArr.size + 1) [] with
                    | .err m p => .err m p
                    | .ok decoded _ =>
                      -- `depth' + 1` rather than `depth`: matching on
                      -- `depth` generalised it, so naming the successor
                      -- form is what lets the `(depth, budget)` measure
                      -- see this call keep the depth and drop the budget.
                      expandEntityValue ents visited s pos' (depth' + 1) budget' (decoded :: acc)
      else
        expandEntityValue ents visited s (pos + 1) depth budget'
          (String.singleton ch :: acc)
termination_by (depth, budget)

/-- Parse one `[67] Reference` whose leading `&` has already been
consumed, returning its replacement text and the position after the
`;`. Port of F* `parse_reference`. -/
def parseReference (ents : EntityTable) (s : Chars) (pos : Nat) : PResult String :=
  if pos ≥ s.size then .err "unterminated reference" pos
  else if charAt s pos == '#' then
    if pos + 1 ≥ s.size then .err "unterminated character reference" pos
    -- Only LOWERCASE 'x' introduces the hexadecimal form; an uppercase
    -- 'X' is not the hex marker at all and falls through to the decimal
    -- path, where it is not a digit and rejects.
    else if charAt s (pos + 1) == 'x' then
      match parseRefDigits isHexDigit s (pos + 2) [] (s.size + 1) with
      | .err m p => .err m p
      | .ok digits pos' =>
        let cp := hexValue digits
        if isXmlCharCode cp then .ok (codepointToString cp) pos'
        else .err "character reference to a non-Char codepoint" pos'
    else
      match parseRefDigits isDecDigit s (pos + 1) [] (s.size + 1) with
      | .err m p => .err m p
      | .ok digits pos' =>
        let cp := decValue digits
        if isXmlCharCode cp then .ok (codepointToString cp) pos'
        else .err "character reference to a non-Char codepoint" pos'
  else
    match parseName s pos with
    | .err m p => .err m p
    | .ok name posN =>
      if posN ≥ s.size || charAt s posN != ';' then
        .err "entity reference not terminated by ';'" posN
      else
        let pos' := posN + 1
        if isPredefinedEntity name then .ok (predefinedValue name) pos'
        else
          match lookupEntity name ents with
          | none => .err "reference to undeclared entity (WFC: Entity Declared)" pos
          | some subval =>
            let subArr : Chars := subval.toList.toArray
            match expandEntityValue ents [name] subArr 0 (ents.length + 1)
                    (subArr.size + 1) [] with
            | .err m p => .err m p
            | .ok decoded _ => .ok decoded pos'

/-! ## `[10] AttValue` -/

/-- §3.3.3 attribute-value normalisation: a LITERAL tab, CR or LF in an
attribute value is replaced by a single space.

This is applied only to raw runs sliced straight out of the document,
never to the decoded output of a reference — §3.3.3 explicitly carves
out character references (`&#9;` `&#10;` `&#13;` keep the referenced
character itself). `parseAttrValueBody` keeps that distinction by
construction. Port of F* `normalize_attr_literal_ws`. -/
def normalizeAttrLiteralWs (str : String) : String :=
  String.ofList (str.toList.map
    (fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c))

/-- The body of an `[10] AttValue`, up to its closing quote `qch`.
Port of F* `parse_attr_value_body`. -/
def parseAttrValueBody (ents : EntityTable) (qch : Char) (s : Chars) (pos : Nat)
    (acc : List String) : Nat → PResult String
  | 0 => .err "attribute value too long" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated attribute value" pos
    else
      let ch := charAt s pos
      if ch == qch then .ok (String.join acc.reverse) (pos + 1)
      else if ch == '<' then
        -- AttValue excludes '<' unconditionally ([10] / §3.1).
        .err "attribute values exclude '<'" pos
      else if ch == '&' then
        match parseReference ents s (pos + 1) with
        | .err m p => .err m p
        | .ok decoded pos' => parseAttrValueBody ents qch s pos' (decoded :: acc) fuel
      else
        let stop := scanWhile (fun c => c != qch && c != '&' && c != '<') s pos (s.size - pos)
        if stop > pos then
          if !rangeCharsValid s pos stop then
            .err "invalid character in attribute value" pos
          else
            parseAttrValueBody ents qch s stop (normalizeAttrLiteralWs (sub s pos stop) :: acc) fuel
        else .err "unterminated attribute value" pos

/-- `[10] AttValue ::= '"' … '"' | "'" … "'"`. Port of F*
`parse_attr_value`. -/
def parseAttrValue (ents : EntityTable) (s : Chars) (pos : Nat) : PResult String :=
  if pos ≥ s.size then .err "expected attribute value" pos
  else
    let qch := charAt s pos
    if qch == '"' || qch == '\'' then
      parseAttrValueBody ents qch s (pos + 1) [] (s.size + 1)
    else .err "expected quote to start attribute value" pos

/-! ## `[41] Attribute` -/

/-- `[41] Attribute ::= Name Eq AttValue`. Port of F*
`parse_xml_attribute`. -/
def parseAttribute (ents : EntityTable) (s : Chars) (pos : Nat) : PResult Attribute :=
  match parseName s pos with
  | .err m p => .err m p
  | .ok name pos1 =>
    let pos2 := skipSpace s pos1
    match pchar '=' s pos2 with
    | .err m p => .err m p
    | .ok _ pos3 =>
      let pos4 := skipSpace s pos3
      match parseAttrValue ents s pos4 with
      | .err m p => .err m p
      | .ok value pos5 => .ok { name := name, value := value } pos5

/-- The attribute list of a start tag, enforcing **WFC: Unique Att
Spec**: no two attributes of one element may share a name.
Port of F* `parse_attributes`. -/
def parseAttributes (ents : EntityTable) (s : Chars) (pos : Nat) :
    Nat → PResult (List Attribute)
  | 0 => .ok [] pos
  | fuel + 1 =>
    if pos ≥ s.size then .ok [] pos
    else
      match skipSpace1 s pos with
      | .err _ _ => .ok [] pos
      | .ok _ pos1 =>
        if pos1 < s.size && isNameStartChar (charAt s pos1) then
          match parseAttribute ents s pos1 with
          | .err m p => .err m p
          | .ok attr pos2 =>
            match parseAttributes ents s pos2 fuel with
            | .err m p => .err m p
            | .ok attrs pos3 =>
              if hasAttr attr.name attrs then
                .err s!"duplicate attribute name '{attr.name}' (WFC: Unique Att Spec)" pos2
              else .ok (attr :: attrs) pos3
        else .ok [] pos1

/-! ## `[14] CharData` -/

/-- True when the literal `]]>` occurs anywhere in `[start, stop)`.
`[14] CharData` excludes it — it is legal only as a CDATA section's own
closing delimiter. Port of F* `bytes_have_cdata_close`. -/
def hasCdataClose (s : Chars) (start stop : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if start + 2 ≥ stop then false
    else if charAt s start == ']' && charAt s (start + 1) == ']' && charAt s (start + 2) == '>' then true
    else hasCdataClose s (start + 1) stop fuel

/-- Character data with `[67] Reference`s resolved, up to the next `<`.
Port of F* `parse_text_content`. -/
def parseTextContent (ents : EntityTable) (s : Chars) (pos : Nat)
    (acc : List String) : Nat → PResult String
  | 0 => .ok (String.join acc.reverse) pos
  | fuel + 1 =>
    if pos ≥ s.size then .ok (String.join acc.reverse) pos
    else
      let ch := charAt s pos
      if ch == '<' then .ok (String.join acc.reverse) pos
      else if ch == '&' then
        match parseReference ents s (pos + 1) with
        | .err m p => .err m p
        | .ok decoded pos' => parseTextContent ents s pos' (decoded :: acc) fuel
      else
        let stop := scanWhile (fun c => c != '<' && c != '&') s pos (s.size - pos)
        if stop > pos then
          if !rangeCharsValid s pos stop then
            .err "invalid character in text content" pos
          else if hasCdataClose s pos stop (stop - pos) then
            .err "text may not contain a literal ']]>' sequence" pos
          else parseTextContent ents s stop (sub s pos stop :: acc) fuel
        else .ok (String.join acc.reverse) pos

/-- A `[14] CharData` node. Fails on an empty run so the caller can
tell "no text here" from "text consumed". Port of F* `parse_xml_text`. -/
def parseText (ents : EntityTable) (s : Chars) (pos : Nat) : PResult Node :=
  match parseTextContent ents s pos [] (s.size + 1) with
  | .err m p => .err m p
  | .ok text pos' =>
    if text.isEmpty then .err "empty text node" pos else .ok (.text text) pos'

/-! ## `[15] Comment` -/

/-- True when `--` occurs anywhere in `str`.
Port of F* `bytes_have_double_dash`. -/
def hasDoubleDash (str : String) : Bool :=
  let rec go : List Char → Bool
    | a :: b :: rest => (a == '-' && b == '-') || go (b :: rest)
    | _ => false
  go str.toList

/-- The body of a comment, from `start`, up to its `-->`.
Port of F* `parse_comment_body`. -/
def parseCommentBody (s : Chars) (start pos : Nat) : Nat → PResult String
  | 0 => .err "unterminated comment" pos
  | fuel + 1 =>
    if pos + 2 < s.size &&
       charAt s pos == '-' && charAt s (pos + 1) == '-' && charAt s (pos + 2) == '>' then
      .ok (sub s start pos) (pos + 3)
    else if pos < s.size then
      if !isXmlChar (charAt s pos) then .err "invalid character in comment" pos
      else parseCommentBody s start (pos + 1) fuel
    else .err "unterminated comment" pos

/-- `[15] Comment ::= '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'`
— so `--` may not occur in the body, and the body may not end in `-`
(that would make the closing delimiter need a third dash).
Port of F* `parse_xml_comment`. -/
def parseComment (s : Chars) (pos : Nat) : PResult Node :=
  match pstring "<!--" s pos with
  | .err m p => .err m p
  | .ok _ pos1 =>
    match parseCommentBody s pos1 pos1 (s.size + 1) with
    | .err m p => .err m p
    | .ok text pos2 =>
      if hasDoubleDash text || text.toList.getLast? == some '-' then
        .err "comment must not contain '--' or end in '-'" pos1
      else .ok (.comment text) pos2

/-! ## `[18] CDSect` -/

/-- The content of a CDATA section, up to its `]]>`.
Port of F* `parse_cdata_body`. -/
def parseCdataBody (s : Chars) (start pos : Nat) : Nat → PResult String
  | 0 => .err "unterminated CDATA section" pos
  | fuel + 1 =>
    if pos + 2 < s.size &&
       charAt s pos == ']' && charAt s (pos + 1) == ']' && charAt s (pos + 2) == '>' then
      .ok (sub s start pos) (pos + 3)
    else if pos < s.size then
      if !isXmlChar (charAt s pos) then .err "invalid character in CDATA section" pos
      else parseCdataBody s start (pos + 1) fuel
    else .err "unterminated CDATA section" pos

/-- `[18] CDSect ::= CDStart CData CDEnd`. Port of F* `parse_xml_cdata`. -/
def parseCdata (s : Chars) (pos : Nat) : PResult Node :=
  match pstring "<![CDATA[" s pos with
  | .err m p => .err m p
  | .ok _ pos1 =>
    match parseCdataBody s pos1 pos1 (s.size + 1) with
    | .err m p => .err m p
    | .ok text pos2 => .ok (.cdata text) pos2

/-! ## `[16] PI` -/

/-- The data of a processing instruction, up to its `?>`.
Port of F* `collect_pi_body`. -/
def parsePiBody (s : Chars) (start pos : Nat) : Nat → PResult String
  | 0 => .err "unterminated processing instruction" pos
  | fuel + 1 =>
    if pos + 1 < s.size && charAt s pos == '?' && charAt s (pos + 1) == '>' then
      .ok (sub s start pos) (pos + 2)
    else if pos + 1 < s.size then
      if !isXmlChar (charAt s pos) then
        .err "invalid character in processing instruction" pos
      else parsePiBody s start (pos + 1) fuel
    else .err "unterminated processing instruction" pos

/-- `[16] PI ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'`.

A `[17] PITarget` is required, and the reserved target `xml` (any case)
is rejected here — that token may be consumed only by `[23] XMLDecl`,
at the literal start of the document, so an XML-declaration-shaped token
in the prolog, in content, or in the epilog fails as a PI and rejects
the document. `S` is required between the target and the data unless
`?>` follows the target immediately; the data excludes that separating
whitespace, per the DOM/XPath string-value convention.
Port of F* `parse_xml_pi`. -/
def parsePi (s : Chars) (pos : Nat) : PResult Node :=
  match pstring "<?" s pos with
  | .err m p => .err m p
  | .ok _ pos1 =>
    match parseName s pos1 with
    | .err m p => .err m p
    | .ok target pos2 =>
      if isXmlTargetNameCI target then
        .err "PI target name 'xml' (any case) is reserved" pos1
      else if pos2 + 1 < s.size && charAt s pos2 == '?' && charAt s (pos2 + 1) == '>' then
        .ok (.pi target "") (pos2 + 2)
      else
        match skipSpace1 s pos2 with
        | .err _ _ => .err "S after PITarget is required" pos2
        | .ok _ posData =>
          match parsePiBody s posData posData (s.size + 1) with
          | .err m p => .err m p
          | .ok data pos3 => .ok (.pi target data) pos3

/-! ## `[23] XMLDecl` -/

/-- `[26] VersionNum ::= '1.' [0-9]+` (the Fifth Edition's relaxed
lexicon). Port of F* `is_version_num`. -/
def isVersionNum (str : String) : Bool :=
  match str.toList with
  | '1' :: '.' :: rest => !rest.isEmpty && rest.all isDecDigit
  | _ => false

/-- `[81] EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')*`.
Port of F* `is_enc_name`. -/
def isEncName (str : String) : Bool :=
  let first (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
  let rest (c : Char) : Bool := first c || isDecDigit c || c == '.' || c == '_' || c == '-'
  match str.toList with
  | [] => false
  | c :: cs => first c && cs.all rest

/-- `[32] SDDecl` value — lowercase `yes` or `no` only; `"YES"`
rejects. Port of F* `is_sd_value`. -/
def isSdValue (str : String) : Bool := str == "yes" || str == "no"

/-- Try `S name Eq AttValue` at `pos`, requiring the literal `name`.
Returns the value and the position after the whole pseudo-attribute, or
`none` with the position untouched so the caller can try the next
production from the same point. Port of F* `try_pseudo_attr`. -/
def tryPseudoAttr (name : String) (s : Chars) (pos : Nat) : Option (String × Nat) :=
  match skipSpace1 s pos with
  | .err _ _ => none
  | .ok _ pos1 =>
    match pstring name s pos1 with
    | .err _ _ => none
    | .ok _ pos2 =>
      let pos3 := skipSpace s pos2
      match pchar '=' s pos3 with
      | .err _ _ => none
      | .ok _ pos4 =>
        let pos5 := skipSpace s pos4
        match parseAttrValue [] s pos5 with
        | .err _ _ => none
        | .ok v pos6 => some (v, pos6)

/-- `S? '?>'` — anything left over (an unknown, duplicate or
out-of-order pseudo-attribute) makes the whole declaration fail.
Port of F* `finish_xml_decl`. -/
def finishXmlDecl (s : Chars) (pos : Nat) (d : XmlDecl) : PResult XmlDecl :=
  match pstring "?>" s (skipSpace s pos) with
  | .err m p => .err m p
  | .ok _ pos2 => .ok d pos2

/-- `[23] XMLDecl ::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'`
as a strict ordered walk. Port of F* `parse_xml_declaration`. -/
def parseXmlDecl (s : Chars) (pos : Nat) : PResult XmlDecl :=
  match pstring "<?xml" s pos with
  | .err m p => .err m p
  | .ok _ pos0 =>
    match skipSpace1 s pos0 with
    | .err m p => .err m p
    | .ok _ pos1 =>
      match pstring "version" s pos1 with
      | .err m p => .err m p
      | .ok _ pos2 =>
        let pos3 := skipSpace s pos2
        match pchar '=' s pos3 with
        | .err m p => .err m p
        | .ok _ pos4 =>
          let pos5 := skipSpace s pos4
          match parseAttrValue [] s pos5 with
          | .err m p => .err m p
          | .ok vernum pos6 =>
            if !isVersionNum vernum then .err "illegal VersionNum" pos5
            else
              match tryPseudoAttr "encoding" s pos6 with
              | some (encval, pos7) =>
                if !isEncName encval then .err "illegal EncName" pos7
                else
                  match tryPseudoAttr "standalone" s pos7 with
                  | some (sdval, pos8) =>
                    if !isSdValue sdval then .err "illegal SDDecl value" pos8
                    else finishXmlDecl s pos8
                      { version := vernum, encoding := some encval, standalone := some sdval }
                  | none => finishXmlDecl s pos7
                      { version := vernum, encoding := some encval, standalone := none }
              | none =>
                match tryPseudoAttr "standalone" s pos6 with
                | some (sdval, pos7) =>
                  if !isSdValue sdval then .err "illegal SDDecl value" pos7
                  else finishXmlDecl s pos7
                    { version := vernum, encoding := none, standalone := some sdval }
                | none => finishXmlDecl s pos6
                    { version := vernum, encoding := none, standalone := none }

/-! ## `[39] element` -/

mutual

/-- `[43] content` — the children of an element, up to its `[42] ETag`.
Accumulates in reverse and reverses once, as the F* does (the F* rewrote
this to be accumulator-based because a per-sibling stack frame blew the
native stack on flat RDF/XML documents). Port of F* `parse_children`. -/
def parseChildren (ents : EntityTable) (s : Chars) (pos : Nat)
    (acc : List Node) : Nat → PResult (List Node)
  | 0 => .ok acc.reverse pos
  | fuel + 1 =>
    if pos ≥ s.size then .ok acc.reverse pos
    else if charAt s pos == '<' then
      if pos + 1 < s.size then
        let ch2 := charAt s (pos + 1)
        if ch2 == '/' then .ok acc.reverse pos
        else if ch2 == '!' then
          -- Comment or CDATA section. The F* tries the comment parser
          -- first and falls back to CDATA, reporting the CDATA failure;
          -- picking the message by which delimiter is actually present
          -- changes the MESSAGE only, never the accept/reject verdict.
          if peekLit "<!--" s pos then
            match parseComment s pos with
            | .err m p => .err m p
            | .ok node pos' => parseChildren ents s pos' (node :: acc) fuel
          else
            match parseCdata s pos with
            | .err m p => .err m p
            | .ok node pos' => parseChildren ents s pos' (node :: acc) fuel
        else if ch2 == '?' then
          match parsePi s pos with
          | .err m p => .err m p
          | .ok node pos' => parseChildren ents s pos' (node :: acc) fuel
        else
          match parseElement ents s pos fuel with
          | .err m p => .err m p
          | .ok node pos' => parseChildren ents s pos' (node :: acc) fuel
      else .err "unexpected end after '<'" pos
    else
      -- Character data. This is the ONE place the port deliberately
      -- departs from `Parser.XML.fst`'s behaviour, for two reasons.
      --
      -- The F* calls `parse_xml_text`, which conflates two outcomes
      -- into one failure: "there is no text here" (the decoded run is
      -- empty) and "the text is bad" (a malformed character
      -- reference, a character outside `[2] Char`, a literal `]]>`).
      -- `parse_children` then discards BOTH alike
      -- (`ParseFail _ _ -> ParseOk`).
      --
      -- 1. DIAGNOSTIC. A real content error surfaced later as a
      --    confusing "expected '</'". Calling `parseTextContent`
      --    directly propagates it with its own message. This half
      --    changes no verdict: where the F* discarded the error it
      --    then required `[42] ETag` at `pos`, and `pos` cannot be `<`
      --    here (that case is handled above), so `</` never matched
      --    and the document rejected either way.
      --
      -- 2. VERDICT, and this half DOES change one. The F* treats a run
      --    that CONSUMED input but decoded to nothing — content that
      --    is exactly one reference to an entity whose replacement
      --    text is empty, `<!ENTITY e "">` with `<doc>&e;</doc>` — as
      --    a failure, stops collecting children at the `&`, and then
      --    rejects the document for want of an end tag. Those
      --    documents are well-formed, and the W3C conformance suite
      --    marks them valid: `xmltest/valid/sa/023.xml`, `085.xml` and
      --    `086.xml` are rejected by the F* parser and accepted here.
      --    Measured 2026-08-22 by running both parsers over the same
      --    files; those three are the only disagreement on the 306
      --    files of `xmltest/valid/sa` and `xmltest/not-wf/sa`.
      --
      -- The empty run is skipped rather than recorded: an expansion
      -- that yields no characters contributes no `[14] CharData` to
      -- the infoset, so emitting an empty text node would both
      -- misreport the infoset and break the serialiser round-trip
      -- (`<doc></doc>` re-parses with no child at all).
      match parseTextContent ents s pos [] (s.size + 1) with
      | .err m p => .err m p
      | .ok text pos' =>
        if pos' == pos then .ok acc.reverse pos
        else if text.isEmpty then parseChildren ents s pos' acc fuel
        else parseChildren ents s pos' (.text text :: acc) fuel

/-- `[39] element ::= EmptyElemTag | STag content ETag`, enforcing
**WFC: Element Type Match** — the `[42] ETag` name must equal the
`[40] STag` name. Port of F* `parse_xml_element`. -/
def parseElement (ents : EntityTable) (s : Chars) (pos : Nat) :
    Nat → PResult Node
  | 0 => .err "element nesting too deep (out of fuel)" pos
  | fuel + 1 =>
    match pchar '<' s pos with
    | .err m p => .err m p
    | .ok _ pos1 =>
      match parseName s pos1 with
      | .err m p => .err m p
      | .ok tag pos2 =>
        match parseAttributes ents s pos2 (s.size + 1) with
        | .err m p => .err m p
        | .ok attrs pos3 =>
          let pos4 := skipSpace s pos3
          if peekLit "/>" s pos4 then
            -- [44] EmptyElemTag
            .ok (.element tag attrs []) (pos4 + 2)
          else
            match pchar '>' s pos4 with
            | .err m p => .err m p
            | .ok _ pos5 =>
              match parseChildren ents s pos5 [] fuel with
              | .err m p => .err m p
              | .ok children pos6 =>
                match pstring "</" s pos6 with
                | .err m p => .err m p
                | .ok _ pos7 =>
                  match parseName s pos7 with
                  | .err m p => .err m p
                  | .ok closeTag pos8 =>
                    if closeTag != tag then
                      .err s!"closing tag '</{closeTag}>' does not match opening '<{tag}>' (WFC: Element Type Match)" pos7
                    else
                      match pchar '>' s (skipSpace s pos8) with
                      | .err m p => .err m p
                      | .ok _ pos10 => .ok (.element tag attrs children) pos10

end

/-! ## `[28] doctypedecl` and the internal subset -/

/-- Consume a quoted literal whose opening quote is already consumed.
Port of F* `skip_quoted_literal`. -/
def skipQuotedLiteral (s : Chars) (pos : Nat) (q : Char) : Nat → PResult Unit
  | 0 => .err "unterminated literal" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated literal" pos
    else if charAt s pos == q then .ok () (pos + 1)
    else skipQuotedLiteral s (pos + 1) q fuel

/-- Consume up to and including the next top-level `>`, treating quoted
literals opaquely so a `>` inside one does not terminate the
declaration. Port of F* `skip_decl_to_gt`. -/
def skipDeclToGt (s : Chars) (pos : Nat) : Nat → PResult Unit
  | 0 => .err "unterminated markup declaration" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated markup declaration" pos
    else
      let ch := charAt s pos
      if ch == '>' then .ok () (pos + 1)
      else if ch == '"' || ch == '\'' then
        match skipQuotedLiteral s (pos + 1) ch fuel with
        | .err m p => .err m p
        | .ok _ pos' => skipDeclToGt s pos' fuel
      else skipDeclToGt s (pos + 1) fuel

/-- Read the raw characters of a `[9] EntityValue` verbatim, up to the
closing quote — references inside are NOT expanded here; that happens
lazily at the reference site. Port of F* `read_entity_value_raw`. -/
def readEntityValueRaw (s : Chars) (start pos : Nat) (q : Char) :
    Nat → PResult String
  | 0 => .err "unterminated entity value" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated entity value" pos
    else if charAt s pos == q then .ok (sub s start pos) (pos + 1)
    else readEntityValueRaw s start (pos + 1) q fuel

/-- Consume a `[69] PEReference` (not expanded — Stage A). `pos` is just
after the `%`. Port of F* `skip_pe_reference`. -/
def skipPeReference (s : Chars) (pos : Nat) : Nat → PResult Unit
  | 0 => .err "unterminated parameter-entity reference" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated parameter-entity reference" pos
    else if charAt s pos == ';' then .ok () (pos + 1)
    else skipPeReference s (pos + 1) fuel

-- `parseEntityDecl` used to live here. It now sits below
-- `parseExternalID`, which it needs.

/-! ### `[52] AttlistDecl` — reading out the `[54] AttType` = `ID` pairs

This scanner runs OVER the region a `<!ATTLIST … >` occupies and never
moves the parser position or changes accept/reject: it only reads out
ID pairs. Any structural surprise stops it early (fewer pairs), so a
malformed ATTLIST can lose IDs but can never corrupt the
well-formedness verdict. -/

/-- Skip whitespace up to (not past) `gt`. Port of F* `skip_ws_to`. -/
def skipWsTo (s : Chars) (pos gt : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    if pos ≥ gt then pos
    else if isXmlSpace (charAt s pos) then skipWsTo s (pos + 1) gt fuel
    else pos

/-- From a `(` at `pos`, skip to just after the matching `)`.
Port of F* `skip_parens_to`. -/
def skipParensTo (s : Chars) (pos gt depth : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    if pos ≥ gt then pos
    else
      let c := charAt s pos
      if c == '(' then skipParensTo s (pos + 1) gt (depth + 1) fuel
      else if c == ')' then
        if depth ≤ 1 then pos + 1 else skipParensTo s (pos + 1) gt (depth - 1) fuel
      else skipParensTo s (pos + 1) gt depth fuel

/-- From just after an opening quote `q`, skip to just after its closer.
Port of F* `skip_quoted_to`. -/
def skipQuotedTo (s : Chars) (pos gt : Nat) (q : Char) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    if pos ≥ gt then pos
    else if charAt s pos == q then pos + 1
    else skipQuotedTo s (pos + 1) gt q fuel

/-- Skip a `[60] DefaultDecl`: `#REQUIRED` | `#IMPLIED` |
`(('#FIXED' S)? AttValue)`. Port of F* `skip_default_decl`. -/
def skipDefaultDecl (s : Chars) (pos gt : Nat) : Nat :=
  if pos ≥ gt then pos
  else
    let c := charAt s pos
    if c == '#' then
      match parseName s (pos + 1) with
      | .err _ _ => pos + 1
      | .ok kw p2 =>
        if kw == "FIXED" then
          let p3 := skipWsTo s p2 gt gt
          if p3 < gt && (charAt s p3 == '"' || charAt s p3 == '\'') then
            skipQuotedTo s (p3 + 1) gt (charAt s p3) gt
          else p2
        else p2
    else if c == '"' || c == '\'' then skipQuotedTo s (pos + 1) gt c gt
    else pos

/-- Iterate over the `[53] AttDef`s of one ATTLIST for element `elem`,
collecting the pairs whose `[54] AttType` is exactly `ID` — not `IDREF`
or `IDREFS`. Port of F* `scan_attdefs`. -/
def scanAttDefs (s : Chars) (pos gt : Nat) (elem : String)
    (acc : List (String × String)) : Nat → List (String × String)
  | 0 => acc
  | fuel + 1 =>
    let pos := skipWsTo s pos gt gt
    if pos ≥ gt || charAt s pos == '>' then acc
    else
      match parseName s pos with
      | .err _ _ => acc
      | .ok attr p2 =>
        let p2 := skipWsTo s p2 gt gt
        if p2 < gt && charAt s p2 == '(' then
          -- [59] Enumeration — never ID.
          let p3 := skipParensTo s p2 gt 0 gt
          let p4 := skipDefaultDecl s (skipWsTo s p3 gt gt) gt
          scanAttDefs s p4 gt elem acc fuel
        else
          match parseName s p2 with
          | .err _ _ => acc
          | .ok typ p3 =>
            let (p3b, isId) :=
              if typ == "NOTATION" then
                let pn := skipWsTo s p3 gt gt
                if pn < gt && charAt s pn == '(' then (skipParensTo s pn gt 0 gt, false)
                else (p3, false)
              else (p3, typ == "ID")
            let p4 := skipDefaultDecl s (skipWsTo s p3b gt gt) gt
            scanAttDefs s p4 gt elem (if isId then (elem, attr) :: acc else acc) fuel

/-- Scan a `<!ATTLIST … >` region `[pos, gt)`; `pos` is just after the
`<!ATTLIST` keyword. Port of F* `scan_attlist_ids`. -/
def scanAttlistIds (s : Chars) (pos gt : Nat) (acc : List (String × String)) :
    List (String × String) :=
  match parseName s (skipWsTo s pos gt gt) with
  | .err _ _ => acc
  | .ok elem p1 => scanAttDefs s p1 gt elem acc gt

/-! ### The internal subset's markup declarations, parsed rather than
skipped

`parseIntSubset` used to step over `<!ELEMENT`, `<!ATTLIST`,
`<!NOTATION` and anything else beginning `<!` by scanning to the next
`>` outside quotes. That accepts a malformed declaration, and the W3C
conformance suite is largely made of them: `<!ENTITY foo PUBLIC "id">`
with no system literal, a comment inside a declaration, an ATTLIST
whose default is a bare token, an `<![INCLUDE[ ]]>` in the internal
subset. 674 `not-wf` documents were accepted for that one reason
(measured 2026-08-23).

These productions are the grammar, and they REJECT. They do not build
a DTD model — this parser stays non-validating, so an `<!ELEMENT`
declaration is checked for shape and then discarded. -/

/-- `[11] SystemLiteral ::= ('"' [^"]* '"') | ("'" [^']* "'")`. -/
def parseSystemLiteral (s : Chars) (pos : Nat) : PResult String :=
  if pos ≥ s.size then .err "expected a system literal" pos
  else
    let q := charAt s pos
    if q != '"' && q != '\'' then .err "expected a quoted system literal" pos
    else
      let rec go (i : Nat) : Nat → PResult String
        | 0 => .err "unterminated system literal" i
        | f + 1 =>
            if i ≥ s.size then .err "unterminated system literal" i
            else if charAt s i == q then .ok (sub s (pos + 1) i) (i + 1)
            else go (i + 1) f
      go (pos + 1) (s.size + 1)

/-- `[13] PubidChar`. -/
def isPubidChar (c : Char) : Bool :=
  c == ' ' || c == '\r' || c == '\n' ||
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') ||
  "-'()+,./:=?;!*#@$_%".toList.contains c

/-- `[12] PubidLiteral`. Its character repertoire is RESTRICTED, and a
    character outside it is a well-formedness error rather than a
    curiosity. -/
def parsePubidLiteral (s : Chars) (pos : Nat) : PResult String :=
  match parseSystemLiteral s pos with
  | .err m p => .err m p
  | .ok lit p' =>
      if lit.toList.all isPubidChar then .ok lit p'
      else .err "character not permitted in a public identifier" pos

/-- `[75] ExternalID ::= 'SYSTEM' S SystemLiteral
                        | 'PUBLIC' S PubidLiteral S SystemLiteral`.
    The PUBLIC form REQUIRES the system literal; without it the
    declaration is malformed, which is what `not-wf-sa-054` checks. -/
def parseExternalIDSys (s : Chars) (pos : Nat) : PResult String :=
  if peekLit "SYSTEM" s pos then
    match skipSpace1 s (pos + 6) with
    | .err m p => .err m p
    | .ok _ p1 => match parseSystemLiteral s p1 with
      | .err m p => .err m p
      | .ok sys p2 => .ok sys p2
  else if peekLit "PUBLIC" s pos then
    match skipSpace1 s (pos + 6) with
    | .err m p => .err m p
    | .ok _ p1 => match parsePubidLiteral s p1 with
      | .err m p => .err m p
      | .ok _ p2 => match skipSpace1 s p2 with
        | .err m p => .err m p
        | .ok _ p3 => match parseSystemLiteral s p3 with
          | .err m p => .err m p
          | .ok sys p4 => .ok sys p4
  else .err "expected SYSTEM or PUBLIC" pos

/-- The same production with the system identifier discarded. -/
def parseExternalID (s : Chars) (pos : Nat) : PResult Unit :=
  match parseExternalIDSys s pos with
  | .err m p => .err m p
  | .ok _ p  => .ok () p

/-- `[83] PublicID ::= 'PUBLIC' S PubidLiteral` — the NOTATION-only
    form, which takes no system literal. -/
def parseNotationID (s : Chars) (pos : Nat) : PResult Unit :=
  if peekLit "PUBLIC" s pos then
    match skipSpace1 s (pos + 6) with
    | .err m p => .err m p
    | .ok _ p1 => match parsePubidLiteral s p1 with
      | .err m p => .err m p
      | .ok _ p2 =>
          -- The system literal is OPTIONAL here, unlike in ExternalID.
          let p3 := skipSpace s p2
          if p3 < s.size && (charAt s p3 == '"' || charAt s p3 == '\'') then
            match parseSystemLiteral s p3 with
            | .err m p => .err m p
            | .ok _ p4 => .ok () p4
          else .ok () p2
  else parseExternalID s pos

/-- Require `S? '>'` — the tail every markup declaration ends with. A
    declaration that has anything else left is malformed. -/
def declEnd (s : Chars) (pos : Nat) : PResult Unit :=
  let p := skipSpace s pos
  if p < s.size && charAt s p == '>' then .ok () (p + 1)
  else .err "expected '>' at the end of a markup declaration" p

/-- `[7] Nmtoken ::= (NameChar)+`. -/
def parseNmtoken (s : Chars) (pos : Nat) : PResult Unit :=
  let e := scanNameEnd s pos (s.size - pos + 1)
  if e > pos then .ok () e else .err "expected an Nmtoken" pos

/-- The loop of `parenList`. Fuel-based like the rest of this parser:
    `PResult` has no `Inhabited` instance, so a `partial def` cannot
    return one, and adding an instance to a shared result type to buy
    one loop is the wrong trade. -/
def parenListGo (item : Chars → Nat → PResult Unit) (conn : Char)
    (s : Chars) (i : Nat) : Nat → PResult Unit
  | 0 => .err "list too long" i
  | f + 1 =>
    let j := skipSpace s i
    match item s j with
    | .err m p => .err m p
    | .ok _ k =>
        let k2 := skipSpace s k
        if k2 < s.size && charAt s k2 == conn then parenListGo item conn s (k2 + 1) f
        else if k2 < s.size && charAt s k2 == ')' then .ok () (k2 + 1)
        else .err "expected a connector or ')'" k2

/-- A parenthesised list of `item`s separated by ONE connector,
    consistently: `'(' S? item (S? conn S? item)* S? ')'`. Used for the
    ATTLIST enumeration forms, where the connector is always `|`. -/
def parenList (item : Chars → Nat → PResult Unit) (conn : Char)
    (s : Chars) (pos : Nat) : PResult Unit :=
  if pos ≥ s.size || charAt s pos != '(' then .err "expected '('" pos
  else parenListGo item conn s (pos + 1) (s.size + 1)

/-! #### `[47]–[51]` content models

A content model is a GRAMMAR, not a balanced-paren blob. The suite
tests it directly: `(a,b,c)` is not an attribute enumeration (those
take `|`), `((root) ?)` puts whitespace before an occurrence indicator
where the production allows none, and `(foo, bar? foo)` omits a
connector. Stepping over the parentheses accepted all three. -/

mutual

/-- `[48] cp ::= (Name | choice | seq) ('?' | '*' | '+')?`. The
    occurrence indicator binds IMMEDIATELY — no whitespace before
    it. -/
def parseCp (s : Chars) (pos : Nat) : Nat → PResult Unit
  | 0 => .err "content model too deep" pos
  | fuel + 1 =>
  let after :=
    if pos < s.size && charAt s pos == '(' then parseChoiceOrSeq s pos fuel
    else match parseName s pos with
      | .err m p => .err m p
      | .ok _ p' => .ok () p'
  match after with
  | .err m p => .err m p
  | .ok _ p =>
      if p < s.size && (charAt s p == '?' || charAt s p == '*' || charAt s p == '+')
      then .ok () (p + 1) else .ok () p

/-- The loop of `parseChoiceOrSeq`: one member, then either the SAME
    connector again or the closing paren. -/
def cpListGo (s : Chars) (i : Nat) (conn : Option Char) : Nat → PResult Unit
  | 0 => .err "content model too long" i
  | fuel + 1 =>
  let j := skipSpace s i
  match parseCp s j fuel with
  | .err m p => .err m p
  | .ok _ k =>
      let k2 := skipSpace s k
      if k2 ≥ s.size then .err "unterminated content model" k2
      else
        let c := charAt s k2
        if c == ')' then .ok () (k2 + 1)
        else if c == '|' || c == ',' then
          match conn with
          | some c0 =>
              if c0 == c then cpListGo s (k2 + 1) conn fuel
              else .err "a content model mixes ',' and '|'" k2
          | none => cpListGo s (k2 + 1) (some c) fuel
        else .err "expected ',', '|' or ')' in a content model" k2

/-- `[49] choice` / `[50] seq`: one `(`-group whose members are joined
    by a SINGLE connector, `|` throughout or `,` throughout. -/
def parseChoiceOrSeq (s : Chars) (pos : Nat) : Nat → PResult Unit
  | 0 => .err "content model too deep" pos
  | fuel + 1 =>
  if pos ≥ s.size || charAt s pos != '(' then .err "expected '('" pos
  else cpListGo s (pos + 1) none fuel

end

/-- The name list of a mixed content model. -/
def mixedGo (s : Chars) (i : Nat) (n : Nat) : Nat → PResult Unit
  | 0 => .err "mixed content model too long" i
  | f + 1 =>
  let j := skipSpace s i
  if j ≥ s.size then .err "unterminated mixed content model" j
  else if charAt s j == '|' then
    let k := skipSpace s (j + 1)
    match parseName s k with
    | .err m p => .err m p
    | .ok _ k' => mixedGo s k' (n + 1) f
  else if charAt s j == ')' then
    -- With NAMES the trailing `*` is required; with none it is
    -- OPTIONAL — `(#PCDATA)` and `(#PCDATA)*` are both in [51], and
    -- rejecting the second broke eight documents the suite calls
    -- valid.
    (if j + 1 < s.size && charAt s (j + 1) == '*' then .ok () (j + 2)
     else if n == 0 then .ok () (j + 1)
     else .err "a mixed content model with names must end ')*'" j)
  else .err "expected '|' or ')' in a mixed content model" j

/-- `[51] Mixed ::= '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*'
                  | '(' S? '#PCDATA' S? ')'`. With one or more names
    the trailing `*` is REQUIRED. -/
def parseMixed (s : Chars) (pos : Nat) : PResult Unit :=
  match pchar '(' s pos with
  | .err m p => .err m p
  | .ok _ p1 =>
      let p2 := skipSpace s p1
      match pstring "#PCDATA" s p2 with
      | .err m p => .err m p
      | .ok _ p3 =>
          mixedGo s p3 0 (s.size + 1)

/-- `[46] contentspec ::= 'EMPTY' | 'ANY' | Mixed | children`. -/
def parseContentSpec (s : Chars) (pos : Nat) : PResult Unit :=
  if peekLit "EMPTY" s pos then .ok () (pos + 5)
  else if peekLit "ANY" s pos then .ok () (pos + 3)
  else if pos < s.size && charAt s pos == '(' then
    let p := skipSpace s (pos + 1)
    if peekLit "#PCDATA" s p then parseMixed s pos
    else
      -- `[47] children ::= (choice | seq) ('?' | '*' | '+')?`
      match parseChoiceOrSeq s pos (s.size + 1) with
      | .err m q => .err m q
      | .ok _ q =>
          if q < s.size && (charAt s q == '?' || charAt s q == '*' || charAt s q == '+')
          then .ok () (q + 1) else .ok () q
  else .err "expected a content specification" pos

/-- `[45] elementdecl ::= '<!ELEMENT' S Name S contentspec S? '>'`,
    with `[46] contentspec ::= 'EMPTY' | 'ANY' | Mixed | children`. -/
def parseElementDecl (s : Chars) (pos : Nat) : PResult Unit :=
  match pstring "<!ELEMENT" s pos with
  | .err m p => .err m p
  | .ok _ p1 => match skipSpace1 s p1 with
    | .err m p => .err m p
    | .ok _ p2 => match parseName s p2 with
      | .err m p => .err m p
      | .ok _ p3 => match skipSpace1 s p3 with
        | .err m p => .err m p
        | .ok _ p4 =>
            match parseContentSpec s p4 with
            | .err m p => .err m p
            | .ok _ p5 => declEnd s p5

/-- The ten `[54] AttType` forms. `NOTATION` takes an enumeration. -/
def parseAttType (s : Chars) (pos : Nat) : PResult Unit :=
  let simple := ["CDATA", "IDREFS", "IDREF", "ID", "ENTITIES", "ENTITY",
                 "NMTOKENS", "NMTOKEN"]
  match simple.find? (fun k => peekLit k s pos) with
  | some k => .ok () (pos + k.length)
  | none =>
      if peekLit "NOTATION" s pos then
        -- `[58] NotationType`: a `|`-separated list of NAMES.
        match skipSpace1 s (pos + 8) with
        | .err m p => .err m p
        | .ok _ p1 =>
            parenList (fun s' i => match parseName s' i with
              | .err m p => .err m p
              | .ok _ p' => .ok () p') '|' s p1
      else if pos < s.size && charAt s pos == '(' then
        -- `[59] Enumeration`: a `|`-separated list of Nmtokens. A
        -- COMMA-separated one is an SGML-ism, not XML (not-wf
        -- `attlist03`).
        parenList parseNmtoken '|' s pos
      else .err "expected an attribute type" pos

/-- `[60] DefaultDecl ::= '#REQUIRED' | '#IMPLIED'
                        | (('#FIXED' S)? AttValue)`. A BARE token is
    NOT a default, which is what `not-wf-sa-059` checks. -/
def parseDefaultDecl (s : Chars) (pos : Nat) : PResult Unit :=
  if peekLit "#REQUIRED" s pos then .ok () (pos + 9)
  else if peekLit "#IMPLIED" s pos then .ok () (pos + 8)
  else
    let p := if peekLit "#FIXED" s pos then
        match skipSpace1 s (pos + 6) with
        | .err _ _ => pos
        | .ok _ p' => p'
      else pos
    if p < s.size && (charAt s p == '"' || charAt s p == '\'') then
      match skipQuotedLiteral s (p + 1) (charAt s p) (s.size + 1) with
      | .err m q => .err m q
      | .ok _ p' => .ok () p'
    else .err "expected #REQUIRED, #IMPLIED, #FIXED or a quoted default" p

/-- `[52] AttlistDecl ::= '<!ATTLIST' S Name AttDef* S? '>'`. -/
def parseAttlistDecl (s : Chars) (pos : Nat) : PResult Unit :=
  match pstring "<!ATTLIST" s pos with
  | .err m p => .err m p
  | .ok _ p1 => match skipSpace1 s p1 with
    | .err m p => .err m p
    | .ok _ p2 => match parseName s p2 with
      | .err m p => .err m p
      | .ok _ p3 =>
          let rec defs (i : Nat) : Nat → PResult Unit
            | 0 => .err "attribute list too long" i
            | f + 1 =>
                let j := skipSpace s i
                if j < s.size && charAt s j == '>' then .ok () (j + 1)
                else if j == i then
                  .err "expected whitespace before an attribute definition" i
                else match parseName s j with
                  | .err m p => .err m p
                  | .ok _ k1 => match skipSpace1 s k1 with
                    | .err m p => .err m p
                    | .ok _ k2 => match parseAttType s k2 with
                      | .err m p => .err m p
                      | .ok _ k3 => match skipSpace1 s k3 with
                        | .err m p => .err m p
                        | .ok _ k4 => match parseDefaultDecl s k4 with
                          | .err m p => .err m p
                          | .ok _ k5 => defs k5 f
          defs p3 (s.size + 1)

/-- `[82] NotationDecl ::= '<!NOTATION' S Name S (ExternalID | PublicID)
                           S? '>'`. -/
def parseNotationDecl (s : Chars) (pos : Nat) : PResult Unit :=
  match pstring "<!NOTATION" s pos with
  | .err m p => .err m p
  | .ok _ p1 => match skipSpace1 s p1 with
    | .err m p => .err m p
    | .ok _ p2 => match parseName s p2 with
      | .err m p => .err m p
      | .ok _ p3 => match skipSpace1 s p3 with
        | .err m p => .err m p
        | .ok _ p4 => match parseNotationID s p4 with
          | .err m p => .err m p
          | .ok _ p5 => declEnd s p5


/-- `[70] EntityDecl ::= GEDecl | PEDecl`,
    `[71] GEDecl ::= '<!ENTITY' S Name S EntityDef S? '>'`,
    `[72] PEDecl ::= '<!ENTITY' S '%' S Name S PEDef S? '>'`,
    `[73] EntityDef ::= EntityValue | (ExternalID NDataDecl?)`,
    `[74] PEDef ::= EntityValue | ExternalID`,
    `[76] NDataDecl ::= S 'NDATA' S Name`.

    The previous version SKIPPED TO THE NEXT `>` for every shape but a
    quoted entity value, so the whole of [73]–[76] went unchecked and
    the following were all accepted as well-formed:

      * `<!ENTITY foo PUBLIC "some public id">` — [75] PUBLIC requires
        a SystemLiteral after the PubidLiteral (`not-wf-sa-054`);
      * `<!ENTITY e "whatever" -- a comment -->` — a declaration ends
        at `S? '>'` and nothing else (`not-wf-sa-057`);
      * `<!ENTITY e PUBLIC "whatever""e.ent">` — [75] requires the
        space between the two literals (`not-wf-sa-061`);
      * `<!ENTITY foo SYSTEM "foo.eps"NDATA eps>` — [76] begins with
        `S` (`not-wf-sa-069`, `o-p76fail1`);
      * `<!ENTITY %pe "…">` — [72] requires the space after `%`
        (`o-p72fail2`);
      * `<!ENTITY ge CDATA "…">` — `CDATA` is not an [73] EntityDef
        (`o-p73fail1`);
      * `<!ENTITY % pe SYSTEM "nop.ent" NDATA unknot>` — [74] PEDef
        admits no NDataDecl (`o-p74fail1`);
      * `<!ENTITY ent PUBLIC"PublicID" "nop.ent">` — [75] requires the
        space after `PUBLIC` (`o-p75fail1`).

    Every one of those is a document the parser said YES to, which is
    the direction that matters: a well-formedness checker that accepts
    malformed input reports nothing, while one that rejects valid
    input at least announces itself. -/
def parseEntityDecl (s : Chars) (pos : Nat) (ents : EntityTable) :
    PResult EntityTable :=
  match pstring "<!ENTITY" s pos with
  | .err m p => .err m p
  | .ok _ p1 =>
    match skipSpace1 s p1 with
    | .err m p => .err m p
    | .ok _ p2 =>
      let isPE := p2 < s.size && charAt s p2 == '%'
      match (if isPE then skipSpace1 s (p2 + 1) else PResult.ok () p2) with
      | .err m p => .err m p
      | .ok _ p3 =>
      match parseName s p3 with
      | .err m p => .err m p
      | .ok name p4 =>
        match skipSpace1 s p4 with
        | .err m p => .err m p
        | .ok _ p5 =>
          if p5 < s.size && (charAt s p5 == '"' || charAt s p5 == '\'') then
            match readEntityValueRaw s (p5 + 1) (p5 + 1) (charAt s p5) (s.size + 1) with
            | .err m p => .err m p
            | .ok rawval p6 =>
              match declEnd s p6 with
              | .err m p => .err m p
              | .ok _ p7 =>
                -- A PARAMETER entity is not a general entity, so it
                -- never enters the table a `&name;` reference reads.
                let ents' := if isPE then ents else
                  match lookupEntity name ents with
                  | some _ => ents
                  | none   => (name, rawval) :: ents
                .ok ents' p7
          else
            match parseExternalID s p5 with
            | .err m p => .err m p
            | .ok _ p6 =>
              let p7 := skipSpace s p6
              if p7 < s.size && peekLit "NDATA" s p7 then
                if isPE then
                  .err "NDATA is not permitted on a parameter entity ([74] PEDef)" p7
                else if p7 == p6 then
                  .err "expected space before NDATA ([76] NDataDecl)" p7
                else match skipSpace1 s (p7 + 5) with
                  | .err m p => .err m p
                  | .ok _ p8 => match parseName s p8 with
                    | .err m p => .err m p
                    | .ok _ p9 => match declEnd s p9 with
                      | .err m p => .err m p
                      | .ok _ p10 => .ok ents p10
              else match declEnd s p6 with
                | .err m p => .err m p
                | .ok _ p' => .ok ents p'

/-- `[28b] intSubset` — the internal subset body, from just after `[`
up to and including the `]`. Collects general entity declarations and
ATTLIST ID pairs; every markup declaration is PARSED against its
production, not stepped over.
Port of F* `parse_int_subset`. -/
def parseIntSubset (s : Chars) (pos : Nat) (ents : EntityTable)
    (ids : List (String × String)) : Nat → PResult (EntityTable × List (String × String))
  | 0 => .err "internal subset too long" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated internal subset (missing ']')" pos
    else
      let ch := charAt s pos
      if ch == ']' then .ok (ents, ids) (pos + 1)
      else if isXmlSpace ch then parseIntSubset s (pos + 1) ents ids fuel
      else if ch == '%' then
        -- `[69] PEReference ::= '%' Name ';'`. Scanning to the next
        -- `;` accepted `% pe;`, which has a space where the Name must
        -- start (`o-p69fail2`), and `%;`, which has no Name at all.
        (match parseName s (pos + 1) with
         | .err m p => .err m p
         | .ok _ p1 =>
             if p1 < s.size && charAt s p1 == ';' then
               parseIntSubset s (p1 + 1) ents ids fuel
             else .err "expected ';' after a parameter-entity reference ([69])" p1)
      else if ch == '<' then
        if peekLit "<!--" s pos then
          match parseComment s pos with
          | .err m p => .err m p
          | .ok _ pos' => parseIntSubset s pos' ents ids fuel
        else if peekLit "<!ENTITY" s pos then
          match parseEntityDecl s pos ents with
          | .err m p => .err m p
          | .ok ents' pos' => parseIntSubset s pos' ents' ids fuel
        else if peekLit "<?" s pos then
          match parsePi s pos with
          | .err m p => .err m p
          | .ok _ pos' => parseIntSubset s pos' ents ids fuel
        else if peekLit "<!ELEMENT" s pos then
          match parseElementDecl s pos with
          | .err m p => .err m p
          | .ok _ pos' => parseIntSubset s pos' ents ids fuel
        else if peekLit "<!ATTLIST" s pos then
          match parseAttlistDecl s pos with
          | .err m p => .err m p
          | .ok _ pos' =>
            -- The ID-typed attributes are read out of the region the
            -- declaration occupies; that scan never changes the
            -- verdict, only which names are known to be IDs.
            let ids' := scanAttlistIds s (pos + "<!ATTLIST".length) pos' ids
            parseIntSubset s pos' ents ids' fuel
        else if peekLit "<!NOTATION" s pos then
          match parseNotationDecl s pos with
          | .err m p => .err m p
          | .ok _ pos' => parseIntSubset s pos' ents ids fuel
        else if peekLit "<![" s pos then
          -- `[61] conditionalSect` is an EXTERNAL-subset production.
          -- An `<![INCLUDE[` or `<![IGNORE[` in the internal subset is
          -- a well-formedness error (not-wf-sa-063).
          .err "a conditional section is not allowed in the internal subset" pos
        else .err "malformed internal subset declaration" pos
      else .err "unexpected character in internal subset" pos

/-- Scan (respecting quoted literals) up to the next top-level `[` or
`>` without consuming it — used to step over the DOCTYPE's optional
`[75] ExternalID`. Port of F* `skip_to_subset_or_gt`. -/
def skipToSubsetOrGt (s : Chars) (pos : Nat) : Nat → PResult Unit
  | 0 => .err "unterminated DOCTYPE" pos
  | fuel + 1 =>
    if pos ≥ s.size then .err "unterminated DOCTYPE" pos
    else
      let ch := charAt s pos
      if ch == '[' || ch == '>' then .ok () pos
      else if ch == '"' || ch == '\'' then
        match skipQuotedLiteral s (pos + 1) ch fuel with
        | .err m p => .err m p
        | .ok _ pos' => skipToSubsetOrGt s pos' fuel
      else skipToSubsetOrGt s (pos + 1) fuel

/-- `[28] doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S?
('[' intSubset ']' S?)? '>'`. The external subset is recognised and
STEPPED OVER, never loaded — no external resource is read.
Port of F* `parse_doctype` (which discards the root Name; it is
recorded here). -/
def parseDoctype (s : Chars) (pos : Nat) : PResult Doctype :=
  match pstring "<!DOCTYPE" s pos with
  | .err m p => .err m p
  | .ok _ p1 =>
    match skipSpace1 s p1 with
    | .err m p => .err m p
    | .ok _ p2 =>
      match parseName s p2 with
      | .err m p => .err m p
      | .ok rootName p3 =>
        -- `(S ExternalID)?`. `skipToSubsetOrGt` used to scan over
        -- ANYTHING here, so `<!DOCTYPE doc -- a comment -- []>` was
        -- accepted (`not-wf-sa-056`) — a comment is not part of
        -- `[28]`, and neither is anything else between the Name and
        -- the subset.
        let p3s := skipSpace s p3
        match (if p3s > p3 && p3s < s.size &&
                  (peekLit "SYSTEM" s p3s || peekLit "PUBLIC" s p3s)
               then (match parseExternalIDSys s p3s with
                     | .err m p  => PResult.err m p
                     | .ok sys p => PResult.ok (some sys) p)
               else PResult.ok none p3) with
        | .err m p => .err m p
        | .ok sysId p3' =>
          let p4 := skipSpace s p3'
          if p4 < s.size && charAt s p4 == '[' then
            match parseIntSubset s (p4 + 1) [] [] (s.size + 1) with
            | .err m p => .err m p
            | .ok (ents, ids) p5 =>
              let p6 := skipSpace s p5
              if p6 < s.size && charAt s p6 == '>' then
                .ok { rootName := rootName, entities := ents, idAttrs := ids,
                      systemId := sysId } (p6 + 1)
              else .err "DOCTYPE: expected '>' after internal subset" p6
          else if p4 < s.size && charAt s p4 == '>' then
            .ok { rootName := rootName, entities := [], idAttrs := [],
                  systemId := sysId } (p4 + 1)
          else .err "DOCTYPE: expected '[' or '>'" p4

/-! ## `[27] Misc` — the prolog and epilog

`Misc ::= Comment | PI | S`. Whitespace between them is not a node
(XML has no document-level text nodes), so only Comment and PI are
accumulated. `parsePi` already rejects the reserved `xml` target in any
case, so an XML-declaration-shaped token here fails as Misc and rejects
the document — which is what the "XML declaration may not follow
content" cases require. Port of F* `collect_misc` /
`collect_epilog_misc` (identical to `skip_misc` / `skip_epilog_misc`
except that the nodes are remembered). -/
def collectMisc (s : Chars) (pos : Nat) (acc : List Node) :
    Nat → PResult (List Node)
  | 0 => .ok acc.reverse pos
  | fuel + 1 =>
    let pos1 := skipSpace s pos
    if peekLit "<!--" s pos1 then
      match parseComment s pos1 with
      | .err _ _ => .ok acc.reverse pos1
      | .ok node pos2 => collectMisc s pos2 (node :: acc) fuel
    else if peekLit "<?" s pos1 then
      match parsePi s pos1 with
      | .err _ _ => .ok acc.reverse pos1
      | .ok node pos2 => collectMisc s pos2 (node :: acc) fuel
    else .ok acc.reverse pos1

/-! ## Document-level pre-passes -/

/-- §2.11 line-ending normalisation: every `#xD #xA` pair and every lone
`#xD` becomes a single `#xA`. Unconditional — every processor, every
input, before any other parsing step. Structurally recursive on the
character list (the F* needs a fuel here because it walks byte offsets).
Port of F* `normalize_line_endings`. -/
def normalizeLineEndings : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: normalizeLineEndings rest
  | '\r' :: rest => '\n' :: normalizeLineEndings rest
  | c :: rest => c :: normalizeLineEndings rest
  | [] => []

/-- §4.3.3 / Appendix F: a UTF-8 entity may begin with a byte-order
mark, which is not part of the document's markup or character data and
is consumed before parsing begins — at position 0 ONLY. The same
character elsewhere is ordinary character data.

The F* checks the three bytes `EF BB BF`; decoded, those are the single
character U+FEFF, which is what a Lean `String` holds. Port of F*
`skip_utf8_bom`. -/
def skipBom : List Char → List Char
  | c :: rest => if c.toNat == 0xFEFF then rest else c :: rest
  | [] => []

/-! ## `[1] document` -/

/-- Parse a whole XML document.

`[1] document ::= prolog element Misc*`. Returns the infoset the F*
`parse_xml_document_children_with_ids` computes — prolog Misc, the
single document element, epilog Misc, and the ID-typed attribute pairs
— plus the `[23] XMLDecl` and `[28] doctypedecl`, which the F* parses
and then discards.

**This is the well-formedness decision.** `Except.ok` means well-formed
under the profile documented in this module's header (XML 1.0,
non-validating, non-namespace); `Except.error` carries the violated
production or WFC and the character position.

Two failure paths are deliberately silent, mirroring the F* exactly:
a missing `[23] XMLDecl` and a missing `[28] doctypedecl` are simply
absent constructs, not errors. A declaration or DOCTYPE that IS present
but malformed leaves the cursor where it was, and the element parser
then rejects the document from there. -/
def parseXML (input : String) : Except XmlError Document :=
  let chars := normalizeLineEndings (skipBom input.toList)
  let s : Chars := chars.toArray
  let fuel := s.size + 1
  -- The declaration, if present, must be the very first thing: no
  -- whitespace is skipped before trying it (§2.8 — nothing may precede
  -- the prolog).
  let (decl, pos1) :=
    match parseXmlDecl s 0 with
    | .ok d p => (some d, p)
    | .err _ _ => (none, 0)
  match collectMisc s pos1 [] fuel with
  | .err m p => .error { message := m, position := p }
  | .ok pre1 pos2 =>
    let (doctype, posDt) :=
      match parseDoctype s pos2 with
      | .ok d p => (some d, p)
      | .err _ _ => (none, pos2)
    let ents := (doctype.map (·.entities)).getD []
    match collectMisc s posDt [] fuel with
    | .err m p => .error { message := m, position := p }
    | .ok pre2 pos3 =>
      match parseElement ents s pos3 fuel with
      | .err m p => .error { message := m, position := p }
      | .ok root pos4 =>
        match collectMisc s pos4 [] fuel with
        | .err m p => .error { message := m, position := p }
        | .ok post pos5 =>
          if pos5 < s.size then
            .error { message := "content after the document element ([1] document ::= prolog element Misc*)",
                     position := pos5 }
          else
            .ok { decl := decl, doctype := doctype,
                  prolog := pre1 ++ pre2, root := root, epilog := post }

/-- The well-formedness decision as a plain `Bool` — the signal
`bin/xml-runner` scores against the W3C XML Conformance Test Suite. -/
def isWellFormed (input : String) : Bool := (parseXML input).isOk

end L4Factoidal.XML
