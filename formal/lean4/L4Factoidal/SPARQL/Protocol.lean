/-
L4Factoidal.SPARQL.Protocol — SPARQL 1.1 Protocol, the pure request
decoder. Port of `formal/fstar/SPARQL.Protocol.fst` Parts 2–7 and 14.

W3C spec: https://www.w3.org/TR/sparql11-protocol/

THIS MODULE IS PURE. It contains no HTTP transport code, no sockets,
no I/O. What is here:

  * percent-decoding (`urlDecode` / `formDecode`, RFC 3986 §2.1 and
    the application/x-www-form-urlencoded `+` rule) and its inverse
    `percentEncode` (the subject of the round-trip theorem in
    `ProtocolTheorems.lean`);
  * query-string parsing into an ordered key/value bag
    (`parseQueryString`); duplicate keys are kept because
    `default-graph-uri` / `named-graph-uri` may repeat (§2.1.4);
  * `decodeRequest` — HTTP method + URL path + query string +
    Content-Type + body become a typed `SparqlRequest` or a `bad`
    (4xx-class) verdict, applying Protocol §2.1 (query) and §2.2
    (update): `query=` / `update=` parameters, GET vs POST,
    `application/x-www-form-urlencoded`, `application/sparql-query`,
    `application/sparql-update`, the UTF-8 charset rule (§2.1.6), the
    one-query / one-update rule (§2.1.4 / §2.2.4), UPDATE-never-via-GET
    (§2.2.2), and the `using-graph-uri` vs `USING`/`WITH` conflict
    (§2.2.4);
  * the W3C protocol test-manifest scrapers the F* tree keeps in the
    same module (Part 14): `extractRequest` reads the indented HTTP
    request block under `#### Request` in an entry's `rdfs:comment`,
    `extractStatusClass` reads the expected `2xx`/`4xx`/`5xx` under
    `#### Response`, and `extractResponseStatus` reads the numeric
    status the Graph Store tests carry (`bin/w3c-runner/w3c_runner.ml`
    `_gsp_extract_response_status`).

NOT PORTED, each with its reason:

  * Accept-header parsing and content negotiation
    (`parse_accept_header` / `pick_response_format`, F* Part 6): the
    protocol tests assert on status class, not on the response media
    type; a later rung when a Lean HTTP front end needs it.
  * The SELECT / ASK response serialisers (F* Parts 8–12): the Lean
    tree already has `SPARQL/ResultsXml.lean`, `ResultsJson.lean`,
    `ResultsCsvTsv.lean` as its serialisers, so a second copy would
    be duplication, not a port.

One deliberate divergence from the F* source, recorded in
`PORT_NOTES.md`: `containsWord` keeps scanning after a prefix match
that is NOT bounded by whitespace (`withdraw using`), where the F*
`chars_contains_word` (SPARQL.Protocol.fst:509–533) returns `false`
outright at that point and never sees the later `using`.

Percent-decoding decodes `%XX` escapes to BYTES and then reads those
byte runs as UTF-8, so `%C3%A9` is `é`. The F* `url_decode_chars`
(SPARQL.Protocol.fst:146–167) maps each `%XX` to the codepoint XX, so
the same input is `Ã©` there — also recorded as a finding. An escape
run that is not valid UTF-8 falls back to one codepoint per byte (the
F* reading), so decoding is total.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.SPARQL.Protocol

/-! ## Types -/

/-- A decoded SPARQL protocol request (F* `sparql_request`).

`query` / `update` carry the operation text plus the two
protocol-level dataset lists — `default-graph-uri` values and
`named-graph-uri` values for a query (§2.1.4), `using-graph-uri` and
`using-named-graph-uri` are read separately for an update (§2.2.3) —
and `bad` carries the reason a 4xx-class rejection was chosen. -/
inductive SparqlRequest where
  | query  (text : String) (defaultGraphUris namedGraphUris : List String)
  | update (text : String) (defaultGraphUris namedGraphUris : List String)
  | bad    (reason : String)
  deriving DecidableEq, Repr

/-- True for the 4xx-class verdict. -/
def SparqlRequest.isBad : SparqlRequest → Bool
  | .bad _ => true
  | _      => false

/-! ## Low-level helpers (F* Part 2) -/

/-- `0-9`, `A-F`, `a-f`. -/
def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

/-- The value of one hex digit; 0 for a non-digit (F* `hex_value`). -/
def hexValue (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - 48
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 65 + 10
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 97 + 10
  else 0

/-- ASCII-only lower-casing of one character. -/
def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- ASCII-only lower-casing (F* `ascii_lower_string`). Header names,
methods and media types are matched this way; non-ASCII characters
are untouched. -/
def asciiLower (s : String) : String := String.ofList (s.toList.map asciiLowerChar)

/-- Trim the four ASCII whitespace characters (space, tab, CR, LF)
from both ends — the F* `trim_ws` set, which is exactly
`Char.isWhitespace`. -/
def trimWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

/-! ## Percent-decoding (F* Part 3, RFC 3986 §2.1) -/

/-- One unit of a percent-decoded string: a character that was not
escaped, or the byte value of one `%XX` escape. Keeping the two apart
is what lets a run of escape bytes be read as UTF-8 while a literal
non-ASCII character passes through unchanged. -/
inductive PctUnit where
  | ch   (c : Char)
  | byte (b : Nat)
  deriving DecidableEq, Repr

/-- Split a character list into decoding units. `%XX` with two hex
digits becomes `byte`; a `%` not followed by two hex digits is kept
literally (the F* rule); with `plusIsSpace` a `+` becomes a space
(application/x-www-form-urlencoded). -/
def pctUnits (plusIsSpace : Bool) (cs : List Char) : List PctUnit :=
  match cs with
  | [] => []
  | c :: rest =>
    if c == '%' then
      match rest with
      | h1 :: h2 :: rest' =>
        if isHexDigit h1 && isHexDigit h2 then
          .byte (hexValue h1 * 16 + hexValue h2) :: pctUnits plusIsSpace rest'
        else .ch c :: pctUnits plusIsSpace (h1 :: h2 :: rest')
      | [h1] => .ch c :: pctUnits plusIsSpace [h1]
      | []   => [.ch c]
    else if plusIsSpace && c == '+' then .ch ' ' :: pctUnits plusIsSpace rest
    else .ch c :: pctUnits plusIsSpace rest
termination_by cs.length

/-- A UTF-8 continuation byte `10xxxxxx`. -/
def isCont (b : Nat) : Bool := 0x80 ≤ b && b < 0xC0

/-- Assemble units into characters: escape-byte runs are read as
UTF-8 (2-, 3- and 4-byte forms, rejecting overlong encodings and
surrogates); a byte that does not start a valid sequence becomes the
codepoint of its own value (Latin-1 reading — the F* behaviour), so
the function is total on every input. -/
def utf8Assemble (us : List PctUnit) : List Char :=
  match us with
  | [] => []
  | .ch c :: rest => c :: utf8Assemble rest
  | .byte b :: rest =>
    if b < 0x80 then Char.ofNat b :: utf8Assemble rest
    else if 0xC2 ≤ b && b < 0xE0 then
      match rest with
      | .byte b2 :: rest' =>
        if isCont b2 then Char.ofNat ((b - 0xC0) * 64 + (b2 - 0x80)) :: utf8Assemble rest'
        else Char.ofNat b :: utf8Assemble (.byte b2 :: rest')
      | .ch c2 :: rest' => Char.ofNat b :: utf8Assemble (.ch c2 :: rest')
      | [] => [Char.ofNat b]
    else if 0xE0 ≤ b && b < 0xF0 then
      match rest with
      | .byte b2 :: .byte b3 :: rest' =>
        let v := (b - 0xE0) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80)
        if isCont b2 && isCont b3 && 0x800 ≤ v && !(0xD800 ≤ v && v < 0xE000) then
          Char.ofNat v :: utf8Assemble rest'
        else Char.ofNat b :: utf8Assemble (.byte b2 :: .byte b3 :: rest')
      | u :: rest' => Char.ofNat b :: utf8Assemble (u :: rest')
      | [] => [Char.ofNat b]
    else if 0xF0 ≤ b && b < 0xF5 then
      match rest with
      | .byte b2 :: .byte b3 :: .byte b4 :: rest' =>
        let v := (b - 0xF0) * 262144 + (b2 - 0x80) * 4096 + (b3 - 0x80) * 64 + (b4 - 0x80)
        if isCont b2 && isCont b3 && isCont b4 && 0x10000 ≤ v && v < 0x110000 then
          Char.ofNat v :: utf8Assemble rest'
        else Char.ofNat b :: utf8Assemble (.byte b2 :: .byte b3 :: .byte b4 :: rest')
      | u :: rest' => Char.ofNat b :: utf8Assemble (u :: rest')
      | [] => [Char.ofNat b]
    else Char.ofNat b :: utf8Assemble rest
termination_by us.length

/-- Percent-decode a character list (F* `url_decode_chars`). -/
def percentDecodeChars (plusIsSpace : Bool) (cs : List Char) : List Char :=
  utf8Assemble (pctUnits plusIsSpace cs)

/-- RFC 3986 percent-decoding: `%XX` only; `+` is a literal plus
(F* `url_decode`). -/
def urlDecode (s : String) : String := String.ofList (percentDecodeChars false s.toList)

/-- Form decoding: `%XX` and `+` → space (F* `form_decode`,
application/x-www-form-urlencoded). -/
def formDecode (s : String) : String := String.ofList (percentDecodeChars true s.toList)

/-! ## Percent-encoding (RFC 3986 §2.3 unreserved set)

The inverse used by the round-trip theorem. Unreserved characters
(`ALPHA / DIGIT / "-" / "." / "_" / "~"`) pass through; every other
character is written as the `%XX` of each of its UTF-8 bytes, which
covers the reserved set `:/?#[]@!$&'()*+,;=` and `%` itself. -/

/-- RFC 3986 §2.3 unreserved characters (ASCII only). -/
def isUnreserved (c : Char) : Bool :=
  c.toNat < 128 && (c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~')

/-- Upper-case hex digit for `n < 16`. -/
def hexDigitUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `%XX` for one byte value. -/
def percentEncodeByte (b : Nat) : List Char :=
  ['%', hexDigitUpper (b / 16), hexDigitUpper (b % 16)]

/-- Encode one character: unreserved as itself, other ASCII as one
escape, non-ASCII as one escape per UTF-8 byte. -/
def percentEncodeChar (c : Char) : List Char :=
  if isUnreserved c then [c]
  else if c.toNat < 128 then percentEncodeByte c.toNat
  else (String.utf8EncodeChar c).flatMap (fun u => percentEncodeByte u.toNat)

def percentEncodeChars (cs : List Char) : List Char := cs.flatMap percentEncodeChar

def percentEncode (s : String) : String := String.ofList (percentEncodeChars s.toList)

/-! ## Split utilities (F* Part 4) -/

/-- Split at the FIRST occurrence of `sep`: `(before, some after)`,
or `(s, none)` when `sep` is absent (F* `split_once_on`). -/
def splitOnceChars (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: rest =>
    if c == sep then ([], some rest)
    else
      let (before, after) := splitOnceChars sep rest
      (c :: before, after)

def splitOnce (s : String) (sep : Char) : String × Option String :=
  let (b, a) := splitOnceChars sep s.toList
  (String.ofList b, a.map String.ofList)

/-- Split at EVERY occurrence of `sep`; the empty string gives `[""]`
and a trailing separator a trailing `""` (F* `split_all_on`, which is
`String.splitOn`'s behaviour). -/
def splitAll (s : String) (sep : Char) : List String := s.splitOn sep.toString

/-! ## Query-string parsing (F* Part 5) -/

/-- `k=v` → `(formDecode k, formDecode v)`; a bare `k` → `(k, "")`;
the empty segment (from `a&&b`) is dropped. -/
def parseKvPair (pair : String) : Option (String × String) :=
  match splitOnce pair '=' with
  | (k, some v) => some (formDecode k, formDecode v)
  | (k, none)   => if k.isEmpty then none else some (formDecode k, "")

/-- `"a=1&b=hello+world&a=2"` → `[("a","1"), ("b","hello world"),
("a","2")]`. Duplicates preserved in order. -/
def parseQueryString (qs : String) : List (String × String) :=
  (splitAll qs '&').filterMap parseKvPair

/-- Every value for `key`, in order (keys compared byte-exactly —
RFC 3986 query keys are case-sensitive). -/
def collectValues (key : String) (kvs : List (String × String)) : List String :=
  kvs.filterMap (fun kv => if kv.1 == key then some kv.2 else none)

def firstValue (key : String) (kvs : List (String × String)) : Option String :=
  (collectValues key kvs).head?

/-! ## Request decoder (F* Part 7; Protocol §2.1, §2.2) -/

/-- True iff the path's final segment is `update`, case-insensitively.
Every other path is a query path (the spec allows any path; the
discriminator is only a tiebreaker when no `query=`/`update=` is
present). -/
def pathIsUpdate (urlPath : String) : Bool :=
  match (splitAll urlPath '/').getLast? with
  | some last => asciiLower last == "update"
  | none      => false

/-- Strip an embedded `?query-string` from a path the caller did not
split. -/
def splitPathQs (urlPath : String) : String × String :=
  match splitOnce urlPath '?' with
  | (p, none)    => (p, "")
  | (p, some qs) => (p, qs)

/-- The media type without parameters, lower-cased and trimmed:
`"application/sparql-query; charset=utf-8"` →
`"application/sparql-query"`. -/
def contentTypeBase (ct : String) : String :=
  asciiLower (trimWs (splitOnce ct ';').1)

/-- The `charset=` parameter of a Content-Type, lower-cased and
trimmed, when present (RFC 7231 §3.1.1.1: parameter names are
case-insensitive). -/
def extractCharsetParam (ct : String) : Option String :=
  match splitOnce ct ';' with
  | (_, none) => none
  | (_, some params) =>
    match (splitAll params ';').find? (fun p => (asciiLower (trimWs p)).startsWith "charset=") with
    | none   => none
    | some p => some (trimWs (String.ofList ((asciiLower (trimWs p)).toList.drop 8)))

/-- Protocol §2.1.6 / §2.2.x: a declared charset other than UTF-8 is
rejected; an absent charset is UTF-8. -/
def charsetIsUtf8OrAbsent (ct : String) : Bool :=
  match extractCharsetParam ct with
  | none   => true
  | some v => v == "utf-8" || v == "utf8"

/-- Does `cs` contain `kw` as a whitespace-bounded word? The scan
continues past a prefix match that is not followed by whitespace or
end of input (see the module header for the F* divergence). -/
def containsWord (kw : List Char) (prevWs : Bool) : List Char → Bool
  | [] => false
  | c :: rest =>
    if prevWs && kw.isPrefixOf (c :: rest) &&
       (match (c :: rest).drop kw.length with
        | []     => true
        | n :: _ => n.isWhitespace) then true
    else containsWord kw c.isWhitespace rest

/-- Case-insensitive whitespace-bounded word search (`kwLower` must
already be lower-case). -/
def containsWordCi (haystack kwLower : String) : Bool :=
  containsWord kwLower.toList true (asciiLower haystack).toList

/-- Protocol §2.2.4: does the update text carry a `USING` / `WITH`
dataset clause? (`USING NAMED` starts with `USING`, so two keywords
suffice.) -/
def updateHasDatasetClause (u : String) : Bool :=
  containsWordCi u "using" || containsWordCi u "with"

/-- Is `using-graph-uri` or `using-named-graph-uri` among the
parameters? -/
def kvsHaveUsingParam (kvs : List (String × String)) : Bool :=
  (firstValue "using-graph-uri" kvs).isSome || (firstValue "using-named-graph-uri" kvs).isSome

/-- Build the request from the parameter bag of a GET query string or
a form-encoded POST body. The form key (`query=` vs `update=`) is
authoritative (§2.1.2 / §2.2.2); `isGet` rejects `update=` outright
(§2.2.2: update is never invoked via GET); `isUpdatePath` is only the
tiebreaker for the diagnostic when neither key is present. -/
def buildFromKvs (isGet isUpdatePath : Bool) (kvs : List (String × String)) : SparqlRequest :=
  let qsAll := collectValues "query"  kvs
  let usAll := collectValues "update" kvs
  -- §2.1.4 / §2.2.4: more than one query= (or update=) is a 400.
  if qsAll.length > 1 then .bad "more than one query= parameter (Protocol 2.1.4)"
  else if usAll.length > 1 then .bad "more than one update= parameter (Protocol 2.2.4)"
  else
  let dflt  := collectValues "default-graph-uri" kvs
  let named := collectValues "named-graph-uri"   kvs
  match firstValue "query" kvs, firstValue "update" kvs with
  | some _, some _ => .bad "both query= and update= present (Protocol 2.2.4)"
  | none, none =>
    if isUpdatePath then .bad "missing update parameter" else .bad "missing query parameter"
  | some q, none =>
    if isUpdatePath then .bad "expected update= on /update endpoint, got query="
    else .query q dflt named
  | none, some u =>
    if isGet then .bad "UPDATE invoked via GET (Protocol 2.2.2)"
    -- §2.2.4: using-graph-uri / using-named-graph-uri form params must
    -- not coexist with USING / WITH inside the update text.
    else if kvsHaveUsingParam kvs && updateHasDatasetClause u then
      .bad "using-graph-uri/using-named-graph-uri form params conflict with USING/WITH in update text (Protocol 2.2.4)"
    else .update u dflt named

/-- The clean path and the query string that applies: an explicit
`urlQuery` wins; otherwise one embedded in the path after `?`. -/
def effectiveQs (urlPath urlQuery : String) : String × String :=
  let (cleanPath, embedded) := splitPathQs urlPath
  (cleanPath, if urlQuery.length > 0 then urlQuery else embedded)

/-- Decode an HTTP request into a SPARQL protocol request.
`httpMethod` as received (`GET` / `POST` / …), `urlPath` the path
(a trailing `?…` is split off defensively), `urlQuery` the raw query
string without the `?`, `contentType` the header value (`""` when
absent), `body` the request body as text. -/
def decodeRequest (httpMethod urlPath urlQuery contentType body : String) : SparqlRequest :=
  let (cleanPath, qs) := effectiveQs urlPath urlQuery
  let isUpdate := pathIsUpdate cleanPath
  let m := asciiLower httpMethod
  if m == "get" then
    buildFromKvs true isUpdate (parseQueryString qs)
  else if m == "post" then
    let ct := contentTypeBase contentType
    if !(charsetIsUtf8OrAbsent contentType) then
      .bad "non-UTF-8 charset rejected per Protocol 2.1.6"
    else if ct == "application/sparql-query" then .query body [] []
    else if ct == "application/sparql-update" then .update body [] []
    else if ct == "application/x-www-form-urlencoded" then
      buildFromKvs false isUpdate (parseQueryString body)
    else if ct.isEmpty then .bad "POST request missing Content-Type"
    else .bad ("unsupported Content-Type: " ++ ct)
  else if m == "head" || m == "options" then
    .bad ("method " ++ httpMethod ++ " not supported by decoder")
  else .bad ("unsupported HTTP method: " ++ httpMethod)

/-! ## Test-manifest request / response extraction (F* Part 14)

The W3C protocol and graph-store manifests describe each test as an
HTTP exchange in Markdown inside `rdfs:comment`:

    #### Request

        POST /sparql/ HTTP/1.1
        Host: www.example
        Content-Type: application/x-www-form-urlencoded

        query=ASK%20%7B%7D

    #### Response

        2xx or 3xx response

The request block is the indented text under the first
`#### Request` heading: a request line, `Key: Value` headers to the
first blank line, then the body. -/

/-- A decoded request block. Header keys are lower-cased. -/
structure ProtoRequest where
  method  : String
  /-- Path only, no query string. -/
  path    : String
  /-- Query string, no leading `?`. -/
  qs      : String
  headers : List (String × String)
  body    : String
  deriving DecidableEq, Repr

/-- Expected status class read from the `#### Response` block. -/
inductive StatusClass where
  | s2or3
  | s4xx
  | s5xx
  | unknown
  deriving DecidableEq, Repr

def StatusClass.label : StatusClass → String
  | .s2or3   => "2xx/3xx"
  | .s4xx    => "4xx"
  | .s5xx    => "5xx"
  | .unknown => "?"

/-- How many leading characters to drop: up to 4 spaces, or one tab
(a tab stops the scan at once; any other character stops it without
being consumed). -/
def indentBudget : List Char → Nat → Nat
  | _, 0 => 0
  | [], _ => 0
  | c :: rest, budget + 1 =>
    if c == ' ' then 1 + indentBudget rest budget
    else if c == '\t' then 1
    else 0

def stripIndent (s : String) : String :=
  let cs := s.toList
  String.ofList (cs.drop (indentBudget cs 4))

def isBlankLine (s : String) : Bool := (trimWs s).isEmpty

def isIndentedLine (s : String) : Bool :=
  match s.toList with
  | c :: _ => c == ' ' || c == '\t'
  | []     => false

/-- The lines after the first `#### Request` heading. -/
def findReqHeader : List String → Option (List String)
  | [] => none
  | line :: rest => if trimWs line == "#### Request" then some rest else findReqHeader rest

def skipBlankLines : List String → List String
  | [] => []
  | line :: rest => if isBlankLine line then skipBlankLines rest else line :: rest

/-- Lines while indented-or-blank; the remainder starts at the first
non-indented non-blank line (the next `####` heading). -/
def takeIndented : List String → List String × List String
  | [] => ([], [])
  | line :: rest =>
    if isIndentedLine line || isBlankLine line then
      let (taken, remaining) := takeIndented rest
      (line :: taken, remaining)
    else ([], line :: rest)

/-- Drop only a TRAILING run of blank lines. -/
def rtrimBlanks : List String → List String
  | [] => []
  | x :: rest =>
    match rtrimBlanks rest with
    | []    => if isBlankLine x then [] else [x]
    | rest' => x :: rest'

def ltrimBlanks : List String → List String
  | "" :: rest => ltrimBlanks rest
  | xs         => xs

/-- `Key: Value` lines to the first blank line (or a line with no
`:`); keys lower-cased and trimmed, values trimmed. Returns the
headers and the remaining body lines. -/
def readHeaders : List String → List (String × String) × List String
  | [] => ([], [])
  | "" :: rest => ([], rest)
  | line :: rest =>
    match splitOnce line ':' with
    | (_, none) => ([], line :: rest)
    | (before, some after) =>
      let (hdrs, bodyLines) := readHeaders rest
      ((asciiLower (trimWs before), trimWs after) :: hdrs, bodyLines)

/-- The first `#### Request` block as a `ProtoRequest`, or `none` when
the comment has no such block or no request line. -/
def extractRequest (comment : String) : Option ProtoRequest :=
  match findReqHeader (splitAll comment '\n') with
  | none => none
  | some afterHdr =>
    let (blockLines, _) := takeIndented (skipBlankLines afterHdr)
    let stripped := (rtrimBlanks blockLines).map
      (fun l => if isBlankLine l then "" else stripIndent l)
    match ltrimBlanks stripped with
    | [] => none
    | reqLine :: rest =>
      -- "POST /sparql/ HTTP/1.1" (3 tokens) or "GET /sparql?query=…"
      -- (2 tokens); the first token is the method.
      match splitAll (trimWs reqLine) ' ' with
      | mthd :: target :: _ =>
        let (path, qs) := match splitOnce target '?' with
                          | (p, none)   => (p, "")
                          | (p, some q) => (p, q)
        let (headers, bodyLines) := readHeaders rest
        some { method := mthd, path := path, qs := qs, headers := headers,
               body := trimWs (String.intercalate "\n" bodyLines) }
      | _ => none

/-- The lines after the first `#### Response` heading (all of them —
the class scan below looks at the whole remainder, as the F* does). -/
def findRespLines : List String → List String
  | [] => []
  | line :: rest => if trimWs line == "#### Response" then rest else findRespLines rest

/-- Substring test. -/
def strContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Classify the expected status: `4xx` is checked before `5xx` before
`2xx`/`3xx`, since a block may mention several loosely. -/
def extractStatusClass (comment : String) : StatusClass :=
  let body := String.intercalate "\n" (findRespLines (splitAll comment '\n'))
  if strContains body "4xx" || strContains body "4XX" then .s4xx
  else if strContains body "5xx" || strContains body "5XX" then .s5xx
  else if strContains body "2xx" || strContains body "3xx" ||
          strContains body "2XX" || strContains body "3XX" then .s2or3
  else .unknown

/-- The first numeric status (`200 OK`, `404 Not Found`, …) after the
first `#### Response` heading: three digits followed by a space or
the end of the trimmed line. The Graph Store manifest carries exact
codes where the protocol manifest carries classes. -/
def extractResponseStatus (comment : String) : Option Nat :=
  let parseCode (line : String) : Option Nat :=
    match (trimWs line).toList with
    | d1 :: d2 :: d3 :: rest =>
      if d1.isDigit && d2.isDigit && d3.isDigit &&
         (match rest with | [] => true | c :: _ => c == ' ') then
        some ((d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48))
      else none
    | _ => none
  (findRespLines (splitAll comment '\n')).findSome? parseCode

/-- Header lookup by lower-cased key; `""` when absent. -/
def header (hdrs : List (String × String)) (key : String) : String :=
  match hdrs.find? (fun kv => kv.1 == asciiLower key) with
  | some kv => kv.2
  | none    => ""

end L4Factoidal.SPARQL.Protocol
