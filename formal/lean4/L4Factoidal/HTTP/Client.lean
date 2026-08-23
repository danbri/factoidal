/-
L4Factoidal.HTTP.Client — the SPARQL HTTP CLIENT framing: an HTTP/1.1
request formatter and a response parser.

Port of `formal/fstar/SPARQL.HTTP.Client.fst`. Spec: RFC 7230 message
syntax, as the SPARQL 1.1 Protocol
(https://www.w3.org/TR/sparql11-protocol/) uses it.

The mirror of `HTTP/Server.lean`. Where the server PARSES a request it
received, this module FORMATS a request it is about to send and parses
the response that comes back.

## I/O stays outside, on purpose

Nothing here opens a socket. `formatRequest` returns the bytes to
write; `parseHttpResponse` reads the buffer someone else filled. That
makes every framing decision — the request line, the injected `Host`
and `Content-Length`, the status line, the header block, the body
length — testable with no network at all, which is the same purity
doctrine the server side follows.

## Response framing is NOT the same as request framing

A request must carry a `Content-Length` when it has a body. A
RESPONSE need not: connection-close framing lets the peer send until
it closes, and the body is then everything after the blank line.
`parseHttpResponse` therefore treats an ABSENT `Content-Length` as
"take what is available" and a MALFORMED one as an error. Reading the
two the same way is how a client either truncates a legitimate
response or trusts a broken header.
-/
namespace L4Factoidal.HTTP.Client

/-- A request to send. -/
structure RequestMsg where
  method   : String
  path     : String
  queryStr : String := ""
  version  : String := "HTTP/1.1"
  host     : String := ""
  headers  : List (String × String) := []
  body     : String := ""
deriving Repr, Inhabited

/-- A parsed response. Header names are LOWERCASED and values trimmed,
    so a lookup is a plain comparison. -/
structure Response where
  version : String
  status  : Nat
  reason  : String
  headers : List (String × String)
  body    : String
deriving Repr, Inhabited

inductive Error where
  | malformedStatusLine
  | malformedHeader
  | badStatusCode
  | headersTooLarge
  | bodyTooLarge
  | missingCRLF
  | badResponse (why : String)
deriving Repr, DecidableEq, Inhabited

/-! ## Character helpers -/

def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

def trimWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile isAsciiWs).reverse.dropWhile isAsciiWs).reverse)

def lowerAscii (s : String) : String := s.toLower

/-- A substring that CANNOT go out of range: an over-long request is
    clipped rather than refused, so one malformed length cannot make
    the parser itself the failure. -/
def safeSub (s : List Char) (start len : Nat) : String :=
  String.ofList ((s.drop start).take len)

def suffixFrom (s : List Char) (start : Nat) : String :=
  String.ofList (s.drop start)

/-- The index of the first `c` at or after `from`. -/
def findChar (s : List Char) (from' : Nat) (c : Char) : Option Nat :=
  ((s.drop from').findIdx? (· == c)).map (· + from')

/-- The index of the first occurrence of the two-character sequence. -/
def find2 (s : List Char) (from' : Nat) (a b : Char) : Option Nat :=
  let rec go (i : Nat) (rest : List Char) : Option Nat :=
    match rest with
    | x :: y :: t => if x == a && y == b then some i else go (i + 1) (y :: t)
    | _           => none
  (go 0 (s.drop from')).map (· + from')

/-- The index of the first occurrence of the four-character sequence —
    the CRLFCRLF that ends the head region. -/
def find4 (s : List Char) (from' : Nat) (a b c d : Char) : Option Nat :=
  let rec go (i : Nat) (rest : List Char) : Option Nat :=
    match rest with
    | w :: x :: y :: z :: t =>
        if w == a && x == b && y == c && z == d then some i
        else go (i + 1) (x :: y :: z :: t)
    | _ => none
  (go 0 (s.drop from')).map (· + from')

def containsCrlf (s : String) : Bool :=
  s.toList.any (fun c => c == '\r' || c == '\n')

def headerLookup (hs : List (String × String)) (name : String) : Option String :=
  (hs.find? (fun (k, _) => lowerAscii k == lowerAscii name)).map (·.2)

def hasHeader (hs : List (String × String)) (name : String) : Bool :=
  (headerLookup hs name).isSome

/-- A run of ASCII digits, and nothing else. An empty string or a
    stray character is `none`, which the caller turns into a named
    error rather than a zero. -/
def parseNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty then none
  else cs.foldl (fun acc c =>
    acc.bind (fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 10 + (c.toNat - '0'.toNat)) else none))
    (some 0)

/-! ## Formatting a request -/

def crlf : String := "\r\n"

def formatHeaders (hs : List (String × String)) : String :=
  String.join (hs.map (fun (k, v) => k ++ ": " ++ v ++ crlf))

def formatRequestLine (meth path qs ver : String) : String :=
  let target := if qs.isEmpty then path else path ++ "?" ++ qs
  meth ++ " " ++ target ++ " " ++ ver ++ crlf

/-- Inject `Host` and `Content-Length` when the caller has not set
    them. A caller that set either KEEPS its own value — this fills a
    gap, it does not overwrite a decision. -/
def completeHeaders (r : RequestMsg) : List (String × String) :=
  let h1 := if hasHeader r.headers "Host" then r.headers
            else r.headers ++ [("Host", r.host)]
  let bodyLen := r.body.length
  if bodyLen == 0 || hasHeader h1 "Content-Length" then h1
  else h1 ++ [("Content-Length", toString bodyLen)]

def formatRequest (r : RequestMsg) : String :=
  formatRequestLine r.method r.path r.queryStr r.version
    ++ formatHeaders (completeHeaders r) ++ crlf ++ r.body

/-! ## Parsing a response -/

/-- `HTTP/1.1 404 Not Found` → `("HTTP/1.1", 404, "Not Found")`. The
    reason phrase may contain SPACES, so it is everything after the
    second space; it may not contain CR or LF. -/
def parseStatusLine (line : String) : Except Error (String × Nat × String) :=
  if containsCrlf line then .error .malformedStatusLine
  else
    let cs := line.toList
    match findChar cs 0 ' ' with
    | none    => .error .malformedStatusLine
    | some i1 =>
      let ver := safeSub cs 0 i1
      match findChar cs (i1 + 1) ' ' with
      | none    => .error .malformedStatusLine
      | some i2 =>
        if i2 ≤ i1 + 1 then .error .malformedStatusLine
        else
          match parseNat (safeSub cs (i1 + 1) (i2 - (i1 + 1))) with
          | none      => .error .badStatusCode
          | some code =>
              if ver.isEmpty then .error .malformedStatusLine
              else .ok (ver, code, suffixFrom cs (i2 + 1))

def parseHeaderLine (line : String) : Except Error (String × String) :=
  if containsCrlf line then .error .malformedHeader
  else
    let cs := line.toList
    match findChar cs 0 ':' with
    | none   => .error .malformedHeader
    | some i =>
        let name := lowerAscii (trimWs (safeSub cs 0 i))
        let value := trimWs (suffixFrom cs (i + 1))
        if name.isEmpty then .error .malformedHeader else .ok (name, value)

def parseHeaderLines (raw : List Char) (pos headEnd : Nat)
    : Nat → List (String × String) → Except Error (List (String × String))
  | 0,     acc => .ok acc
  | f + 1, acc =>
      if pos ≥ headEnd then .ok acc
      else
        match find2 raw pos '\r' '\n' with
        | none =>
            let line := safeSub raw pos (headEnd - pos)
            if line.isEmpty then .ok acc
            else (parseHeaderLine line).map (fun kv => acc ++ [kv])
        | some crlfPos =>
            if crlfPos > headEnd || crlfPos ≤ pos then .ok acc
            else
              match parseHeaderLine (safeSub raw pos (crlfPos - pos)) with
              | .error e => .error e
              | .ok kv   => parseHeaderLines raw (crlfPos + 2) headEnd f (acc ++ [kv])

/-- Parse a whole buffered response.

    1. find the first CRLFCRLF within `maxHeaderBytes`;
    2. the status line is the first CRLF-terminated line;
    3. the rest of the head region is header lines;
    4. with a `Content-Length`, take that many bytes; WITHOUT one,
       take everything available — connection-close framing. -/
def parseHttpResponse (rawS : String) (maxHeaderBytes maxBodyBytes : Nat)
    : Except Error Response :=
  let raw := rawS.toList
  let rawLen := raw.length
  match find4 raw 0 '\r' '\n' '\r' '\n' with
  | none =>
      if rawLen ≥ maxHeaderBytes then .error .headersTooLarge else .error .missingCRLF
  | some headEnd =>
    if headEnd > maxHeaderBytes then .error .headersTooLarge
    else
      match find2 raw 0 '\r' '\n' with
      | none => .error .malformedStatusLine
      | some slEnd =>
        if slEnd > headEnd then .error .malformedStatusLine
        else
          match parseStatusLine (safeSub raw 0 slEnd) with
          | .error e => .error e
          | .ok (ver, code, reason) =>
            let headersStart := slEnd + 2
            let headersEnd := if headEnd ≥ headersStart then headEnd else headersStart
            match parseHeaderLines raw headersStart headersEnd
                    (headersEnd - headersStart + 1) [] with
            | .error e => .error e
            | .ok headers =>
              let bodyStart := headEnd + 4
              let available := if rawLen ≥ bodyStart then rawLen - bodyStart else 0
              -- An ABSENT Content-Length is connection-close framing;
              -- a MALFORMED one is an error. Reading the two the same
              -- way truncates a legitimate response or trusts a broken
              -- header.
              let bodyLen? : Option Nat :=
                match headerLookup headers "content-length" with
                | none    => some available
                | some cl => parseNat cl
              match bodyLen? with
              | none => .error (.badResponse "invalid Content-Length")
              | some bodyLen =>
                  if bodyLen > maxBodyBytes then .error .bodyTooLarge
                  else
                    let effective := if bodyLen ≤ available then bodyLen else available
                    .ok { version := ver, status := code, reason := reason,
                          headers := headers, body := safeSub raw bodyStart effective }

end L4Factoidal.HTTP.Client
