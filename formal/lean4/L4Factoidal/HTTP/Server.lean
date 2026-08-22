/-
L4Factoidal.HTTP.Server — the request/response layer of the SPARQL
endpoint, ported from `formal/fstar/SPARQL.HTTP.fst`,
`SPARQL.HTTP.Routes.fst` and `SPARQL.HTTP.Response.fst`.

Specs: SPARQL 1.1 Protocol (https://www.w3.org/TR/sparql11-protocol/)
and SPARQL 1.1 Graph Store HTTP Protocol
(https://www.w3.org/TR/sparql11-http-rdf-update/), over RFC 7230
message syntax.

Everything here is a TOTAL FUNCTION from a parsed request to a
response decision. Sockets, reads and writes stay outside — the
purity doctrine, which for a server means the routing, negotiation
and status-code logic is testable with no network at all.

This module matters to the project's framing: a linked information
system with the Web at its heart needs its Web surface specified,
not bolted on.
-/

namespace L4Factoidal.HTTP

/-- A parsed request. Header names arrive LOWERCASED and values
    trimmed, so lookup is a plain comparison — the normalisation
    happens once, at parse time. -/
structure Request where
  method   : String
  path     : String
  queryStr : String
  version  : String := "HTTP/1.1"
  headers  : List (String × String) := []
  body     : String := ""
deriving Repr, Inhabited

inductive Error where
  | malformedRequestLine
  | malformedHeader
  | badRequest (why : String)
  | bodyTooLarge
  | headersTooLarge
  | missingCRLF
deriving Repr, DecidableEq, Inhabited

/-- Case-insensitive header lookup over already-lowercased names. -/
def Request.header? (r : Request) (name : String) : Option String :=
  (r.headers.find? (fun (k, _) => k == name.toLower)).map (·.2)

/-! ## Query-string parsing -/

private def splitOnChar (c : Char) (s : String) : List String :=
  let rec go (cur : List Char) (acc : List String) : List Char → List String
    | []      => acc ++ [String.ofList cur.reverse]
    | x :: r  => if x == c then go [] (acc ++ [String.ofList cur.reverse]) r
                 else go (x :: cur) acc r
  go [] [] s.toList

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decoding for `application/x-www-form-urlencoded`, where
    `+` also means space.

    Decoding happens at the BYTE level and the result is interpreted
    as UTF-8 at the end. Building a `Char` per escape would turn
    `%C3%A9` into two Latin-1 characters instead of `é` — the classic
    mojibake bug, and one this port had until a guard caught it.

    A malformed escape is left VERBATIM rather than dropped: silently
    deleting bytes from a query changes what was asked. -/
partial def formDecode (s : String) : String :=
  let rec go (acc : List UInt8) : List Char → List UInt8
    | [] => acc.reverse
    | '+' :: r => go (32 :: acc) r
    | '%' :: a :: b :: r =>
        match hexVal a, hexVal b with
        | some x, some y => go (UInt8.ofNat (x * 16 + y) :: acc) r
        | _, _           => go (37 :: acc) (a :: b :: r)
    | c :: r => go ((String.mk [c]).toUTF8.toList.reverse ++ acc) r
  let bytes := ByteArray.mk (go [] s.toList).toArray
  match String.fromUTF8? bytes with
  | some out => out
  | none     => s          -- undecodable bytes: keep the original

/-- Parse `a=1&b=2` into pairs, percent-decoding both sides. -/
def parseQuery (qs : String) : List (String × String) :=
  if qs == "" then []
  else (splitOnChar '&' qs).filterMap (fun kv =>
    if kv == "" then none
    else match splitOnChar '=' kv with
      | [k]        => some (formDecode k, "")
      | k :: v :: _ => some (formDecode k, formDecode v)
      | []         => none)

/-! ## Routing -/

def protocolPaths : List String := ["/sparql", "/query", "/update"]
def gspPathPrefix : String := "/data"

def isProtocolPath (p : String) : Bool := protocolPaths.contains p
def isGspPath (p : String) : Bool := p == gspPathPrefix || p.startsWith (gspPathPrefix ++ "/")

/-- What a request is asking for. -/
inductive Route where
  | query | update | graphStore | options | notFound
deriving Repr, DecidableEq, Inhabited

/-- Route a request. `OPTIONS` is answered before path matching, since
    CORS preflight must work on every endpoint. -/
def route (r : Request) : Route :=
  if r.method == "OPTIONS" then .options
  else if isGspPath r.path then .graphStore
  else if r.path == "/update" then .update
  else if isProtocolPath r.path then
    -- On a shared endpoint, an `update=` parameter selects update
    -- even on the query path (Protocol §2.2).
    if (parseQuery r.queryStr).any (fun (k, _) => k == "update") ||
       (r.header? "content-type" == some "application/sparql-update")
    then .update else .query
  else .notFound

/-! ## Content negotiation -/

/-- A media type with its q-value, scaled by 1000 so the ordering is
    exact integer comparison rather than a float. -/
structure MediaRange where
  media : String
  q     : Nat := 1000
deriving Repr, DecidableEq, Inhabited

private def trim (s : String) : String :=
  String.ofList (((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse)

/-- Parse an `Accept` header. An unparseable q-value falls back to
    1.0, per RFC 7231's "recipients SHOULD treat it as 1". -/
def parseAccept (h : String) : List MediaRange :=
  (splitOnChar ',' h).filterMap (fun part =>
    match splitOnChar ';' part with
    | [] => none
    | m :: params =>
        let media := trim m
        if media == "" then none
        else
          let q := params.findSome? (fun p =>
            let p := trim p
            if p.startsWith "q=" then
              let v := String.ofList (p.toList.drop 2)
              match splitOnChar '.' v with
              | ["1"] | ["1", "0"] | ["1", "00"] | ["1", "000"] => some 1000
              | ["0"] => some 0
              | ["0", frac] =>
                  let ds := frac.toList.take 3
                  let padded := ds ++ List.replicate (3 - ds.length) '0'
                  some (padded.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
              | _ => none
            else none)
          some ⟨media, q.getD 1000⟩)

/-- Pick the best supported type. Ties break toward the SERVER's
    preference order, which is what `supported`'s order encodes;
    a q-value of 0 means "not acceptable" and can never be chosen. -/
def negotiate (accept : String) (supported : List String) : Option String :=
  let ranges := parseAccept accept
  if ranges.isEmpty then supported.head?
  else
    let scored := supported.filterMap (fun s =>
      let best := ranges.filterMap (fun r =>
        if r.media == s || r.media == "*/*" ||
           (r.media.endsWith "/*" &&
            s.startsWith (String.ofList (r.media.toList.dropLast)))
        then some r.q else none)
      match best.max? with
      | some q => if q == 0 then none else some (s, q)
      | none   => none)
    (scored.foldl (fun acc (s, q) =>
      match acc with
      | none => some (s, q)
      | some (_, bq) => if q > bq then some (s, q) else acc) none).map (·.1)

/-! ## Responses -/

structure Response where
  status  : Nat
  headers : List (String × String) := []
  body    : String := ""
deriving Repr, Inhabited

def Response.ok (contentType body : String) : Response :=
  ⟨200, [("content-type", contentType)], body⟩

def Response.noContent : Response := ⟨204, [], ""⟩

def Response.badRequest (msg : String) : Response :=
  ⟨400, [("content-type", "text/plain")], msg⟩

def Response.notFound : Response :=
  ⟨404, [("content-type", "text/plain")], "Not Found"⟩

/-- 405 MUST carry `Allow` (RFC 7231 §6.5.5) — a bare 405 is a
    protocol violation, not merely unhelpful. -/
def Response.methodNotAllowed (allowed : List String) : Response :=
  ⟨405, [("allow", String.intercalate ", " allowed)], ""⟩

def Response.notAcceptable : Response :=
  ⟨406, [("content-type", "text/plain")], "Not Acceptable"⟩

def Response.unsupportedMediaType : Response :=
  ⟨415, [("content-type", "text/plain")], "Unsupported Media Type"⟩

/-- The methods each route accepts. -/
def allowedMethods : Route → List String
  | .query      => ["GET", "POST", "OPTIONS"]
  | .update     => ["POST", "OPTIONS"]
  | .graphStore => ["GET", "PUT", "POST", "DELETE", "HEAD", "OPTIONS"]
  | .options    => ["OPTIONS"]
  | .notFound   => []

/-- Method check for a routed request. `HEAD` is allowed wherever
    `GET` is, per RFC 7231. -/
def methodAllowed (rt : Route) (method : String) : Bool :=
  let allowed := allowedMethods rt
  allowed.contains method ||
  (method == "HEAD" && allowed.contains "GET")

end L4Factoidal.HTTP
