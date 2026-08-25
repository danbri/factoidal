/-
L4Factoidal.SPARQL.ProtocolClient — SPARQL 1.1 Protocol, client side.

Port of `formal/fstar/SPARQL.Protocol.Client.fst` (533 lines).

Spec: <https://www.w3.org/TR/sparql11-protocol/> §2.1.

Request construction and response dispatch, layered on modules that
already exist:

* `HTTP.Client` frames a request into bytes and bytes back into a
  response. Socket I/O is consumer glue outside the verified library, so
  no primitive is introduced here.
* `SPARQL.Protocol` supplies percent-encoding and `mediaTypeToFormat`.
* `SPARQL.ResultsJson` / `ResultsXml` / `ResultsCsvTsv` /
  `Syntax.Turtle` / `Syntax.NTriples` parse the response. This module
  parses nothing itself; it DISPATCHES to them.

## What sniffing is for, and what it is not

`sniffQueryKind` scans for the query's top-level form keyword. It is not
a grammar parser: it skips the `PREFIX` and `BASE` prologue and returns
the first form keyword it meets, without tracking string literals, IRIs
or comments, so a query carrying "SELECT" inside a literal before its
real keyword can be sniffed wrongly.

Correctness never rests on the guess. It biases the Accept header's
q-values only, `acceptHeaderForKind` always lists EVERY media type this
client can parse, and `handleResponse` dispatches on the response's
ACTUAL `Content-Type`. A wrong guess costs a sub-optimal q-value
ordering on a conforming server, never a failure.

## What is not here

No socket I/O, no SPARQL grammar parsing, and no redirect, retry or
authentication logic — those belong to the consumer, not the protocol
shape. SPARQL Update dispatch is a separate and smaller surface (direct
POST or form POST, never GET) and is absent from the F\* module too.
-/
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.HTTP.Client
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsCsvTsv
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.SPARQL.ProtocolClient

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol (ResponseFormat mediaTypeToFormat contentTypeBase
  percentEncode asciiLower trimWs)

/-! ## Types -/

/-- Which query form we BELIEVE we are sending. Used only to bias
Accept-header q-values; never to interpret a response. -/
inductive QueryKind where
  | select | ask | construct | describe
  deriving DecidableEq, Repr, Inhabited

/-- The three request dispatch methods for the query operation
(§2.1.1–2.1.3). -/
inductive DispatchMethod where
  | get | postDirect | postForm
  deriving DecidableEq, Repr, Inhabited

/-- The outcome of a fully handled response. `httpError` carries the raw
body as well, so a caller can surface the server's own error detail —
which is what a 400 on a malformed query is for. -/
inductive ClientResult where
  | result (r : QueryResult)
  | graph (g : Graph)
  | httpError (status : Nat) (body : String)
  | parseError (detail : String)
  | unknownContentType (contentType : String) (body : String)
  deriving Repr

/-! ## Query-string parameters -/

def encodePair (kv : String × String) : String :=
  percentEncode kv.1 ++ "=" ++ percentEncode kv.2

def encodePairs (pairs : List (String × String)) : String :=
  String.intercalate "&" (pairs.map encodePair)

/-- The `default-graph-uri` and `named-graph-uri` parameters, which all
three dispatch methods share. -/
def graphUriPairs (defaultGraphUris namedGraphUris : List String) :
    List (String × String) :=
  defaultGraphUris.map (fun g => ("default-graph-uri", g)) ++
  namedGraphUris.map (fun g => ("named-graph-uri", g))

/-! ## The Accept header

Every media type this client can parse is always listed; only the
q-value ORDER changes with the guessed kind. That is what makes a wrong
guess harmless rather than a 406 on a conforming server. -/

def acceptHeaderForKind : QueryKind → String
  | .select | .ask =>
      "application/sparql-results+json, application/sparql-results+xml;q=0.9, \
       text/turtle;q=0.2, application/n-triples;q=0.1"
  | .construct | .describe =>
      "text/turtle, application/n-triples;q=0.9, \
       application/sparql-results+json;q=0.2, application/sparql-results+xml;q=0.1"

/-! ## Sniffing the query form

Tokenise on ASCII whitespace, skip the `PREFIX` and `BASE` prologue
declarations, return the first form keyword. See the header for why a
wrong answer is not a correctness problem. -/

def isAsciiWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def asciiUpper (s : String) : String :=
  String.ofList (s.toList.map (fun c =>
    if c.toNat ≥ 0x61 && c.toNat ≤ 0x7A then Char.ofNat (c.toNat - 32) else c))

/-- The next whitespace-delimited token and what follows it. -/
def nextToken (cs : List Char) : String × List Char :=
  let rest := cs.dropWhile isAsciiWs
  let tok := rest.takeWhile (fun c => !isAsciiWs c)
  (String.ofList tok, rest.drop tok.length)

/-- Walk tokens until a form keyword appears. A `PREFIX` declaration
consumes two more tokens and a `BASE` one; anything else that is not a
form keyword consumes one, so the walk always advances. -/
def sniffLoop : Nat → List Char → QueryKind
  | 0, _ => .select                      -- budget spent: the default bias
  | fuel + 1, cs =>
      let (tok, rest) := nextToken cs
      if tok.isEmpty then .select        -- ran out of input
      else
        match asciiUpper tok with
        | "SELECT"   => .select
        | "ASK"      => .ask
        | "CONSTRUCT" => .construct
        | "DESCRIBE" => .describe
        | "PREFIX"   => sniffLoop fuel (nextToken (nextToken rest).2).2
        | "BASE"     => sniffLoop fuel (nextToken rest).2
        | _          => sniffLoop fuel rest

def sniffQueryKind (queryText : String) : QueryKind :=
  sniffLoop (queryText.length + 1) queryText.toList

/-! ## Request construction

Each builder returns an `HTTP.Client.RequestMsg`; the caller frames it
and hands the bytes to socket I/O. None of these does any I/O. -/

/-- query-via-GET (§2.1.1). -/
def buildGetRequest (host path queryText : String)
    (defaultGraphUris namedGraphUris : List String) (accept : String) :
    HTTP.Client.RequestMsg :=
  { method := "GET", path := path,
    queryStr := encodePairs (("query", queryText) ::
                             graphUriPairs defaultGraphUris namedGraphUris),
    host := host, headers := [("Accept", accept)], body := "" }

/-- query-via-POST-direct (§2.1.2): the query text is the WHOLE body.
The graph-URI parameters still travel in the query string, as the spec
says. -/
def buildPostDirectRequest (host path queryText : String)
    (defaultGraphUris namedGraphUris : List String) (accept : String) :
    HTTP.Client.RequestMsg :=
  { method := "POST", path := path,
    queryStr := encodePairs (graphUriPairs defaultGraphUris namedGraphUris),
    host := host,
    headers := [("Accept", accept), ("Content-Type", "application/sparql-query")],
    body := queryText }

/-- query-via-URL-encoded-POST (§2.1.3): everything, `query` included,
travels as a form body. -/
def buildPostFormRequest (host path queryText : String)
    (defaultGraphUris namedGraphUris : List String) (accept : String) :
    HTTP.Client.RequestMsg :=
  { method := "POST", path := path, queryStr := "", host := host,
    headers := [("Accept", accept),
                ("Content-Type", "application/x-www-form-urlencoded")],
    body := encodePairs (("query", queryText) ::
                         graphUriPairs defaultGraphUris namedGraphUris) }

/-- Pick a builder and sniff the Accept header from the query text. -/
def buildQueryRequest (m : DispatchMethod) (host path queryText : String)
    (defaultGraphUris namedGraphUris : List String) : HTTP.Client.RequestMsg :=
  let accept := acceptHeaderForKind (sniffQueryKind queryText)
  match m with
  | .get        => buildGetRequest host path queryText defaultGraphUris namedGraphUris accept
  | .postDirect => buildPostDirectRequest host path queryText defaultGraphUris namedGraphUris accept
  | .postForm   => buildPostFormRequest host path queryText defaultGraphUris namedGraphUris accept

/-! ## Response dispatch

On the response's ACTUAL `Content-Type`, never on the sniffed guess.

A graph body is parsed with NO base IRI: a conforming endpoint's Turtle
or N-Triples response carries absolute IRIs and blank nodes only. A
relative-IRI CONSTRUCT response is a documented simplification here and
in the F\* source. -/

def dispatchBody (fmt : ResponseFormat) (body : String) : ClientResult :=
  match fmt with
  | .json =>
      match parseSrj body with
      | .ok r => .result r
      | .error e => .parseError s!"invalid application/sparql-results+json body: {e.msg}"
  | .xml =>
      match parseSrx body with
      | .ok r => .result r
      | .error e => .parseError s!"invalid application/sparql-results+xml body: {e.msg}"
  | .csv =>
      match parseCsv body with
      | .ok r => .result r
      | .error e => .parseError s!"invalid text/csv results body: {e.msg}"
  | .tsv =>
      match parseTsv body with
      | .ok r => .result r
      | .error e => .parseError s!"invalid text/tab-separated-values results body: {e.msg}"
  | .turtle =>
      match Syntax.parseTurtle body with
      | .ok g => .graph g
      | .error _ => .parseError "invalid text/turtle graph body"
  | .nTriples =>
      match Syntax.parseNTriples body with
      | .ok g => .graph g
      | .error _ => .parseError "invalid application/n-triples graph body"
  | .text => .parseError "text/plain response body is not a SPARQL result"

/-- A parsed response to a typed result. A non-2xx status becomes
`httpError` carrying the raw body, so the server's own detail survives.

`HTTP.Client.parseResponse` lowercases header names, so the lookup here
is by the lowercased name. -/
def handleResponse (resp : HTTP.Client.Response) : ClientResult :=
  if resp.status < 200 || resp.status ≥ 300 then .httpError resp.status resp.body
  else
    match HTTP.Client.headerLookup resp.headers "Content-Type" with
    | none => .unknownContentType "" resp.body
    | some ct =>
        match mediaTypeToFormat (contentTypeBase ct) with
        | some fmt => dispatchBody fmt resp.body
        | none => .unknownContentType ct resp.body

/-! ## Build-time checks -/

section Checks

/-! ### Percent-encoding of the query parameter -/

#guard encodePairs [("query", "ASK {}")] == "query=ASK%20%7B%7D"
#guard encodePairs [("a", "1"), ("b", "2")] == "a=1&b=2"
#guard encodePairs [] == ""
#guard percentEncode "http://e.org/g" == "http%3A%2F%2Fe.org%2Fg"

/-! ### The graph-URI parameters keep their spec names and their order -/

#guard graphUriPairs ["d1", "d2"] ["n1"] ==
  [("default-graph-uri", "d1"), ("default-graph-uri", "d2"), ("named-graph-uri", "n1")]

/-! ### Sniffing skips the prologue -/

#guard sniffQueryKind "SELECT * WHERE { ?s ?p ?o }" == .select
#guard sniffQueryKind "ask {}" == .ask
#guard sniffQueryKind "PREFIX ex: <http://e.org/> CONSTRUCT { ?s ?p ?o } WHERE {}" == .construct
#guard sniffQueryKind "BASE <http://e.org/> DESCRIBE <x>" == .describe
#guard sniffQueryKind "PREFIX a: <u> PREFIX b: <v> ASK {}" == .ask

/-! And it terminates on input with no form keyword at all, rather than
looping on a token it cannot classify. -/

#guard sniffQueryKind "" == .select
#guard sniffQueryKind "not a query" == .select

/-! ### A wrong guess costs ordering, not capability

Both Accept headers list every media type this client can parse, which
is what makes the sniff safe. Checked rather than asserted. -/

private def listsEveryType (h : String) : Bool :=
  ["application/sparql-results+json", "application/sparql-results+xml",
   "text/turtle", "application/n-triples"].all (fun t => (h.splitOn t).length > 1)

#guard listsEveryType (acceptHeaderForKind .select)
#guard listsEveryType (acceptHeaderForKind .construct)

/-! ### The three dispatch methods put the query where the spec says -/

private def getReq : HTTP.Client.RequestMsg :=
  buildQueryRequest .get "e.org" "/sparql" "ASK {}" [] []
private def directReq : HTTP.Client.RequestMsg :=
  buildQueryRequest .postDirect "e.org" "/sparql" "ASK {}" [] []
private def formReq : HTTP.Client.RequestMsg :=
  buildQueryRequest .postForm "e.org" "/sparql" "ASK {}" [] []

#guard getReq.method == "GET" && getReq.body == "" &&
       getReq.queryStr == "query=ASK%20%7B%7D"
#guard directReq.method == "POST" && directReq.body == "ASK {}" &&
       directReq.queryStr == "" &&
       HTTP.Client.headerLookup directReq.headers "content-type" ==
         some "application/sparql-query"
#guard formReq.method == "POST" && formReq.queryStr == "" &&
       formReq.body == "query=ASK%20%7B%7D" &&
       HTTP.Client.headerLookup formReq.headers "content-type" ==
         some "application/x-www-form-urlencoded"

/-! Direct POST still sends the graph URIs in the QUERY STRING, which is
the part of §2.1.2 that is easy to get wrong. -/

#guard (buildQueryRequest .postDirect "e.org" "/sparql" "ASK {}"
          ["http://e.org/g"] []).queryStr ==
  "default-graph-uri=http%3A%2F%2Fe.org%2Fg"

/-! ### Response dispatch goes by the ACTUAL Content-Type -/

private def resp (status : Nat) (ct body : String) : HTTP.Client.Response :=
  { version := "HTTP/1.1", status := status, reason := "",
    headers := [("content-type", ct)], body := body }

private def srjBoolean : String := "{\"head\":{},\"boolean\":true}"

#guard match handleResponse (resp 200 "application/sparql-results+json" srjBoolean) with
       | .result (.boolean true) => true
       | _ => false

/-! A parameterised Content-Type still dispatches: the charset is
stripped before the lookup. -/

#guard match handleResponse
             (resp 200 "application/sparql-results+json; charset=utf-8" srjBoolean) with
       | .result (.boolean true) => true
       | _ => false

/-! A graph body reaches the graph parser. -/

#guard match handleResponse (resp 200 "text/turtle"
             "<http://e.org/s> <http://e.org/p> <http://e.org/o> .") with
       | .graph g => g.length == 1
       | _ => false
#guard match handleResponse (resp 200 "application/n-triples"
             "<http://e.org/s> <http://e.org/p> <http://e.org/o> .\n") with
       | .graph g => g.length == 1
       | _ => false

/-! ### The three failure shapes are DISTINCT

A malformed body, an unknown media type and a server error are three
different things, and collapsing any two of them would hide which one
happened. -/

#guard match handleResponse (resp 200 "application/sparql-results+json" "not json") with
       | .parseError _ => true
       | _ => false
#guard match handleResponse (resp 200 "application/octet-stream" "xx") with
       | .unknownContentType ct b => ct == "application/octet-stream" && b == "xx"
       | _ => false
#guard match handleResponse (resp 400 "text/plain" "syntax error at line 1") with
       | .httpError s b => s == 400 && b == "syntax error at line 1"
       | _ => false

/-! A 2xx response with NO Content-Type is `unknownContentType` with an
empty type, not a parse error against a guessed format. -/

#guard match handleResponse
             { version := "HTTP/1.1", status := 200, reason := "", headers := [],
               body := "x" } with
       | .unknownContentType ct _ => ct == ""
       | _ => false

/-! The status test is on the CLASS, so a 204 and a 299 are successes
and a 199 and a 300 are not. -/

#guard match handleResponse (resp 204 "text/plain" "") with
       | .parseError _ => true | _ => false
#guard match handleResponse (resp 300 "text/plain" "") with
       | .httpError _ _ => true | _ => false
#guard match handleResponse (resp 199 "text/plain" "") with
       | .httpError _ _ => true | _ => false

end Checks

end L4Factoidal.SPARQL.ProtocolClient
