/-
L4Factoidal.HTTP.Tests — build-time checks for routing, query
parsing and content negotiation.
-/
import L4Factoidal.HTTP.Server

namespace L4Factoidal.HTTP

private def req (m p : String) (qs : String := "") (hs : List (String × String) := []) : Request :=
  { method := m, path := p, queryStr := qs, headers := hs }

-- Query-string parsing with percent and plus decoding.
#guard parseQuery "a=1&b=2" == [("a", "1"), ("b", "2")]
#guard parseQuery "" == []
#guard parseQuery "flag" == [("flag", "")]
#guard parseQuery "q=SELECT+%2A" == [("q", "SELECT *")]
#guard formDecode "%C3%A9" == "é"
-- A MALFORMED escape is kept verbatim rather than dropped: deleting
-- bytes from a query silently changes what was asked.
#guard formDecode "100%zz" == "100%zz"
#guard formDecode "trailing%" == "trailing%"

-- Routing.
#guard route (req "GET" "/query") == .query
#guard route (req "POST" "/update") == .update
#guard route (req "GET" "/data/graph") == .graphStore
#guard route (req "GET" "/data") == .graphStore
#guard route (req "GET" "/nope") == .notFound
-- OPTIONS is answered before path matching, so CORS preflight works
-- everywhere.
#guard route (req "OPTIONS" "/nope") == .options

-- On a SHARED endpoint an `update=` parameter selects update even on
-- the query path (Protocol 2.2), as does the update content type.
#guard route (req "POST" "/sparql" "update=DELETE%20%7B%7D") == .update
#guard route (req "POST" "/sparql" "" [("content-type", "application/sparql-update")]) == .update
#guard route (req "POST" "/sparql" "query=SELECT") == .query

-- Method rules. HEAD is allowed wherever GET is.
#guard methodAllowed .query "GET"
#guard methodAllowed .query "HEAD"
#guard !(methodAllowed .update "GET")
#guard methodAllowed .graphStore "DELETE"

-- 405 MUST carry Allow — a bare 405 is a protocol violation.
#guard (Response.methodNotAllowed ["GET", "POST"]).status == 405
#guard (Response.methodNotAllowed ["GET", "POST"]).headers
       == [("allow", "GET, POST")]

-- Accept parsing, with q-values scaled to exact integers.
#guard parseAccept "text/turtle" == [⟨"text/turtle", 1000⟩]
#guard parseAccept "text/turtle;q=0.5" == [⟨"text/turtle", 500⟩]
#guard parseAccept "a/b;q=0" == [⟨"a/b", 0⟩]
#guard parseAccept "a/b;q=0.333" == [⟨"a/b", 333⟩]
-- An unparseable q falls back to 1.0, per RFC 7231.
#guard parseAccept "a/b;q=bogus" == [⟨"a/b", 1000⟩]

-- Negotiation picks the highest q among supported types.
private def sup : List String := ["text/turtle", "application/n-triples"]
#guard negotiate "application/n-triples" sup == some "application/n-triples"
#guard negotiate "text/turtle;q=0.1, application/n-triples;q=0.9" sup
       == some "application/n-triples"
#guard negotiate "*/*" sup == some "text/turtle"        -- server preference
#guard negotiate "text/*" sup == some "text/turtle"
-- q=0 means NOT ACCEPTABLE and can never be chosen, even when the
-- type is the server's own first preference.
#guard negotiate "text/turtle;q=0, application/n-triples" sup
       == some "application/n-triples"
#guard negotiate "text/turtle;q=0" sup == none
#guard negotiate "image/png" sup == none
-- An empty Accept means the server's first preference.
#guard negotiate "" sup == some "text/turtle"

-- Header lookup is case-insensitive on the caller's side.
#guard (req "GET" "/query" "" [("content-type", "text/turtle")]).header? "Content-Type"
       == some "text/turtle"

-- Response constructors.
#guard (Response.ok "text/turtle" "data").status == 200
#guard Response.noContent.status == 204
#guard Response.notAcceptable.status == 406
#guard Response.unsupportedMediaType.status == 415

end L4Factoidal.HTTP
