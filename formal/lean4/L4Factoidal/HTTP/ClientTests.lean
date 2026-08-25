/-
L4Factoidal.HTTP.ClientTests — build-time checks for the client
framing, mirroring the compile-time smoke tests of the F* module.
-/
import L4Factoidal.HTTP.Client

namespace L4Factoidal.HTTP.Client

/-! ## Formatting -/

#guard formatRequestLine "GET" "/sparql" "" "HTTP/1.1" == "GET /sparql HTTP/1.1\r\n"
#guard formatRequestLine "GET" "/sparql" "query=X" "HTTP/1.1"
      == "GET /sparql?query=X HTTP/1.1\r\n"
#guard formatHeaders [] == ""
#guard formatHeaders [("Host", "a"), ("Accept", "b")] == "Host: a\r\nAccept: b\r\n"

private def getReq : RequestMsg :=
  { method := "GET", path := "/sparql", queryStr := "query=ASK%7B%7D",
    host := "example.org" }

#guard formatRequest getReq ==
  "GET /sparql?query=ASK%7B%7D HTTP/1.1\r\nHost: example.org\r\n\r\n"

private def postReq : RequestMsg :=
  { method := "POST", path := "/sparql", host := "example.org",
    headers := [("Content-Type", "application/sparql-query")],
    body := "ASK{}" }

/-! `Content-Length` is INJECTED for a body the caller did not measure,
    and `Host` for a host it did not set. -/
#guard formatRequest postReq ==
  "POST /sparql HTTP/1.1\r\nContent-Type: application/sparql-query\r\n\
Host: example.org\r\nContent-Length: 5\r\n\r\nASK{}"

/-! A caller that SET either header keeps its own value. This fills a
    gap; it does not overwrite a decision. -/
#guard formatRequest { postReq with headers := [("Content-Length", "99")] } ==
  "POST /sparql HTTP/1.1\r\nContent-Length: 99\r\nHost: example.org\r\n\r\nASK{}"

/-! ## Status lines -/

private def sl (s : String) : Option (String × Nat × String) :=
  (parseStatusLine s).toOption

private def slErr (s : String) : Option Error :=
  match parseStatusLine s with | .error e => some e | .ok _ => none

#guard sl "HTTP/1.1 200 OK" == some ("HTTP/1.1", 200, "OK")
/-! The reason phrase may contain SPACES. -/
#guard sl "HTTP/1.1 404 Not Found" == some ("HTTP/1.1", 404, "Not Found")
#guard slErr "HTTP/1.1 abc OK" == some Error.badStatusCode
#guard slErr "nonsense" == some Error.malformedStatusLine

/-! ## Header lines are lowercased and trimmed once, at parse time -/

#guard (parseHeaderLine "Content-Type:  text/turtle  ").toOption
      == some ("content-type", "text/turtle")
#guard (parseHeaderLine ": empty").isOk == false

/-! ## Whole responses -/

private def withCl : String :=
  "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 5\r\n\r\nhello world"

#guard (parseHttpResponse withCl 8192 65536).toOption.map (·.body) == some "hello"
#guard (parseHttpResponse withCl 8192 65536).toOption.map (·.status) == some 200

/-! WITHOUT a Content-Length the framing is connection-close: the body
    is everything after the blank line. An absent header is not the
    same as a zero-length body. -/
private def noCl : String :=
  "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nhello world"

#guard (parseHttpResponse noCl 8192 65536).toOption.map (·.body) == some "hello world"

/-! A MALFORMED Content-Length is an error, not a fallback to
    connection-close framing — trusting a broken header is how a
    client reads someone else's bytes as its own body. -/
private def badCl : String :=
  "HTTP/1.1 200 OK\r\nContent-Length: twelve\r\n\r\nhello"

#guard (parseHttpResponse badCl 8192 65536).isOk == false

/-! A Content-Length LONGER than what arrived is clipped to what
    arrived, so a truncated transfer cannot make the parser read past
    the buffer. -/
private def shortBody : String :=
  "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\nhello"

#guard (parseHttpResponse shortBody 8192 65536).toOption.map (·.body) == some "hello"

/-! The two size caps are separate, and each names itself. -/
private def respErr (s : String) (h b : Nat) : Option Error :=
  match parseHttpResponse s h b with | .error e => some e | .ok _ => none

#guard respErr withCl 8192 2 == some Error.bodyTooLarge
#guard respErr "HTTP/1.1 200 OK" 8192 65536 == some Error.missingCRLF

end L4Factoidal.HTTP.Client
