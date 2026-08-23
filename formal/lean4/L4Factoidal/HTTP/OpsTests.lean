/-
L4Factoidal.HTTP.OpsTests — build-time checks for the server's
operational surfaces.
-/
import L4Factoidal.HTTP.Ops

namespace L4Factoidal.HTTP.Ops

/-! ## MIME types

An unrecognised extension is `application/octet-stream`, so a browser
does not auto-execute content the server could not name. That
fallback is the policy, not a gap. -/

#guard contentTypeForPath "/a/b.html" == "text/html; charset=utf-8"
#guard contentTypeForPath "/A/B.HTML" == "text/html; charset=utf-8"
#guard contentTypeForPath "x.ttl" == "text/turtle; charset=utf-8"
#guard contentTypeForPath "x.nq" == "application/n-quads; charset=utf-8"
#guard contentTypeForPath "x.exe" == "application/octet-stream"
#guard contentTypeForPath "noextension" == "application/octet-stream"

/-! ## Path traversal

Two characters, rejected outright. Coarse on purpose: the path is
only ever appended to an already resolved root, and a canonicaliser
is a much larger thing to get right than this scan. -/

#guard pathHasDotDot "/a/../b"
#guard pathHasDotDot ".."
#guard !(pathHasDotDot "/a/b/c.html")
/-! A single dot is not traversal, and a filename may carry one. -/
#guard !(pathHasDotDot "/a/./b")
#guard !(pathHasDotDot "/a/b.min.js")

/-! ## The saved-query index -/

#guard stripRqSuffix "03-members.rq" == "03-members"
#guard stripRqSuffix "noSuffix" == "noSuffix"
#guard stripRqSuffix "rq" == "rq"
#guard parliamentLabel "Vendored - main" "03-members.rq"
      == "Vendored - main / 03-members"

private def e1 : QueryEntry :=
  { group := "g", key := "k", label := "l", body := "SELECT * {}" }

#guard renderQueriesIndex [] == "[\n]\n"
#guard renderQueriesIndex [e1] ==
  "[\n  {\"group\":\"g\",\"key\":\"k\",\"label\":\"l\",\"body\":\"SELECT * {}\"}\n]\n"

/-! A quotation mark in a query body is ESCAPED, so the index stays
    JSON. An unescaped one would end the string early and make the
    whole document unparsable. -/
#guard ((renderQueriesIndex [{ e1 with body := "\"" }]).splitOn "\\\"").length > 1

#guard (flattenGroups [{ name := "a", entries := [e1] },
                       { name := "b", entries := [e1] }]).length == 2

/-! ## Backend state

`triples` is the SUM of memory and disk. Reporting one of them is how
a hybrid backend looks empty. -/

private def bi : BackendInfo :=
  { kind := .hybrid, source := "a.nq, b.cottas",
    inMemoryTriples := 10, inMemoryDefaultGraphTriples := 4,
    inMemoryNamedGraphs := 2, inMemoryNamedGraphTriples := 6,
    cottas := [{ path := "b.cottas", quads := 90, rowGroups := 3 }] }

#guard ((renderBackendInfo bi).splitOn "\"triples\":100").length > 1
#guard ((renderBackendInfo bi).splitOn "\"cottas_files\":1").length > 1
#guard ((renderBackendInfo bi).splitOn "\"kind\":\"mixed\"").length > 1

#guard backendKindOfFlags true true == BackendKind.hybrid
#guard backendKindOfFlags true false == BackendKind.inMem
#guard backendKindOfFlags false true == BackendKind.cottasOnDisk
#guard backendKindOfFlags false false == BackendKind.empty

#guard backendSourceString none [] == "(none)"
#guard backendSourceString (some "a.nq") [] == "a.nq"
#guard backendSourceString none ["x", "y"] == "x, y"
#guard backendSourceString (some "a.nq") ["x"] == "a.nq, x"

/-! ## Timing surfaces

Their SHAPE is public: the log line is what people grep for and the
header is what a client reads, so the spacing and the unit suffixes
are part of the contract. -/

#guard renderTimingResponseHeader "0.4" "137.2" "0.0" "137.6"
      == "Server-Timing: parse;dur=0.4, eval;dur=137.2, format;dur=0.0, total;dur=137.6"

#guard renderTimingLogLine "SELECT" 200 42 412 "0.4" "137.2" "0.0" "137.6" "\"q\""
      == "[timing] form=SELECT status=200 rows=42 body=412B parse=0.4ms \
eval=137.2ms format=0.0ms total=137.6ms q=\"q\""

#guard renderRecentQueriesEnvelope 3 "12.5" 2 1 0 []
      == "{\"total_queries_seen\":3,\"total_wall_ms\":12.5,\"status_2xx\":2,\
\"status_4xx\":1,\"status_5xx\":0,\"recent\":[]}\n"

/-! ## Truncation MARKS itself

Cutting without the marker makes a long query look like a different,
short one. -/

#guard truncateForLog "abcdef" 10 == "abcdef"
#guard truncateForLog "abcdef" 3 == "abc..."

end L4Factoidal.HTTP.Ops
