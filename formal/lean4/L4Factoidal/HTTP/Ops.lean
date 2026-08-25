/-
L4Factoidal.HTTP.Ops — the server's operational surfaces: static-file
policy, the saved-query index, backend-state reporting, and the
admin/timing renderers.

Ports of `formal/fstar/SPARQL.HTTP.StaticFiles.fst`,
`SPARQL.HTTP.QueriesIndex.fst`, `SPARQL.HTTP.BackendInfo.fst` and
`SPARQL.HTTP.Admin.fst`.

## Why these are here and not in whatever opens the socket

Each is a DECISION dressed as plumbing: which MIME type an extension
gets, whether a path may escape its root, what a status envelope says.
The syscalls stay outside; the policy is here, where it can be read
and tested. A MIME table that lives in the request handler is a
security decision nobody reviews.

## Float formatting is the CALLER's

Every timing renderer takes an ALREADY-FORMATTED string. Neither this
module nor the F* one reproduces the host's `%.2f` rounding, and
inventing a rounding of our own would change bytes that a log parser
or a `Server-Timing` consumer reads.
-/
import L4Factoidal.JSON.Serialize
import L4Factoidal.RDF.Graph

namespace L4Factoidal.HTTP.Ops

open L4Factoidal.JSON (escapeString)

/-! ## Static files -/

/-- The Content-Type an extension earns. Anything unrecognised is
    `application/octet-stream`, so a browser does not auto-execute
    content the server could not name. That fallback is the policy,
    not a gap. -/
def contentTypeForPath (path : String) : String :=
  let p := path.toLower
  if p.endsWith ".html" || p.endsWith ".htm" then "text/html; charset=utf-8"
  else if p.endsWith ".css" then "text/css; charset=utf-8"
  else if p.endsWith ".js" || p.endsWith ".mjs" then
    "application/javascript; charset=utf-8"
  else if p.endsWith ".json" then "application/json; charset=utf-8"
  else if p.endsWith ".svg" then "image/svg+xml; charset=utf-8"
  else if p.endsWith ".png" then "image/png"
  else if p.endsWith ".jpg" || p.endsWith ".jpeg" then "image/jpeg"
  else if p.endsWith ".ico" then "image/x-icon"
  else if p.endsWith ".txt" || p.endsWith ".md" then "text/plain; charset=utf-8"
  else if p.endsWith ".ttl" then "text/turtle; charset=utf-8"
  else if p.endsWith ".nt" then "application/n-triples; charset=utf-8"
  else if p.endsWith ".nq" then "application/n-quads; charset=utf-8"
  else "application/octet-stream"

/-- The path-traversal guard: the URL path must not contain `..`.

    Coarse ON PURPOSE. The path is only ever appended to an already
    resolved root, so rejecting the two characters is enough and needs
    no URL canonicalisation — and a canonicaliser is a much larger
    thing to get right than a two-character scan. -/
def pathHasDotDot (p : String) : Bool :=
  let rec go : List Char → Bool
    | '.' :: '.' :: _ => true
    | _ :: t          => go t
    | []              => false
  go p.toList

/-! ## The saved-query index -/

structure QueryEntry where
  group : String
  key   : String
  label : String
  body  : String
deriving Repr, Inhabited

structure QueryGroup where
  name    : String
  entries : List QueryEntry
deriving Repr, Inhabited

/-- Drop a `.rq` suffix. Total: a filename without one comes back
    unchanged. The FILENAME is the canonical handle for these fixture
    queries — the SPARQL body is deliberately not parsed to name
    them. -/
def stripRqSuffix (s : String) : String :=
  if s.endsWith ".rq" then String.ofList (s.toList.take (s.length - 3)) else s

def parliamentLabel (group filename : String) : String :=
  group ++ " / " ++ stripRqSuffix filename

def renderEntry (e : QueryEntry) : String :=
  "  {\"group\":\"" ++ escapeString e.group
    ++ "\",\"key\":\"" ++ escapeString e.key
    ++ "\",\"label\":\"" ++ escapeString e.label
    ++ "\",\"body\":\"" ++ escapeString e.body
    ++ "\"}"

def renderQueriesIndex (entries : List QueryEntry) : String :=
  let body := String.join ((entries.zipIdx).map (fun (e, i) =>
    (if i == 0 then "\n" else ",\n") ++ renderEntry e))
  "[" ++ body ++ "\n]\n"

def flattenGroups (gs : List QueryGroup) : List QueryEntry :=
  gs.flatMap (·.entries)

/-! ## Backend state -/

inductive BackendKind where
  | inMem | cottasOnDisk | hybrid | empty
deriving Repr, DecidableEq, Inhabited

def backendKindString : BackendKind → String
  | .inMem        => "in-memory"
  | .cottasOnDisk => "binary"
  | .hybrid       => "mixed"
  | .empty        => "empty"

structure CottasSummary where
  path      : String
  quads     : Int
  rowGroups : Int
deriving Repr, Inhabited

structure BackendInfo where
  kind                        : BackendKind
  source                      : String
  inMemoryTriples             : Int
  inMemoryDefaultGraphTriples : Int
  inMemoryNamedGraphs         : Int
  inMemoryNamedGraphTriples   : Int
  cottas                      : List CottasSummary
deriving Repr, Inhabited

def sumCottasQuads (xs : List CottasSummary) : Int :=
  xs.foldl (fun a x => a + x.quads) 0

/-- The `triples` field is the SUM of what is in memory and what is on
    disk. Reporting only one of them is how a hybrid backend looks
    empty. -/
def renderBackendInfo (info : BackendInfo) : String :=
  let cottasQuads := sumCottasQuads info.cottas
  String.join
    [ "{\"kind\":\"", escapeString (backendKindString info.kind),
      "\",\"triples\":", toString (info.inMemoryTriples + cottasQuads),
      ",\"in_memory_triples\":", toString info.inMemoryTriples,
      ",\"in_memory_default_graph_triples\":",
        toString info.inMemoryDefaultGraphTriples,
      ",\"in_memory_named_graphs\":", toString info.inMemoryNamedGraphs,
      ",\"in_memory_named_graph_triples\":",
        toString info.inMemoryNamedGraphTriples,
      ",\"cottas_triples\":", toString cottasQuads,
      ",\"cottas_files\":", toString info.cottas.length,
      ",\"source\":\"", escapeString info.source, "\"}\n" ]

/-- `(total, default, named-graph count, named-graph triples)`. -/
def countDatasetTriples (ds : L4Factoidal.RDF.Dataset) : Int × Int × Int × Int :=
  let dflt := ds.default.length
  let namedCount := ds.named.length
  let namedTriples := ds.named.foldl (fun a ng => a + ng.graph.length) 0
  (((dflt + namedTriples : Nat) : Int), ((dflt : Nat) : Int),
   ((namedCount : Nat) : Int), ((namedTriples : Nat) : Int))

def backendKindOfFlags (hasDataset hasCottas : Bool) : BackendKind :=
  if hasDataset then (if hasCottas then .hybrid else .inMem)
  else (if hasCottas then .cottasOnDisk else .empty)

def backendSourceString (datasetBasename : Option String)
    (cottasBasenames : List String) : String :=
  match datasetBasename, cottasBasenames with
  | none,   []    => "(none)"
  | some f, []    => f
  | none,   paths => String.intercalate ", " paths
  | some f, paths => String.intercalate ", " (f :: paths)

/-! ## Admin and timing renderers

Every float arrives ALREADY FORMATTED, for the reason the module
header gives. -/

def renderRecentQueryJson (startedAt queryEscaped form : String)
    (status rows bodyBytes : Int)
    (parseMs evalMs formatMs totalMs : String) : String :=
  "{\"started_at\":" ++ startedAt
    ++ ",\"query\":\"" ++ queryEscaped
    ++ "\",\"form\":\"" ++ form
    ++ "\",\"status\":" ++ toString status
    ++ ",\"rows\":" ++ toString rows
    ++ ",\"body_bytes\":" ++ toString bodyBytes
    ++ ",\"parse_ms\":" ++ parseMs
    ++ ",\"eval_ms\":" ++ evalMs
    ++ ",\"format_ms\":" ++ formatMs
    ++ ",\"total_ms\":" ++ totalMs
    ++ "}"

def renderRecentQueriesEnvelope (totalQueriesSeen : Int) (totalWallMs : String)
    (status2xx status4xx status5xx : Int) (recent : List String) : String :=
  "{\"total_queries_seen\":" ++ toString totalQueriesSeen
    ++ ",\"total_wall_ms\":" ++ totalWallMs
    ++ ",\"status_2xx\":" ++ toString status2xx
    ++ ",\"status_4xx\":" ++ toString status4xx
    ++ ",\"status_5xx\":" ++ toString status5xx
    ++ ",\"recent\":[" ++ String.intercalate "," recent
    ++ "]}\n"

/-- The `[timing]` log line. Its shape is a PUBLIC surface — the
    convention people grep for — so the spacing and the unit suffixes
    are part of it. -/
def renderTimingLogLine (form : String) (status rows bodyBytes : Int)
    (parseMs evalMs formatMs totalMs qSummary : String) : String :=
  "[timing] form=" ++ form
    ++ " status=" ++ toString status
    ++ " rows=" ++ toString rows
    ++ " body=" ++ toString bodyBytes ++ "B"
    ++ " parse=" ++ parseMs ++ "ms"
    ++ " eval=" ++ evalMs ++ "ms"
    ++ " format=" ++ formatMs ++ "ms"
    ++ " total=" ++ totalMs ++ "ms"
    ++ " q=" ++ qSummary

/-- The `Server-Timing` response header. -/
def renderTimingResponseHeader (parseMs evalMs formatMs totalMs : String) : String :=
  "Server-Timing: parse;dur=" ++ parseMs
    ++ ", eval;dur=" ++ evalMs
    ++ ", format;dur=" ++ formatMs
    ++ ", total;dur=" ++ totalMs

/-- Cap a query text for logging, marking that it WAS cut. Truncating
    without the marker makes a long query look like a different, short
    one. -/
def truncateForLog (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "..."

end L4Factoidal.HTTP.Ops
