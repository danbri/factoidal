module SPARQL.HTTP.Routes

(* Pure-F\* classifier for SPARQL Protocol HTTP request paths.
   #200 Section 2 MIXED-row migration (try_static_route at
   bin/factoidal-http/factoidal_http.ml:2063 — boundary-audit
   recommended target).

   Per the SPARQL 1.1 Protocol spec (W3C Recommendation, 2013):

     §2.1 — Query operation: GET or POST to a *query endpoint*.
     §2.2 — Update operation: POST to an *update endpoint*.

   The endpoint paths themselves are deployer-chosen, but the
   conventional defaults (and the ones every spec example uses) are
   `/sparql` and `/update`. `/query` is a long-standing alternative
   path for query-only endpoints; many SPARQL servers (Virtuoso,
   Fuseki, GraphDB) expose it.

   What this module decides:
     - is_sparql_protocol_path : whether a given URL path is a
       SPARQL Protocol endpoint (i.e. should be routed to the F\*
       protocol decoder rather than served as a static asset).

   What stays in OCaml glue:
     - The HTTP request parsing (SPARQL.HTTP.fst already in F-star).
     - The try_static_route consumer-dispatch, which decides which
       static file each non-protocol path resolves to. This is
       per-server configuration, not part of the SPARQL Protocol
       surface. *)

(* SPARQL Protocol query / update endpoint paths.

   Conservative default — exactly the three paths every SPARQL 1.1
   server is expected to expose. Deployers who want to mount their
   endpoint at a different path can extend this list, but doing so
   requires editing the F\* spec and re-extracting (intentional —
   the routing decision is part of the verified surface). *)
let sparql_protocol_paths : list string = [
  "/sparql";  (* canonical query endpoint, also accepts UPDATE per server policy *)
  "/query";   (* alternative read-only endpoint (Virtuoso/Fuseki convention) *)
  "/update";  (* canonical SPARQL Update endpoint *)
]

(* List membership over decidable-equality strings. Total. *)
let rec mem_string (p : string) (xs : list string)
  : Tot bool (decreases xs)
  =
  match xs with
  | [] -> false
  | x :: rest -> if p = x then true else mem_string p rest

(* Membership predicate. *)
let is_sparql_protocol_path (p : string) : Tot bool =
  mem_string p sparql_protocol_paths

(* ------------------------------------------------------------------
   SPARQL 1.1 Graph Store HTTP Protocol (GSP) mount point.

   Durable-UPDATE stage 8 (docs/designissues/2026-07-06-durable-update-
   design.md §5 row 8) routes SPARQL.GraphStore.fst's verified GET/HEAD/
   PUT/POST/DELETE handlers into factoidal_http's dispatch — previously
   verified (W3C http-rdf-update, 19/19) but only exercised in-process
   by bin/w3c-runner/w3c_runner.ml's `_gsp_dispatch`, never routed over
   a real socket (hub post 17's documented gap).

   Mount point: a fixed path PREFIX, "/data" (the Fuseki/Jena
   convention for a dataset's Graph Store endpoint — chosen so it
   cannot collide with `sparql_protocol_paths` above or with a
   `--web-demo` static tree mounted at "/"). GSP §4.1's three URL
   shapes all resolve under this one prefix:
     1. `/data?default`         -> the default graph (indirect id).
     2. `/data?graph=<URI>`     -> a named graph, IRI given by value
                                    (indirect id).
     3. `/data/<anything>`      -> "direct" identification: the
                                    request URL itself denotes the
                                    graph (the shape every W3C
                                    http-rdf-update test file uses).
   Query-string parsing (shapes 1/2 vs. the exact-key derivation) is
   OCaml glue at the HTTP boundary (rule #15 — string/URL mechanics,
   not a GSP semantic decision); THIS module only decides which
   request paths are routed to the Graph Store dispatcher at all,
   exactly the same "is this a protocol path" role
   `is_sparql_protocol_path` plays for /sparql,/query,/update. *)

let gsp_path_prefix : string = "/data"

(* `s` starts with `pfx`. Non-recursive (String.length / .sub are Tot
   primitives) — same idiom as RDF.Pretty.fst's `starts_with_strict`,
   but non-strict here: "/data" itself (bare, no trailing segment) IS
   a GSP path (the indirect-identification query-string shapes hang
   off exactly that path with no extra path segment). *)
let starts_with (s : string) (pfx : string) : Tot bool =
  let pl = FStar.String.length pfx in
  let sl = FStar.String.length s in
  if sl >= pl then FStar.String.sub s 0 pl = pfx else false

let is_gsp_path (p : string) : Tot bool =
  starts_with p gsp_path_prefix
