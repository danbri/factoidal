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
