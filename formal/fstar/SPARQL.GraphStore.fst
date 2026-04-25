module SPARQL.GraphStore

(** ======================================================================== **)
(** SPARQL 1.1 Graph Store HTTP Protocol — pure store model                  **)
(**                                                                          **)
(** Reference: https://www.w3.org/TR/sparql11-http-rdf-update/               **)
(**                                                                          **)
(** A `graph_store` is a logical RDF dataset addressable via URI, with a     **)
(** distinguished default graph. The five operations below match the         **)
(** five HTTP methods specified by the protocol. We deliberately keep the    **)
(** model untyped over IRIs (plain `string`) because GSP graph IRIs are     **)
(** dereferenceable URIs, *not* `wf_iri` per RDF.Graph.Executable's          **)
(** colon-required predicate. The runner glue does its own URL parsing.     **)
(**                                                                          **)
(** Constraints (CLAUDE.md iron rules #1, #2, #4):                           **)
(**   - F* is the source of truth for the GSP semantic decisions             **)
(**     (PUT-creates-vs-replaces, POST-merges, DELETE-existence).            **)
(**   - No `assume val`. No `--lax`. No `--admit_smt_queries`.               **)
(**   - All recursion is structural over the named-graph list.               **)
(**                                                                          **)
(** Phase 1 (Agent Pe, 2026-04-25): in-process per-test dispatch.            **)
(** Phase 2+ : cross-test (manifest-ordered) replay; Turtle round-trip.      **)
(** ======================================================================== **)

open RDF.Graph.Executable

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"

(* Graph IRI key. Plain string because GSP graph IRIs may not contain a
   colon in their relative-path form (the runner does URL resolution). *)
type graph_key = string

(* Named-graph slot in the store. *)
noeq type gs_named = {
  gn_iri   : graph_key;
  gn_graph : rdf_graph;
}

(* The graph store: one default graph plus a list of named graphs. *)
noeq type graph_store = {
  gs_default : rdf_graph;
  gs_named   : list gs_named;
}

let empty_store : graph_store = {
  gs_default = empty_graph;
  gs_named   = [];
}

(* Look up a named graph by IRI key. *)
let rec lookup_named (key : graph_key) (xs : list gs_named)
  : Tot (option rdf_graph) (decreases xs) =
  match xs with
  | [] -> None
  | hd :: tl -> if hd.gn_iri = key then Some hd.gn_graph else lookup_named key tl

(* Replace (or insert) a named graph by IRI key. The new entry is appended
   if no match is found; otherwise the matching slot is overwritten. *)
let rec replace_named (key : graph_key) (g : rdf_graph) (xs : list gs_named)
  : Tot (list gs_named) (decreases xs) =
  match xs with
  | [] -> [{ gn_iri = key; gn_graph = g }]
  | hd :: tl ->
    if hd.gn_iri = key
    then { gn_iri = key; gn_graph = g } :: tl
    else hd :: replace_named key g tl

(* Drop a named graph by IRI key. *)
let rec remove_named (key : graph_key) (xs : list gs_named)
  : Tot (list gs_named) (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl ->
    if hd.gn_iri = key then tl
    else hd :: remove_named key tl

(* Existence check on a named graph. *)
let rec named_exists (key : graph_key) (xs : list gs_named)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | hd :: tl -> if hd.gn_iri = key then true else named_exists key tl

(** ====================================================================== **)
(** GSP request target: either default-graph or named graph                **)
(** ====================================================================== **)

type gs_target =
  | GT_Default : gs_target
  | GT_Named   : graph_key -> gs_target

(** ====================================================================== **)
(** GSP operations (one per HTTP method)                                    **)
(** ====================================================================== **)

(* GET. Returns the graph at the target, or `None` if not present.

   Per W3C GSP §5: the default graph is "always present" at the
   server's discretion — it MAY be empty. We return `Some []` for the
   default graph when it's empty, so the runner can choose the response
   code. Named graphs return `None` when absent (→ 404). *)
let gsp_get (t : gs_target) (s : graph_store) : option rdf_graph =
  match t with
  | GT_Default  -> Some s.gs_default
  | GT_Named k  -> lookup_named k s.gs_named

(* HEAD. Existence check.

   Default-graph existence follows the W3C convention: present iff
   non-empty (this matches the Fuseki/Jena behaviour the W3C tests
   assume). Named graphs follow the obvious set membership. *)
let gsp_head (t : gs_target) (s : graph_store) : bool =
  match t with
  | GT_Default  -> Cons? s.gs_default
  | GT_Named k  -> named_exists k s.gs_named

(* PUT. Replaces the target with the given graph. Returns the new store
   and a `did_replace` flag — `true` if the target previously existed
   (response 204 No Content), `false` if it was created (201 Created). *)
let gsp_put (t : gs_target) (g : rdf_graph) (s : graph_store)
  : graph_store & bool =
  match t with
  | GT_Default ->
    let did = Cons? s.gs_default in
    ({ s with gs_default = g }, did)
  | GT_Named k ->
    let did = named_exists k s.gs_named in
    ({ s with gs_named = replace_named k g s.gs_named }, did)

(* POST. Merges the given graph into the target. Returns the new store
   and a `did_exist` flag — `true` if the target previously existed
   (response 200 OK), `false` if it was created (201 Created with
   Location header). *)
let gsp_post (t : gs_target) (g : rdf_graph) (s : graph_store)
  : graph_store & bool =
  match t with
  | GT_Default ->
    let did = Cons? s.gs_default in
    let merged = graph_union g s.gs_default in
    ({ s with gs_default = merged }, did)
  | GT_Named k ->
    let did = named_exists k s.gs_named in
    let prev = match lookup_named k s.gs_named with
               | Some g0 -> g0
               | None    -> empty_graph in
    let merged = graph_union g prev in
    ({ s with gs_named = replace_named k merged s.gs_named }, did)

(* DELETE. Removes the target. Returns the new store and a `did_exist`
   flag — `true` if the target previously existed (response 200 OK or
   204 No Content), `false` if not (response 404 Not Found). *)
let gsp_delete (t : gs_target) (s : graph_store) : graph_store & bool =
  match t with
  | GT_Default ->
    let did = Cons? s.gs_default in
    ({ s with gs_default = empty_graph }, did)
  | GT_Named k ->
    let did = named_exists k s.gs_named in
    ({ s with gs_named = remove_named k s.gs_named }, did)

(** ====================================================================== **)
(** Convenience: status-code mapping for typical GSP outcomes              **)
(**                                                                        **)
(** These are the spec-derived status codes for the W3C test suite.       **)
(** Real servers may pick alternatives (200 vs 204 for PUT-replace, etc); **)
(** the runner's `accept_status` helper treats those alternatives as      **)
(** equivalent. The numbers below are the ones the W3C manifest expects.  **)
(** ====================================================================== **)

let status_put (did_replace : bool) : int =
  if did_replace then 204 else 201

let status_post (did_exist : bool) : int =
  if did_exist then 200 else 201

let status_delete (did_exist : bool) : int =
  if did_exist then 204 else 404

let status_get_named (found : bool) : int =
  if found then 200 else 404

let status_head_named (found : bool) : int =
  if found then 200 else 404

#pop-options
