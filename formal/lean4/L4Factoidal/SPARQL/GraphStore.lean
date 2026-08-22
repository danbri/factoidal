/-
L4Factoidal.SPARQL.GraphStore — SPARQL 1.1 Graph Store HTTP Protocol,
the pure store model. Port of `formal/fstar/SPARQL.GraphStore.fst`
plus the request-target decoding the F* tree keeps in its runner
(`bin/w3c-runner/w3c_runner.ml` `_gsp_target_of_request`).

Spec: https://www.w3.org/TR/sparql11-http-rdf-update/

A `GraphStore` is one default graph plus named graphs keyed by
string. Keys are plain strings, not `WfIri`, for the reason the F*
gives: a graph under direct identification (§4.1) is named by the
request URL, which in the W3C manifest is a relative path such as
`$GRAPHSTORE$/person/1.ttl` with no colon in it.

What is here:

  * the five operations, one per HTTP method the protocol specifies
    (§5.2 GET, §5.3 PUT, §5.4 DELETE, §5.5 POST, §5.7 HEAD), each
    returning the new store and the pre-existence flag the status
    code depends on; PATCH (§5.6) is answered 405 — the protocol
    makes it optional and this tree does not implement it;
  * the status-code mapping the W3C manifest expects
    (`statusPut` …) and `handle`, the whole state machine as one
    total function `Method → Target → Graph → GraphStore →
    GraphStore × Nat`;
  * `decodeTarget` — §4.1 graph identification from the request URL:
    `?default` is the default graph, `?graph=<IRI>` the named graph
    (indirect identification), anything else the request path itself
    (direct identification). A `graph=` value that is not an IRI
    (empty, or no scheme colon) is a 400 — the subject of
    `decodeTarget_malformed_graph` in `ProtocolTheorems.lean`.

What is NOT here: the W3C-manifest placeholder canonicalisation
(`$GRAPHSTORE$`, `$HOST$`, `$NEWPATH$`) and the test-name heuristics
of the F* runner live in `Harness/ProtocolRun.lean` — they are
manifest-shape glue, not protocol semantics.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.SPARQL.Protocol

namespace L4Factoidal.SPARQL.GraphStore

open L4Factoidal.RDF
open L4Factoidal.SPARQL.Protocol

/-- Graph IRI key (F* `graph_key`). -/
abbrev GraphKey := String

/-- The graph store: a default graph and named graphs (F* `graph_store`). -/
structure GraphStore where
  default : Graph := []
  named   : List (GraphKey × Graph) := []
  deriving Repr

def GraphStore.empty : GraphStore := {}

def lookupNamed (key : GraphKey) : List (GraphKey × Graph) → Option Graph
  | [] => none
  | (k, g) :: tl => if k == key then some g else lookupNamed key tl

/-- Replace (or append) the graph under `key`. -/
def replaceNamed (key : GraphKey) (g : Graph) : List (GraphKey × Graph) → List (GraphKey × Graph)
  | [] => [(key, g)]
  | (k, g0) :: tl => if k == key then (key, g) :: tl else (k, g0) :: replaceNamed key g tl

def removeNamed (key : GraphKey) : List (GraphKey × Graph) → List (GraphKey × Graph)
  | [] => []
  | (k, g0) :: tl => if k == key then tl else (k, g0) :: removeNamed key tl

def namedExists (key : GraphKey) : List (GraphKey × Graph) → Bool
  | [] => false
  | (k, _) :: tl => if k == key then true else namedExists key tl

/-! ## Request target (§4.1) -/

/-- The graph a request addresses (F* `gs_target`). -/
inductive Target where
  | default
  | named (key : GraphKey)
  deriving DecidableEq, Repr

def Target.show : Target → String
  | .default => "<default>"
  | .named k => k

/-- §4.1 graph identification from the request path and query
string. `?default` → the default graph (§4.1.2); `?graph=<IRI>` → the
named graph, after percent-decoding (§4.1.1 indirect); otherwise the
path names the graph (direct). A `graph=` whose decoded value is not
an IRI — empty, or without a scheme colon (`isIri`) — is `400 Bad
Request`. -/
def decodeTarget (path qs : String) : Except Nat Target :=
  let kvs := parseQueryString qs
  if kvs.any (fun kv => kv.1 == "default") then .ok .default
  else
    match firstValue "graph" kvs with
    | some g => if isIri g then .ok (.named g) else .error 400
    | none   => .ok (.named path)

/-! ## Operations (§5) -/

/-- §5.2 GET: the graph at the target. The default graph is always
present (possibly empty) — `some []`; an absent named graph is `none`
(→ 404). -/
def get (t : Target) (s : GraphStore) : Option Graph :=
  match t with
  | .default => some s.default
  | .named k => lookupNamed k s.named

/-- §5.7 HEAD: existence. The default graph "exists" iff non-empty —
the convention the W3C tests (and Fuseki) follow; named graphs by
membership. -/
def head (t : Target) (s : GraphStore) : Bool :=
  match t with
  | .default => !s.default.isEmpty
  | .named k => namedExists k s.named

/-- §5.3 PUT: replace the target. The flag is `true` when the target
existed before (→ 204 No Content), `false` when it was created
(→ 201 Created). -/
def put (t : Target) (g : Graph) (s : GraphStore) : GraphStore × Bool :=
  match t with
  | .default => ({ s with default := g }, !s.default.isEmpty)
  | .named k => ({ s with named := replaceNamed k g s.named }, namedExists k s.named)

/-- §5.5 POST: merge into the target. The flag is `true` when the
target existed (→ 200 OK), `false` when it was created (→ 201 Created
with a Location header). -/
def post (t : Target) (g : Graph) (s : GraphStore) : GraphStore × Bool :=
  match t with
  | .default => ({ s with default := Graph.union g s.default }, !s.default.isEmpty)
  | .named k =>
    let prev := match lookupNamed k s.named with
                | some g0 => g0
                | none    => []
    ({ s with named := replaceNamed k (Graph.union g prev) s.named }, namedExists k s.named)

/-- §5.4 DELETE: remove the target. The flag is `true` when it
existed (→ 204 No Content), `false` otherwise (→ 404 Not Found). -/
def delete (t : Target) (s : GraphStore) : GraphStore × Bool :=
  match t with
  | .default => ({ s with default := [] }, !s.default.isEmpty)
  | .named k => ({ s with named := removeNamed k s.named }, namedExists k s.named)

/-! ## Status codes the W3C manifest expects -/

def statusPut (didReplace : Bool) : Nat := if didReplace then 204 else 201
def statusPost (didExist : Bool) : Nat := if didExist then 200 else 201
def statusDelete (didExist : Bool) : Nat := if didExist then 204 else 404
def statusGet (found : Bool) : Nat := if found then 200 else 404
def statusHead (found : Bool) : Nat := if found then 200 else 404

/-- The HTTP methods §5 specifies. -/
inductive Method where
  | get | head | put | post | delete | patch
  deriving DecidableEq, Repr

def Method.ofString (s : String) : Option Method :=
  match asciiLower s with
  | "get" => some .get
  | "head" => some .head
  | "put" => some .put
  | "post" => some .post
  | "delete" => some .delete
  | "patch" => some .patch
  | _ => none

/-- The state machine: one request against the store gives the new
store and the status code. GET on the default graph answers 200 only
when it is non-empty (the same convention as `head`); PATCH is 405. -/
def handle (m : Method) (t : Target) (payload : Graph) (s : GraphStore) : GraphStore × Nat :=
  match m with
  | .get    => (s, statusGet (head t s))
  | .head   => (s, statusHead (head t s))
  | .put    => let (s', did) := put t payload s; (s', statusPut did)
  | .post   => let (s', did) := post t payload s; (s', statusPost did)
  | .delete => let (s', did) := delete t s; (s', statusDelete did)
  | .patch  => (s, 405)

end L4Factoidal.SPARQL.GraphStore
