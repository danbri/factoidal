/-
L4Factoidal.SPARQL.UpdateSandbox — the UPDATE sandbox policy.

Port of `formal/fstar/SPARQL.Update.Sandbox.fst` (323 lines). Migrated in
the F\* tree out of `factoidal_http.ml` per iron rules #1 and #15: the
policy is semantics, the HTTP status codes are glue.

The sandbox walks an update's operations and:

- rewrites templates so a write is wrapped in `GRAPH <usergraph>` when
  no outer `GRAPH` clause is present;
- rejects an operation whose target graph — template wrapper or graph
  reference — is not the user's sandbox graph;
- rejects `LOAD` defensively, even though the HTTP layer already filters
  it (`UpdateAnalysis.updateHasLoad`).

## `{authid}` expansion

`expandUserGraph` substitutes `{authid}` in a template. `templatePrefix`
returns the fixed part before the FIRST `{authid}`, which the server uses
to decide which named graphs belong to a sandbox.

`templatePrefix` scans for the literal placeholder ANYWHERE, not for the
first `{`. A template with a stray `{x}` before the real placeholder
splits at the placeholder, not at the brace. The F\* module pins that
with `assert_norm`; here it is a `#guard`, and the stray-brace case is
one of them.

## One difference from the F\*

The F\* `replace_all_aux` indexes by CHARACTER (`FStar.String.length` /
`.sub`), and its own comment says this matches the previous byte-level
OCaml "only when the haystack is ASCII — which is the case for our auth
template". Lean's `String` is a codepoint sequence and
`String.replace` does the whole substitution, so the hand-rolled scan
disappears. On ASCII templates the two agree; on a non-ASCII template
Lean's is codepoint-correct where the OCaml was byte-based. Neither tree
has a test with a non-ASCII template.
-/
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Template expansion -/

def authidPlaceholder : String := "{authid}"

def expandUserGraph (template authid : String) : String :=
  template.replace authidPlaceholder authid

/-- The fixed part of a template before the first `{authid}`. The whole
    template when the placeholder is absent. -/
def templatePrefix (template : String) : String :=
  match template.splitOn authidPlaceholder with
  | []          => template
  | [_]         => template          -- no placeholder: one piece
  | pre :: _    => pre

/-! ## Graph-target checks -/

/-- What an outer `GRAPH` wrapper around a template says. -/
inductive GgpTargetStatus where
  /-- No wrapper, or the wrapper matches the sandbox. -/
  | ok
  /-- The wrapper targets some other IRI. -/
  | mismatch (iri : String)
  /-- The wrapper uses a variable or another non-IRI. -/
  | nonIri
  deriving Repr, DecidableEq, Inhabited

def checkGgpGraphTarget (g : QueryPattern) (usergraph : WfIri) : GgpTargetStatus :=
  match g with
  | .graph pt _ =>
      match pt with
      | .iri i => if i == usergraph then .ok else .mismatch i.val
      | _      => .nonIri
  | _ => .ok

/-- Wrap an unwrapped pattern in `GRAPH <usergraph>`. A pattern that
    already has a wrapper is left alone — the caller has checked that it
    matches. -/
def wrapIfUnwrapped (g : QueryPattern) (usergraph : WfIri) : QueryPattern :=
  match g with
  | .graph _ _ => g
  | _          => .graph (.iri usergraph) g

inductive GgpCheckResult where
  | rewrite (g : QueryPattern)
  | reject (msg : String)

def checkGgp (which : String) (g : QueryPattern) (usergraph : WfIri) : GgpCheckResult :=
  match checkGgpGraphTarget g usergraph with
  | .ok => .rewrite (wrapIfUnwrapped g usergraph)
  | .mismatch iri =>
      .reject (which ++ " targets graph <" ++ iri ++ ">; your sandbox is <"
               ++ usergraph.val ++ ">")
  | .nonIri =>
      .reject (which ++ " uses a non-IRI graph target; only GRAPH <"
               ++ usergraph.val ++ "> is allowed")

inductive GrefCheckResult where
  | ok
  | reject (msg : String)

def checkGref (which : String) (gr : GraphRef) (usergraph : WfIri) : GrefCheckResult :=
  match gr with
  | .graph i =>
      if i == usergraph then .ok
      else .reject (which ++ " targets graph <" ++ i.val ++ ">; your sandbox is <"
                    ++ usergraph.val ++ ">")
  | .default =>
      .reject (which ++ " targets the default graph; your sandbox is <"
               ++ usergraph.val ++ ">")
  | .named =>
      .reject (which ++ " targets NAMED; your sandbox is <" ++ usergraph.val ++ ">")
  | .all =>
      .reject (which ++ " targets ALL graphs; your sandbox is <"
               ++ usergraph.val ++ ">")

/-! ## Per-operation -/

inductive SandboxResult where
  | ok (op : UpdateOp)
  | reject (msg : String)

inductive TplOptResult where
  | rewrite (t : Option QueryPattern)
  | reject (msg : String)

def checkTplOpt (label : String) (t : Option QueryPattern) (usergraph : WfIri) :
    TplOptResult :=
  match t with
  | none   => .rewrite none
  | some g =>
      match checkGgp label g usergraph with
      | .rewrite g' => .rewrite (some g')
      | .reject msg => .reject msg

def sandboxOp (usergraph : WfIri) (op : UpdateOp) : SandboxResult :=
  match op with
  | .insertData g =>
      match checkGgp "INSERT DATA" g usergraph with
      | .rewrite g' => .ok (.insertData g')
      | .reject msg => .reject msg
  | .deleteData g =>
      match checkGgp "DELETE DATA" g usergraph with
      | .rewrite g' => .ok (.deleteData g')
      | .reject msg => .reject msg
  | .deleteWhere g =>
      match checkGgp "DELETE WHERE" g usergraph with
      | .rewrite g' => .ok (.deleteWhere g')
      | .reject msg => .reject msg
  | .modify w delTpl insTpl usingCl whereCl =>
      match checkTplOpt "INSERT/DELETE: DELETE clause" delTpl usergraph with
      | .reject msg => .reject msg
      | .rewrite delTpl' =>
          match checkTplOpt "INSERT/DELETE: INSERT clause" insTpl usergraph with
          | .reject msg => .reject msg
          | .rewrite insTpl' => .ok (.modify w delTpl' insTpl' usingCl whereCl)
  | .clear silent gr =>
      match checkGref "CLEAR" gr usergraph with
      | .ok => .ok (.clear silent gr)
      | .reject msg => .reject msg
  | .drop silent gr =>
      match checkGref "DROP" gr usergraph with
      | .ok => .ok (.drop silent gr)
      | .reject msg => .reject msg
  | .create silent i =>
      if i == usergraph then .ok (.create silent i)
      else .reject ("CREATE targets graph <" ++ i.val ++ ">; your sandbox is <"
                    ++ usergraph.val ++ ">")
  | .add silent src dst =>
      match checkGref "ADD source" src usergraph with
      | .reject msg => .reject msg
      | .ok =>
          match checkGref "ADD dest" dst usergraph with
          | .ok => .ok (.add silent src dst)
          | .reject msg => .reject msg
  | .move silent src dst =>
      match checkGref "MOVE source" src usergraph with
      | .reject msg => .reject msg
      | .ok =>
          match checkGref "MOVE dest" dst usergraph with
          | .ok => .ok (.move silent src dst)
          | .reject msg => .reject msg
  | .copy silent src dst =>
      match checkGref "COPY source" src usergraph with
      | .reject msg => .reject msg
      | .ok =>
          match checkGref "COPY dest" dst usergraph with
          | .ok => .ok (.copy silent src dst)
          | .reject msg => .reject msg
  | .load _ _ _ => .reject "LOAD is not permitted in sandboxed updates"

/-! ## Whole update -/

inductive UpdateSandboxResult where
  | ok (u : Update)
  | error (msg : String)

def sandboxOpsAux (usergraph : WfIri) : List UpdateOp → List UpdateOp →
    Except String (List UpdateOp)
  | acc, []        => .ok acc.reverse
  | acc, op :: rest =>
      match sandboxOp usergraph op with
      | .ok op'     => sandboxOpsAux usergraph (op' :: acc) rest
      | .reject msg => .error msg

def sandboxUpdate (usergraph : WfIri) (u : Update) : UpdateSandboxResult :=
  match sandboxOpsAux usergraph [] u.ops with
  | .error msg => .error msg
  | .ok ops'   => .ok { u with ops := ops' }

/-! ## Build-time checks

### Template expansion, including the stray-brace case the F\* pins -/

#guard expandUserGraph "https://e.org/users/{authid}/graph" "bob"
        == "https://e.org/users/bob/graph"
#guard expandUserGraph "https://e.org/fixed" "bob" == "https://e.org/fixed"
#guard templatePrefix "https://e.org/users/{authid}/graph" == "https://e.org/users/"
#guard templatePrefix "https://e.org/fixed-graph" == "https://e.org/fixed-graph"

/-! A `{` that is NOT `{authid}` must not cause an early split. -/

#guard templatePrefix "https://e.org/{x}/{authid}/graph" == "https://e.org/{x}/"
#guard templatePrefix "https://e.org/{x}/graph" == "https://e.org/{x}/graph"

/-! Every occurrence is replaced, not just the first. -/

#guard expandUserGraph "{authid}/{authid}" "b" == "b/b"

/-! ### The policy -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def gi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩
private def mine : WfIri := gi "mine"
private def bgp0 : QueryPattern := .bgp []

private def isOk : SandboxResult → Bool
  | .ok _ => true | .reject _ => false
private def isWrapped : QueryPattern → Bool
  | .graph _ _ => true | _ => false

/-! An unwrapped template is WRAPPED, not rejected — that is the
    rewriting half of the policy. -/

#guard match sandboxOp mine (.insertData bgp0) with
       | .ok (.insertData g) => isWrapped g
       | _ => false

/-! A template already wrapped in the sandbox graph is left alone, and
    NOT double-wrapped. -/

#guard match sandboxOp mine (.insertData (.graph (.iri mine) bgp0)) with
       | .ok (.insertData (.graph _ inner)) => !isWrapped inner
       | _ => false

/-! A template wrapped in someone else's graph is REJECTED. This is the
    check the sandbox exists for. -/

#guard !isOk (sandboxOp mine (.insertData (.graph (.iri (gi "yours")) bgp0)))
#guard !isOk (sandboxOp mine (.deleteData (.graph (.iri (gi "yours")) bgp0)))
#guard !isOk (sandboxOp mine (.deleteWhere (.graph (.iri (gi "yours")) bgp0)))

/-! A VARIABLE graph target is rejected too — a wrapper that could bind
    to any graph is not a wrapper that targets the sandbox. -/

#guard !isOk (sandboxOp mine (.insertData (.graph (.var "g") bgp0)))

/-! Graph references: only the sandbox graph. DEFAULT, NAMED and ALL are
    each rejected separately, because each is a different way to reach
    outside the sandbox. -/

#guard isOk (sandboxOp mine (.clear false (.graph mine)))
#guard !isOk (sandboxOp mine (.clear false (.graph (gi "yours"))))
#guard !isOk (sandboxOp mine (.clear false .default))
#guard !isOk (sandboxOp mine (.clear false .named))
#guard !isOk (sandboxOp mine (.clear false .all))
#guard !isOk (sandboxOp mine (.drop false .all))

/-! ADD, MOVE and COPY check BOTH ends. A check on the destination alone
    would let data be copied OUT of another graph. -/

#guard isOk (sandboxOp mine (.copy false (.graph mine) (.graph mine)))
#guard !isOk (sandboxOp mine (.copy false (.graph (gi "yours")) (.graph mine)))
#guard !isOk (sandboxOp mine (.copy false (.graph mine) (.graph (gi "yours"))))
#guard !isOk (sandboxOp mine (.move false (.graph (gi "yours")) (.graph mine)))
#guard !isOk (sandboxOp mine (.add false (.graph mine) (.graph (gi "yours"))))

/-! CREATE may only create the sandbox graph. -/

#guard isOk (sandboxOp mine (.create false mine))
#guard !isOk (sandboxOp mine (.create false (gi "yours")))

/-! LOAD is rejected here as well as at the HTTP layer. Two gates, on
    purpose. -/

#guard !isOk (sandboxOp mine (.load false (gi "d") none))
#guard !isOk (sandboxOp mine (.load true (gi "d") (some mine)))

/-! ### A whole update stops at the FIRST rejection

An update whose second operation is out of bounds must not have its
first applied. -/

private def isUOk : UpdateSandboxResult → Bool
  | .ok _ => true | .error _ => false

#guard isUOk (sandboxUpdate mine { ops := [.insertData bgp0, .create false mine] })
#guard !isUOk (sandboxUpdate mine
        { ops := [.insertData bgp0, .create false (gi "yours")] })
#guard isUOk (sandboxUpdate mine { ops := [] })

/-! And an accepted update keeps its operations IN ORDER — the
    accumulator is reversed, and an unreversed one would pass every
    single-operation check above. -/

#guard match sandboxUpdate mine { ops := [.create false mine, .drop false (.graph mine)] } with
       | .ok u => match u.ops with
                  | [.create _ _, .drop _ _] => true
                  | _ => false
       | _ => false

end L4Factoidal.SPARQL
