/-
L4Factoidal.SPARQL.UpdateTests — build-time `#guard`s for the SPARQL
1.1 Update parser and semantics, one group per §3 operation, on small
inline Graph Stores.

Every `#guard` evaluates during `lake build`: a wrong answer is a
BUILD FAILURE. The requests are written out as the strings a client
would send, so each guard exercises `parseSparqlUpdate` AND
`applyUpdate` together. Concrete-input facts are guards, never
`decide` (pitfall 10 in `skills/factoidal-lean-basics`).

Not a conformance claim: the W3C sparql11 update suites are scored by
`lake exe l4w3c` over the real manifests (iron rule #6).
-/
import L4Factoidal.SPARQL.UpdateParser

namespace L4Factoidal.SPARQL.UpdateTests

open L4Factoidal.RDF L4Factoidal.SPARQL

def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def exS  : WfIri := iri! "http://example.org/s"
def exS2 : WfIri := iri! "http://example.org/s2"
def exP  : WfIri := iri! "http://example.org/p"
def exQ  : WfIri := iri! "http://example.org/q"
def exO  : WfIri := iri! "http://example.org/o"
def exO2 : WfIri := iri! "http://example.org/o2"
def g1   : WfIri := iri! "http://example.org/g1"
def g2   : WfIri := iri! "http://example.org/g2"

def tSPO  : Triple := { s := .iri exS,  p := exP, o := .iri exO }
def tSPO2 : Triple := { s := .iri exS,  p := exP, o := .iri exO2 }
def tS2PO : Triple := { s := .iri exS2, p := exP, o := .iri exO }
def tSQO  : Triple := { s := .iri exS,  p := exQ, o := .iri exO }

def dsDefault : Dataset := { default := [tSPO], named := [] }
def dsNamed   : Dataset := { default := [], named := [{ name := .iri g1, graph := [tSPO] }] }
def dsBoth    : Dataset := { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO] }] }

/-- Parse and apply; `none` on a parse error or an `UpdateError`. -/
def run? (ds : Dataset) (text : String) : Option Dataset :=
  match parseSparqlUpdate text with
  | .ok u    => (applyUpdate ds u).toOption
  | .error _ => none

/-- The `UpdateError` a request raises, if any. -/
def error? (ds : Dataset) (text : String) : Option UpdateError :=
  match parseSparqlUpdate text with
  | .ok u    => (match applyUpdate ds u with | .error e => some e | .ok _ => none)
  | .error _ => none

/-- Parsed with a BASE, so a relative `<s>` is not what a negative case
is rejected for. -/
def parses (text : String) : Bool :=
  match parseSparqlUpdate text (some "http://example.org/") with
  | .ok _    => true
  | .error _ => false

def opCount (text : String) : Nat :=
  match parseSparqlUpdate text with
  | .ok u    => u.ops.length
  | .error _ => 0

def pfx : String := "PREFIX : <http://example.org/> "

/-! ## §3.1.1 INSERT DATA -/

#guard run? Dataset.empty (pfx ++ "INSERT DATA { :s :p :o }") == some dsDefault
#guard run? Dataset.empty (pfx ++ "INSERT DATA { GRAPH :g1 { :s :p :o } }") == some dsNamed
-- Set semantics: inserting a triple already present changes nothing.
#guard run? dsDefault (pfx ++ "INSERT DATA { :s :p :o }") == some dsDefault
-- Default-graph and GRAPH blocks in one QuadData.
#guard run? Dataset.empty (pfx ++ "INSERT DATA { :s :p :o2 . GRAPH :g1 { :s :p :o } }") == some dsBoth
-- §4.1.1 / W3C insert-data-same-bnode: one `_:b` in two GRAPH blocks of
-- one INSERT DATA is ONE node.
#guard (run? Dataset.empty (pfx ++ "INSERT DATA { GRAPH :g1 { _:b :p :o } GRAPH :g2 { _:b :p :o2 } }")).map
         (fun ds => ds.bnodes.length) == some 1
-- A request-fresh label: `_:b` inserted into a store that already has a
-- blank node labelled `b` is a DIFFERENT node.
#guard (run? { default := [{ s := .bnode "b", p := exP, o := .iri exO }], named := [] }
              (pfx ++ "INSERT DATA { _:b :p :o2 }")).map (fun ds => ds.bnodes.length) == some 2

/-! ## §3.1.2 DELETE DATA -/

#guard run? dsDefault (pfx ++ "DELETE DATA { :s :p :o }") == some Dataset.empty
#guard run? dsNamed (pfx ++ "DELETE DATA { GRAPH :g1 { :s :p :o } }")
       == some { default := [], named := [{ name := .iri g1, graph := [] }] }
-- Deleting an absent triple is a no-op, not an error …
#guard run? dsDefault (pfx ++ "DELETE DATA { :s :q :o }") == some dsDefault
-- … and deleting from an absent graph does not create it.
#guard run? dsDefault (pfx ++ "DELETE DATA { GRAPH :g2 { :s :p :o } }") == some dsDefault

/-! ## §3.1.3.3 DELETE WHERE -/

#guard run? dsBoth (pfx ++ "DELETE WHERE { ?s ?p ?o }")
       == some { default := [], named := [{ name := .iri g1, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "DELETE WHERE { GRAPH ?g { ?s ?p ?o } }")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [] }] }
#guard run? dsBoth (pfx ++ "DELETE WHERE { GRAPH :g1 { :s :p :o } }")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [] }] }

/-! ## §3.1.3 DELETE/INSERT -/

-- Rename a predicate.
#guard run? dsDefault (pfx ++ "DELETE { ?s :p ?o } INSERT { ?s :q ?o } WHERE { ?s :p ?o }")
       == some { default := [tSQO], named := [] }
-- §3.1.3: DELETE runs before INSERT within one operation, so the
-- same triple in both templates survives.
#guard run? dsDefault (pfx ++ "DELETE { :s :p :o } INSERT { :s :p :o } WHERE {}") == some dsDefault
-- An INSERT-only operation; `{}` matches once.
#guard run? Dataset.empty (pfx ++ "INSERT { :s :p :o } WHERE {}") == some dsDefault
-- A template triple with an unbound variable is dropped (§3.1.3.3).
#guard run? dsDefault (pfx ++ "INSERT { ?s :q ?zzz } WHERE { ?s :p ?o }") == some dsDefault
-- A literal subject is ill-formed and dropped.
#guard run? dsDefault (pfx ++ "INSERT { ?o :q :s } WHERE { ?s :p ?o }")
       == some { default := [tSPO, { s := .iri exO, p := exQ, o := .iri exS }], named := [] }
#guard run? { default := [{ s := .iri exS, p := exP, o := .literal (Literal.string "x") }], named := [] }
            (pfx ++ "INSERT { ?o :q :s } WHERE { ?s :p ?o }")
       == some { default := [{ s := .iri exS, p := exP, o := .literal (Literal.string "x") }], named := [] }
-- WITH: the unscoped template targets, and WHERE matches, graph g1.
#guard run? dsNamed (pfx ++ "WITH :g1 INSERT { :s :p :o2 } WHERE { :s :p :o }")
       == some { default := [], named := [{ name := .iri g1, graph := [tSPO, tSPO2] }] }
-- WITH on a DELETE: the template triple leaves g1, not the default graph.
#guard run? dsBoth (pfx ++ "WITH :g1 DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [] }] }
-- USING: WHERE sees g1 as its default graph; the insert targets the store's.
#guard run? dsNamed (pfx ++ "INSERT { ?s ?p ?o } USING :g1 WHERE { ?s ?p ?o }")
       == some { default := [tSPO], named := [{ name := .iri g1, graph := [tSPO] }] }
-- USING NAMED: GRAPH ?g in WHERE ranges over the USING NAMED graphs only.
#guard run? dsBoth (pfx ++ "INSERT { ?s :q ?o } USING NAMED :g1 WHERE { GRAPH ?g { ?s ?p ?o } }")
       == some { default := [tSPO2, tSQO], named := [{ name := .iri g1, graph := [tSPO] }] }
-- GRAPH ?g in a template targets the matched graph.
#guard run? dsBoth (pfx ++ "INSERT { GRAPH ?g { ?s :q ?o } } WHERE { GRAPH ?g { ?s ?p ?o } }")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO, tSQO] }] }
-- §3.1.3.2: a template blank node is fresh PER SOLUTION.
#guard (run? { default := [tSPO, tS2PO], named := [] }
              (pfx ++ "INSERT { ?s :q _:x } WHERE { ?s :p ?o }")).map (fun ds => ds.bnodes.length)
       == some 2
-- … and per OPERATION: the same template in two operations gives two nodes.
#guard (run? dsDefault
              (pfx ++ "INSERT { :s :q _:x } WHERE { :s :p :o } ; INSERT { :s :q _:x } WHERE { :s :p :o }")).map
         (fun ds => ds.bnodes.length) == some 2
-- A blank node a VARIABLE is bound to is the existing node, not a fresh one.
#guard (run? { default := [{ s := .bnode "n", p := exP, o := .iri exO }], named := [] }
              (pfx ++ "INSERT { ?s :q :o2 } WHERE { ?s :p :o }")).map (fun ds => ds.bnodes.length) == some 1
-- §3.1.3.1: a blank node in WHERE is a non-distinguished variable.
#guard run? dsDefault (pfx ++ "DELETE { :s :p :o } WHERE { _:x :p :o }") == some Dataset.empty

/-! ## §3.1.4 LOAD -/

#guard run? dsDefault (pfx ++ "LOAD SILENT <http://example.org/remote.ttl>") == some dsDefault
#guard run? dsDefault (pfx ++ "LOAD SILENT <http://example.org/remote.ttl> INTO GRAPH :g1") == some dsDefault
#guard error? dsDefault (pfx ++ "LOAD <http://example.org/remote.ttl>")
       == some (.loadUnavailable (iri! "http://example.org/remote.ttl"))
#guard (parseSparqlUpdate (pfx ++ "LOAD <http://example.org/remote.ttl>")).toOption.map
         Update.hasNonSilentLoad == some true
#guard (parseSparqlUpdate (pfx ++ "LOAD SILENT <http://example.org/remote.ttl>")).toOption.map
         Update.hasNonSilentLoad == some false

/-! ## §3.1.5 CLEAR -/

#guard run? dsBoth (pfx ++ "CLEAR DEFAULT")
       == some { default := [], named := [{ name := .iri g1, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "CLEAR GRAPH :g1")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [] }] }
#guard run? dsBoth (pfx ++ "CLEAR NAMED")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [] }] }
#guard run? dsBoth (pfx ++ "CLEAR ALL")
       == some { default := [], named := [{ name := .iri g1, graph := [] }] }
#guard error? dsBoth (pfx ++ "CLEAR GRAPH :g2") == some (.graphMissing g2)
#guard run? dsBoth (pfx ++ "CLEAR SILENT GRAPH :g2") == some dsBoth

/-! ## §3.2.1 CREATE, §3.2.2 DROP -/

#guard run? Dataset.empty (pfx ++ "CREATE GRAPH :g1")
       == some { default := [], named := [{ name := .iri g1, graph := [] }] }
#guard error? dsNamed (pfx ++ "CREATE GRAPH :g1") == some (.graphExists g1)
#guard run? dsNamed (pfx ++ "CREATE SILENT GRAPH :g1") == some dsNamed
#guard run? dsBoth (pfx ++ "DROP GRAPH :g1") == some { default := [tSPO2], named := [] }
#guard run? dsBoth (pfx ++ "DROP DEFAULT")
       == some { default := [], named := [{ name := .iri g1, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "DROP NAMED") == some { default := [tSPO2], named := [] }
#guard run? dsBoth (pfx ++ "DROP ALL") == some Dataset.empty
#guard error? dsBoth (pfx ++ "DROP GRAPH :g2") == some (.graphMissing g2)
#guard run? dsBoth (pfx ++ "DROP SILENT GRAPH :g2") == some dsBoth

/-! ## §3.2.3 COPY, §3.2.4 MOVE, §3.2.5 ADD -/

#guard run? dsBoth (pfx ++ "COPY DEFAULT TO GRAPH :g1")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO2] }] }
#guard run? dsBoth (pfx ++ "COPY :g1 TO DEFAULT")
       == some { default := [tSPO], named := [{ name := .iri g1, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "COPY GRAPH :g1 TO GRAPH :g2")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO] },
                                             { name := .iri g2, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "COPY GRAPH :g1 TO GRAPH :g1") == some dsBoth
#guard error? dsBoth (pfx ++ "COPY GRAPH :g2 TO DEFAULT") == some (.graphMissing g2)
#guard run? dsBoth (pfx ++ "COPY SILENT GRAPH :g2 TO DEFAULT") == some dsBoth
#guard run? dsBoth (pfx ++ "MOVE GRAPH :g1 TO DEFAULT") == some { default := [tSPO], named := [] }
#guard run? dsBoth (pfx ++ "MOVE DEFAULT TO GRAPH :g1")
       == some { default := [], named := [{ name := .iri g1, graph := [tSPO2] }] }
#guard error? dsBoth (pfx ++ "MOVE GRAPH :g2 TO DEFAULT") == some (.graphMissing g2)
#guard run? dsBoth (pfx ++ "ADD GRAPH :g1 TO DEFAULT")
       == some { default := [tSPO2, tSPO], named := [{ name := .iri g1, graph := [tSPO] }] }
#guard run? dsBoth (pfx ++ "ADD DEFAULT TO GRAPH :g2")
       == some { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO] },
                                             { name := .iri g2, graph := [tSPO2] }] }
#guard error? dsBoth (pfx ++ "ADD GRAPH :g2 TO DEFAULT") == some (.graphMissing g2)
#guard run? dsBoth (pfx ++ "ADD SILENT GRAPH :g2 TO DEFAULT") == some dsBoth

/-! ## [29] The request: separators, prologue, empty request -/

#guard opCount "" == 0
#guard opCount (pfx ++ "CREATE GRAPH :g1 ;") == 1
#guard opCount (pfx ++ "CREATE GRAPH :g1 ; DROP GRAPH :g1") == 2
-- A prologue may recur between operations (§2.1).
#guard opCount "PREFIX a: <http://a/> INSERT DATA { a:s a:p a:o } ; PREFIX b: <http://b/> INSERT DATA { b:s b:p b:o }" == 2
-- The sequence is applied in order: the second operation sees the first's result.
#guard run? Dataset.empty (pfx ++ "CREATE GRAPH :g1 ; INSERT DATA { GRAPH :g1 { :s :p :o } } ; DROP GRAPH :g1")
       == some Dataset.empty
-- BASE resolves relative IRIs in a following operation.
#guard run? Dataset.empty "BASE <http://example.org/> INSERT DATA { <s> <p> <o> }" == some dsDefault

/-! ## Rejections — the W3C syntax-update-1 negative fixtures, verbatim -/

#guard !parses "LOAD ;"                                           -- bad-01
#guard !parses "CREATE DEAFULT"                                   -- bad-02
#guard !parses "DELETE DATA { ?s <p> <o> }"                       -- bad-03
#guard !parses "INSERT DATA { GRAPH ?g {<s> <p> <o> } }"          -- bad-04
#guard !parses "DELETE DATA { GRAPH <G> { <s> <p> <o> . GRAPH <G1> { <s> <p1> 'o1' } } }" -- bad-05
#guard !parses "INSERT WHERE { ?s ?p ?o }"                        -- bad-06
#guard !parses "CREATE GRAPH <g>\nLOAD <remote> INTO GRAPH <g>"   -- bad-07
#guard !parses "CREATE GRAPH <g>\n;;\nLOAD <remote> INTO GRAPH <g>" -- bad-08
#guard !parses "CREATE GRAPH <g>\n;\nLOAD <remote> INTO GRAPH <g>\n;;" -- bad-09
#guard !parses "DELETE WHERE { _:a <p> <o> }"                     -- bad-10
#guard !parses "DELETE { <s> <p> [] } WHERE { ?x <p> <o> }"       -- bad-11
#guard !parses "DELETE DATA { _:a <p> <o> }"                      -- bad-12
-- §19.6 (syntax-update-54): a DATA-block label reused across operations.
#guard !parses "INSERT DATA { _:b1 <p> <o> } ; INSERT DATA { _:b1 <p> <o2> }"
-- … but a TEMPLATE may reuse a label across operations (basic-update).
#guard parses "INSERT { <s> <p> _:b1 } WHERE {} ; INSERT { <s> <p> _:b1 } WHERE {}"
#guard !parses ";"
#guard !parses "INSERT DATA { <s> <p> <o> } extra"
-- A property path is not ground data.
#guard !parses "INSERT DATA { <s> <p>/<q> <o> }"

end L4Factoidal.SPARQL.UpdateTests
