/-
L4Factoidal.LWS.Patch — the update operation as an insertions/deletions
formula, with the blank-node refusal the LWS draft states.

Source: https://w3c.github.io/lws-protocol/lws10-core/ (editor's draft, read
2026-09-06), section "For Editors", the CG-to-ED delta list:

  "The PATCH ?insertions formulae MUST NOT contain blank nodes."

That is the ONLY thing the LWS draft says about the shape of a patch. The
shape itself — three formulae named `?conditions`, `?insertions` and
`?deletions`, matched against the target document — and the processing
order come from the Solid Protocol v0.11.0 §5.3.1, which the draft's
Acknowledgements name as its source:

  "Servers MUST process a patch resource against the target document as
  follows: Start from the RDF dataset in the target document, or an empty
  RDF dataset if the target resource does not exist yet. If ?conditions is
  non-empty, find all (possibly empty) variable mappings such that all of
  the resulting triples occur in the dataset. If no such mapping exists, or
  if multiple mappings exist, the server MUST respond with a 409 status
  code. The resulting variable mapping is propagated to the ?deletions and
  ?insertions formulae to obtain two sets of resulting triples. If the set
  of triples resulting from ?deletions is non-empty and the dataset does not
  contain all of these triples, the server MUST respond with a 409 status
  code. The triples resulting from ?deletions are to be removed from the RDF
  dataset. The triples resulting from ?insertions are to be added to the RDF
  dataset […]"

  "The ?insertions and ?deletions formulae MUST NOT contain variables that
  do not occur in the ?conditions formula."

  "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."

A formula is a `SPARQL11.Bgp`: the specification says the formulae consist
"only of triples and/or triple patterns [SPARQL11-QUERY]", which is what a
Basic Graph Pattern is. Matching is therefore `SPARQL.evalBgp` and
instantiation is `SPARQL.instantiateTemplate` — the same functions the
SPARQL engine uses, not a second matcher written for this specification.

This module holds NO syntax. `L4Factoidal.Solid.Server.N3Patch` parses the
`text/n3` document into a `Patch` and calls `apply`.
-/
import L4Factoidal.LWS.Model
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.LWS

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- The three formulae of a patch. An absent formula is the empty one,
which is what the specification says: "When not present, they are presumed
to be the empty formula {}." -/
structure Patch where
  conditions : Bgp := []
  insertions : Bgp := []
  deletions  : Bgp := []
deriving Repr, Inhabited

/-- Why a patch is refused, and the status code the Solid binding gives it.
`blankNodeIn*` and `unboundVariable` are 422 (§5.3.1: "Servers MUST respond
with a 422 status code if a patch document does not satisfy all of the above
constraints"); the rest are 409. -/
inductive PatchError where
  | blankNodeInInsertions
  | blankNodeInDeletions
  | unboundVariable (v : VarName)
  | noMatch
  | multipleMatches
  | deletionsNotPresent
deriving DecidableEq, Repr

def PatchError.status : PatchError → Nat
  | .blankNodeInInsertions | .blankNodeInDeletions | .unboundVariable _ => 422
  | .noMatch | .multipleMatches | .deletionsNotPresent => 409

def PatchError.message : PatchError → String
  | .blankNodeInInsertions => "the ?insertions formula contains a blank node"
  | .blankNodeInDeletions  => "the ?deletions formula contains a blank node"
  | .unboundVariable v     => "variable ?" ++ v ++ " does not occur in the ?where formula"
  | .noMatch               => "the ?where formula matches no part of the target document"
  | .multipleMatches       => "the ?where formula matches the target document more than once"
  | .deletionsNotPresent   => "the target document does not contain every triple of ?deletions"

/-! ## Inspecting a formula -/

def termHasBlankNode : PatternTerm → Bool
  | .bnode _ => true
  | .tripleTerm s p o => termHasBlankNode s || termHasBlankNode p || termHasBlankNode o
  | _ => false

def subjectHasBlankNode : PatternSubject → Bool
  | .bnode _ => true
  | .tripleTerm s p o => termHasBlankNode s || termHasBlankNode p || termHasBlankNode o
  | _ => false

def tpHasBlankNode (tp : TriplePattern) : Bool :=
  subjectHasBlankNode tp.s || termHasBlankNode tp.p || termHasBlankNode tp.o

/-- Does the formula contain a blank node? -/
def formulaHasBlankNode (b : Bgp) : Bool := b.any tpHasBlankNode

def termVars : PatternTerm → List VarName
  | .var v => [v]
  | .tripleTerm s p o => termVars s ++ termVars p ++ termVars o
  | _ => []

def subjectVars : PatternSubject → List VarName
  | .var v => [v]
  | .tripleTerm s p o => termVars s ++ termVars p ++ termVars o
  | _ => []

def tpVars (tp : TriplePattern) : List VarName :=
  subjectVars tp.s ++ termVars tp.p ++ termVars tp.o

/-- The variables of a formula, in order of first appearance is not
guaranteed; membership is what the constraint needs. -/
def formulaVars (b : Bgp) : List VarName := b.flatMap tpVars

/-! ## The constraints -/

/-- Every constraint the specification puts on a patch resource, in the
order the specification lists them. The first violation is the answer. -/
def wellFormed (p : Patch) : Option PatchError :=
  if formulaHasBlankNode p.insertions then some .blankNodeInInsertions
  else if formulaHasBlankNode p.deletions then some .blankNodeInDeletions
  else
    let bound := formulaVars p.conditions
    match (formulaVars p.insertions ++ formulaVars p.deletions).find?
            (fun v => !bound.contains v) with
    | some v => some (.unboundVariable v)
    | none   => none

/-! ## Applying a patch -/

/-- Remove every triple of `ts` from `g`. -/
def graphMinus (g : Graph) (ts : List Triple) : Graph :=
  g.filter (fun t => !(ts.any (fun d => Triple.eqb d t)))

/-- Add every triple of `ts` to `g` as a set. -/
def graphPlus (g : Graph) (ts : List Triple) : Graph :=
  ts.foldl (fun acc t => Graph.add t acc) g

/-- Apply a patch to a graph, or say why not.

The order is the specification's: check the constraints, match
`?conditions`, refuse zero or several matches, instantiate, refuse absent
deletions, then delete and insert. -/
def applyPatch (p : Patch) (g : Graph) : Except PatchError Graph :=
  match wellFormed p with
  | some e => .error e
  | none =>
      let sols := evalBgp p.conditions g
      match sols with
      | []      => .error .noMatch
      | [mu]    =>
          let dels := instantiateTemplate p.deletions mu 0
          let ins  := instantiateTemplate p.insertions mu 0
          if dels.any (fun d => !Graph.mem d g) then .error .deletionsNotPresent
          else .ok (graphPlus (graphMinus g dels) ins)
      | _ :: _ :: _ => .error .multipleMatches

/-- The operation the patch counts as, for the access decision. §5.3.1:
"When ?conditions is non-empty, servers MUST treat the request as a Read
operation. When ?insertions is non-empty, servers MUST (also) treat the
request as an Append operation. When ?deletions is non-empty, servers MUST
treat the request as a Read and Write operation." -/
structure PatchOperations where
  read   : Bool
  append : Bool
  write  : Bool
deriving DecidableEq, Repr

def patchOperations (p : Patch) : PatchOperations :=
  { read   := !p.conditions.isEmpty || !p.deletions.isEmpty
  , append := !p.insertions.isEmpty
  , write  := !p.deletions.isEmpty }

end L4Factoidal.LWS
