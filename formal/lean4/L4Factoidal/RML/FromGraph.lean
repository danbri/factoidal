/-
L4Factoidal.RML.FromGraph — read a mapping document, which is RDF,
into `RML.Model`.

A mapping is not a file format: it is a GRAPH, and the reader walks it
by predicate. A term (subject, predicate, object) that the model has
no place for is skipped rather than guessed at; a triples map with no
subject map produces no triples at all, which is what a mapping that
says nothing about subjects should produce.
-/
import L4Factoidal.RML.Model
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RML

open L4Factoidal.RDF

def rmlNs : String := "http://w3id.org/rml/"
def rdfTypeStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- A subject or object as the key the reader indexes by. Blank nodes
    and IRIs are both node identities here, so one string names
    either — and the two spaces are kept apart by the `_:` prefix,
    which no IRI has. -/
def nodeKey : Term → Option String
  | .iri i   => some i.val
  | .bnode b => some ("_:" ++ b)
  | _        => none

def subjKey : Subject → String
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

/-- Every object of `(s, rml:p)`. -/
def objectsOf (g : Graph) (s : String) (p : String) : List Term :=
  (g.filter (fun t => subjKey t.s == s && t.p.val == p)).map (·.o)

def objOf (g : Graph) (s p : String) : Option Term := (objectsOf g s p).head?

def strOf (g : Graph) (s p : String) : Option String :=
  (objOf g s p).bind (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | _          => none)

def nodesOf (g : Graph) (s p : String) : List String :=
  (objectsOf g s p).filterMap nodeKey

/-- The `rml:termType` an IRI names. -/
def termTypeOf (iri : String) : Option TermType :=
  if iri == rmlNs ++ "IRI" then some .iri
  else if iri == rmlNs ++ "URI" then some .uri
  else if iri == rmlNs ++ "UnsafeIRI" then some .unsafeIri
  else if iri == rmlNs ++ "BlankNode" then some .blankNode
  else if iri == rmlNs ++ "Literal" then some .literal
  else none

/-- A TERM MAP at node `n`, or the SHORTCUT form where the value sits
    directly on the parent (`rml:predicate ex:id` rather than
    `rml:predicateMap [ rml:constant ex:id ]`). -/
def termMapAt (g : Graph) (n : String) : TermMap :=
  let form : TermMapForm :=
    match strOf g n (rmlNs ++ "template") with
    | some t => .template t
    | none =>
      match strOf g n (rmlNs ++ "reference") with
      | some r => .reference r
      | none =>
        match objOf g n (rmlNs ++ "constant") with
        | some t => .constant t
        | none   => .unknown
  { form     := form
    termType := (strOf g n (rmlNs ++ "termType")).bind termTypeOf
    datatype := strOf g n (rmlNs ++ "datatype")
    language := strOf g n (rmlNs ++ "language") }

/-- A constant term map from a shortcut object. -/
def constantMap (t : Term) : TermMap := { form := .constant t }

/-- Term maps for a property that has both a MAP form and a SHORTCUT
    form — `rml:predicateMap` / `rml:predicate`, `rml:objectMap` /
    `rml:object`, `rml:graphMap` / `rml:graph`. Both are collected:
    a predicate-object map may state several of each. -/
def mapsFor (g : Graph) (n : String) (mapProp shortcutProp : String) : List TermMap :=
  (nodesOf g n (rmlNs ++ mapProp)).map (termMapAt g)
  ++ (objectsOf g n (rmlNs ++ shortcutProp)).map constantMap

/-- One side of a join: the `rml:child` / `rml:parent` SHORTCUT (a
    reference expression) or the `rml:childMap` / `rml:parentMap` term
    map, which may hold a template. -/
def joinSide (g : Graph) (j : String) (short mapProp : String) : Option TermMap :=
  match strOf g j (rmlNs ++ short) with
  | some r => some { form := .reference r }
  | none   => (nodesOf g j (rmlNs ++ mapProp)).head?.map (termMapAt g)

def joinsAt (g : Graph) (n : String) : List JoinCondition :=
  (nodesOf g n (rmlNs ++ "joinCondition")).filterMap (fun j =>
    match joinSide g j "child" "childMap", joinSide g j "parent" "parentMap" with
    | some c, some p => some { child := c, parent := p }
    | _, _           => none)

/-- An object map: a `rml:parentTriplesMap` makes it a reference, and
    everything else makes it a term map. -/
def objectMapAt (g : Graph) (n : String) : ObjectMap :=
  match (nodesOf g n (rmlNs ++ "parentTriplesMap")).head? with
  | some parent => .ref parent (joinsAt g n)
  | none =>
      .term (termMapAt g n)
        ((nodesOf g n (rmlNs ++ "datatypeMap")).head?.map (termMapAt g))
        ((nodesOf g n (rmlNs ++ "languageMap")).head?.map (termMapAt g))

def pomAt (g : Graph) (n : String) : PredicateObjectMap :=
  { predicates := mapsFor g n "predicateMap" "predicate"
    objects    := (nodesOf g n (rmlNs ++ "objectMap")).map (objectMapAt g)
                  ++ (objectsOf g n (rmlNs ++ "object")).map
                       (fun t => ObjectMap.term (constantMap t) none none)
    graphs     := mapsFor g n "graphMap" "graph" }

def sourceAt (g : Graph) (n : String) : LogicalSource :=
  let src := (nodesOf g n (rmlNs ++ "source")).head?
  { path           := (src.bind (fun s => strOf g s (rmlNs ++ "path"))).getD ""
    iterator       := strOf g n (rmlNs ++ "iterator")
    refFormulation := (strOf g n (rmlNs ++ "referenceFormulation")).getD "" }

/-- Every `rml:TriplesMap` in the graph. A map with NO subject map is
    dropped: it can generate nothing, and keeping it would put an
    entry in the mapping that produces no triples for a reason the
    caller cannot see. -/
def mappingOf (g : Graph) : Mapping :=
  let tmNodes := (g.filter (fun t =>
      t.p.val == rdfTypeStr &&
      (match t.o with
       | .iri i => i.val == rmlNs ++ "TriplesMap"
       | _      => false))).map (fun t => subjKey t.s)
  tmNodes.filterMap (fun n =>
    -- The SUBJECT map, either as a map or as the `rml:subject`
    -- shortcut. Everything else about the triples map is the same
    -- either way — reading the shortcut in a branch of its own
    -- dropped the predicate-object maps with it, so `RMLTC0029a`
    -- produced nothing at all from a mapping that has one.
    let smNode := (nodesOf g n (rmlNs ++ "subjectMap")).head?
    let subject : Option TermMap := match smNode with
      | some sm => some (termMapAt g sm)
      | none    => (objectsOf g n (rmlNs ++ "subject")).head?.map constantMap
    match subject with
    | none    => none
    | some sm =>
        some { id      := n
               base    := strOf g n (rmlNs ++ "baseIRI")
               source  := sourceAt g ((nodesOf g n (rmlNs ++ "logicalSource")).head?.getD "")
               subject := sm
               classes := (smNode.map (fun x =>
                            (objectsOf g x (rmlNs ++ "class")).filterMap (fun t =>
                              match t with | .iri i => some i.val | _ => none))).getD []
               graphs  := (smNode.map (fun x => mapsFor g x "graphMap" "graph")).getD []
               poms    := (nodesOf g n (rmlNs ++ "predicateObjectMap")).map (pomAt g) })

end L4Factoidal.RML
