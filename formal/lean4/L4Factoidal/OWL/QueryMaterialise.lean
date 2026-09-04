/-
L4Factoidal.OWL.QueryMaterialise — query-time materialisation for the
query's anonymous class expressions.

## The defect this repairs

`SELECT * WHERE { ?parent a [ a owl:Restriction ; owl:onProperty
:hasChild ; owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger ;
owl:onClass :Female ] }` (the W3C entailment-regime test `parent7`)
returned 0 rows through `evalSelectOwl`; the correct answer is one row.

The rewrite (`QueryRewriteExpand`, the `cardN == 1` qualified branch)
turns that pattern into a search for a node in the DATA carrying the
restriction's four shape triples, plus a membership triple and the
anchor. The F\* engine satisfies that search because its closure
materialises a canonical restriction node and types individuals into it
— over-broadly, which is what the anchor then filters
(<https://github.com/danbri/factoidal/issues/236>). The Lean closure
materialises no such node, so the rewritten query matched nothing.

## The repair, and why it is sound

Before evaluation, for each maximum-qualified-cardinality-one shape in
the QUERY's basic graph patterns, add to the default graph one fresh
canonical node carrying the four shape triples, and one membership
triple per individual whose membership `Mat.isMember` PROVES — the
filler-bound rule from `Materialise.lean`: an individual inside
`∀ p. {a₁ … a_m}` with `m ≤ 1` has at most one distinct `p`-filler in
any model. Every added membership is entailed, so adding it cannot
create a row a model could refuse; individuals whose membership is
unprovable are not added, so no spurious rows appear — the two wrongs
of the F\* route (over-typing, then anchor-filtering) are replaced by
one sound step.

ⓘ Scope: basic graph patterns reachable without entering a sub-SELECT.
A counting class expression inside a sub-SELECT keeps the old
behaviour (no canonical node, no rows) rather than a wrong one.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteNested
import L4Factoidal.OWL.Materialise

namespace L4Factoidal.OWL.QueryMaterialise

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.OWL
open L4Factoidal.OWL.RL
open L4Factoidal.OWL.QueryRewriteCore

/-- Every basic graph pattern reachable without entering a
sub-SELECT. -/
def bgpsOf : QueryPattern → List Bgp
  | .bgp b => [b]
  | .join l r => bgpsOf l ++ bgpsOf r
  | .union l r => bgpsOf l ++ bgpsOf r
  | .minus l r => bgpsOf l ++ bgpsOf r
  | .lateral l r => bgpsOf l ++ bgpsOf r
  | .leftJoin l r _ => bgpsOf l ++ bgpsOf r
  | .filter _ p => bgpsOf p
  | .graph _ p => bgpsOf p
  | .bind _ _ p => bgpsOf p
  | .service _ _ p => bgpsOf p
  | .serviceVar _ _ p => bgpsOf p
  | _ => []

/-- The GROUND triples of a basic graph pattern: those with a
blank-node subject, IRI predicate, and constant object. These are the
triples that state a class expression inside the query. -/
def groundTriples (b : Bgp) : List Triple :=
  b.filterMap (fun tp =>
    match tp.s, tp.p, tp.o with
    | .bnode k, .iri p, .iri o => some ⟨.bnode k, p, .iri o⟩
    | .bnode k, .iri p, .bnode o => some ⟨.bnode k, p, .bnode o⟩
    | .bnode k, .iri p, .literal o => some ⟨.bnode k, p, .literal o⟩
    | _, _, _ => none)

/-- The blank nodes standing in CLASS position: the object of an
`rdf:type` pattern. These are the query's anonymous class
expressions. -/
def ceMarkerKeys (b : Bgp) : List BNodeId :=
  (b.filterMap (fun tp =>
    match tp.p, tp.o with
    | .iri p, .bnode k => if p == rdfType then some k else none
    | _, _ => none)).eraseDups

def canonLabel (k : String) : BNodeId := "_cecanon_" ++ k

/-- The blank-node-reachable subtree of `k` inside `ts`, every blank
node renamed into the canonical namespace of `k` — so the added
triples can collide with nothing. -/
partial def canonSubtree (ts : List Triple) (k : BNodeId) : List Triple :=
  let rename (b : BNodeId) : BNodeId :=
    if b == k then canonLabel k else canonLabel k ++ "_" ++ b
  let rec walk (queue : List BNodeId) (seen : List BNodeId)
      (acc : List Triple) (fuel : Nat) : List Triple :=
    match fuel, queue with
    | 0, _ => acc
    | _, [] => acc
    | fuel + 1, b :: rest =>
        if seen.contains b then walk rest seen acc fuel
        else
          let mine := ts.filter (fun t => t.s == Subject.bnode b)
          let next := mine.filterMap (fun t =>
            match t.o with | .bnode b2 => some b2 | _ => none)
          let renamed := mine.map (fun t =>
            { t with s := Subject.bnode (rename b),
                     o := match t.o with
                          | .bnode b2 => Term.bnode (rename b2)
                          | o => o })
          walk (rest ++ next) (b :: seen) (acc ++ renamed) fuel
  walk [k] [] [] (ts.length + 1)

/-- The candidate individuals: every subject of the graph, once. -/
def subjectsOf (g : Graph) : List Subject :=
  (g.map (·.s)).eraseDups

/-- The canonical node for one query class expression, with its proved
members. Skipped (empty) when the expression parses to a named class
or to nothing — the closure answers those. -/
def canonTriples (g : Graph) (qts : List Triple) (k : BNodeId) : List Triple :=
  let qst := RL.Store.ofGraph qts
  let ce := parseClassExpr qst (Term.bnode k) (qts.length + 8)
  match ce with
  | .unknown => []
  | .named _ => []
  | _ =>
      let st := RL.Store.ofGraph g
      let proved (i : Subject) : Bool :=
        Mat.runWork (Mat.isMember st i ce (g.length + 64)) == some true
      -- `∃ p. F` with a NESTED filler is rewritten into the edge
      -- pattern `subj p ?v` conjoined with `F` expanded at `?v`
      -- (`QueryRewriteExpand`, someValuesFrom arm), so membership
      -- triples are invisible to that query form. For each individual
      -- whose membership the TYPE route proves — an asserted type
      -- `∃ p. c'` with `c' ⊑ F` (`Mat.ceEntailsCe`) — and whose
      -- known `p`-successors do NOT already prove membership, add the
      -- comprehension witness the type asserts: a fresh blank node as
      -- `p`-successor, typed `c'`. Entailed (the existential read
      -- back as a blank node), and added only when the edge pattern
      -- would otherwise miss the proved member, so no row is doubled.
      -- A NAMED-filler `∃ p. F` is never rewritten
      -- (`restrictionHasNestedFiller`), so the membership triples
      -- below serve that form; the witness edges do not match it.
      let witnesses : List Triple :=
        match ce with
        | .someOf p c =>
            let fuel := g.length + 64
            (subjectsOf g).flatMap (fun i =>
              if Mat.runWork (Mat.anyIsMember st (Mat.successors st i p) c fuel)
                   == some true
              then []
              else
                match (Mat.typeCEsOf st i fuel).findSome? (fun tce =>
                    match tce with
                    | .someOf q (.named c') =>
                        if q == p && Mat.ceEntailsCe st (.named c') c
                        then some c' else none
                    | _ => none) with
                | some c' =>
                    let w : BNodeId := canonLabel k ++ "_w_" ++
                      (match i with
                       | .iri x => x.val
                       | .bnode b => b)
                    [⟨i, p, Term.bnode w⟩,
                     ⟨.bnode w, rdfType, Term.iri c'⟩]
                | none => [])
        | _ => []
      witnesses ++
      -- One realisation per class expression, because answers are
      -- bags: a second node stating the same expression would double
      -- every member's row. If a node already states it — asserted in
      -- the data, or materialised by the closure — the missing PROVED
      -- members are typed into THAT node; otherwise a canonical node
      -- is created carrying the query's shape and the proved members.
      match (subjectsOf g).find? (fun s =>
              ClassExpr.beq (parseClassExpr st s.toTerm (g.length + 8)) ce) with
      | some node =>
          (subjectsOf g).filterMap (fun i =>
            let t : Triple := ⟨i, rdfType, node.toTerm⟩
            if proved i && !(g.any (fun t0 => t0 == t))
            then some t else none)
      | none =>
          let shape := canonSubtree qts k
          let members : List Triple :=
            (subjectsOf g).filterMap (fun i =>
              if proved i
              then some ⟨i, rdfType, Term.bnode (canonLabel k)⟩ else none)
          shape ++ members

/-- Augment the dataset's default graph for every anonymous class
expression in the query. A query with none leaves the dataset
unchanged. -/
def augmentForQuery (ds : Dataset) (q : Query) : Dataset :=
  -- The parser splits `?x a _:b` and `_:b`'s property list into
  -- SEPARATE basic graph patterns of one join, so the expression is
  -- only parseable from their UNION.
  let bgps := bgpsOf q.pattern
  let qts := groundTriples bgps.flatten
  let keys := (bgps.flatMap ceMarkerKeys).eraseDups
  let adds := keys.flatMap (fun k => canonTriples ds.default qts k)
  match adds with
  | [] => ds
  | _ => { ds with default := ds.default ++ adds }

/-! ## Build-time checks -/

/-! A query pattern with no restriction shape changes nothing. -/
#guard
  ((augmentForQuery { Dataset.empty with default := [] }
      (mkQuery (.select .all) (.bgp []))).default.length == 0)

end L4Factoidal.OWL.QueryMaterialise
