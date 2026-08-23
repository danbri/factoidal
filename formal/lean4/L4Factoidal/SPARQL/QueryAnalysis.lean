/-
L4Factoidal.SPARQL.QueryAnalysis — structural predicates over queries.

Port of `formal/fstar/SPARQL.Query.Analysis.fst` (53 lines). Companion
to `UpdateAnalysis`. One question per function, all pure and total.

Migrated in the F\* tree out of `factoidal_explain.ml`: the explain dump
walks a parsed query and reports one row per basic graph pattern. The
semantic question "what counts as a BGP under nested patterns" belongs
here per iron rule #1, even though the dump itself is observability
glue.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## `bgpsInQuery`

Collect every non-empty BGP of a query's pattern in source order.
Recurses through join / leftJoin / filter / union / graph / minus /
lateral / bind / service / serviceVar; bottoms out at subSelect,
values, propertyPath and empty, which are not BGPs under the SPARQL 1.1
algebra's flattening rules — the explain dump lists those as their own
constructors instead.

First-seen order, so the dump's row order matches what someone reading
the query top to bottom expects. -/

def collectBgpsAux : List Bgp → QueryPattern → List Bgp
  | acc, .bgp tps         => if tps.isEmpty then acc else tps :: acc
  | acc, .join p1 p2      => collectBgpsAux (collectBgpsAux acc p1) p2
  | acc, .leftJoin p1 p2 _ => collectBgpsAux (collectBgpsAux acc p1) p2
  | acc, .union p1 p2     => collectBgpsAux (collectBgpsAux acc p1) p2
  | acc, .minus p1 p2     => collectBgpsAux (collectBgpsAux acc p1) p2
  | acc, .lateral p1 p2   => collectBgpsAux (collectBgpsAux acc p1) p2
  | acc, .filter _ p1     => collectBgpsAux acc p1
  | acc, .graph _ p1      => collectBgpsAux acc p1
  | acc, .bind _ _ p1     => collectBgpsAux acc p1
  | acc, .service _ _ p1  => collectBgpsAux acc p1
  | acc, .serviceVar _ _ p1 => collectBgpsAux acc p1
  | acc, .subSelect _     => acc
  | acc, .values _ _      => acc
  | acc, .propertyPath _ _ _ => acc
  | acc, .empty           => acc

def bgpsInQuery (q : Query) : List Bgp := (collectBgpsAux [] q.pattern).reverse

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def qi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

private def tp (s : String) : TriplePattern :=
  { s := .iri (qi s), p := .iri (qi "p"), o := .iri (qi "o") }

private def b1 : Bgp := [tp "a"]
private def b2 : Bgp := [tp "b"]

/-! `TriplePattern` derives `Repr` and not `BEq`, so these compare
    lengths and, where order is the point, rendered forms. -/

private def shape (ps : List Bgp) : String := toString (repr ps)

#guard (collectBgpsAux [] (.bgp b1)).length == 1
#guard (collectBgpsAux [] (.bgp [])).length == 0

/-! Source order, not reverse order — the reason `bgpsInQuery` reverses
    the accumulator. `collectBgpsAux` alone returns the last-seen BGP
    first, so these two must differ. -/

#guard shape (collectBgpsAux [] (.join (.bgp b1) (.bgp b2))) == shape [b2, b1]
#guard shape (collectBgpsAux [] (.join (.bgp b1) (.bgp b2))) != shape [b1, b2]
#guard shape (bgpsInQuery (.mk (.select .all) []
        (.join (.bgp b1) (.bgp b2)) none [] {} none none)) == shape [b1, b2]

/-! The four bottoming-out constructors contribute nothing, so a query
    made only of them has no BGP rows. -/

#guard (collectBgpsAux [] (.values [] [])).length == 0
#guard (collectBgpsAux [] .empty).length == 0
#guard (collectBgpsAux [] (.propertyPath (.iri (qi "a"))
                            (.iri (qi "p")) (.iri (qi "o")))).length == 0

/-! A BGP inside FILTER, GRAPH, BIND or SERVICE is still reached — the
    recursion goes through the wrapper, it is not stopped by it. -/

#guard (collectBgpsAux [] (.filter (.boolLit true) (.bgp b1))).length == 1
#guard (collectBgpsAux [] (.graph (.iri (qi "g")) (.bgp b1))).length == 1
#guard (collectBgpsAux [] (.service (qi "e") false (.bgp b1))).length == 1
#guard (collectBgpsAux [] (.bind (.boolLit true) "v" (.bgp b1))).length == 1
#guard (collectBgpsAux [] (.union (.bgp b1)
          (.filter (.boolLit true) (.bgp b2)))).length == 2

/-! A sub-SELECT's own BGPs are NOT reported at this level. The F\*
    source stops there deliberately: the explain dump reports the
    sub-SELECT as its own row. -/

#guard (collectBgpsAux [] (.subSelect
        (.mk (.select .all) [] (.bgp b1) none [] {} none none))).length == 0

end L4Factoidal.SPARQL
