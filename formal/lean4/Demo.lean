/- Demo.lean — run with:  lake env lean --run Demo.lean
   A guided tour: build a graph, query it, watch the algebra behave. -/
import L4Factoidal

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Tests

/-! ### A tiny Turtle-ish pretty-printer, so answers read like RDF -/

def showSubj : Subject → String
  | .iri i   => s!"<{i.val}>"
  | .bnode b => s!"_:{b}"

def showTerm : Term → String
  | .iri i   => s!"<{i.val}>"
  | .bnode b => s!"_:{b}"
  | .literal l =>
      let base := s!"\"{l.val.lexicalForm}\""
      match l.val.langTag with
      | some t => base ++ "@" ++ t
      | none   =>
          if l.val.datatype.val = "http://www.w3.org/2001/XMLSchema#string"
          then base else base ++ "^^<" ++ l.val.datatype.val ++ ">"
  | .tripleTerm s p o => s!"<<( {showSubj s} <{p.val}> {showTerm o} )>>"

def showRow (mu : Binding) : String :=
  if mu.isEmpty then "  (empty row)"
  else String.intercalate "   " (mu.reverse.map fun (v, t) => s!"?{v} = {showTerm t}")

def showRows (label : String) (omega : SolutionSeq) : IO Unit := do
  IO.println s!"— {label}: {omega.length} row(s)"
  for mu in omega do IO.println s!"    {showRow mu}"
  IO.println ""

def main : IO Unit := do
  IO.println "=== L4Factoidal live demo ===\n"
  IO.println s!"Graph g has {g.length} triples about Alice and Bob.\n"

  showRows "?s <name> ?n" (evalBgp qNames g)
  showRows "?s <name> ?n . ?s <age> ?a   (correlated on ?s)"
    (evalBgp qNameAge g)

  showRows "FILTER(isAdult) over the same"
    ((GraphPattern.filter isAdult (.bgp qNameAge)).eval g)

  showRows "names MINUS ages  — shared ?s: everything cancels"
    ((GraphPattern.minus (.bgp qNames) (.bgp qNameAge)).eval g)
  showRows "names MINUS ages with DISJOINT variables — §18.5 keeps every row"
    ((GraphPattern.minus (.bgp qNames) (.bgp qAges)).eval g)

  showRows "OPTIONAL age, kept only when adult (LeftJoin)"
    ((GraphPattern.leftJoin (.bgp qNames)
        (.bgp [{ s := .var "s", p := .iri exAge, o := .var "a" }])
        isAdult).eval g)

  -- Monotonicity, live: the theorem evalBgp_mono says growing the
  -- graph never loses answers. Watch it hold:
  let carol : Subject := .iri (iri! "http://example.org/carol")
  let g' := Graph.add { s := carol, p := exName,
                        o := .literal (Literal.string "Carol") } g
  showRows "same name query after ADDING carol (old answers all survive)"
    (evalBgp qNames g')

  -- RDF 1.2 triple terms:
  showRows "RDF 1.2: ?who <claims> <<( ?subj ?pred ?val )>>"
    (evalBgp qClaim gClaims)

  -- Literal equality subtleties, printed:
  IO.println s!"\"chat\"@EN  ==engine==  \"chat\"@en   ? {lEN.eqb lEnLc}"
  IO.println s!"\"chat\"@EN  ==strict==  \"chat\"@en   ? {lEN.termEq lEnLc}"
  IO.println s!"XMLLiteral <a x y> vs <a y x> (attr order) ? {xml1.eqb xml2}"
  IO.println s!"XMLLiteral <a x=1> vs <a x=9>             ? {xml1.eqb xml3}"
