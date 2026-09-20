/-
L4Factoidal.Syntax.TurtleProvenanceTests — build-time `#guard`s for
`Syntax.TurtleProvenance`: spans, ordinals, agreement with `parseTurtle`
on a document with a directive, a predicateObjectList and a comment, and
the shape of the reified graph.
-/

import L4Factoidal.Syntax.TurtleProvenance

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

private def doc : String :=
  "@prefix ex: <http://example.org/> .\n" ++      -- statement 0, no triples
  "ex:a ex:p ex:b ; ex:q \"x\" .\n" ++           -- statement 1, two triples
  "# a comment\n" ++
  "ex:c ex:p ex:d .\n"                             -- statement 2, one triple

private def annotated : List (Triple × TripleProvenance) :=
  match parseTurtleProv doc with
  | .ok xs => xs
  | .error _ => []

/-- `Except` has no `BEq`; compare the two parses by hand. -/
private def sameParse : Except ParseError Graph → Except ParseError Graph → Bool
  | .ok g1,    .ok g2    => g1 == g2
  | .error e1, .error e2 => e1 == e2
  | _,         _         => false

/- Three triples come out, in document order, and they are `parseTurtle`'s. -/
#guard annotated.length == 3
#guard sameParse ((parseTurtleProv doc).map (List.map Prod.fst)) (parseTurtle doc)

/- Statement ordinals count directives; ordinals within a statement restart at 0. -/
#guard annotated.map (fun x => (x.2.span.index, x.2.ordinal)) == [(1, 0), (1, 1), (2, 0)]

/- Spans: statement 1 starts after the prefix line and ends just past its `.`;
statement 2 starts after the comment line. -/
#guard annotated.map (fun x => (x.2.span.startPos, x.2.span.endPos))
  == [(36, 63), (36, 63), (76, 92)]
#guard (doc.toList.drop 36).take 27 == "ex:a ex:p ex:b ; ex:q \"x\" .".toList
#guard (doc.toList.drop 76).take 16 == "ex:c ex:p ex:d .".toList

/- A syntax error surfaces with the same position as `parseTurtle`. -/
private def bad : String := "ex:a ex:p .\n"
#guard (match parseTurtleProv bad, parseTurtle bad with
        | .error e1, .error e2 => e1 == e2
        | _, _ => false)

/- Reification: six triples per annotated triple, reifiers linked by `rdf:reifies`. -/
private def reified : Graph := reifyProvenance "file:doc.ttl" annotated
#guard reified.length == 18
#guard (reified.filter (fun t => t.p == rdfReifies)).length == 3
#guard (reified.filter (fun t => t.p == rdfReifies)).map (fun t => t.s)
  == [.bnode "prov/1/0", .bnode "prov/1/1", .bnode "prov/2/0"]
#guard (match reified.head? with
        | some ⟨.bnode "prov/1/0", _, .tripleTerm (.iri s) p (.iri o)⟩ =>
            s.val == "http://example.org/a" && p.val == "http://example.org/p"
              && o.val == "http://example.org/b"
        | _ => false)

/- Dataset form: one named graph per triple, numbered from 1, five facts each
in the default graph, and the N-Quads serialiser accepts it. -/
private theorem baseIri : isIri "https://factoidal.example/data/" = true := by decide
private def graphBase : WfIri := ⟨"https://factoidal.example/data/", baseIri⟩
private def ds : Dataset := perTripleDataset graphBase "file:doc.ttl" annotated
#guard ds.named.length == 3
#guard ds.named.map (fun ng => ng.name)
  == [.iri (graphName graphBase 1), .iri (graphName graphBase 2), .iri (graphName graphBase 3)]
#guard (graphName graphBase 2).val == "https://factoidal.example/data/2"
#guard (ds.named.map NamedGraph.graph).flatten == annotated.map Prod.fst
#guard ds.default.length == 15
#guard (match Dataset.toNQuads ds with
        | .ok text => ((text.splitOn "\n").filter (fun l => !l.isEmpty)).length == 18
                      && (text.splitOn "<https://factoidal.example/data/1> .").length == 2
        | .error _ => false)
#guard (match parseTurtleDataset graphBase "file:doc.ttl" doc with
        | .ok d => d.named.length == 3
        | .error _ => false)

/- The span-forgetting fold is the plain fold on this document. -/
#guard (match parseTurtleFoldProv (fun (n : Nat) _ ts => n + ts.length) 0 doc,
              parseTurtleFold (fun (n : Nat) ts => n + ts.length) 0 doc with
        | .ok a, .ok b => a == b && a == 3
        | _, _ => false)

end L4Factoidal.Syntax
