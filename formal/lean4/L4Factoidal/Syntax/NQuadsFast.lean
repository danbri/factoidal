/-
L4Factoidal.Syntax.NQuadsFast — the N-Quads parser with an indexed
accumulator.

`parseNQuads` builds its `Dataset` with `addQuad`, whose set semantics use
`Graph.add`: a linear `Graph.mem` scan (engine equality `Triple.eqb`) before
every append.  That is quadratic in the size of each graph — measured
natively on 2026-09-02: 11,398 lines 1.4 s, 22,000 lines 2.7 s, 43,106 lines
14.6 s, and 31,325 default-graph label lines 10.3 s.

This module keeps the SAME lexer and the SAME fold (`foldQuadLinesAcc`, the
parametric consumer the streaming proofs are stated over) and replaces only
the accumulator:

- `FastGraph` keeps triples in reverse insertion order plus a hash map from a
  bucket key to the triples carrying that key.  The key is the subject and
  predicate structurally and the object's `Term.joinKey`; `Term.joinKey` is
  constant on `Term.eqb` classes (`Term.joinKey_eq_of_eqb`), `Subject.eqb`
  and `WfIri` equality are structural, so two `Triple.eqb`-equal triples
  always share a bucket.  Membership is decided by `Triple.eqb` INSIDE the
  bucket, exactly as `Graph.mem` decides it over the whole graph — the key
  only narrows the candidates, it never decides equality (the same discipline
  as the fast DISTINCT refinement in `SPARQL/QueryTheorems.lean`).
- `FastDataset` keeps named graphs in a hash map keyed by the structural
  graph name (the reference compares names with `==`) and records the
  first-seen order of names, which is the order `addQuad` appends them.

`FastDataset.toDataset` reverses the accumulated lists, restoring first
occurrence order; `parseNQuadsFast` is therefore intended to be extensionally
equal to `parseNQuads`.  That refinement is currently established by the
`#guard`s below (duplicates, engine-equal language tags, named-graph order,
whole-document comparison) and by `tools/nquads-parser-differential.sh`,
which serialises both parsers' results and compares them byte for byte
(identical on the 43,103-statement life-sciences corpus and the
31,325-statement label file, 2026-09-02); the kernel-checked theorem
`parseNQuadsFast_eq_parseNQuads` is an open obligation, stated rather than
admitted.  No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NQuadsFold
import Std.Data.HashMap

namespace L4Factoidal.Syntax

open L4Factoidal.RDF
open L4Factoidal.Syntax.NQuadsStreaming

/-- Bucket key: subject and predicate structurally, object by `joinKey`. -/
abbrev TripleKey := Subject × WfIri × Term

def tripleKey (t : Triple) : TripleKey := (t.s, t.p, t.o.joinKey)

/-- A graph under construction: reverse insertion order plus buckets. -/
structure FastGraph where
  rev : List Triple := []
  buckets : Std.HashMap TripleKey (List Triple) := ∅

/-- Set-semantics add with bucketed `Triple.eqb` membership — the fast twin
    of `Graph.add t` (which is `if g.mem t then g else g ++ [t]`). -/
def FastGraph.add (t : Triple) (g : FastGraph) : FastGraph :=
  let k := tripleKey t
  let bucket := g.buckets.getD k []
  if bucket.any (fun u => u.eqb t) then g
  else { rev := t :: g.rev, buckets := g.buckets.insert k (t :: bucket) }

def FastGraph.toGraph (g : FastGraph) : Graph := g.rev.reverse

/-- A dataset under construction.  `namesRev` is the reverse of the order in
    which graph names were first seen, which is the order `addQuad` keeps
    them in `Dataset.named`. -/
structure FastDataset where
  default : FastGraph := {}
  namesRev : List Subject := []
  named : Std.HashMap Subject FastGraph := ∅

/-- The fast twin of `addQuad`. -/
def addQuadFast (ds : FastDataset) (t : Triple) (gopt : Option Subject) : FastDataset :=
  match gopt with
  | none => { ds with default := ds.default.add t }
  | some name =>
      match ds.named[name]? with
      | some g => { ds with named := ds.named.insert name (g.add t) }
      | none =>
          { ds with namesRev := name :: ds.namesRev,
                    named := ds.named.insert name (FastGraph.add t {}) }

def FastDataset.toDataset (ds : FastDataset) : Dataset :=
  { default := ds.default.toGraph
  , named := ds.namesRev.reverse.map fun name =>
      { name := name, graph := (ds.named.getD name {}).toGraph } }

/-- Parse a complete N-Quads document with the indexed accumulator.  Same
    lexer, same fold and same fuel as `parseNQuads`; only the accumulator
    differs. -/
def parseNQuadsFast (s : String) (mode : Mode := .rdf11) : Except ParseError Dataset :=
  let cs := s.toList
  (foldQuadLinesAcc mode addQuadFast (cs.length + 1) 0 cs {}).map FastDataset.toDataset

/-! ## Executable agreement with the reference parser

Each guard compares whole `Dataset` values (structural equality) between the
reference and the fast parser on a document chosen to exercise one
accumulator behaviour. -/

private def docDup : String :=
  "<http://e/a> <http://e/p> <http://e/b> .\n" ++
  "<http://e/a> <http://e/p> <http://e/b> .\n" ++
  "<http://e/a> <http://e/p> \"x\"@en .\n" ++
  "<http://e/a> <http://e/p> \"x\"@EN .\n" ++
  "<http://e/a> <http://e/p> \"x\"@fr .\n" ++
  "<http://e/c> <http://e/p> <http://e/b> .\n"

private def docGraphs : String :=
  "<http://e/a> <http://e/p> <http://e/b> <http://g/2> .\n" ++
  "<http://e/a> <http://e/p> <http://e/b> .\n" ++
  "<http://e/a> <http://e/p> <http://e/c> <http://g/1> .\n" ++
  "<http://e/a> <http://e/p> <http://e/b> <http://g/2> .\n" ++
  "<http://e/d> <http://e/p> <http://e/b> <http://g/1> .\n" ++
  "_:b1 <http://e/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> _:gb .\n" ++
  "<http://e/a> <http://e/p> <http://e/b> <http://g/1> .\n"

private def docEmpty : String := "# only a comment\n\n"

private def docBad : String := "<http://e/a> <http://e/p> .\n"

/-- Structural shape of a parse result, for guard-level comparison:
    `Dataset` itself carries no `BEq`. -/
private def shape (r : Except ParseError Dataset) : Option (Graph × List (Subject × Graph)) :=
  r.toOption.map fun ds => (ds.default, ds.named.map fun ng => (ng.name, ng.graph))

#guard shape (parseNQuadsFast docDup) == shape (parseNQuads docDup)
#guard (parseNQuadsFast docDup).toOption.map (fun ds => ds.default.length) == some 4
#guard shape (parseNQuadsFast docGraphs) == shape (parseNQuads docGraphs)
#guard (parseNQuadsFast docGraphs).toOption.map (fun ds => ds.named.map (fun ng => ng.graph.length)) == some [1, 3, 1]
#guard shape (parseNQuadsFast docEmpty) == shape (parseNQuads docEmpty)
#guard (parseNQuadsFast docBad).toOption.isNone && (parseNQuads docBad).toOption.isNone
#guard shape (parseNQuadsFast docGraphs .rdf12) == shape (parseNQuads docGraphs .rdf12)

end L4Factoidal.Syntax
