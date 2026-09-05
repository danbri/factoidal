/-
L4Factoidal.Syntax.NQuads — the N-Quads parser and serialiser.

Port of `formal/fstar/Parser.NQuads.fst`'s document-level grammar
(`parse_graph_label` / `parse_opt_graph_label` / `parse_nquad` /
`parse_nquads_strict` / `parse_nquads_strict_12` / `dataset_add_quad`) and
of the N-Quads half of `formal/fstar/RDF.NQuads.Serialize.fst`
(`nq_line_for_triple`, folded over a dataset's named graphs), built on
`Syntax.NTriples` (N-Quads reuses N-Triples' subject/predicate/object/
literal readers verbatim — RDF 1.1 N-Quads §"N-Quads" extends N-Triples
with exactly one addition: an optional fourth GRAPH LABEL slot).

Grammar productions ported (RDF 1.1 N-Quads, https://www.w3.org/TR/n-quads/):
  [1] nquadsDoc  [2] statement  [6] graphLabel
(`[3] subject`, `[4] predicate`, `[5] object`, `[7] literal`, etc. are
identical to N-Triples and are NOT re-ported — `Syntax.NTriples`'s
readers are reused directly.)

Ported entry points: `parseNQuads` (strict — port of `parse_nquads_strict`
/ `parse_nquads_strict_12`; any malformed line aborts the whole parse,
same STRICT design choice as `Syntax.NTriples.parseNTriples` and for the
same reason: a lenient skip-and-recover parser is a CLI/import-pipeline
convenience, not part of the grammar this module specifies). NOT ported:
the F* source's lenient `parse_nquads`/`parse_nquads_12`, the streaming
fold (`fold_nquads`), the `--count` scanners (`count_nquads_quads`,
`validate_*`), and the flat-quad-list convenience (`parse_nquads_flat`) —
all CLI/performance pragmatics over the same grammar.

The blank-node-as-graph-name sentinel encoding the F* source uses
(`"_:label"` packed into the `iri` string slot, because `named_graph.ng_name`
has no sum type — see `docs/designissues/2026-04-25-nquads-bnode-graph-fix.md`)
is NOT needed here and is NOT used: `RDF.NamedGraph.name` is a `Subject`,
exactly the "IRI or blank node" RDF 1.1 Concepts §4 allows, so a parsed
`[6] graphLabel` goes into the dataset unchanged and comes back out of
`Dataset.toNQuads` unchanged. No string encoding stands between the
grammar and the data model.
-/

import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Graph label — [6] graphLabel: `graphLabel ::= IRIREF | BLANK_NODE_LABEL`

A literal is explicitly NOT a legal graph label (RDF 1.1 N-Quads
§"N-Quads", port of `parse_opt_graph_label`'s literal-rejection branch). -/

/-- Read a graph label as a `Subject` (IRI or blank node) — the same shape
as `readSubject`, kept as a distinct reader because the ERROR MESSAGE at
the literal-rejection branch is graph-label-specific (port of
`parse_graph_label`). -/
def readGraphLabel (pos : Nat) (cs : List Char) : Except ParseError (Subject × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (s, pos', rest') =>
          match mkIri pos s with
          | .error e => .error e
          | .ok wi => .ok (.iri wi, pos', rest')
  | '_' :: ':' :: _ =>
      match readBlankNodeLabel pos cs with
      | .error e => .error e
      | .ok (label, pos', rest') => .ok (.bnode label, pos', rest')
  | '"' :: _ => .error ⟨"literals are not allowed as graph names in N-Quads", pos⟩
  | _ => .error ⟨"expected graph label (IRIREF or BLANK_NODE_LABEL)", pos⟩

/-- Optional fourth (graph-label) slot: peeks past whitespace; `none` if
the next non-whitespace character is `.` (default graph). Port of
`parse_opt_graph_label`. -/
def readOptGraphLabel (pos : Nat) (cs : List Char) :
    Except ParseError (Option Subject × Nat × List Char) :=
  let (pos1, cs1) := skipWs pos cs
  match cs1 with
  | '.' :: _ => .ok (none, pos1, cs1)
  | '<' :: _ =>
      (match readGraphLabel pos1 cs1 with
       | .error e => .error e
       | .ok (g, pos', rest') => .ok (some g, pos', rest'))
  | '_' :: ':' :: _ =>
      (match readGraphLabel pos1 cs1 with
       | .error e => .error e
       | .ok (g, pos', rest') => .ok (some g, pos', rest'))
  | '"' :: _ => .error ⟨"literals are not allowed as graph names in N-Quads", pos1⟩
  | _ => .ok (none, pos1, cs1)

/-! ## Statement — [2] statement:
`statement ::= subject predicate object graphLabel? '.'`

Reuses `Syntax.NTriples.readSubject` / `readPredicate` /
`readObject11` / `readObject12` verbatim (RDF 1.1 N-Quads §"N-Quads":
"The syntax of N-Quads is a superset of the syntax for N-Triples […]
extended to represent an optional context"). -/

/-- One N-Quad line (RDF 1.1 object grammar). Port of `parse_nquad`. -/
def readNQuad11 (pos : Nat) (cs : List Char) :
    Except ParseError (Triple × Option Subject × Nat × List Char) :=
  let (pos1, cs1) := skipWs pos cs
  match readSubject pos1 cs1 with
  | .error e => .error e
  | .ok (subj, pos2, cs2) =>
      let (pos3, cs3) := skipWs pos2 cs2
      match readPredicate pos3 cs3 with
      | .error e => .error e
      | .ok (pred, pos4, cs4) =>
          let (pos5, cs5) := skipWs pos4 cs4
          match readObject11 pos5 cs5 with
          | .error e => .error e
          | .ok (obj, pos6, cs6) =>
              match readOptGraphLabel pos6 cs6 with
              | .error e => .error e
              | .ok (gopt, pos7, cs7) =>
                  let (pos8, cs8) := skipWs pos7 cs7
                  match cs8 with
                  | '.' :: cs9 =>
                      .ok ({ s := subj, p := pred, o := obj }, gopt, pos8 + 1, cs9)
                  | _ => .error ⟨"expected '.' terminator", pos8⟩

/-! ### The RDF 1.2 object fuel

`readObject12` takes a fuel that bounds `<<( ... )>>` NESTING, and each level
consumes three characters, so any count of the characters the object can
occupy is a sufficient bound. Until 2026-09-05 the bound was `cs.length`,
which walks the WHOLE remaining input for every statement and is therefore
quadratic in what the caller hands over: in the streaming packer that is a
65,536-character chunk, and `/usr/bin/sample` put 10,159 of 15,405 samples of
a wire-version-10 pack of a 52,428,626-byte skosdex prefix inside that one
`List.length`. Version 10 reads its source as RDF 1.2, so it was the first
route to pay it.

An N-Quads statement never spans a raw line break — a literal carries `\n`
escaped, RDF 1.1 N-Quads section 4 — so the characters up to the next line
break bound the object, and counting them is linear in the line rather than
in the document. The bound is only ever LARGER than the nesting depth it must
cover, so no document that parsed before is refused now and no committed byte
changes. -/
def lineFuelGo : List Char → Nat → Nat
  | [], acc => acc
  | c :: rest, acc => if c == '\n' then acc else lineFuelGo rest (acc + 1)

/-- One more than the number of characters before the next line break. -/
def lineFuel (cs : List Char) : Nat := lineFuelGo cs 1

/-- One N-Quad line (RDF 1.2 object grammar: the object slot may be a
triple term). Port of `parse_nquad_12`. -/
def readNQuad12 (pos : Nat) (cs : List Char) :
    Except ParseError (Triple × Option Subject × Nat × List Char) :=
  let (pos1, cs1) := skipWs pos cs
  match readSubject pos1 cs1 with
  | .error e => .error e
  | .ok (subj, pos2, cs2) =>
      let (pos3, cs3) := skipWs pos2 cs2
      match readPredicate pos3 cs3 with
      | .error e => .error e
      | .ok (pred, pos4, cs4) =>
          let (pos5, cs5) := skipWs pos4 cs4
          match readObject12 (lineFuel cs5) pos5 cs5 with
          | .error e => .error e
          | .ok (obj, pos6, cs6) =>
              match readOptGraphLabel pos6 cs6 with
              | .error e => .error e
              | .ok (gopt, pos7, cs7) =>
                  let (pos8, cs8) := skipWs pos7 cs7
                  match cs8 with
                  | '.' :: cs9 =>
                      .ok ({ s := subj, p := pred, o := obj }, gopt, pos8 + 1, cs9)
                  | _ => .error ⟨"expected '.' terminator", pos8⟩

/-! ## Dataset construction -/

/-- Add one parsed quad to a dataset: no graph label → default graph,
`Some g` → the named graph `g` (created if absent). Port of
`dataset_add_quad`, minus its `graph_add_unchecked` / `dataset_finalise`
prepend-then-reverse performance split (an O(1)-amortised-append
optimisation over the same set semantics `RDF.Graph.add`/`Graph.union`
already implement for this port's executable `Dataset`) — this port adds
directly via `Graph.add`/list-append, matching `RDF.Graph`'s existing
representation. -/
def addQuad (ds : Dataset) (t : Triple) (gopt : Option Subject) : Dataset :=
  match gopt with
  | none => { ds with default := ds.default.add t }
  | some name =>
      match ds.named.find? (fun ng => ng.name == name) with
      | some ng =>
          let updated : NamedGraph := { name := name, graph := ng.graph.add t }
          { ds with named := ds.named.map (fun ng' => if ng'.name == name then updated else ng') }
      | none =>
          { ds with named := ds.named ++ [{ name := name, graph := [t] }] }

/-! ## Document — [1] nquadsDoc

`nquadsDoc ::= statement? (EOL statement?)*`, plus `#`-comments and blank
lines (identical document structure to N-Triples). STRICT: any malformed
line aborts the whole parse. Port of `parse_nquads_strict_acc` /
`parse_nquads_strict_12_acc`. -/
def parseQuadLinesAcc (mode : Mode) :
    Nat → Nat → List Char → Dataset → Except ParseError Dataset
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, cs, ds =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => .ok ds
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          parseQuadLinesAcc mode fuel' pos3 cs3 ds
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseQuadLinesAcc mode fuel' pos2 cs2 ds
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseQuadLinesAcc mode fuel' pos2 cs2 ds
      | _ =>
          let step := match mode with
            | .rdf11 => readNQuad11 pos1 cs1
            | .rdf12 => readNQuad12 pos1 cs1
          match step with
          | .error e => .error e
          | .ok (t, gopt, pos2, cs2) =>
              let ds' := addQuad ds t gopt
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              parseQuadLinesAcc mode fuel' pos5 cs5 ds'

/-- Parse a complete N-Quads document into a `Dataset`. Default mode is
RDF 1.1. Port of `parse_nquads_strict_mode`. -/
def parseNQuads (s : String) (mode : Mode := .rdf11) : Except ParseError Dataset :=
  let cs := s.toList
  parseQuadLinesAcc mode (cs.length + 1) 0 cs Dataset.empty

/-! ## Serialisation

Port of `RDF.NQuads.Serialize.fst`'s `nq_line_for_triple` (named-graph
lines) composed with `Syntax.NTriples`'s default-graph line
(`Triple.toNTriples`) over a whole `Dataset` — the F* source has no single
"serialise a dataset" entry point at this layer either (see the note on
`Graph.toNTriples`); this is the natural `Except`-threaded fold. -/

/-- One line for a triple in a named graph: `s p o g .\n`, where the
graph label `g` is written `<iri>` or `_:label` — the `[6] graphLabel`
production, back out the way it came in. Port of
`nq_line_for_triple`. -/
def namedLine (mode : Mode) (graphName : Subject) (t : Triple) : Except String String :=
  match Term.toNTriples mode t.o with
  | .error e => .error e
  | .ok oStr =>
      .ok (Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++ oStr ++
           " " ++ Subject.toNTriples graphName ++ " .\n")

/-- Serialise a whole `Dataset`: default-graph lines (N-Triples form),
then named-graph lines, input order preserved within each graph. -/
def Dataset.toNQuads (ds : Dataset) (mode : Mode := .rdf11) : Except String String :=
  match Graph.toNTriples ds.default mode with
  | .error e => .error e
  | .ok defaultLines =>
      ds.named.foldl (fun acc ng =>
        match acc with
        | .error e => .error e
        | .ok s =>
            ng.graph.foldl (fun acc2 t =>
              match acc2 with
              | .error e => .error e
              | .ok s2 =>
                  match namedLine mode ng.name t with
                  | .error e => .error e
                  | .ok line => .ok (s2 ++ line))
              (.ok s))
        (.ok defaultLines)

/-! ## Canonical N-Quads (RDF 1.2 N-Quads §canonical form)

https://www.w3.org/TR/rdf12-n-quads/#canonical-quads — the byte-exact
form the W3C `rdf12/rdf-n-quads/c14n` suite compares against. Port of
`RDF.NQuads.Serialize.fst`'s `nq_canon_line_graph`,
`canon_nq_named_lines`, `canon_nq_named` and `canonical_nq_document`.
The term-level rules live in `Syntax.NTriples`
(`Term.toCanonicalNTriples`); only the graph slot is added here.

The F* source writes the graph label as `<iri>` unconditionally
(`nq_canon_line_graph` takes a `string` name), because its
`named_graph.ng_name` is an IRI string. This tree's `NamedGraph.name`
is a `Subject`, so a blank-node graph label round-trips as `_:label`
via `Subject.toNTriples`; on the IRI names the suite uses, the two
renderings are identical. -/

/-- One canonical line for a triple in a named graph. Port of
`nq_canon_line_graph`. -/
def canonNamedLine (graphName : Subject) (t : Triple) : String :=
  Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++
  Term.toCanonicalNTriples t.o ++ " " ++ Subject.toNTriples graphName ++ " .\n"

/-- Canonical N-Quads document: default-graph lines, then each named
graph's lines, order preserved throughout. Port of
`canonical_nq_document`. -/
def Dataset.toCanonicalNQuads (ds : Dataset) : String :=
  Graph.toCanonicalNTriples ds.default ++
  String.join (ds.named.map (fun ng =>
    String.join (ng.graph.map (canonNamedLine ng.name))))

end L4Factoidal.Syntax
