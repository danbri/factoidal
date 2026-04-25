# N-Quads bnode graph names — RDFC-1.0 tests 058/059/071/073

Author: Aleph2 (subagent), 2026-04-25

## Problem

Sade flagged in commit `b726c50` that ~4 RDFC-1.0 eval tests fail because
our N-Quads round-trip emits a blank-node graph name as
`<_:e3>` (an IRI literally containing `_:`) instead of `_:e3`
(an actual blank-node label).

Failing tests (canon-output ground truth in
`third_party/testing/rdf-canon/tests/rdfc10/test058-rdfc10.nq` etc.):

```
<https://example.com/1> <https://example.com/2> _:c14n1 _:c14n0 .
                                                          ^^^^^^
                                              bnode in graph slot
```

Our output puts `<_:c14n0>` (angle-bracket-wrapped) in that slot.

## Root cause

`RDF.Graph.Executable.fst` declares
```fstar
noeq type named_graph = { ng_name : iri; ng_graph : rdf_graph }
```

The `ng_name` field is typed as `iri` (a `string`) and cannot
discriminate IRI vs. bnode at the type level.

`Parser.NQuads.fst.parse_graph_label` already detects `_:` and stores
`"_:e3"` (with the `_:` prefix preserved) into the iri-typed slot.
Downstream `RDF.Canonical.fst.canon_quad` unconditionally wraps this
as `"<" ^ gi ^ ">"`, producing `<_:e3>`.

## Fix shape

Refactoring `ng_name` to a `graph_label = GL_IRI iri | GL_BNode bnode_id`
sum type would touch ~30 sites across `SPARQL11.Algebra.fst`,
`SPARQL11.Store.fst`, both `Parser.Ballyhoo*`, etc. — much bigger than
45 min.

Pragmatic minimal fix: keep the current `iri`-typed sentinel scheme
(parser stores `"_:e3"` in `ng_name` for bnode graphs) and make the
two consumers that care — the canonical serializer and the bnode
enumerator — detect the `_:` prefix.

Files changed:
- `Parser.NQuads.fst` — comments / docstring documenting the
  sentinel scheme. The parser already does the right thing.
- `Parser.TriG.fst` — same docstring/sentinel handling for `GRAPH _:b { … }`.
- `RDF.Canonical.fst` — `canon_quad` and `bnodes_in_quad`/`quad_mentions_bnode`
  treat a `Some gi` graph name with `String.starts_with gi "_:"` as a
  bnode label rather than an IRI. This is *serializer + enumerator*
  policy, not algorithm changes — HFDQ / HNDQ / issuer logic is untouched.

## Test impact

Local RDFC-1.0 eval suite (currently 38/64): tests 058/059/071/073
should flip green; aim +4 to 42/64. No regressions expected on the
36 already-passing — those datasets have IRI graph names only.

## Out of scope

- Refactoring `ng_name` to a sum type — tracked separately.
- Extending HFDQ to consider bnode-in-graph-position as a degree-1
  neighbour (would lift more HNDQ-bound tests out of collisions).
  Today's fix unblocks the simple cases where a bnode graph name has
  a unique HFDQ via subject/object incidences.
