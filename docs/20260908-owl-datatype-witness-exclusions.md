# OWL datatype witness exclusions and complete RDF lists — 2026-09-08

## Scope and semantics

This change extends the executable OWL DL refuter's concrete-domain
checks. It does not add a general soundness bridge from `Refute` to
`Tableau`; that open assurance gap remains tracked by
https://github.com/danbri/factoidal/issues/586.

For one node and one data property, the refuter now derives forbidden
data values from:

- explicit OWL negative property assertions; and
- asserted values on properties declared disjoint from that property.

Property lookup follows the cached subproperty/superproperty closure,
and subject lookup follows branch identifications. The exclusions are
applied separately to each existential obligation. Different
existentials are not intersected with each other.

Enumeration exclusions use `termProvablyEqual`. Integer lexical aliases
and derived integer datatypes therefore collide by value. Unknown or
incomparable values remain. Bounded integer intervals count distinct,
parsed, in-range integer exclusions against the exact interval size.

`xsd:pattern` is read by `ClassExpr`. The finite-pattern helper uses the
existing XSD regex parser and enumerates only a complete finite AST
fragment: empty, epsilon, singleton ranges, concatenation, alternation,
and intersection. Star, complement, non-singleton ranges, unsupported
syntax, and oversized languages return `none`. Pattern text is limited
to 256 Unicode scalar values and brace quantifiers are rejected before
the shared parser is invoked, avoiding large repetition expansion.
Generated languages are limited to 256 words of at most 256 codepoints.
Multiple pattern facets are enumerated independently and intersected by
a tail-recursive fold.

OWL 2 uses XSD 1.1 pattern semantics. XSD 1.1 Part 2 §G states that the
regular expression is implicitly anchored at the head and tail, so
`a(b|c)` denotes exactly `ab` and `ac`:
https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#regexs . OWL 2
Syntax references this datatype map:
https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/ .

Anonymous `rdfs:range` data expressions are parsed once into `RState`.
Minimum and exact cardinalities of at least one are treated as existence
obligations when all admissible values are excluded. Focused guards
cover the two-range intersection `{1,2,3,4} ∩ {4,5,6}` and the
`nonPositiveInteger ∩ nonNegativeInteger = {0}` case.

## RDF collection safety repair

`walkRdfListComplete` reads an entire RDF collection as
`Option (List Term)`. It uses graph-size fuel, a `HashSet` cycle check,
and a tail-recursive reversed accumulator. Blank-node and IRI cells are
accepted; only `rdf:nil` terminates the list. Exact duplicate
`rdf:first` or `rdf:rest` values normalize to one value, while missing
or genuinely ambiguous values reject the whole list. Intersection,
union, nominal, and datatype-facet parsing now return `unknown` for an
incomplete collection instead of treating a fuel-bounded prefix as the
whole list.

This repairs a false refutation where `minQualifiedCardinality 33` over
a 64-member nominal was truncated at the old class-expression depth 32.
Guards cover satisfiable 33-of-64, inconsistent 65-of-64, malformed and
cyclic lists, IRI cells, duplicate and ambiguous cells, and indexed
reader lengths 1000, 2000, and 4000. Qualified min/max comparison also
uses `ceEq`, so two unrelated `unknown` fillers cannot license a clash.

The stricter list reader exposes a malformed W3C RDF/XML premise in
`New-Feature-Rational-002`. Its final `rdf:rest` is the RDF namespace
IRI `http://www.w3.org/1999/02/22-rdf-syntax-ns#`, not `rdf:nil`. The
old reader silently treated every IRI as termination. The case is now a
visible failure in the RDF/XML probe. Its separately expressed
functional-syntax premise is well formed; a focused graph with the
intended proper list confirms that decimal `0.5` and rational `1/2`
still give the expected cardinality clash.

## Measured evidence

Fixture verification:

```text
tools/ensure-test-env.sh --check
OWL fixture: ok
overall: gaps (XSD, Xalan, Wycheproof, Solid CRUD/WAC/spec fixtures)
```

The missing unrelated fixtures do not affect the OWL catalogs used
below.

Baseline before this change:

```text
type-inconsistency.rdf --dl: 116 pass, 11 fail, 1 skip, 0 unsupported / 128
cap_hits=0, wall_ms=3642, process real=3.89 s
```

Final result:

```text
type-inconsistency.rdf --dl: 118 pass, 9 fail, 1 skip, 0 unsupported / 128
cap_hits=0, wall_ms=3671
```

Newly decided by refutation:

- `Inconsistent Disjoint Dataproperties`
- `Inconsistent String Pattern with Disjoint Dataproperties`
- `Minus Infinity is not in owl:real`

New visible failure from the list-safety repair:

- `New-Feature-Rational-002` — malformed RDF/XML list tail described
  above.

The remaining eight prior failures are `one=two`,
`WebOnt-description-logic-035`, `-040`, `-108`, `-502`, `-504`, `-909`,
and `-910`.

Current profile guards after the change:

```text
profile-RL.rdf --dl: 126 pass, 0 fail / 126
profile-QL.rdf --dl: 87 pass, 0 fail / 87
profile-EL.rdf --dl: 119 pass, 1 fail, 1 skip / 121
```

The full `type-positive-entailment.rdf --dl` run was stopped after
226.46 seconds while processing `WebOnt-description-logic-202`; it had
not emitted another case result for more than two minutes. The target
`WebOnt-I5.8-010` had already reported `noGoals`: the harness cannot
negate its `rdf:type owl:Thing` conclusion, so this runner cannot expose
the datatype refutation for that unit. The anonymous-range and signed
zero mechanisms are instead covered by focused `RefuteTests` graphs.

Build evidence:

```text
lake build L4Factoidal.OWL.RefuteTests
lake build
```

Both passed. The full build completed 1196 jobs. Existing repository
lint warnings remained; the changed files introduced no build warning.

## Assurance checks and limits

No `sorry`, user `axiom`, `native_decide`, `unsafe`,
`@[implemented_by]`, or new `partial` declaration was added. The only
new theorem is the arithmetic identity
`finiteSpaceRemainingUpperBound_eq_zero_iff`; its axiom report is
checked separately and is not presented as a graph-refuter soundness
proof. The finite regex enumeration and graph-to-constraint connection
remain executable, guarded logic within the existing issue 586 trust
boundary.
