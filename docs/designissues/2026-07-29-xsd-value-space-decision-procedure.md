# A decision procedure for XSD / OWL 2 datatype value spaces

Date: 2026-07-29 · Modules: `formal/fstar/XSD.Facets.fst`,
`formal/fstar/Tableau.Refute.fst` · Consumer: `bin/owl-runner/owl_runner.ml`

The OWL 2 datatype residuals were each described in the ledger as its own
problem — "owl:real excludes minus infinity", "0 is the only value in two
integer subtypes", "precisely 128 values of xsd:byte are also
xsd:unsignedInt". They are one problem: nobody had written down what the
value spaces ARE, so every question about them had to be answered by
hand. This note records the single mechanism that answers all of them,
what already existed before it, and what it does not reach.

## What already existed

The 2026-07-16 concrete-domain wave built most of the interval layer in
`XSD.Facets.fst`, and this work extends it rather than starting again:

| Piece | Status before |
|---|---|
| `interval` with `B_Unbounded` / `B_Incl` / `B_Excl` `int` bounds, intersection, membership | existed |
| `interval_empty` (discrete rule) and `interval_empty_dense` | existed |
| `base_interval_for` — the natural range of each finite XSD integer subtype | existed |
| `facets_to_interval` — min/max Inclusive/Exclusive over an integer base | existed |
| `interval_count` — exact size of a bounded integer interval | existed |
| `rational` with exact decimal / `owl:rational` lexical parsing | existed |
| IEEE-754 single-precision ordinal grid (`float_ordinal_of_lexical`) | existed |
| `value_set` — interval / dateTime-interval / enum / family / top / bottom | existed |
| `term_provably_equal` / `term_provably_distinct`, three-valued | existed |
| `value_set_max_size` — sound UPPER bound on a value space's size | existed |
| `xsd_family` = numeric / string / boolean | existed |
| `fold_datatype_constraint`, `universal_for_property`, `range_value_set` in `Tableau.Refute` | existed |
| datatype range clash (C6) and datatype cardinality clash | existed |

What that layer could not say: which datatypes share a value space beyond
the integer family; that floating-point values are not real numbers; that
a dense space needs different emptiness and counting rules than a
discrete one; WHICH values a finite space holds (only how many); and what
a negative assertion removes.

## What was added

### 1. The numeric value spaces of the OWL 2 datatype map

OWL 2 Syntax, 2nd edition, section 4.1 "Real Numbers, Decimal Numbers,
and Integers":

> The value space of owl:real is the set of all real numbers.

> The value space of owl:rational is the set of all rational numbers. It
> is a subset of the value space of owl:real, and it contains the value
> space of xsd:decimal.

> In accordance with this principle, the value space of owl:real is
> defined as being disjoint with the value spaces of xsd:double and
> xsd:float as well.

> Although floating-point values are numbers, they are not contained in
> the value space of owl:real.

So the numeric part of the datatype map is not one space but three
pairwise-disjoint ones: the owl:real number line (with owl:rational,
xsd:decimal, xsd:integer and the derived integer types nested inside it),
the IEEE single grid, and the IEEE double grid. `xsd_family` gains
`Fam_Float` and `Fam_Double` to say so, and `classify_family` now places
`owl:real`, `owl:rational`, `xsd:float` and `xsd:double`, which it
previously left unknown.

### 2. The special values, named

XSD 1.1 Datatypes sections 3.3.5 / 3.3.6 put positive infinity, negative
infinity and not-a-number in the value spaces of `xsd:float` and
`xsd:double`, with lexical forms `INF`, `-INF` and `NaN`. `float_special`
and `float_special_of_lexical` name them. They were already handled
correctly-but-silently (no decimal lexical form denotes them, so the
rational parser refused them); naming them makes the reason inspectable
and gives `term_in_owl_real` — the three-valued membership test for a
parsed literal — something to point at.

### 3. Dense intervals with exact rational endpoints

`interval` carries integer granularity: `(lo, hi)` is empty once the ends
are adjacent, and a bounded one has an exact finite size. Both are wrong
on the owl:real line, where `(0, 1)` holds no integer but infinitely many
decimals. `qinterval` is the dense counterpart — same bound algebra,
endpoints drawn from the exact `rational` type so `"0.1"^^xsd:decimal` is
an endpoint with no rounding, dense emptiness rule. `qinterval_to_int_interval`
bridges the two by ceiling the lower bound and flooring the upper, which
is exactly the set of integers a dense interval contains. `VS_Dense`
carries it into `value_set`, with the full intersection table against
every other shape.

### 4. Exact enumeration, and its contract

`value_set_max_size` answers "how many values at most". The new
`value_set_exact_values` answers "which values", and that is what turns a
value-space computation from a refutation into an entailment. Its
contract on the returned list L, for a value_set standing for the true
admissible set A:

1. **COVER** — `A ⊆ set(L)`. L never misses an admissible value.
2. **DISTINCT** — L's members are pairwise distinct by value, so
   `|set(L)| = length L`.

An integer interval with two finite ends enumerates (capped at 4096, above
which the answer is `None` and every consumer withholds). An enum
qualifies only when its members are pairwise provably distinct, so that
its length is a count rather than a guess. Dense, dateTime, bare-family
and unconstrained spaces answer `None`: they are infinite.

### 5. What a negative assertion removes

OWL 2 Syntax section 9.6.6: `NegativeDataPropertyAssertion(DP a lt)` holds
iff the pair is not in DP's extension. The OWL 2 Mapping to RDF writes it
as an `owl:NegativePropertyAssertion` reification.
`Tableau.Refute.negated_values` reads those off the graph for an
individual and a property set, and `remove_negated_values` takes them out
of a value space. A negation on a super-property propagates down
(`EXT(p) ⊆ EXT(q)`), never up. Only shapes with a COVER can shrink to
empty; dense and unbounded ones are left alone, since minus a finite set
of points they stay non-empty. A hot-path guard means a graph with no
`owl:targetValue` triple costs one linear scan.

### 6. Forced fillers — the entailment side

The clash rules use a value space to refute. The identical machinery
entails whenever the count matches exactly. Let U be the value space every
`p`-filler of `i` must lie in (the `∀q.D` labels with `p ⊑* q`, the
`rdfs:range` datatypes, minus the negated values), and let some axiom
force at least k pairwise-distinct `p`-fillers all inside a data range D.
Write `W = U ⊓ D`. If `value_set_exact_values W` returns a list L of
length exactly k, every member of L is a `p`-filler of `i`.

Proof: let A be the true set of admissible fillers. `A ⊆ W ⊆ set(L)` by
COVER; the obligation gives `|A| ≥ k`; DISTINCT gives `|set(L)| = k`.
Chaining, `k ≤ |A| ≤ |set(L)| = k`, so `A = set(L)`. The argument survives
L over-approximating W — only the cover and the exact length are used.

The obligation shapes it reads are `∃p.D` (k = 1), min-cardinality,
exact-cardinality, and the two qualified variants. RL-closure scaffolding
bnodes (`__rl_*`) are mapped to `CE_Unknown` first, the same guard the
axiom and branching paths already carry, because their cardinality
reading is deliberately loose and is not sound read as a real
restriction.

### 7. Literal matching by value

OWL 2 Direct Semantics interprets a literal as the value its datatype's
lexical-to-value map assigns. `"0"^^xsd:int` and `"0"^^xsd:integer` are
therefore the same data-property assertion, and a graph entails one
exactly when it entails the other. The OWL runner's conclusion matcher
now calls the F*-extracted `XSD_Facets.term_provably_equal` instead of
`rdf_term_eq`. That predicate is one-sided: true only on a proof that two
terms denote one value, false — not "distinct" — when it cannot tell. The
runner picks which verified predicate to call; it decides nothing itself
(rule #15).

This step is not optional for the entailment rule above. The value space
`xsd:nonNegativeInteger ⊓ xsd:nonPositiveInteger` determines the VALUE 0,
not a lexical form; `WebOnt-I5.8-010`'s conclusion writes that value as
`"0"^^xsd:int`, a datatype its own premise never mentions. No engine can
pick that spelling; it can only match by value.

## What falls out

- **`Minus Infinity is not in owl:real`** (inconsistency). The forced
  `:dp`-filler lies in `{-INF^^xsd:float, -0^^xsd:integer} ⊓ owl:real`.
  `-INF` is a float value and floats are not reals (section 4.1), so the
  set is `{0}`; the negative assertion forbids 0
  (`"-0"^^xsd:integer` and `"0"^^xsd:unsignedInt` denote one integer);
  nothing is left. Clash.
- **`WebOnt-I5.8-010`** (positive entailment). `U = [0, ∞)` from the
  range, `D = (-∞, 0]` from the `∃`, `W = [0, 0]`, k = 1, `L = ["0"]`.
  The test's own sentence, arrived at by counting.
- **`WebOnt-I5.8-004`** (positive entailment, marked Extracredit).
  `U = [-128, 127] ⊓ [0, 4294967295] = [0, 127]`, k = 128 = length L, so
  all 128 values are fillers, `"5"` among them. Again the test's own
  sentence.

Nothing above is coded per test. Each is the same three steps: normalise
the value spaces, intersect, count.

Measured, all four OWL 2 DL catalogs re-run 2026-07-29 against the
rebuilt `bin/linux-x86_64/owl_runner`:

| Catalog / section | Before | After |
|---|---|---|
| `type-positive-entailment.rdf` PositiveEntailment | 189 pass, 15 fail (out of 204) | 191 pass, 13 fail (out of 204) |
| `type-inconsistency.rdf` Inconsistency | 125 pass, 2 fail (out of 127) | 126 pass, 1 fail (out of 127) |
| `type-consistency.rdf` Consistency | 352 pass, 0 fail (out of 352) | 352 pass, 0 fail (out of 352) |
| `type-negative-entailment.rdf` NegativeEntailment | 23 pass, 0 fail (out of 23) | 23 pass, 0 fail (out of 23) |

FAIL-name diff: `WebOnt-I5.8-004`, `WebOnt-I5.8-010` and `Minus Infinity
is not in owl:real` leave; nothing joins.

## Two measured soundness traps, and what each forced

Both were caught by the gates, not by inspection, and both are recorded
here because the reasoning that produced them looked correct.

**1. A DERIVED range triple is not an asserted one.** Classifying
`xsd:double` as its own value space made `p rdfs:range xsd:double`
empty an integer value space. But that range triple is not in any
premise: the RL/RDFS closure ships an RDF-Based datatype-subsumption
table with `xsd:byte rdfs:subClassOf xsd:double`, and range propagation
manufactures it from the asserted `p rdfs:range xsd:byte`. Three
consistent premises were refuted (`WebOnt-I5.8-002 / -004 / -005`).
`fold_datatype_constraint` therefore adds NO constraint for
`Fam_Float` / `Fam_Double`; the disjointness is used only where it is
read off an asserted literal's own datatype, which is what the
`Minus Infinity` test needs. The underlying tension — an RDF-Based
subsumption table feeding a Direct Semantics fold — is still there.

**2. Asserting an entailed data value can trip the marker path.** The
forced fillers are entailments, but feeding a concrete data-property
assertion into the closure makes rdfs3 range propagation type that
literal, and the datatype-membership marker then reported three
consistent premises as inconsistent (`WebOnt-I5.8-002 / -004 / -010`,
352 pass 0 fail -> 349 pass 3 fail). The fillers are therefore routed
through the PositiveEntailmentTest-only closure
(`apply_closure_with_witnesses`), the same `g_rl` / `g_dl` separation the
runner already applies to the materialiser's other emissions. The marker
path's false positive on a typed literal is a real defect and is
unfixed — it is now reachable by a one-line routing change, which makes
it easy to pick up next.

## What it does not reach

- **`WebOnt-I5.8-017`** (datatype aliasing). Its premise says
  `xsd:decimal owl:sameAs :bar` and types a literal with `:bar`. Treating
  a datatype IRI as an individual that can be `owl:sameAs` something is
  OWL Full — the catalog carries `test:species FULL` and an explicit
  negative assertion against `DL`. Deriving it needs the datatype-IRI
  rewriting rule to live in the flag-gated `--semantics rdf-based-full`
  engine mode, where (like `WebOnt-Class-001/-002/-003`) it would not move
  the default-scored catalog. The value-equality half of the test —
  `"01"` and `"1"` as `xsd:decimal` — is covered; the aliasing half is
  not.
- **Dense facet arithmetic is built but unexercised.** `qinterval` and
  `dense_facets_to_qinterval` handle `xsd:decimal` / `owl:rational` /
  `owl:real` `DatatypeRestriction`s, but no corpus fixture currently
  builds one, so that path has no test standing behind it.
- **Forced fillers read only asserted `rdf:type` labels**, not TBox
  unfolding: an obligation reachable only through a `SubClassOf` chain is
  not seen by the materialiser (the refuter does unfold, for clashes).
  Withholding is sound; widening this is the obvious next step.
- **`xsd:double` has no ordinal grid.** `xsd:float` does (section 4c);
  the double grid would be the same construction at 52 mantissa bits.
- **The forced fillers reach only the entailment closure**, for the
  marker-path reason above. A consistency or inconsistency verdict does
  not see them.

## Scoped follow-up: the two functional-syntax-only cardinality tests

`Qualified-cardinality-boolean` and `Qualified-cardinality-restricted-int`
are reported `SKIP/functional-syntax-only`, so they sit OUTSIDE the
204-test denominator; deciding them is a coverage gain, not a pass/fail
flip. Their reasoning is already this note's section 6 rule verbatim —
`DataExactCardinality(2 :dp xsd:boolean)` over a two-member value space,
`DataExactCardinality(3 :dp DatatypeRestriction(xsd:integer [1,3]))` over
a three-member one. Nothing new is needed on the counting side.

An attempt to land them was measured and reverted (commit `bdcfd80`,
reverted by `6e7490d`). It moved `type-positive-entailment` from
191 pass, 13 fail to 190 pass, 14 fail and did NOT unskip the targets.
Four coupled pieces are needed, and that commit had two:

1. **`Data{Exact,Min,Max}Cardinality` in `Parser.OWLFunctional.fst`** —
   written and verified in the reverted commit, mapped per the OWL 2
   Mapping to RDF Graphs Data Property Cardinality Restrictions rows.
   Correct as far as it goes. Needs a bare-integer scanner: the syntax
   writes cardinalities unquoted and untyped.
2. **`owl:onDataRange` as a qualified-cardinality filler in
   `Tableau.parse_class_expr`** — written, and the more faithful reading;
   without it `DataExactCardinality(n DP DR)` silently reads as the
   unqualified `= n DP`. This is what regressed
   `New-Feature-DataQCR-001`, whose conclusion is a restriction with
   `owl:minQualifiedCardinality 2` + `owl:onDataRange xsd:string`: read
   unqualified it was provable from two asserted string values, read
   correctly it is not — because of piece 4.
3. **`Ontology(<IRI> Axiom*)`** — NOT started, and the actual reason the
   two targets still skip. `parse_functional_syntax` hands the position
   straight to `parse_axioms_acc` after `(`, so a leading ontology IRI
   fails the parse. Independent of cardinality, and invisible until the
   cardinality gap was closed.
4. **Qualified cardinality counted over LITERAL fillers** — NOT started
   and not small. `Tableau.count_qual_successors` decides filler
   membership through `is_member`, which takes a `subject`; a literal is
   not a subject. Data-range-qualified counting is structurally absent,
   not a missing case.

Order that works: 4, then 2, then 1 and 3 together. Landing 1+2 alone
regresses; landing 1+3 without 2 converts two honest skips into two
fails, since the filler is dropped and the count cannot be decided.

The one datatype fact still missing on the reasoning side is trivial:
`value_set_exact_values` should enumerate the `xsd:boolean` value space,
`{true, false}` (XSD 1.1 Datatypes section 3.3.2) — the only finite
value space in the OWL 2 datatype map that is not a numeric interval.
Three lines, carried in the reverted commit.
