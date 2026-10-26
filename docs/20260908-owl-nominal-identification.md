# OWL nominal identification and fresh tableau witnesses

Date: 2026-09-08. This is a bounded Lean OWL DL/tableau completion step.
It is tracked by [the Lean partial-definition audit](https://github.com/danbri/factoidal/issues/617)
and [the executable tableau certificate work](https://github.com/danbri/factoidal/issues/586).

## Implemented behavior

OWL/Refute.lean now reads every complete RDF collection attached to a
named owl:oneOf, owl:unionOf, owl:intersectionOf, or
owl:disjointUnionOf marker. Multiple markers on one named class each
contribute an axiom. Boolean definitions add both directions and their
NNF contrapositives; a disjoint union also adds pairwise disjointness.
Members of each complete named enumeration are seeded with the named
class label.

An unresolved resource-valued i : {m1, ..., mn} label creates an
exhaustive equality choice. The search preserves member order, threads
the existing shared budget through siblings, and closes the nominal
only after every live choice closes. It skips alternatives proved
distinct from the whole current identification group. A singleton live
choice is propagated without allocating a sibling frame. The clash
check also rejects an identification group containing an asserted
owl:differentFrom pair.

A singleton existential some p.{a} creates the exact countable edge
p(i,a). This differs from a general existential witness, whose fresh
blank node is only an internal model candidate.

Generated existential names are checked against input subject/object
blank nodes, current tableau nodes, expansion edges, witness-depth
entries, and identification pairs. The search starts with the previous
deterministic witnessId and advances only on collision. This repairs
the alpha-renaming counterexample in which an unrelated input blank
node happened to use the generated spelling and incorrectly inherited
the witness filler. OWL 2 inputs exclude RDF 1.2 triple terms, so this
freshness scope does not inspect blank nodes nested inside triple terms.

All collection reads use ClassExpr.walkRdfListComplete. An
unterminated, cyclic, or ambiguous list withholds the whole definition.
The refuter never treats a readable prefix as the complete enumeration.

## Guards and scaling

RefuteTests.lean contains paired controls for:

- a two-member nominal whose first branch clashes and second stays open;
- the corresponding case where both branches clash;
- singleton aliases and owl:differentFrom across an identification group;
- a live literal alternative, which withholds the whole choice;
- multiple named owl:oneOf declarations;
- empty, malformed, named Boolean, and disjoint-union definitions;
- singleton nominal exact edges;
- a satisfiable generated-witness collision and an inconsistent neighbor.

Nominal candidate collection is a foldl plus one final reverse.
The 1,000/2,000/4,000 member guards preserve source-order cardinality.
Pairwise disjointness also uses accumulator folds; its output is
necessarily quadratic, and 25/50/100 operand guards pin exact sizes
604/2,454/9,904. Inspection of generated Refute.c found _start
loops in both fold bodies and no recursive C call for either input
walk. The repository recursion gate still reports seven unrelated
pre-existing findings in OWL/Comprehension.lean and RIF/Engine.lean.

After synchronising the already-integrated datatype files into the
isolated checkout, this focused command passed 465 jobs:

    lake build L4Factoidal.OWL.RefuteTests l4owl-probe l4factoidal

It ran from formal/lean4/. The build log reports the existing search
theorems with only propext, Classical.choice, and Quot.sound.
This change adds no theorem and no axiom.

The positive-entailment catalog, native l4owl-probe --dl at the
default refuter budget 64, reported:

    TOTAL [closure alone]: 343 pass, 65 fail, 0 skip, 4 unsupported (out of 412)
    TOTAL [closure or refutation]: 379 pass, 29 fail, 0 skip, 4 unsupported (out of 412)

New-Feature-DisjointUnion-001 and WebOnt-oneOf-003 were explicitly
reported DECIDED-BY-REFUTER; refuter_flips_to_fail=0 and
pe_refuter_budget=0 for this catalog run. This absolute result is not
a six-catalog conformance score.

WebOnt-description-logic-502 and -504 still exhaust the default
budget. The latter returned budget-out in about 0.55 seconds in the
isolated run; the former remained expensive and was stopped rather
than increasing the budget. The shared TBox/setup performance work may
change their wall time, but nominal branching alone does not establish
these cases.

tools/ensure-test-env.sh --check found the OWL fixtures present. This
checkout lacks the XSD, Xalan XSLT 1.0, Wycheproof, Solid CRUD, Solid
WAC, and Solid specification suites; no result above uses or counts
those absent manifests.

## Boundary

This step does not prove SROIQ(D) completeness, a blocking theorem, or
the general executable-to-Tableau.Refuted certificate relation.
Literal-valued nominal equality choices remain unrepresentable and are
withheld as a whole. Generated pairwise-distinct minimum-cardinality
witnesses, needed by the description-logic-035 spy-point pattern,
remain separate work. Existing witness depth, witness count, search
budget, and wall-clock caps still apply. A returned some true remains
an open tableau branch under those bounds, not a proved satisfiability
result.
