# OWL literal-valued entailment goals

Date: 2026-09-09

## Problem

`NegationGoals` could negate object-property assertions with the
singleton `≤ 0 p.{y}` encoding, but returned `none` for every literal
object. This left positive-entailment conclusions such as `i p 0`
unstated even when the datatype constraints in the premise forced
that exact data value.

## Change

The negation of a literal-valued assertion on a named subject is now a
four-triple OWL negative data-property assertion using
`owl:targetValue`. This preserves the singleton negation: it forbids
only the stated subject-property-value pair.

`negativeDataPropertyAssertionClash` checks a complete negative
assertion against positive assertions in the state store. Equality is
OWL data-value equality where the implementation can prove it:

- existing integer, decimal/rational, Boolean, and exact RDF-term
  equality;
- exclusive canonical XML equality;

Malformed lexical forms and unknown datatype mappings with different
RDF terms return false and withhold a clash. Blank-node subjects in a
conclusion remain unsupported because negating an existential
conclusion blank node requires different quantifier handling.
`owl:sameAs` between datatype IRIs does not import an XSD lexical
mapping: OWL 2 Direct Semantics keeps individual and datatype
interpretations separate. A guard pins this withholding behavior.

## Validation

`lake build L4Factoidal.OWL.RefuteTests` passed 28 jobs. Focused guards
cover integer lexical aliases, decimal/integer equality, canonical XML,
no mapping through a datatype-IRI `owl:sameAs`, exact equality for an unknown
datatype, and satisfiable controls for different numeric values,
different subjects, and incomparable unknown datatype values.

A verbatim three-case subset extracted from the real
`type-positive-entailment.rdf` catalog ran with:

```text
.lake/build/bin/l4owl-probe --dl --cap-ms 20000 --refute-budget 64 \
  /private/tmp/owl-literal-pe-targets-20260909 type-positive-entailment.rdf
```

The corrected run reports `DECIDED-BY-REFUTER` for
`WebOnt-I5.8-010` and `WebOnt-oneOf-004`. `WebOnt-I5.8-017` remains a
countermodel/closure gap. The subset therefore scores 5 pass and 1
fail across its three positive-entailment and three consistency units;
closure alone scores 3 pass and 3 fail. There are no caps, refuter
flips, absent goals, or budget exhaustions. Raw output is preserved at
`/private/tmp/factoidal-owl-literal-pe-targets-corrected-20260909.log`.

The superseded first run reported all three as decided, but it used
the rejected datatype-alias rule and is retained only as rejected raw
evidence.

An attempted full `type-positive-entailment.rdf` run was interrupted
after more than 90 seconds when a later unrelated case stopped
producing output. Before interruption it independently printed
`DECIDED-BY-REFUTER` for `WebOnt-I5.8-010`; its result for
`WebOnt-I5.8-017` came from the same rejected alias rule. It produced no complete catalog score and is not
used as coverage evidence.

The graph refuter still has no general model-theoretic soundness
bridge; issue 586 remains the explicit boundary.
