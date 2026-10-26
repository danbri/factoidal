# Lean SPARQL 1.0 RDF result sets — 2026-09-08

Tracking: <https://github.com/danbri/factoidal/issues/466>

## Problem

The Lean W3C runner did not decode the complete DAWG RDF result-set
vocabulary. It treated `rs:boolean` ASK results as empty SELECT results.
It also rejected the ten RDF/XML result files in the SPARQL 1.0 `sort`
manifest because expected-result dispatch had no `.rdf` branch.

The measured baseline was 397 pass and 84 fail (out of 481):

- 30 failures said that an ASK query had a non-boolean expected result;
- 10 failures said that `.rdf` was an unknown result format;
- 34 evaluation result mismatches and 10 query-parser verdict failures
  were separate semantic defects.

## Repair

`L4Factoidal.SPARQL.ResultsRdf` now decodes an RDF graph whose subject has
type `rs:ResultSet` into the common `QueryResult` type. It implements the
vocabulary terms used by the W3C SPARQL 1.0 tests:
`ResultSet`, `solution`, `binding`, `variable`, `value`, `index`, and
`boolean`.

The decoder preserves every `rs:value` RDF term. It does not change blank
node labels, datatype IRIs, lexical forms, language tags, or row
multiplicity. When every solution has an `rs:index`, it sorts the rows by
that index. This supplies the expected sequence for ORDER BY tests.

The decoder builds one hash index over the graph instead of rescanning the
whole graph for every solution and binding. The index ignores repeated
identical triples, as required by RDF graph set semantics. It still retains
distinct `rs:solution` nodes as distinct rows, including two rows with the
same bindings. Objects are accumulated with a tail-recursive fold and the
indexed rows use Lean's merge sort; the earlier input-length insertion
recursion is gone.

The decoder accepts the four lexical forms in the XML Schema boolean
lexical space: `true`, `false`, `1`, and `0`. It requires the
`xsd:boolean` datatype. It rejects incomplete bindings, invalid indexes,
multiple values for a singular property, and a result set that combines
ASK and SELECT properties.

`Harness.Run.parseExpected` now parses `.rdf` with the Lean RDF/XML parser.
Both `.rdf` and `.ttl` graphs then use the same library decoder. Plain RDF
graphs still go to CONSTRUCT comparison.

Specification and suite sources:

- [DAWG test case structure](https://www.w3.org/2001/sw/DataAccess/tests/README)
- [SPARQL Query Results XML Format](https://www.w3.org/TR/rdf-sparql-XMLres/)
- [W3C SPARQL 1.0 test suite](https://www.w3.org/2001/sw/DataAccess/tests/)

## Regression evidence

Three build-time guards failed before the repair and pass after it:

- a Turtle `rs:boolean "true"^^xsd:boolean` graph decodes as ASK true;
- an RDF/XML `rs:boolean` graph decodes as ASK false;
- a plain-string `rs:boolean "true"` graph is rejected.

The existing guard for indexed SELECT rows also passes after its decoder
call moves from the harness to the library.

Additional guards pin the RDF graph and result-sequence semantics:

- decoding a graph is unchanged when every triple is repeated;
- two distinct solution nodes with equal blank-node values remain two rows;
- the shared blank node keeps one identity across those rows;
- `rs:index` orders the rows by their distinguishing value.

A synthetic decoder run measured `n`, `2n`, and `4n` result rows. Each row
has five result-set triples and the input indexes are reversed, so the run
exercises graph indexing, binding decoding, and sorting:

| Rows | Triples | Wall time inside decoder |
| ---: | ---: | ---: |
| 2,000 | 10,002 | 148 ms |
| 4,000 | 20,002 | 295 ms |
| 8,000 | 40,002 | 584 ms |

The ratios were 1.99 and 1.98. `tools/lean-tail-recursion-audit.py --gate`
reported no recursion from `ResultsRdf.lean`; its repository-wide gate still
failed on 12 unrelated, pre-existing declarations outside this change.

Fresh runs from the repository root, with absolute manifest paths, give:

| Suite | Before | After |
| --- | --- | --- |
| SPARQL 1.0 evaluation manifests | 208 pass, 74 fail (out of 282) | 230 pass, 52 fail (out of 282) |
| SPARQL 1.0 full legacy manifest | 397 pass, 84 fail (out of 481) | 419 pass, 62 fail (out of 481) |
| SPARQL 1.1 `manifest-all.ttl` | 631 pass, 0 fail (out of 631) | 631 pass, 0 fail (out of 631) |
| SPARQL 1.2 ten leaf manifests | 254 pass, 0 fail (out of 254) | 254 pass, 0 fail (out of 254) |

All 40 result-format failures are absent after the repair. The ten sort
tests now pass. Of the 30 type-promotion ASK tests, 12 now pass and 18
report the evaluator's boolean mismatch. The remaining 62 failures consist
of 52 evaluation semantics failures and 10 parser verdict failures. They
remain in the normal failure buckets; this change adds no override or
comparator leniency.

Fixture verification found all SPARQL and RDF paths used here. The checkout
does not contain the unrelated XSD, Apache Xalan XSLT, Wycheproof, Solid
CRUD, Solid WAC, or Solid specification fixtures.

## Numeric promotion follow-up

The exposed ASK failures showed that the evaluator represented only three
numeric result kinds. SPARQL 1.0 §11.3 requires the XML Schema numeric type
promotion lattice to distinguish `xsd:float` from `xsd:double`, and to admit
integer-derived types by subtype substitution. The evaluator now carries four
kinds: integer, decimal, float, and double. It validates the value-space facets
of the built-in integer-derived datatypes, accepts the optional leading plus in
integer lexical forms, and promotes operands in the specified order.

Finite float and double inputs are converted through
`L4Factoidal.XSD.IEEE754`. Float operands and the results of `+`, `-`, and `*`
are rounded directly with `canon 24 (-126) 127`; this intentionally does not
use the RDF helper whose documented contract double-rounds through binary64.
A guard at the first binary32 integer boundary establishes that
`16777216^^xsd:float + 1^^xsd:float` denotes 16777216. A mixed float/double
operation retains 16777217 and has datatype `xsd:double`. Casts from a float
consume that rounded value, so the lexical `16777217` as an `xsd:float` casts
to integer 16777216 and double `1.6777216E7`.

`sameTerm` now retains the RDF term supplied by a variable or primary
expression instead of comparing promoted evaluator constructors. Thus
`"01"^^xsd:integer` and `"1"^^xsd:integer` compare equal by `=`, but remain
distinct under `sameTerm`; an `xsd:float` literal and an identical float term
made by a cast remain the same term. The dedicated comparator follows RDF 1.2
term identity: language tags compare ASCII-case-insensitively, while datatype,
lexical form, and direction remain exact. It therefore does not apply the
engine's broader XML-literal canonicalization. An error operand propagates a
SPARQL type error.

Numeric EBV recognizes signed zero, exponent-form zero, float underflow, and
NaN as false. Integer-family EBV checks the integer lexical space and the
specific subtype facet. As SPARQL 1.1 §17.2.2 requires,
`"1e0"^^xsd:integer` and `"1000"^^xsd:byte` therefore have EBV false rather
than producing a type error. The float/double EBV predicate uses the
fixed binary32/binary64 half-smallest-subnormal decades: decimal order below
-46/-324 is certainly rounded zero, order above it is certainly nonzero, and
only the boundary decade calls the exact IEEE canonicalizer. This avoids an
allocation proportional to an exponent value. A probe of exponents
±1,000, ±1,000,000, and ±1,000,000,000 completed in 1.02 seconds total and
returned true for the positive magnitudes and false for the negative ones.
The generic `XSD.IEEE754.canon` definition was not changed.

The `ExprRefinement.ebvSpec_agrees` theorem proves that the evaluator agrees
with the second transcription in that module. The transcription deliberately
repeats the same fixed decimal-order thresholds, so this theorem does not prove
the mathematical correspondence between those thresholds and IEEE-754. The
boundary and oversized-exponent guards provide executable evidence for that
unformalized correspondence.

The focused W3C manifests now report `type-promotion` 30 pass / 0 fail and
`expr-ops` 18 pass / 0 fail, repairing 24 evaluator cases. The full legacy
manifest reports 445 pass / 36 fail (out of 481), up from the post-decoder
419 / 62. Two additional cases passed when `sameTerm` term identity was
repaired. The `cast` manifest remains 6 pass / 1 fail; its only failure is the
separate `xsd:dateTime` constructor case.

This is not a claim of complete IEEE arithmetic. Division still uses the
existing fixed ten-decimal-digit scaled quotient, aggregates do not yet round
each promoted addition, and non-finite arithmetic is not represented by the
scaled arithmetic model.

Specification source: [SPARQL 1.0 Query Language §11.3](https://www.w3.org/TR/rdf-sparql-query/#operandDataTypes).

The result comparator's pre-existing same-datatype numeric-value rule uses
the same exact IEEE canonical values for `xsd:float` and `xsd:double`. Previously
it compared their decimal lexical forms as exact base-10 rationals. That made a
short spelling such as `4.0E-1` differ from the exact decimal expansion of the
same binary64 value. Integer and decimal result comparison remains exact, and
different numeric datatypes still do not match. Guards cover the binary32
16777216/16777217 rounding boundary, the corresponding binary64 distinction,
exact decimal rejection, and datatype mismatch. This restores the SPARQL 1.1
aggregate floor to 631 pass / 0 fail; SPARQL 1.2 remains 254 / 0.

## Dataset and blank-node scope follow-up

SPARQL `FROM` and `FROM NAMED` clauses construct the query dataset from the
identified RDF graphs. Blank-node identifiers are local to an RDF document;
loading independent graph instances must not merge nodes merely because their
source labels have the same spelling. Fixture loading now scopes labels by the
source document and graph role. The reusable scope encoder writes every
Unicode scalar as decimal digits plus `_`, terminates each tuple component
with `x_`, and terminates the list with `z_`. This makes the prefix syntax-safe,
injective, and prefix-free, including the distinction between an empty tuple
and a tuple containing one empty string. A document loaded once retains
co-reference within that graph.

The harness now loads local `file:` dataset-clause sources into the named graph
store before evaluation. This lets the semantic `applyDataset` operation select
the declared sources instead of treating the clause as an empty dataset when a
manifest has no matching `qt:data` entry.

Build-time guards establish that repeated labels within one document remain
one blank node, different source/role loads are disjoint, repeated `FROM NAMED`
IRIs produce one named graph and one `GRAPH ?g` solution bag, and `FROM` plus
`FROM NAMED` over one source use disjoint graph instances under this runner's
retrieval policy. SPARQL 1.1 §13.2.3 deliberately makes no claim about how
often a source is retrieved or whether those two graph instances share blank
nodes; scoping them apart is permitted behavior rather than a requirement on
all implementations. Dataset construction applies one role-specific uniform
alpha-renaming to all selected named graphs. This preserves cross-graph blank
node co-reference up to uniform renaming and prevents an adversarial stored
label from colliding with the separately renamed default graph. A CONSTRUCT
guard serializes and parses a scoped blank node whose source tuple contains a
slash, space, and non-ASCII characters. Focused W3C
results moved from 14 / 3 to 17 / 0 for `graph` and from 4 / 8 to 12 / 0 for
`dataset`. The full SPARQL 1.0 result after this follow-up is 456 pass / 25 fail
out of 481.

Specification sources:

- [SPARQL 1.0 Query Language §8, RDF Dataset](https://www.w3.org/TR/rdf-sparql-query/#rdfDataset)
- [RDF 1.2 Concepts, blank node identifiers](https://www.w3.org/TR/rdf12-concepts/#section-blank-nodes)

## Value comparison follow-up

The equality evaluator now applies the most-specific viable operator mapping
before the generic RDF-term equality fallback. Numeric operands normalize
across evaluator constructors and raw typed literals. This repairs comparisons
between a variable, a typed literal written in the query, and an
arithmetic-produced result without losing the original RDF term needed by the
fallback. NaN is unequal to every numeric value, including itself, but a NaN
operand paired with a string, IRI, or unsupported typed literal remains a type
error.

Floating comparison canonicalizes both operands at the common promoted IEEE
kind. The same path handles finite values, lexical overflow such as
`"1e100"^^xsd:float` and `"1e400"^^xsd:double`, explicit signed infinity, and
integer values such as `10^400` that overflow only during promotion. Signed
zero compares numerically equal. Guards cover both infinity signs, both operand
orders, finite controls, the binary32 rounding boundary, and mixed raw/promoted
representations. The exact implementation uses `XSD.IEEE754.Fval`; it does not
use a tolerance or host floating arithmetic.

Date-time equality and ordering use `XSD.parseDateTimeLex` and `dtCompare`, so
timezone-equivalent instants and fractional seconds compare in the value space.
An identical ill-formed date-time literal reaches RDF-term identity only because
the typed mapping is not viable; two distinct ill-formed date-time lexicals
remain a type error. `xsd:date` is an explicitly documented implementation
extension. The normative SPARQL 1.0 and 1.1 operator tables require
`xsd:dateTime`, not `xsd:date`.

RDF-term identity compares language tags ASCII-case-insensitively as RDF 1.2
requires, while keeping lexical form, datatype, base direction, and XML literal
spelling exact. Triple terms recurse through the same identity rule. Relational
operators on IRIs now produce a type error; IRI ordering is an ORDER BY rule,
not an `<` operator mapping. Lexical relational comparison of two literals with
the same language tag remains a declared implementation extension.

The refinement file retains executable-spec agreement for integer equality,
plain strings, language-tag inequality, and explicitly classified unsupported
datatypes. Build-time `#print axioms` output for the new and affected theorems
contains only `propext`, `Classical.choice`, and `Quot.sound`. These lemmas do
not constitute a general value-comparison adequacy proof.

This cluster moved the full legacy result from 456 pass / 25 fail to 464 pass /
17 fail. Specification sources:

- [SPARQL 1.0 §11.3 operator mapping](https://www.w3.org/TR/2008/REC-rdf-sparql-query-20080115/#OperatorMapping)
- [SPARQL 1.0 §11.4.10 RDFterm-equal](https://www.w3.org/TR/2008/REC-rdf-sparql-query-20080115/#func-RDFterm-equal)
- [SPARQL 1.1 §17.3 operator mapping](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#OperatorMapping)
- [RDF 1.2 Concepts §3.3 literal term equality](https://www.w3.org/TR/rdf12-concepts/#section-Graph-Literal)

## Parser verdict follow-up

Ten legacy syntax verdicts failed independently of evaluation. The parser now
accepts IRI-named function calls, requires at least one item in a collection,
and recognizes the additional IRIREF forms exercised by the corpus: a leading
ampersand and a valid leading Unicode escape. Rejection guards cover an empty
collection in subject and object positions and malformed, surrogate,
unterminated, or later-invalid escaped IRIREF bodies. The two existing guards
for `<` and `<=` expression operators still pass. The dependent tokenizer and
ASK round-trip theorems were rebuilt with unchanged statements and accepted
axiom foundations.

This cluster moved the syntax result from 189 pass / 10 fail to 199 pass / 0
fail and the combined legacy result from 464 / 17 to 474 / 7. This score does
not establish complete production `[139]` coverage: the current `<`
disambiguation still omits legal relative IRIREFs beginning with a digit, `+`,
`-`, `.`, `:`, or `%`. Replacing that first-character approximation with a
whole-body maximal-munch check, and measuring its `n`, `2n`, `4n` behavior, is
a separate follow-up.

## Current regression evidence and assurance limits

The integrated cluster sequence is:

| Stage | SPARQL 1.0 pass | Fail | Total |
| --- | ---: | ---: | ---: |
| Baseline | 397 | 84 | 481 |
| RDF result-set reader | 419 | 62 | 481 |
| Numeric promotion and term identity | 445 | 36 | 481 |
| Dataset and blank-node scope | 456 | 25 | 481 |
| Value comparison | 464 | 17 | 481 |
| Parser verdicts | 474 | 7 | 481 |

The syntax partition is 199 pass / 0 fail. The evaluation partition is 275
pass / 7 fail. The seven remaining case IDs are `open-eq-12`,
`Optional-filter - 1`, `Optional-filter - 2 filters`, `Cast to xsd:dateTime`,
`str-1`, `str-2`, and `normalization-02`. They remain ordinary failures. The
first three expose correlated OPTIONAL/LeftJoin evaluation; the other four are
separate cast, STR, and Unicode-normalization semantics. This worknote does not
claim full SPARQL 1.0 conformance.

Fresh native runner floors after value comparison and parser repair are:

- SPARQL 1.0 legacy umbrella: 474 pass / 7 fail out of 481;
- SPARQL 1.1 `manifest-all.ttl`: 631 pass / 0 fail out of 631;
- SPARQL 1.2 ten leaf manifests: 254 pass / 0 fail out of 254.

The runs used the built `formal/lean4/.lake/build/bin/l4w3c` from the worktree
root with fixture paths under `third_party/testing/w3c`. The SPARQL 1.2 total is
the sum of the ten leaf totals, not the umbrella manifest. The 1.0 result counts
the full manifest once; cluster deltas above are measured stages rather than a
sum of focused tests.

`Harness.Compare.compareSelectRows` also inherits an older runner rule that
uses multiset comparison for every blank-node-free SELECT result, even when the
query contains `ORDER BY`. This accommodates tied order keys, but it also means
the harness does not detect an incorrect order among non-tied, blank-node-free
rows. The indexed RDF result decoder preserves the expected row sequence; the
comparison limitation remains and needs a separate repair that preserves the
specification's freedom for ties.
