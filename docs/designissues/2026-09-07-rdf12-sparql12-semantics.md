# RDF 1.2 and SPARQL 1.2 semantics in the Lean 4 tree

Date: 2026-09-07. Worktree `/Users/danbri/working/factoidal-wt-rdf12`,
branch `wt/rdf12`. Owner directive, 2026-09-07, verbatim:

> "For RDF/SPARQL 1.2, we MUST HAVE THE SEMANTICS. It is the foundation
> for EVERYTHING WE ARE DOING HERE. If 1.2 semantics is problematic we
> need a tight testcase explaining this. Both Lean4 and F*. Test both
> comprehensively, and look for additional opensource 1.2 tests for both
> RDF and SPARQL."

This record covers the LEAN tree. The F\* tree is a sibling task.

Predecessors: `2026-07-16-rdf12-sparql12-impact-strategy.md` (the F\*
roadmap and the 2026-07-16 census) and
`2026-09-07-lean-rif-rml-csvw-geo-gap.md` § 6, which first ran the
rdf12 `rdf-semantics` manifest in Lean.

## 1. Measured baseline, before any engine change

Method: every vendored RDF 1.2 and SPARQL 1.2 leaf manifest, run
through the Lean runners in this worktree at commit `2715d520c`, from
the repository root as `lake -d formal/lean4 exe l4w3c <manifest>` and
`lake -d formal/lean4 exe l4rdf-semantics`. No number here is quoted
from a dashboard or from an earlier report.

### RDF 1.2

| suite | pass | fail | skip | unsupported | out of |
| --- | --- | --- | --- | --- | --- |
| `rdf-n-triples/syntax` | 29 | 0 | 0 | 0 | 29 |
| `rdf-n-triples/c14n` | 41 | 0 | 0 | 0 | 41 |
| `rdf-n-quads/syntax` | 27 | 0 | 0 | 0 | 27 |
| `rdf-n-quads/c14n` | 41 | 0 | 0 | 0 | 41 |
| `rdf-turtle/syntax` | 67 | 0 | 0 | 0 | 67 |
| `rdf-turtle/eval` | 29 | 0 | 0 | 0 | 29 |
| `rdf-trig/syntax` | 35 | 0 | 0 | 0 | 35 |
| `rdf-trig/eval` | 25 | 0 | 0 | 0 | 25 |
| `rdf-xml/eval` | 30 | 0 | 0 | 0 | 30 |
| **`rdf-semantics`** | **21** | **11** | **0** | **15** | **47** |

### SPARQL 1.2

| suite | pass | fail | skip | unsupported | out of |
| --- | --- | --- | --- | --- | --- |
| `syntax` | 2 | 0 | 0 | 0 | 2 |
| `syntax-triple-terms-positive` | 113 | 0 | 0 | 0 | 113 |
| `syntax-triple-terms-negative` | 65 | 0 | 0 | 0 | 65 |
| `eval-triple-terms` | 41 | 0 | 0 | 0 | 41 |
| `expression` | 1 | 0 | 0 | 0 | 1 |
| `grouping` | 1 | 0 | 0 | 0 | 1 |
| `lang-basedir` | 11 | 0 | 0 | 0 | 11 |
| `codepoint-escapes` | 8 | 0 | 0 | 0 | 8 |
| `version` | 9 | 0 | 0 | 0 | 9 |
| `rdf11` (1.1 regression set) | 3 | 0 | 0 | 0 | 3 |
| **SPARQL 1.2 total** | **254** | **0** | **0** | **0** | **254** |

Every runner read every manifest. No manifest was skipped and no
manifest failed to load, so there is no runner defect to fix first.
The `HARNESS-DIAG` line of each run reports
`no_manifest=0 zero_tests=0 budget_exceeded=0`, which is what rules out
a suite that "passes" by running nothing (anti-pattern #28 — an audit
that finds nothing is evidence about the audit first).

### What the baseline says

The RDF 1.2 concrete syntaxes, the RDF 1.2 canonical forms, and the
whole of SPARQL 1.2 — triple-term syntax and evaluation, `TRIPLE` /
`SUBJECT` / `PREDICATE` / `OBJECT` / `isTRIPLE`, `LANGDIR` /
`STRLANGDIR` / `hasLANG` / `hasLANGDIR`, `VERSION`, codepoint escapes —
are complete in the Lean tree: **584 pass, 0 fail (out of 584)** across
RDF 1.2 syntax/eval/c14n and SPARQL 1.2.

The entire remaining gap is the one suite the owner's directive names:
**RDF 1.2 Semantics, 21 pass, 11 fail, 15 unsupported (out of 47)**.
This record is about that suite.

## 2. The per-test failure list, grouped by cause

### Cause A — three datatypes have no lexical space (15 unsupported)

`Harness/Run.lean`'s `recognizedDatatypesOf` refuses a manifest
`mf:recognizedDatatypes` entry that is not in
`RDF.Datatypes.modelledDatatypes`, and reports `unsupported` rather
than guessing. The three missing IRIs and their fixtures:

* `rdf:JSON` — `json-array-unordered`, `json-object-unordered`,
  `json-zero`, `json-zero-array`, `json-round-different`,
  `json-round-same`, `json-infinity` (7)
* `xsd:float` — `float-zero`, `float-round-different`,
  `float-round-same`, `float-infinity` (4)
* `xsd:double` — `double-zero`, `double-round-different`,
  `double-round-same`, `double-infinity` (4)

The D-VALUE comparison for all three already exists and is
`#guard`-pinned (`RDF/Entailment.lean`'s `dtValueLeq`, over
`XSD.IEEE754.doubleValueEq` / `floatValueEq` and `rdfJsonValueEq`).
What is missing is the LEXICAL space — the decision "is this literal
ill-formed?" — which is a different question and the one
`modelledDatatypes` is the gate for. Adding the three IRIs to that
list without the lexical spaces would make every `xsd:double` literal
count as well-formed, malformed ones included, in a suite that
contains malformed-literal fixtures. That is the widening this record
refuses; the same refusal is recorded at
`2026-09-07-lean-rif-rml-csvw-geo-gap.md` § "rdf-semantics".

### Cause B — language-tag case at the term level (4 fails)

`opaque-literal`, `opaque-language-string`,
`opaque-language-string-control`, `opaque-dir-language-string-control`
— all `mf:entailmentRegime "simple"`, all "should entail under simple
but does not". See § 3, the tight test case.

### Cause C — reifier identity in the `{| |}` shorthand (2 fails)

`annotation`, `annotation-unfolded`. The expected result names an IRI
reifier where the action's annotation shorthand produces a fresh blank
node. The F\* tree fails both identically.

### Cause D — a literal or triple term in SUBJECT position (2 fails)

`literal-type`, `triple-terms-propositions`. `Triple.s : Subject`
cannot represent either. The F\* tree has the same limit. This is a
term-model question, not an entailment question.

### Cause E — the `rdf:reifies` range step under RDFS (1 fail)

`reifies-range`. The step exists (`rdf12ReifiesClosure`) but lives in
`Regime.rdfsPlus`, not `Regime.rdfs`, because moving it into `.rdfs`
widens a closure that `Unified/SparqlAdequacy.regime_sound_rdfs` is
stated about, and the tree stopped building for it on 2026-09-07.
Recovering this test means proving the widened closure sound, not
moving the step back.

### Cause F — malformed-literal polarity (2 fails)

`malformed-literal-no-spurious`, `malformed-literal-bnode-neg`, both
"should NOT entail under RDF but does".

## 3. Tight test case — directional language strings inside a triple term

The owner asked for a tight test case wherever 1.2 semantics is
problematic. This is the one the suite forces.

### The fixtures

Two manifest entries of IDENTICAL shape and OPPOSITE polarity. Both
carry `mf:entailmentRegime "simple"` and `mf:recognizedDatatypes ()`.

| test | polarity | action | result |
| --- | --- | --- | --- |
| `opaque-language-string` | **Positive**Entailment | `:a1 :p1 <<( :a :b "hello"@en-us )>>.` | `:a1 :p1 <<( :a :b "hello"@en-US )>>.` |
| `opaque-dir-language-string` | **Negative**Entailment | `:a1 :p1 <<( :a :b "hello"@en-us--ltr )>>.` | `:a1 :p1 <<( :a :b "hello"@en-US--ltr )>>.` |

The only difference between the two pairs is the `--ltr` base
direction. The suite therefore asserts that, inside a triple term, a
language tag matches case-insensitively but a language tag CARRYING A
BASE DIRECTION does not.

### The two readings

**Reading 1 — the suite is right.** RDF 1.2 Semantics treats the
interior of a triple term differently for `rdf:dirLangString`. Under
this reading a comparator must know whether the comparison site is
inside a triple term, and compare `rdf:dirLangString` language tags
case-sensitively there and case-insensitively elsewhere. The F\* tree
implements exactly this clause in `RDF.Entailment.Regime.fst`'s
`dt_value_leq`, and scores 41 pass, 3 fail on this manifest.

**Reading 2 — the suite contradicts Concepts.** RDF 1.2 Concepts §3.3
gives the value space of both `rdf:langString` and `rdf:dirLangString`
as tuples whose language-tag component is compared without regard to
ASCII case; two literals differing only in tag case are THE SAME RDF
TERM, in every position. Triple terms are transparent (RDF 1.2
Concepts §3.3, the whole point of `<<( )>>` replacing RDF-star's
opaque `<< >>`), so a term identity cannot be suspended inside one.
Under this reading `opaque-dir-language-string` should be a positive
test, its `rdfs:comment` ("Literals within reifying terms ... are
opaque, even when their datatype is recognized") is inconsistent with
its sibling's comment ("Literals within reifying terms (including
language strings) are transparent"), and both fixtures are `rdft:approval
rdft:NotClassified` — the W3C's own marker for a test the working group
has not ratified.

### The choice made

Implement Reading 1 — the position-aware clause — and record Reading 2
here. Three reasons, in order:

1. The manifest is the conformance artifact. A reading that turns a
   `NegativeEntailmentTest` into a pass is a regression against the
   suite regardless of how the prose reads.
2. It is what the F\* tree already does, and CLAUDE.md's standing
   decision (owner, 2026-08-24) is that the two trees should agree in
   behaviour.
3. It is the CONSERVATIVE direction. Reading 1 makes entailment
   strictly LESS permissive than Reading 2 inside a triple term, so it
   cannot manufacture an entailment; Reading 2 can.

Both readings are pinned as `#guard`s next to the implementation, so a
later session cannot flip one without seeing the other.

⚠️ This is a genuine specification-versus-suite divergence on a
`rdft:NotClassified` pair, not an implementation gap. If the RDF WG
ratifies these tests unchanged, Concepts §3.3 needs a sentence about
triple-term interiors; if it ratifies Concepts as written,
`opaque-dir-language-string` has the wrong polarity.

## Status

Filled in per commit below.

| suite | before | after |
| --- | --- | --- |
| `rdf-semantics` | 21 pass, 11 fail, 0 skip, 15 unsupported (of 47) | (in progress) |

Unchanged gates, re-measured each commit: RDF 1.2 syntax/eval/c14n
324 pass 0 fail (of 324); SPARQL 1.2 254 pass 0 fail (of 254).
