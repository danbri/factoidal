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

## 4. Second tight test case — a malformed literal inside a triple term

`malformed-literal-no-spurious` and `malformed-literal-bnode-neg` are
both `mf:NegativeEntailmentTest`, regime `"RDF"`,
`mf:recognizedDatatypes (xsd:integer)`, and both take the same action
graph:

```
:a1 :p1 <<( :a :b "c"^^xsd:integer )>>.
```

`"c"^^xsd:integer` is malformed and `xsd:integer` is recognised. The
tests require that this graph does NOT entail

```
:a1 :p1 <<( :a :b "d"^^xsd:integer )>>.      (no-spurious)
:a1 :p1 <<( :a :b _:x )>>.                   (bnode-neg)
```

### The two readings

**Reading A — the graph is D-inconsistent (what the Lean tree does).**
RDF 1.2 Semantics §7: an ill-typed literal of a recognised datatype
denotes nothing, so a graph using one is satisfied by no
D-interpretation, and an unsatisfiable graph entails EVERY graph. Both
conclusions follow, so both tests fail. This is the current
`DInterpCond` clause 2, whose reach into a triple term's interior was a
deliberate landing (the issue-602 repair, noted at
`Unified/DSchema.lean`'s soundness section), and
`dEntailsMt_illtyped_native` is stated about it.

**Reading B — the interior of a triple term is not asserted (what the
suite requires).** A triple term is a TERM naming a proposition, and
the proposition is not asserted — which the suite states separately in
`triple-term-not-asserted` (positive, and passing). Under this reading
only a literal in the object position of an ASSERTED triple can make a
graph D-inconsistent, the action graph is satisfiable, and neither
conclusion follows.

### The choice made — none yet, and why

Reading B is very probably right, and it is what the fixtures'
`rdfs:comment` says ("Malformed literals within triple terms do not
lead to spurious entailment"). It is NOT taken in this session because
it is not an engine repair: `DInterpCond` clause 2 is the SPECIFICATION
side of the model theory, `dEntailsMt_illtyped_native` and
`regimeEntails_d_sound_mt` are stated about it, and
`Unified.unified_adequate_d` sits downstream. Narrowing it is sound for
the executable procedure (it removes a disjunct, so `regimeEntails`
answers `true` less often) but it changes what the model theory MEANS,
and the reach into the interior was landed on purpose. Reversing a
deliberate modelling decision belongs in a change that re-derives the
theorems, not in the last hour of a session.

⚠️ **Open, with its test ids**: `malformed-literal-no-spurious`,
`malformed-literal-bnode-neg`. The work is: restrict `DInterpCond`
clause 2 (and `hasIllFormedLiteral`, currently
`t.o.mentionedLiterals.any`) to the asserted object position, re-prove
`dEntailsMt_illtyped_native` and `regimeEntails_d_sound_mt`, and check
`triple-term-not-asserted` and `malformed-literal` (both currently
passing) do not move.

## 5. Additional open-source 1.2 test material — surveyed, none vendorable

The directive asked for additional open-source RDF 1.2 / SPARQL 1.2 /
RDF-star tests. Surveyed 2026-09-07; the result is negative, and the
negative is recorded so the search is not repeated.

| source | licence | verdict |
| --- | --- | --- |
| `w3c-cg/rdf-star` `tests/` | W3C 3-clause BSD (LICENSE.md) | The archived CG predecessor of the suite we already vendor; near-total filename overlap. 8 files have no current-manifest match, provenance unverified. |
| other `w3c/rdf-tests` branches | same | All behind current main; stale work in progress, nothing new. |
| `apache/jena` `jena-arq/testing/` | Apache-2.0 | RDF 1.2 test data is embedded in `.java` files. Its 8 TriX-star fixtures are genuinely new syntax coverage, but TriX is not an in-scope concrete syntax here and they carry no manifest. |
| `eclipse-rdf4j/rdf4j` | BSD-3-Clause | Its RDF-star fixtures are vendor result dialects, not spec conformance; W3C data is fetched at build time. |
| `oxigraph/oxigraph` `testsuite/` | MIT OR Apache-2.0 | Its `rdf-tests` entry is a submodule of `w3c/rdf-tests` — a mirror. Its own tests are parser robustness with no star / reifier / triple-term / base-direction content. |
| `RDFLib/rdflib` | BSD-3-Clause | No 1.2 fixtures of its own; its TriX-star files are Jena's. |
| `rdfjs/N3.js` | MIT | Assertions inline in JavaScript; no fixture files to vendor. |
| `dotnetrdf/dotnetrdf` | MIT (`License.txt`) | A byte-for-byte copy of the same CG suite as row 1. |
| `filip26/titanium-*` | Apache-2.0 | RDFC-1.0 tooling; no RDF 1.2 material. |

**Nothing was vendored, and `tools/ensure-test-env.sh` is unchanged.**
The one item worth a later look, not urgent: Jena's Apache-2.0
TriX-star fixtures, if TriX ever becomes an in-scope syntax.

## Status

Final for the 2026-09-07 session. Every number below was measured in
this worktree by running the runner named, not quoted from a report.

| suite | before | after |
| --- | --- | --- |
| `rdf-semantics` | 21 pass, 11 fail, 0 skip, **15 unsupported** (of 47) | **40 pass, 7 fail, 0 skip, 0 unsupported** (of 47) |
| RDF 1.2 syntax/eval/c14n (9 leaf suites) | 324 pass, 0 fail (of 324) | 324 pass, 0 fail (of 324) |
| SPARQL 1.2 (10 leaf suites) | 254 pass, 0 fail (of 254) | 254 pass, 0 fail (of 254) |

**RDF 1.2 and SPARQL 1.2 total: 618 pass, 7 fail, 0 unsupported (of
625).**

### The commits

1. `docs(rdf12)` — this record, with the measured baseline.
2. `lean(rdf12)` — `xsd:double` / `xsd:float` / `rdf:JSON` lexical
   spaces, and the `RDF` regime's D-value comparator. 21 → 36 pass, 15
   unsupported → 0.
3. `lean(rdf12)` — language-tag case at term identity, and the
   triple-term interior tightening. 36 → 40 pass.

### The tight test cases written

* § 3 — `opaque-language-string` vs `opaque-dir-language-string`.
  Implemented (Reading 1); both readings pinned as `#guard`s in
  `L4Factoidal/RDF/EntailmentTests.lean`.
* § 4 — `malformed-literal-no-spurious` / `malformed-literal-bnode-neg`.
  Not implemented; the reason and the work are stated above.

### Open, by test id

| test ids | cause | note |
| --- | --- | --- |
| `malformed-literal-no-spurious`, `malformed-literal-bnode-neg` | § 4 above | Needs `DInterpCond` clause 2 narrowed and its theorems re-derived. |
| `literal-type` | A literal must denote an instance of its datatype: `:a :b "42"^^xsd:integer` entails `:a :b _:x . _:x rdf:type xsd:integer.` This is the RDF-entailment rule that types a literal's denotation, which the closure does not emit. | Tractable; no theorem in the way. |
| `annotation`, `annotation-unfolded` | The expected result names an IRI reifier where the action's `{\| \|}` shorthand makes a fresh blank node. | The F\* tree fails both identically. |
| `triple-terms-propositions` | Needs a literal or triple term in SUBJECT position; `Triple.s : Subject` cannot represent either. | Term-model limit, shared with the F\* tree. |
| `reifies-range` | The `rdf:reifies` range step lives in `Regime.rdfsPlus`, not `.rdfs`, because `.rdfs` is the closure `Unified/SparqlAdequacy.regime_sound_rdfs` is stated about. | Recover by proving the widened closure sound, not by moving the step. |

### Gates, re-measured at the final commit

`lake build` green, 0 errors; hygiene clean (`sorry` 0, user `axiom` 0,
`native_decide` 0, `unsafe` 0, `partial def` 172 against baseline 172);
SPARQL 1.1 `l4w3c` 631 pass, 0 fail (of 631); `l4sparql-probe` 403
pass, 0 fail (of 403); `l4rdfxml-probe` 132 of 132 eval-isomorphic and
41 of 41 reject-negative; `l4turtle-probe` 242 of 242 parse-positive,
115 of 115 reject-negative, 108 of 108 eval-iso; `l4rdfc-probe` 63 of
63 rdfc10 eval, 21 of 21 map eval, 1 of 1 sha384, 1 of 1 negative;
`l4rdfs-semi` 6 of 6.
