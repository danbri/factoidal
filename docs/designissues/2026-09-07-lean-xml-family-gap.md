# Lean 4 coverage gaps in the XML family, measured

Date: 2026-09-07. Branch: `wt/lean-cov-xml`.

This record is written TEST FIRST. Every failing or missing test below
was produced by running a probe before any engine change. Each later
fix commit names the tests it turns green and gives the before and
after score.

Scope: XPath 1.0, XSLT 1.0, MathML (Content markup), XML 1.0
conformance. The comparison is the Lean 4 tree (`formal/lean4`,
`L4Factoidal`) against the F* tree (`formal/fstar`) on the same
corpora.

## Method, and what it can and cannot see

Each area is scored by running a probe over a manifest that lists real
files on disk. No case is synthesised. Where the Lean probe and the F*
runner read different manifests, that difference is named, because a
score taken over a smaller denominator is not comparable with one
taken over a larger denominator (anti-pattern 3, 25, 28).

Probes resolve a relative corpus directory against the process working
directory first and against `../../` second, so
`lake -d formal/lean4 exe NAME` from the repository root and
`lake exe NAME` from inside `formal/lean4` both work. Before this
change some probes worked from only one of the two and reported a
missing corpus from the other, which reads as a broken probe rather
than as a wrong working directory.

## 1. XPath 1.0 — no Lean runner for the F* unit battery

The Lean tree has `L4Factoidal/XPath/` (`Data`, `Expr`, `Eval`,
`Mini`, `Number`) with `#guard` checks compiled into the build. It had
NO runner for the F* unit suite `tests/unit/xpath_tests.ml` — 100
spec-cited cases against XPath 1.0 (REC-xpath-19991116), F* score 100
pass, 0 fail (out of 100).

The 100 cases are not a vendored W3C suite; no machine-checkable
XPath 1.0 suite exists in isolation. The file IS the conformance
signal, so the two trees were being measured by different instruments.

Gap: the 100 cases are extracted verbatim into
`tests/unit/xpath_cases.json` and run by `lake exe l4xpath`
(`Harness/XPathRun.lean`). Before and after scores are in the status
section.

## 2. XSLT 1.0 — three failures, and a 1690-case corpus not run

### 2a. The three failures on the default corpus

`lake exe l4xslt` over `third_party/testing/xslt`:
84 pass, 3 fail (out of 87 decided), 1 refused.
F*: 87 pass, 1 skip.

The three:

| case | category |
| --- | --- |
| `copy-3102` | copy |
| `namespace-4801` | namespace |
| `node-1601` | node |

The one refusal, `select/select-5901`, is a corpus fact rather than an
engine gap: the vendoring renamed each environment's source file, so
the stylesheet's `document('select-59.xml')` names a file the corpus
does not carry.

### 2b. The Apache Xalan mirror was never run through Lean

`third_party/testing/xslt1-xalan` (apache/xalan-test @ 5120be9,
Apache-2.0) holds 1690 tests in 35 categories. F* measured it on
2026-07-17 at 970 pass, 712 fail, 8 skip (out of 1690). Lean had not
been pointed at it.

Two runner defects had to be repaired before a number existed at all:

* `IO.FS.readFile` raises on a file that is not UTF-8, and the Xalan
  mirror carries Latin-1 and UTF-16 documents. The run died at case 60
  of 1690 with an uncaught exception. Reads now go through
  `readUtf8?`, and a file this parser cannot decode is counted apart
  as NOT-UTF-8, the same way the XML conformance runner counts one.
  The profile is UTF-8; a transcoding gap is not a transform defect.
* A failing case printed its whole produced and expected text. Over
  1690 cases that is megabytes, so it is now behind `--verbose`.

Measured Lean baseline, 2026-09-07 (`lake exe l4xslt --base
third_party/testing/xslt1-xalan`):

```
1134 pass, 284 fail (out of 1418 decided)   [1123 exact + 11 whitespace-only]
259 refused, 10 not UTF-8 or missing, 3 unreadable (out of 1690 in the manifest)
```

The Lean and F* numbers are NOT directly comparable: the Lean runner
has a refusal bucket and the F* run did not, so 259 cases the Lean
engine declines are counted apart rather than as failures. On the
decided set Lean fails 284 where F* failed 712 over a denominator of
1690.

Failure clusters, largest first (fail / decided):

```
  69 / 102   output          43 / 47   attribset      10 / 129  string
  57 / 130   namespace       13 / 56   copy            8 / 8    reluri
                             12 / 62   variable        7 / 40   sort
                             11 / 23   lre             6 / 8    mdocs
                             10 / 10   impincl         6 / 129  axes
```
then 5 select, 4 extend, 4 whitespace, 3 node, 3 attribvaltemplate,
3 position, 3 conflictres, 2 idkey, 2 boolean, 1 math,
1 processorinfo, 1 modes.

Refusals, by reason: 112 an expression or instruction did not
evaluate; 99 `xsl:number`; 16 `xsl:apply-imports`; 12 a named template
the stylesheet does not define; 9 an unreadable `key()`/`id()` match
pattern; 4 a top-level `xsl:variable`/`xsl:param` that did not
evaluate; 5 an extension element (`xsl:exciting-new-*`,
`xsl:import-table`) which `xsl:fallback` exists to handle; 2 a
stylesheet root that is neither `xsl:stylesheet` nor `xsl:transform`.

The two categories where the engine has NOTHING (`impincl` 10/10,
`reluri` 8/8) match the F* run's holes 7 and the `document()` partial.
`attribset` at 43 / 47 and `output` at 69 / 102 are the largest
clusters with an engine present but wrong.

## 3. MathML — 25 Content-markup cases not attempted

Lean `lake exe l4mathml`: 56 pass, 0 fail (out of 56).
F* `mathml-content`: 81 pass (out of 81).

The 25-case difference is not a defect list. `third_party/testing/
mathml/` carries TWO manifests and the Lean probe reads only the
first:

* `manifest.json` — 56 cases, Content markup, MathML 3.0 chapter 4.
* `matrix-manifest.json` — 25 cases, Content markup, MathML 3.0
  §4.4.10 (Linear Algebra) and the OpenMath `linalg1`/`linalg2`
  Content Dictionaries.

**All 25 are Content markup. None is a presentation-markup case.**
The F* MathML module is a BACKEND by design — Content MathML decoding
and exact evaluation — and never a presentation renderer or a UI
(owner, 2026-09-07). A presentation case would therefore be out of
scope by design rather than a gap. There are none here, so all 25 are
in scope:

`matrix-literal-2x2`, `matrix-literal-rational`, `vector-literal`,
`matrix-plus`, `matrix-minus`, `matrix-plus-shape-mismatch`,
`scalar-times-matrix`, `matrix-times-2x2`, `matrix-times-rectangular`,
`matrix-times-inner-mismatch`, `transpose-2x3`, `transpose-square`,
`determinant-2x2`, `determinant-3x3`, `determinant-identity-3x3`,
`determinant-nonsquare`, `scalarproduct`, `scalarproduct-mismatch`,
`vectorproduct`, `vectorproduct-general`, `outerproduct`,
`selector-matrix`, `selector-vector`, `selector-out-of-range`,
`matrix-times-then-determinant`.

Four of the 25 expect the UNDEFINED value (`matrix-plus-shape-
mismatch`, `matrix-times-inner-mismatch`, `determinant-nonsquare`,
`scalarproduct-mismatch`, `selector-out-of-range` — five). `undef` is
the expected ANSWER, not a skip: an evaluator that returned a number
for a determinant of a non-square matrix would be wrong in the
direction hardest to notice.

The expected values are written canonically: a scalar as `n` or
`num/den`, a vector as `[a,b,c]`, a matrix as `[[a,b],[c,d]]`. The
Lean probe's `showValue` writes scalars only, so the probe needs a
matrix and vector shape before it can attempt these at all.

## 4. XML 1.0 conformance — the 22 failures

`lake exe l4xmlconf`: 1840 pass, 22 fail (out of 1862 in profile).
Out of profile and reported not scored: 24 optional-behaviour, 55
XML 1.1, 64 not UTF-8, 313 for editions 1 to 4 only, 59
Namespaces-in-XML.

The profile is XML 1.0 Fifth Edition, NON-VALIDATING, NON-NAMESPACE,
UTF-8 only. A `valid` and an `invalid` case must BOTH be accepted;
`invalid` means it violates the DTD, which a non-validating parser is
not asked to notice.

Listed by construct, with the spec section the suite cites.

### Cluster A — the text declaration of an external entity is never checked (7)

`[77] TextDecl ::= '<?xml' VersionInfo? EncodingDecl S? '?>'`
(XML 1.0 §4.3.1). The runner resolves an external entity's replacement
text but never parses or constrains its text declaration, so every
malformed one is accepted.

| id | type | what it violates |
| --- | --- | --- |
| `decl01` | not-wf | an external entity may not carry `standalone=` |
| `not-wf-ext-sa-002` | not-wf | same, §4.3.1/§4.3.2 |
| `dtd07` | not-wf | `encoding=` is REQUIRED in a text declaration |
| `encoding07` | not-wf | same |
| `ibm-not-wf-P77-ibm77n01.xml` | not-wf | `VersionInfo` after `EncodingDecl` |
| `ibm-not-wf-P77-ibm77n03.xml` | not-wf | `>` used as the closing sequence |
| `ibm-not-wf-P77-ibm77n04.xml` | not-wf | closing sequence missing |

These are parser defects. Fixing them is one function: parse `[77]`
at the head of every resolved external entity and reject a text
declaration that omits `encoding`, orders the fields wrongly, carries
`standalone`, or is not closed by `?>`.

### Cluster B — parameter entities (4)

| id | type | section | what it needs |
| --- | --- | --- | --- |
| `not-wf-not-sa-009` | not-wf | §2.8 `[28a]` | WFC: PE Between Declarations — a markup declaration must not straddle a PE boundary |
| `ibm-not-wf-p28a-ibm28an01.xml` | not-wf | §2.8 `[28a]` | same |
| `valid-not-sa-023` | valid | §2.3 §4.1 | a PE reference inside an attribute-list declaration must resolve |
| `rmt-e3e-13` | invalid | 3e erratum | once an internal PE reference appears, an UNDECLARED entity is only a validity error, so a non-validating parser must ACCEPT |

Parser defects, all in the same area: the internal and external subset
does not track parameter-entity boundaries.

### Cluster C — WFC "No External Entity References" in an attribute value (2)

XML 1.0 §3.1 `[41]`. An attribute value must not reference an entity
declared as external, directly or indirectly.

| id | type |
| --- | --- |
| `ibm-not-wf-P41-ibm41n10.xml` | not-wf (direct reference) |
| `ibm-not-wf-P41-ibm41n11.xml` | not-wf (indirect reference) |

Parser defect. Needs the entity table to record which entities are
external, which cluster A's work also needs.

### Cluster D — WFC "Entity Declared" against an external declaration (2)

| id | type | section |
| --- | --- | --- |
| `ibm-not-wf-P32-ibm32n09.xml` | not-wf | §2.9 — `standalone="yes"` with an entity declared in an external markup declaration |
| `ibm-not-wf-P68-ibm68n06.xml` | not-wf | §4.1 `[68]` — an externally declared entity referenced in an `AttValue` |

Parser defects, sharing cluster C's entity table.

### Cluster E — parameter entities in the EXTERNAL subset (2)

| id | type |
| --- | --- |
| `rmt-e2e-18` | valid — a PE in an external subset file declaring a nested PE, then a general entity |
| `o-p28pass5` | valid |

Parser defects; the same PE machinery as cluster B, reached through
an external subset rather than an internal one.

### Cluster F — encoding, and a PROFILE decision not a defect (5)

| id | type | why |
| --- | --- | --- |
| `rmt-e2e-61` | not-wf | the document declares `encoding="UTF-16"` while being byte-encoded otherwise. XML 1.0 §4.3.3: "it is a fatal error if an XML entity is determined to be in UTF-16 and contains no byte order mark". This parser is UTF-8 only and does not read the declared encoding at all, so it cannot raise this error. PROFILE DECISION. |
| `hst-lhs-007` | not-wf | a UTF-8 byte order mark with an `iso-8859-1` declaration. §4.3.3 makes an encoding declaration that contradicts the BOM a fatal error. Same reason: UTF-8 only, encoding declaration not read. PROFILE DECISION. |
| `ext02` | valid | external parsed entities in a DIFFERENT encoding from the base document (§4.3.2 `[78]`). Reading it requires transcoding, which the stated profile excludes. PROFILE DECISION. |
| `rmt-e2e-38` | not-wf | an external general entity whose text declaration is malformed — cluster A. |
| `o-p30fail1` | not-wf | `[30] extSubset ::= TextDecl? extSubsetDecl` — an external subset with a bad text declaration. Cluster A. |

The three PROFILE DECISIONS are the honest reading: a parser that
declares itself UTF-8 only cannot detect a contradiction between a
byte order mark and a declared encoding, because it never reads the
declared encoding. They should move out of the scored denominator and
into the "not UTF-8" out-of-profile bucket that already exists, which
is a runner change, not a parser change. Doing that WITHOUT the
parser fixes would lower the fail count by three while changing
nothing about the parser, so it is landed only alongside the cluster A
work and reported separately.

Summary: of 22, **19 are parser defects** in four related areas
(text declarations, parameter entities, the external-entity table) and
**3 are profile decisions** (`rmt-e2e-61`, `hst-lhs-007`, `ext02`).

## Status

| area | probe | before (2026-09-07) | after | closed | open |
| --- | --- | --- | --- | --- | --- |
| XPath 1.0 | `l4xpath` (new) | no runner existed | see below | | |
| XSLT 1.0 default | `l4xslt` | 84 pass, 3 fail (of 87 decided) | | | `copy-3102`, `namespace-4801`, `node-1601` |
| XSLT 1.0 Xalan | `l4xslt --base …xslt1-xalan` | 1134 pass, 284 fail (of 1418 decided), 259 refused | | | clusters above |
| MathML Content | `l4mathml` | 56 pass, 0 fail (of 56); 25 not attempted | | | the 25 linear-algebra cases |
| XML 1.0 conformance | `l4xmlconf` | 1840 pass, 22 fail (of 1862 in profile) | | | 19 defects, 3 profile decisions |

The "after" column and the closed/open columns are filled in by the
fix commits that follow this one, each naming its own tests.
