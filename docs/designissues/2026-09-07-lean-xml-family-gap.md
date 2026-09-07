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

## Status, at the end of the 2026-09-07 session

| area | probe | before | after | out of |
| --- | --- | --- | --- | --- |
| XPath 1.0 | `l4xpath` (new) | no runner existed; 89 pass, 11 fail on first run | **100 pass, 0 fail** | 100 |
| MathML Content | `l4mathml` | 56 pass, 0 fail; 25 not attempted | **81 pass, 0 fail** | 81 |
| XML 1.0 conformance | `l4xmlconf` | 1840 pass, 22 fail | **1861 pass, 0 fail** | 1861 in profile (see the second session below) |
| XSLT 1.0 default | `l4xslt` | 84 pass, 3 fail | 84 pass, 3 fail | 87 decided |
| XSLT 1.0 Xalan | `l4xslt --base …xslt1-xalan` | not run through Lean | **1134 pass, 284 fail, 259 refused** | 1418 decided of 1690 |

XPath and MathML now equal the F* scores (100 of 100, and 81 of 81).

### Closed

* **XPath 1.0** — the 100-case battery is ported and all 100 pass.
  Four defects were found and fixed by running it: an unbound test
  prefix compared against a constant sentinel so an undeclared prefix
  could never match; `substring()` with an infinite length falling
  into an empty-string catch-all instead of being worked through
  `Num`; relational operators always coercing through `number()` when
  both operands are strings; and namespace-node presentation order,
  which is fixed in the slot index `normalize` sorts on, not
  downstream.
* **MathML** — all 25 linear-algebra cases. All are Content markup;
  none is presentation.
* **XML conformance, 13 of the 22.** `[77] TextDecl` is now enforced
  on external entities and the external subset (10 cases); the two
  section 4.3.3 encoding conflicts a UTF-8-only parser CAN decide
  (`rmt-e2e-61`, `hst-lhs-007`); and section 4.3.4, an entity
  declaring version 1.1 inside a 1.0 document (`rmt-e2e-38`).

### Two corrections to this document's own first version

1. **Only ONE of the 22 is a profile decision, not three.**
   `rmt-e2e-61` and `hst-lhs-007` were filed as profile decisions on
   the reasoning that a UTF-8-only parser cannot read a declared
   encoding. That was backwards. Reading UTF-8 only is exactly what
   decides them: the entity in hand DECODED as UTF-8, so a declaration
   of UTF-16 contradicts the bytes that were read, and a UTF-8 byte
   order mark with a declaration naming anything else is the same
   contradiction from the other side. Both are now enforced. `ext02`
   is the only genuine profile decision: external entities in a
   different encoding need transcoding.
2. **`rmt-e2e-38` was filed under the text-declaration cluster and is
   not one.** Its entity carries a WELL-FORMED text declaration; what
   is wrong is that it says version 1.1 inside an XML 1.0 document
   (section 4.3.4). Fixed separately.

Both corrections come from reading the actual fixture files rather
than the suite's one-line descriptions. A cluster assignment made from
a description is a hypothesis.

### Open, with test ids

* **XML conformance, 9 remaining.**
  * Parameter-entity machinery, 6: `not-wf-not-sa-009`,
    `ibm-not-wf-p28a-ibm28an01.xml` (section 2.8 `[28a]`, WFC PE
    Between Declarations), `valid-not-sa-023`, `rmt-e3e-13` (the 3e
    erratum: once an internal PE reference appears, an undeclared
    entity is only a validity error, so a non-validating parser must
    ACCEPT), `rmt-e2e-18` and `o-p28pass5` (the same machinery reached
    through an external subset). The parser does not track
    parameter-entity boundaries; that is one piece of work covering
    all six.
  * WFC Entity Declared against an external declaration, 2:
    `ibm-not-wf-P32-ibm32n09.xml` (section 2.9),
    `ibm-not-wf-P68-ibm68n06.xml` (section 4.1 `[68]`).
  * `ext02` — the profile decision above.
* **WFC "No External Entity References" (section 3.1 `[41]`) is still
  unimplemented**, even though `ibm-not-wf-P41-ibm41n10.xml` and
  `ibm-not-wf-P41-ibm41n11.xml` are now green. They reject because
  their entity file independently violates `[77]`, not because of the
  constraint they name. Counting them as closing that constraint would
  be wrong.
* **XSLT default corpus, 3.** Two are not defects and one is:
  * `node-1601` and `copy-3102` differ from the gold files only in
    the ORDER of namespace nodes and namespace declarations. XPath 1.0
    section 5.4 makes the relative order of namespace nodes
    IMPLEMENTATION-DEPENDENT; the gold files pin Xalan's order
    (declaration order, `xml` first) and this engine's documented
    order is default first, then prefixes ascending with `xml`
    included — which the XPath battery itself pins. Changing it to
    match the gold files would break three XPath cases and would not
    be more conformant. These are corpus-order differences, not
    defects.
  * `namespace-4801` IS a defect: a literal result element does not
    carry its in-scope namespace declarations to the output
    (XSLT 1.0 section 7.1.1). It is very likely the same defect as the
    57-of-130 `namespace` cluster on the Xalan mirror.
* **XSLT Xalan mirror, 284 failures and 259 refusals**, clustered
  above. The largest actionable clusters are `output` (69 of 102),
  `namespace` (57 of 130), `attribset` (43 of 47), and the two
  categories with nothing implemented at all, `impincl` (10 of 10,
  `xsl:import`/`xsl:include`/`xsl:apply-imports`) and `reluri` (8 of
  8). The largest single refusal reason is `xsl:number`, 99 cases.

### A structural duplication introduced by this session, to repair

`L4Factoidal/MathML/Matrix.lean` was written new for the 25
linear-algebra cases. `L4Factoidal/Math/Matrix.lean` ALREADY EXISTED
— a port of `formal/fstar/Math.Matrix.fst` with the same operations
over the same exact rationals, plus shape theorems and a dynamic
`MRes` layer, and its own docstring says "The Content MathML front end
maps `matrix`/`vector`/`apply` trees onto the operations below". It
was missed because the search for existing work covered
`L4Factoidal/MathML/` and not `L4Factoidal/Math/`.

`Math.Matrix` imports `MathML.Core`, so `MathML.Core` cannot import
it. The duplication is a consequence of putting the linear-algebra
evaluation inside `Core.eval`. The repair is to move the `.mat` /
`.vec` evaluation OUT of `Core.eval` into a MathML front end above
`Math.Matrix` — the module `Math.Matrix` already describes — and
delete `MathML/Matrix.lean`. The 25 cases and their expected values do
not change; only which module computes them does.

Until that repair lands, the shipping behaviour is correct and the 81
cases pass, but there are two implementations of exact-rational linear
algebra in the tree and only one of them carries the shape theorems.

### A method note that cost time

Extending `MathML.Expr` with `.mat` and `.vec` broke exhaustiveness in
three `Math` modules. Rebuilding the module that DECLARES a shared
inductive does not verify the change; only a full `lake build` does.
Three per-module builds were green while the tree was broken.

## The 9 remaining XML conformance failures, diagnosed (2026-09-07, second session)

Written BEFORE any engine change. Each row is the test id, the
construct it tests, the sentence of XML 1.0 (Fifth Edition) it turns
on, and what the Lean parser does today. The "today" column is the
verbose runner line, which now carries the parse error text as well as
the verdict; without it the four `rejected` cases were
indistinguishable from each other.

| id | type | construct | XML 1.0 5e | Lean today |
| --- | --- | --- | --- | --- |
| `o-p28pass5` | valid | `[28a] DeclSep` — a PE reference at declaration-separator position in the external subset whose replacement text IS a whole declaration | section 4.4.8 Included as PE | rejected, `in the external subset: expected a content specification` |
| `valid-not-sa-023` | valid | a PE reference inside an `<!ATTLIST` declaration, whose replacement text is built from two further PE references inside an `[9] EntityValue` | section 4.4.5 Included in Literal; section 4.4.8 Included as PE | rejected, `in the external subset: expected an attribute type` |
| `not-wf-not-sa-009` | not-wf | WFC **PE Between Declarations**: the PE `%e;` expands to `<!--`, and the `-->` that closes it stands outside the entity | section 2.8 `[28a]` | ACCEPTED |
| `ibm-not-wf-p28a-ibm28an01.xml` | not-wf | same WFC: `%make_leopard_element;` expands to `<!ELEMENT leopard `, and `ANY>` stands outside it | section 2.8 `[28a]` | ACCEPTED |
| `ibm-not-wf-P32-ibm32n09.xml` | not-wf | WFC **Entity Declared** under `standalone="yes"`: `&animal_content;` is declared only in the external subset | section 2.9; section 4.1 | ACCEPTED |
| `ibm-not-wf-P68-ibm68n06.xml` | not-wf | same, the reference standing in an `[10] AttValue` | section 4.1 `[68]` | ACCEPTED |
| `rmt-e3e-13` | invalid | the 3e erratum: once an internal PE reference has been included, an undeclared general entity is a VALIDITY error, so a non-validating processor must ACCEPT | section 4.1 WFC Entity Declared, first clause | rejected, `reference to undeclared entity (WFC: Entity Declared)` |
| `rmt-e2e-18` | valid | the base URI for a relative system identifier is the entity that CONTAINS the declaration, not the document | section 4.2.2, section 4.3.2 | rejected, `reference to undeclared entity (WFC: Entity Declared)` |
| `ext02` | valid | external parsed entities in a different encoding from the base document | section 4.3.2 `[78]`, section 4.3.3 | rejected, `reference to undeclared entity (WFC: Entity Declared)` |

### What the four `rejected` lines actually mean

`parseXMLWith` DISCARDS the error `parseDoctype` returns and carries
on as though no DOCTYPE were there, so the element parser then rejects
the document at character 1 with `expected XML name start character`.
Every DOCTYPE defect therefore reached the runner under one wrong
message. The two `expected a content specification` /
`expected an attribute type` texts above were obtained by calling
`parseDoctype` directly; the runner is changed to report the parse
error text, and the parser to report the DOCTYPE error itself.

### Four parser defects, not one

The earlier note said the six PE cases were one piece of work. Reading
the fixtures splits them:

1. **`peScan` truncates a parameter entity SILENTLY.** The nested
   expansion is given the CALLER's remaining fuel, so a replacement
   text longer than what is left of the outer budget is cut off with no
   error. `p28pass5.dtd` is 12 characters (`%rootdecl;` and a line
   end), so the 18-character replacement `<!ELEMENT doc (a)>` arrives
   as `<!ELEMENT doc `. That is `o-p28pass5`, and it is a fuel bug, not
   a PE-boundary one.
2. **A PE reference inside an `[9] EntityValue` is not expanded.**
   Section 4.4.5 Included in Literal requires it to be expanded at
   declaration time WITHOUT the surrounding spaces section 4.4.8
   attaches. `normalizeEntityValue` copies it through instead, so
   `%e3;` still reads `%e1;%e2;` when `peScan` meets it and gets the
   section 4.4.8 spaces attached to each half: ` do  c ` where `doc`
   is meant. That is `valid-not-sa-023`.
3. **`peScan` splices EVERY parameter-entity reference textually,
   including one that stands at declaration-separator position.** That
   is precisely what WFC PE Between Declarations forbids, and it is
   what makes `not-wf-not-sa-009` and `ibm28an01` well-formed to this
   parser. `parseSubset` ALREADY handles a top-level `%name;`
   correctly — it parses the replacement text as a complete
   `[30] extSubsetDecl` — so the repair is to leave the top-level ones
   for it and splice only those inside a markup declaration, which is
   where section 4.4.8 admits them and `parseSubset` has no production
   for them.
4. **The entity table records no provenance and no externality**, which
   is what the `standalone="yes"` cases and the attribute-value WFC
   both need.

### `ext02` is not a profile decision after all

Its two entities are `../invalid/utf16b.xml` and
`../invalid/utf16l.xml` — UTF-16, in a sibling directory. The runner
resolves a system identifier by its LAST path segment among the files
of the document's own directory, so neither is found, the references
come back undeclared, and the case is scored a parser failure. With
relative system identifiers resolved against the base URI (which is
what `rmt-e2e-18` tests), both files are found, both fail to decode as
UTF-8, and the case lands in the `not UTF-8` out-of-profile bucket the
runner already has. That is the same treatment `valid/ext-sa/007`,
`008` and `014` already get, and it needs no profile decision written
into prose.

### WFC No External Entity References, and the two ids that pass for the wrong reason

`ibm41n10.ent` and `ibm41n11.ent` both begin `<?xml verison="1.0"?>` —
`version` is misspelt, so the text declaration carries no `encoding`
and `[77]` rejects it. The documents are therefore rejected for a
constraint they do not test. Section 4.4.4 makes a reference to an
external parsed entity FORBIDDEN in an attribute value, directly or
indirectly, and that constraint is not implemented. The entity table
has to carry the external flag before it can be.


## Second session, 2026-09-07: the 9 closed

`lake -d formal/lean4 exe l4xmlconf`, before and after each commit:

| commit | before | after |
| --- | --- | --- |
| report the DOCTYPE's own error; runner prints the parse error text | 1853 pass, 9 fail (out of 1862) | 1853 pass, 9 fail (out of 1862) |
| parameter-entity boundaries | 1853 pass, 9 fail (out of 1862) | 1857 pass, 5 fail (out of 1862) |
| entity externality and provenance | 1857 pass, 5 fail (out of 1862) | 1861 pass, 1 fail (out of 1862) |
| system identifiers resolved against the document's directory | 1861 pass, 1 fail (out of 1862) | **1861 pass, 0 fail (out of 1861)** |

The denominator falls by one at the last step and the reason must be
read with the score: `ext02` moves from SCORED to the `not UTF-8`
out-of-profile bucket, which now holds 65 rather than 64. Its two
entities are UTF-16 and in a sibling directory, and the runner could
not find them before, so the case was scored as a parser failure for a
missing declaration. Found, they do not decode, and the parser is
UTF-8 only and says so — the same treatment `valid/ext-sa/007`, `008`
and `014` already get. No parser change and no profile prose was
needed for it.

### Per-id verdicts

| id | now | why |
| --- | --- | --- |
| `o-p28pass5` | pass | `peScan`'s nested expansion has its own budget, so `<!ELEMENT doc (a)>` is no longer truncated to `<!ELEMENT doc ` |
| `valid-not-sa-023` | pass | a PE reference in an `[9] EntityValue` is included in literal (section 4.4.5), so `%e3;` reads `doc` and not ` do  c ` |
| `not-wf-not-sa-009` | pass | WFC PE Between Declarations: a PE reference at `[28a]` position is no longer spliced textually, and its replacement text `<!--` does not parse as a complete `[30] extSubsetDecl` |
| `ibm-not-wf-p28a-ibm28an01.xml` | pass | same; `<!ELEMENT leopard ` does not either |
| `ibm-not-wf-P32-ibm32n09.xml` | pass | `standalone="yes"` drops the general entities declared only in the external subset, so `&animal_content;` reports WFC Entity Declared |
| `ibm-not-wf-P68-ibm68n06.xml` | pass | same, the reference standing in an `[10] AttValue` |
| `rmt-e3e-13` | pass | an internal PE reference was recognised, so section 4.1 makes an undeclared general entity a validity error, and a non-validating processor must accept |
| `rmt-e2e-18` | pass, but NOT for the reason it tests | E18 tests that a relative system identifier resolves against the base URI of the entity that CONTAINS the declaration. This parser has no notion of a per-entity base URI and still does not do that. It accepts because the external parameter entity `subdir1/E18-pe` is not read, which is the same section 4.1 clause as `rmt-e3e-13`. |
| `ext02` | out of profile | see above |

### What is implemented, and what is not

Implemented and witnessed by a test that can only pass if it works:

* WFC PE Between Declarations, section 2.8 `[28a]`.
* Section 4.4.5 Included in Literal and section 4.4.8 Included as PE,
  now distinguished.
* WFC **No External Entity References**, section 4.4.4. The two ids
  that name it, `ibm-not-wf-P41-ibm41n10.xml` and
  `ibm-not-wf-P41-ibm41n11.xml`, still reject for `[77]` — their
  entity files open `<?xml verison="1.0"?>` with `version` misspelt,
  so no `encoding` pseudo-attribute is present, and the declaration is
  refused before an attribute is reached. Nothing can change that
  ordering: the declaration is read first. Six `#guard` cases in
  `XML/Tests.lean` witness the constraint instead, over an entity file
  whose `[77] TextDecl` IS valid: direct, indirect and
  attribute-default references are refused, while the same reference
  in content and an internal entity in an attribute value are both
  admitted, so the refusals turn on `external` and not on the
  reference itself.
* Section 2.9 and section 4.1 WFC Entity Declared under
  `standalone="yes"`.
* Section 4.1 WFC Entity Declared, first clause — the 3e erratum.

NOT implemented, and no test in this suite now distinguishes it:

* **Base URI for a relative system identifier** (section 4.2.2,
  XML Base). The parser passes a system identifier to the resolver
  exactly as written; nothing tracks which entity a declaration came
  from. `rmt-e2e-18`, the one case that tests it, now passes for a
  different and correct reason, so this suite no longer measures it.
* **Transcoding.** The profile is UTF-8 only. 65 cases are out of
  profile for it.
