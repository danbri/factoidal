# XPath 1.0 / XSLT 1.0 spec-derived coverage matrix

**Date:** 2026-07-17 · **Trigger:** owner escalation, 2026-07-17 —

> *"I can't show this work proudly to ANYONE if you hide massive holes
> like that. Why didn't it show in w3c tests?"*

The `namespace::` axis was unimplemented while summaries reported XSLT
"near-perfect". **Root cause:** coverage was measured against
*self-selected test corpora and self-authored unit tests*, not against
the specifications. The XSLT corpus is a subset of `w3c/xslt30-test`
filtered to *only the features slice-1 already implements* (see
§Corpus), and the XPath unit suite contains a test that **asserts the
hole is a passing feature** (`tests/unit/xpath_tests.ml:273` —
`check_bool "namespace axis is deferred: clean parse failure" true
(parse_fails "namespace::*")`). A corpus can never surface a hole it
was built to exclude; a unit test that pins the gap green *hides* it.

This document enumerates the **specifications** — every XPath 1.0 axis,
every §4 core function, every XSLT 1.0 element/attribute/function — and
marks each: implemented? (F\* `file:line`), exercised by any test?

---

## 🔴 Holes summary (read this first)

Emoji register: 🔴 unimplemented + user-visible · 🟡 unimplemented
corner · ⚠️ implemented-but-partial / untested-for-correctness · ✅
implemented + exercised.

**~25 spec features unimplemented; +5 partial/stubbed.** The corpus and
unit suites exercise essentially none of the holes.

| # | Feature | Spec | Sev | Why it matters |
|---|---|---|---|---|
| 1 | `namespace::` axis | XPath §2.2 (axis 13/13) | 🔴 | The escalated hole. `namespace::node()` selects nothing; parser rejects the axis outright. |
| 2 | `translate()` | XPath §4.2 core string fn | 🔴 | Common case-folding / char-map idiom. Returns `""` (falls through to unknown-fn default). |
| 3 | `lang()` | XPath §4.3 core boolean fn | 🔴 | `xml:lang` language-range test. Unimplemented → `""`. |
| 4 | `xsl:number` | XSLT §7.7 | 🔴 | List/section numbering. Emits nothing. |
| 5 | `xsl:key` + `key()` | XSLT §12.2 | 🔴 | Cross-reference lookups. Neither element nor fn exists. |
| 6 | `format-number()` + `xsl:decimal-format` | XSLT §12.3 | 🔴 | Numeric formatting. Returns `""`. |
| 7 | `xsl:import` / `xsl:include` / `xsl:apply-imports` | XSLT §2.6 | 🔴 | Stylesheet composition + import precedence. Top-level collector ignores them. |
| 8 | `xsl:processing-instruction` | XSLT §7.3 | 🔴 | PI output. Falls to `else -> []`. |
| 9 | `xsl:message` | XSLT §13 | 🟡 | Diagnostics / `terminate`. |
| 10 | `generate-id()` | XSLT §12.4 | 🔴 | Node-identity keys. Missing. |
| 11 | `system-property()` | XSLT §12.4 | 🔴 | `xsl:version`/`xsl:vendor` probes. Missing. |
| 12 | `unparsed-entity-uri()` | XSLT §12.4 | 🟡 | DTD unparsed-entity lookup. Missing. |
| 13 | `disable-output-escaping` (on `value-of`/`text`) | XSLT §16.4 | 🔴 | Raw markup injection. Ignored. |
| 14 | `use-attribute-sets` + `xsl:attribute-set` | XSLT §7.1.4 | 🟡 | Shared attribute bundles. Ignored. |
| 15 | `xsl:strip-space` / `xsl:preserve-space` | XSLT §3.4 | 🟡 | Source whitespace control. Ignored. |
| 16 | `xsl:namespace-alias` | XSLT §7.1.1 | 🟡 | Aliasing (e.g. generating XSLT). Ignored. |
| 17 | `xsl:fallback` + forwards-compatible processing (`version`) | XSLT §2.5, §15 | 🟡 | Graceful degradation of unknown instructions. Ignored. |
| 18 | `xsl:output` attributes beyond `method` | XSLT §16 | 🟡 | `indent`, `encoding`, `doctype-*`, `cdata-section-elements`, `omit-xml-declaration`. Only `method` read. |
| — | `element-available()` | XSLT §15 | ⚠️ | Hard-coded `false` for all names, incl. supported instructions. |
| — | `document()` | XSLT §12.1 | ⚠️ | Only the empty-string (`document("")` = stylesheet) form; any real URI → empty node-set. |
| — | `current()` | XSLT §12.4 | ⚠️ | Correct at expression top level; inside a predicate returns the step context, not the XSLT current node (self-disclosed divergence, `XPath.Eval.fst:1394`). |
| — | `function-available()` | XSLT §15 | ⚠️ | Knows XPath core + `document`/`current` only; reports `false` for `key`/`format-number`/`generate-id`/`system-property` (consistent with their absence, but not spec-complete). |

**Test-visibility of the holes:** 0 of the 30 rows above is exercised
by the 88-test XSLT corpus or the XPath unit suite. `namespace::` is
"tested" only by an assertion that it fails to parse.

---

## 1. XPath 1.0 axes (§2.2) — 12 of 13 implemented

Parser: `Parser.XPath.axis_of_name` (`Parser.XPath.fst:268-281`).
Evaluator: `XPath.Eval.apply_axis` (`XPath.Eval.fst:718-731`).

| Axis | Parsed? | Evaluated (file:line) | Test coverage | Status |
|---|---|---|---|---|
| `child` | ✅ | `child_axis` :438 | xpath-unit, XSLT corpus | ✅ |
| `descendant` | ✅ | `descendant_axis` :443 | xpath-unit `descendant::` | ✅ |
| `parent` | ✅ | `parent_axis` :422 | xpath-unit `parent::` | ✅ |
| `ancestor` | ✅ | `ancestor_axis` :430 | xpath-unit (4×) | ✅ |
| `following-sibling` | ✅ | :466 | xpath-unit (4×) | ✅ |
| `preceding-sibling` | ✅ | :471 | xpath-unit (2×) | ✅ |
| `following` | ✅ | `following_axis` :703 | xpath-unit (1×) | ✅ |
| `preceding` | ✅ | `preceding_axis` :711 | xpath-unit (1×) | ✅ |
| `attribute` | ✅ | `attribute_axis` :448 | xpath-unit, XSLT `avt`/`axes` | ✅ |
| `self` | ✅ | :720 (`apply_axis`) | xpath-unit (5×) | ✅ |
| `descendant-or-self` (`//`) | ✅ | :723 | xpath-unit, XSLT `match` | ✅ |
| `ancestor-or-self` | ✅ | :726 | xpath-unit | ✅ |
| **`namespace`** | **❌** `axis_of_name`→`None` :281 | **no `Ax_Namespace` constructor** | asserted-to-fail only (`xpath_tests.ml:273`) | **🔴** |

Root cause note (from `Parser.XPath.fst:281`): *"namespace: deferred
(Parser.XML has no namespace-node kind)"*. `Parser.XML`'s `xml_node`
models no namespace-node, so the axis has no node kind to yield. This
is a data-model gap, not a one-line parser addition. The evaluator
*does* carry full namespace-URI machinery (`resolve_ns_uri`,
`elem_ns_uri`, `namespace-uri()`) for name tests — but the *axis* that
materialises namespace nodes as selectable/countable items is absent.
node-1601 (`namespace::node()` → attribute list) is the one W3C test
that hits it; it is the sole XSLT-corpus fail.

## 2. XPath 1.0 core function library (§4) — 25 of 27 implemented

Dispatch: `XPath.Eval.eval_funcall` (`XPath.Eval.fst:1331-1486`).

**§4.1 Node-set (7/7):** `last` :1336, `position` :1335, `count`
:1337, `id` :1344, `local-name` :1370, `namespace-uri` :1381, `name`
:1370 — all ✅ (xpath-unit + XSLT `id`/`function-available` categories;
`id()` DTD-ID landed 2026-07-17).

**§4.2 String (9/10):** `string` :1403, `concat` :1407, `starts-with`
:1415, `contains` :1408, `substring-before` :1420, `substring-after`
:1427, `substring` :1438, `string-length` :1450, `normalize-space`
:1453 — ✅. **`translate` — 🔴 absent** (no branch; hits `else XV_Str
""` :1486). Not in `is_supported_xpath_function` :1091.

**§4.3 Boolean (4/5):** `boolean` :1460, `not` :1456, `true` :1458,
`false` :1459 — ✅. **`lang` — 🔴 absent.**

**§4.4 Number (5/5):** `number` :1462, `sum` :1466, `floor` :1470,
`ceiling` :1472, `round` :1474 — ✅ (xpath-unit `math`).

Grammar-production families (all parsed, `Parser.XPath.fst`): LocationPath
(abs/rel, `//` desugar), Step (axis::/abbrev/`@`/`.`/`..`), NodeTest
(name/`*`/`ns:*`/`text()`/`comment()`/`node()`/`processing-instruction()`),
Predicate, PrimaryExpr (`$var`/`(expr)`/literal/number/FunctionCall),
FilterExpr, all binary/unary operators, Union `|`. **PI-target node
test** `processing-instruction('t')` parses (`NT_PI (Some t)`) and
evaluates (:631), but XSLT.Transform drops PI alternatives from a union
select before eval (self-disclosed, `XSLT.Transform.fst:86`) — ⚠️.

## 3. XSLT 1.0 elements (§ per row) — 22 of ~35 implemented

Instruction dispatch: `XSLT.Transform.fst:1444-1545` (`ln = "…"`
chain, `else -> []`). Top-level collectors: templates
:1673, globals `collect_globals` :1716, output `method` :1693.

| Element | Impl (file:line) | Test | Status |
|---|---|---|---|
| `xsl:stylesheet`/`xsl:transform` | :1786 | corpus | ✅ |
| `xsl:template` (match/name/mode/priority) | :1673-1680 | corpus | ✅ |
| `xsl:apply-templates` (select/mode/sort) | :1466 | corpus | ✅ |
| `xsl:call-template` | :1483 | — (blocklisted in corpus selection) | ✅ (untested by corpus) |
| `xsl:with-param` | `bind_with_params` :1492 | — | ✅ (untested) |
| `xsl:param` / `xsl:variable` (local+global) | :1381, :1716 | corpus `variable` | ✅ |
| `xsl:value-of` | :1446 | corpus | ✅ |
| `xsl:for-each` (+sort) | :1456 | corpus `select` | ✅ |
| `xsl:sort` (data-type/order, stable) | :1209 | corpus `sort` (24) | ✅ |
| `xsl:if` | :1450 | corpus | ✅ |
| `xsl:choose`/`when`/`otherwise` | :1454, :1597-1602 | corpus | ✅ |
| `xsl:element` (name/namespace AVT) | :1509 | corpus `construct-node` | ✅ |
| `xsl:attribute` | :1537 | corpus `avt` | ✅ |
| `xsl:text` | :1448 | corpus | ✅ |
| `xsl:comment` | :1541 | corpus `node` | ✅ |
| `xsl:copy` | `instantiate_copy` :1507 | corpus `copy` | ✅ |
| `xsl:copy-of` (+`copy-namespaces`) | :1495 | corpus `copy` | ✅ |
| `xsl:output` | :1693 (only `method`) | corpus | ⚠️ partial |
| **`xsl:number`** | ❌ (`else->[]`) | — | 🔴 |
| **`xsl:key`** | ❌ | — | 🔴 |
| **`xsl:import`/`xsl:include`** | ❌ (not collected) | — | 🔴 |
| **`xsl:apply-imports`** | ❌ | — | 🔴 |
| **`xsl:processing-instruction`** | ❌ (`else->[]`) | — | 🔴 |
| **`xsl:message`** | ❌ | — | 🟡 |
| **`xsl:decimal-format`** | ❌ | — | 🟡 |
| **`xsl:namespace-alias`** | ❌ | — | 🟡 |
| **`xsl:attribute-set`** | ❌ | — | 🟡 |
| **`xsl:strip-space`/`xsl:preserve-space`** | ❌ | — | 🟡 |
| **`xsl:fallback`** | ❌ | — | 🟡 |

## 4. XSLT 1.0 attributes of significance

| Attribute | Impl (file:line) | Status |
|---|---|---|
| `match`, `name`, `select`, `test` | throughout | ✅ |
| `mode` (template + apply-templates) | :1467, :1679 | ✅ |
| `priority` | `tpl_prio` :1680 | ✅ |
| `namespace` (xsl:element) | :1520 | ✅ |
| `copy-namespaces` (2.0) | :1499 | ✅ |
| `data-type`/`order` (xsl:sort) | :1214 | ✅ |
| **`disable-output-escaping`** | ❌ (comment-only :81) | 🔴 |
| **`use-attribute-sets`** | ❌ | 🟡 |
| **`version` / forwards-compatible processing** | ❌ | 🟡 |
| **`xml:space` / whitespace stripping** | ❌ | 🟡 |
| **`case-order`/`lang` (xsl:sort collations)** | ❌ (disclosed :75) | 🟡 |

## 5. XSLT 1.0 defined functions (§12) — 2 of ~9 complete

| Function | Impl (file:line) | Status |
|---|---|---|
| `document()` | :1357 — empty-string form only | ⚠️ partial |
| `current()` | :1394 — top-level only | ⚠️ partial |
| `function-available()` | :1476 — XPath-core + `document`/`current` | ⚠️ partial |
| `element-available()` | :1480 — hard-coded `false` | ⚠️ stub |
| **`key()`** | ❌ | 🔴 |
| **`format-number()`** | ❌ | 🔴 |
| **`generate-id()`** | ❌ | 🔴 |
| **`system-property()`** | ❌ | 🔴 |
| **`unparsed-entity-uri()`** | ❌ | 🟡 |

---

## Corpus provenance audit

**Where the 88-test suite came from** (`third_party/testing/xslt/README.md`):
a vendored subset of **`w3c/xslt30-test`** @
`fddf1cf920087e791f13315d68dfbe874d97dc56` (cloned 2026-07-07),
W3C-test-suite licence. 64 tests across 18 categories +24 `xsl:sort`
tests (2026-07-08) = 88.

**The selection criteria are the root cause.** README §"Selection
criteria" #4 vendors a test *only if* every `xsl:*` element it uses is
in the slice-1 allowlist, with an explicit **blocklist**:
`import/include, call-template, sort, number, key, function,
apply-imports, next-match, …, message, …, decimal-format,
namespace-alias, attribute-set, fallback` and *no `mode` attribute*.
Any test that would exercise a §Holes row was filtered out at
vendoring time. The suite is structurally incapable of surfacing the
holes — it is a regression pin for what already works, not a
conformance measurement. (The `sort` category was later added when
`xsl:sort` landed, i.e. the corpus grows to match the engine, not the
spec. That is backwards for hole-detection.)

**The full available corpus.** Two established XSLT-1.0 conformance
collections exist beyond `xslt30-test`:

1. **OASIS XSLT/XPath conformance test suite** (the historical
   reference set, ~1900–2400 cases, contributed by Lotus/IBM,
   Microsoft, Oracle/Sun, and others). It is the suite `node-1601`
   itself originates from (the `<?spec xpath#axes?>` PI and the
   `node-NNNN`/`match-NNNN`/`copy-NNNN` naming are OASIS conventions —
   `xslt30-test` re-vendored many OASIS cases). Licensing: OASIS test
   materials carry the OASIS IPR / a per-contributor licence; the
   Xalan-hosted copy is Apache-2.0. This suite has dense coverage of
   exactly our holes: `axes` (namespace axis), `number`, `key`,
   `impincl` (import/include), `attribset`, `namespace-alias`, `output`
   attributes, `string` (`translate`), `boolean` (`lang`).
2. **Apache Xalan `tests/` conformance set** (Apache-2.0, git-clonable)
   — a cleaned, runnable mirror of the OASIS cases plus Xalan-specific
   additions. Most tractable to vendor offline (no HTML-only endpoints).

**Recommendation (concrete).** Import a **hole-targeted** slice —
selection driven by the §Holes matrix, *not* by the current allowlist —
from the Apache-2.0 Xalan mirror (avoids the OASIS IPR question):

- Phase A (~30 tests, ~0.5 day): the `axes` namespace-axis cases,
  `string` `translate()` cases, `boolean` `lang()` cases. These pin the
  three 🔴 XPath holes and would each fail today — turning silent holes
  into visible red, which is the point.
- Phase B (~40 tests, ~1 day): `number`, `key`, `impincl`,
  `attribset`, `namespace-alias`, `output`-attribute cases — the 🔴/🟡
  XSLT-element holes.
- Selection rule change: vendor by **spec feature targeted**, keep
  failing tests as documented reds (iron rule #6 — real W3C files,
  fails reported not dropped). Est. total ~1.5 engineer-days to vendor
  + wire; the engine work to make them pass is separate and larger.

Until then, the honest headline is **"XSLT: 87 pass, 1 fail on a
slice-1-scoped subset of xslt30-test; ~25 spec features unimplemented,
untested by that subset"** — never "near-perfect".

---

## Dispositions-vocabulary rule (added to the ledger)

**New rule** (also added to
`docs/claude-rules/w3c-completeness-ledger.md` §Dispositions):

> **disputed-fixture** and **by-design** may only be applied when the
> underlying capability EXISTS. A missing feature is always
> **planned-family**/gap, stated as such. Labelling a hole
> "implementation-defined" or "disputed fixture" implies the processor
> made a *correct choice among valid behaviours* — which is false when
> the processor produces nothing because the feature was never built.

### Re-audit against the new rule

| Row | Current label | Verdict |
|---|---|---|
| **XSLT `node-1601`** (ledger line 88) | *"dispositioned (implementation-defined namespace-node order / unmodeled `namespace::` axis)"* | **🔴 MISLABEL.** "implementation-defined namespace-node order" implies namespace nodes *are* produced, just ordered differently. Reality: `namespace::` is unmodeled → **zero** nodes, output `<NSlist/>`. Per the new rule this is **planned-family**(#302, branch `xslt-namespace-nodes`)/gap. The XSLT *detail* section (line 600) already correctly calls the family "🟡 in flight / planned" — the **summary row contradicts its own detail**. Fix the summary row's wording. |
| XSLT score row 88 vs detail 593 | Row: "87 pass, 1 fail". Detail header: "79 pass, 9 fail" | ⚠️ Internal inconsistency (row updated 2026-07-17, detail section stale at 79/9). Not a disposition mislabel; flagged for the score-sync pass (out of scope for this docs-only commit — no score change). |
| GRDDL "6 fail-known-gap-xslt-feature", "30 fail-graph-mismatch" | planned-family(#301) | ✅ Correct — missing XSLT-fidelity features labelled as gap, not by-design. |
| rml_io 7+4+1+1 skips | dependency-blocked(named component) | ✅ Correct — each names an absent engine (XPath-in-RML, decompression, RDBMS, SPARQL iterator). Missing capability, honestly labelled. |
| rml_io `RMLSTC0009a` | planned-family(no issue) | ✅ Rule-compliant (gap, flagged as needing triage; capability question is error-detection, which the runner *has* in shape). |
| eecc 47 by-design(non-VCDM serializations) | by-design | ⚠️ Defensible but soft: SD-JWT/mdoc/JWT-VC are *different formats*, out of the VCDM-JSON-LD suite target — closer to "out-of-suite data" than "feature we lack". A no-parser-for-format case borders on gap; recommend re-phrasing to **by-design(out-of-suite serialization; not a VCDM-JSON-LD credential)** to make the "not our target" claim explicit rather than implying we *chose* not to verify a credential we could. |
| eecc 4 crypto skips | dependency-blocked(live did:web + no key material) | ✅ Correct. |
| xml_conformance 386+332+416+37 skips | by-design(Stage-A scope limits) | ✅ Defensible — a **non-validating XML processor** is a conformance class the XML 1.0 spec explicitly defines (§5.1), so declining DTD-*validation* tests is a correct-by-design behaviour, not a hidden hole. The runner's "parsed-but-not-validated" wording is transparent about it. Rule-compliant *because* the label does not claim the missing validation was implemented. (Watch item: if a summary ever rounds this to "XML: green", that would become a mislabel — the 1171 skips must stay visible. Cross-ref `docs/designissues/2026-07-17-xml-conformance-skip-census.md`.) |
| OWL profile EL/QL | 🧭 untriaged | ✅ Honestly marked untriaged, not falsely dispositioned. |
| OWL `dl-909`, `FS2RDF-literals-ar`, `I5.5-005` | disputed-fixture | ✅ Genuine fixture disputes (the *checker capability exists*; the vendored graph/label is contested). Rule-compliant — these are the legitimate use of `disputed-fixture`. |

**Net:** one clear mislabel to correct (node-1601 summary wording),
one score-consistency flag (XSLT row vs detail), one soft re-phrasing
suggestion (eecc). No other gap-class mislabelings found — the other
suites correctly reserve `by-design`/`disputed-fixture` for
scope-classes and genuine fixture disputes where the capability exists.
