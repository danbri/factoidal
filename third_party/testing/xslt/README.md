# XSLT 1.0 test corpus (vendored subset of w3c/xslt30-test)

These tests exercise `formal/fstar/XSLT.Transform.fst` (slice 1) via
`bin/xslt-runner/xslt_runner.ml`.

## Provenance

- Source suite: **[w3c/xslt30-test](https://github.com/w3c/xslt30-test)**
- Commit: **`fddf1cf920087e791f13315d68dfbe874d97dc56`** (cloned 2026-07-07)
- License: the upstream suite's `LICENSE` (W3C test-suite terms).

The OASIS/W3C XSLT 1.0 test suite zip is not directly fetchable (the
endpoint returns HTML), so per the task's priority order the tests were
extracted from the git-clonable `xslt30-test` catalog, restricted to
the XSLT-1.0-expressible subset. These are **real W3C test files**
(stylesheet, source document, and the suite's own `assert-xml`
expected output), not synthetic "inspired by" tests (iron rule #6).

## Selection criteria

A test-set `<test-case>` was vendored only when **all** held:

1. `<dependencies><spec value="XSLT10+"/>` (or `XSLT10`) — the suite's
   own marker that the test is expressible/valid under XSLT 1.0.
2. `<result>` is a single `<assert-xml file="…"/>` — a serialized-tree
   comparison (error-code and `serialization-matches` results skipped).
3. The environment is a single principal `<source role="."/>` (inline
   `<content>` or a `file=`), with no stylesheet params and no schema.
4. The stylesheet's root is `xsl:stylesheet`/`xsl:transform` and every
   `xsl:*` element it uses is in the slice-1 instruction allowlist
   (template, output, apply-templates, value-of, for-each, if,
   choose/when/otherwise, element, attribute, text, copy, copy-of,
   variable, param, comment), with no blocklisted instruction
   (import/include, call-template, sort, number, key, function,
   apply-imports, next-match, sequence, for-each-group, analyze-string,
   iterate, merge, evaluate, message, result-document, with-param,
   decimal-format, namespace-alias, attribute-set, fallback) and no
   `as`/`mode`/`use-when` attribute.

**Note on the `version` attribute:** the upstream stylesheets were
authored for XSLT 3.0 processors and almost all declare
`version="2.0"` or `"3.0"` even when the test is 1.0-expressible. The
task's literal "declaring version=1.0" filter yields ~0 files against
this suite, so selection relies on the suite's own `spec value="XSLT10+"`
1.0-expressibility marker plus the instruction allowlist above. A test
whose stylesheet reaches for an XPath 2.0 construct (e.g. the `eq`/`lt`
value comparisons in `boolean-*`) will simply fail against our XPath
1.0 engine and is reported in the fail clusters — not silently dropped.

## Layout

- `manifest.json` — array of `{name, category, stylesheet, source,
  expected, description}`; paths are relative to this directory.
- `files/<category>__<name>.xsl` — the stylesheet (verbatim upstream).
- `files/<category>__<name>.src.xml` — the principal source document
  (verbatim upstream, or the environment's inline `<content>`).
- `files/<category>__<name>.expected.xml` — the upstream `assert-xml`
  expected output.

Originally 64 tests across 18 categories (apply-templates, avt, axes,
boolean, bug, construct-node, copy, expression, function-available, id,
lre, match, math, namespace, node, position, select, variable).

## `sort` category (added 2026-07-08)

24 `xsl:sort` tests vendored from **`tests/insn/sort`** of the same
upstream commit (`fddf1cf920087e791f13315d68dfbe874d97dc56`), selected
as the `<dependencies><spec value="XSLT10+"/>` (1.0-expressible)
test-cases with a single principal source, an `assert-xml` result, and
no `initial-template` entry point. They exercise the newly added
`xsl:sort` engine support (data-type number|text, order
ascending|descending, stable ordering, NaN-first ascending numeric,
multi-key tie-breakers).

**One normalization** was applied to these vendored files, documented
here for transparency: the upstream `tests/insn/sort` stylesheets carry
a `<?spec …?>` processing-instruction in the document **prolog** (before
the root element). `Parser.XML` deliberately does not consume prolog
PIs — doing so would regress the xmlconf 1442/0 not-wf clusters
(colon-in-PITarget, C0 control chars) — so these test-harness metadata
PIs, which any conformant parser discards and which carry no transform
semantics, are stripped from the prolog of the vendored `.xsl`/`.src`
files. The transform logic itself is verbatim upstream. Of the 24, the
ones that still fail do so on features deliberately out of scope
(`case-order`/`lang` collations, `iso-8859-1` source encoding, dynamic
sort keys chosen through a stylesheet param); they are kept as
documented fails, not dropped.

## Scoring

`assert-xml` is a canonical-XML comparison. The runner normalizes both
sides by stripping the leading XML declaration and comparing (a) exactly
and (b) after collapsing insignificant whitespace, reporting both counts
separately. Whitespace collapse is applied identically to both sides, so
it never turns a real structural difference into a pass; residual
whitespace/serialization-only mismatches land in `pass-loose`.
