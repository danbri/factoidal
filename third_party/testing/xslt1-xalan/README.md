# XSLT 1.0 conformance corpus — Apache Xalan (`xalan-test`)

The **hole-targeted** XSLT 1.0 conformance corpus recommended by
[`docs/designissues/2026-07-17-xpath-xslt-coverage-matrix.md`](../../../docs/designissues/2026-07-17-xpath-xslt-coverage-matrix.md).
Unlike the existing `third_party/testing/xslt/` corpus (a slice-1-filtered
subset of `w3c/xslt30-test` that structurally excludes every unimplemented
feature — a regression pin, not a conformance measurement), this corpus is
the full OASIS/W3C XSLT 1.0 conformance suite as mirrored by Apache Xalan.
It is chosen to **surface** the coverage-matrix holes as measured red, not
hide them (iron rule #6 — real W3C-derived files, fails reported not
dropped).

- **Upstream / license / candidate research:** see
  [`PROVENANCE.md`](./PROVENANCE.md) (Apache-2.0; libxslt/MIT, lxml,
  TransforMiiX/MPL and the OASIS ZIP all considered — verdicts there).
- **Test count, format, initial score, per-feature clustering:** see
  [`INFO.txt`](./INFO.txt).

## Layout

- `xalan-test-src/` — pinned git submodule (`apache/xalan-test`). Contains
  the vendored `tests/conf/*.xsl` + `*.xml` and `tests/conf-gold/*.out`.
  **Never edited** (vendoring policy).
- `manifest.json` — generated here (upstream ships no such manifest). An
  array of `{name, category, stylesheet, source, expected, description}`,
  paths relative to this directory. Same schema as `../xslt/manifest.json`.

## Running

```
tools/ensure-test-env.sh                                    # restore submodule in a fresh env
bin/linux-x86_64/xslt_runner --base third_party/testing/xslt1-xalan
bin/linux-x86_64/xslt_runner --base third_party/testing/xslt1-xalan -v   # print every FAIL
```

The runner is the same committed `bin/xslt-runner/xslt_runner.ml`; `--base`
selects an alternate corpus directory (its own `manifest.json`, same
output-comparison oracle). All transform semantics come from the
F\*-extracted `XSLT.Transform.fst`; the runner is I/O + comparison plumbing
only (iron rule #11).

## Regenerating `manifest.json`

If the submodule pin is bumped, regenerate the manifest (walks
`conf/<cat>/<name>.{xsl,xml}` + `conf-gold/<cat>/<name>.out` triples):

```
python3 tools/gen-xslt1-xalan-manifest.py
```
