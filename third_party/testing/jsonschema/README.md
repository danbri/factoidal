# JSON Schema Test Suite (vendored subset)

Draft-07 conformance fixtures for the F* validator in
`formal/fstar/JSONSchema.Validate.fst`, exercised by
`bin/jsonschema-runner/jsonschema_runner.ml`.

## Provenance

- Upstream: [json-schema-org/JSON-Schema-Test-Suite](https://github.com/json-schema-org/JSON-Schema-Test-Suite)
- Commit: `92acb61eb772a932c077d5ffa634ded719d2d738` (2026-06-30)
- License: MIT — see `LICENSE` (Copyright (c) 2012 Julian Berman)
- Draft targeted: **draft7**

Files are copied verbatim from `tests/draft7/*.json`. Each file is an array of
groups `{description, schema, tests: [{description, data, valid}]}`. The runner
reads them with the F*-extracted RFC 8259 parser (`Parser_JSON.parse_json`) and
compares `JSONSchema_Validate.validate schema data` against the expected
`valid`.

`manifest.json` lists every vendored file with its test count (770 total).

## Score

**770 pass, 0 fail, 0 skip (of 770)** — every vendored draft-07 test passes.

The 58 within-file skips that the runner used to report were closed
2026-07-17:

- **`pattern` / `patternProperties`** (and pattern-keyed
  `additionalProperties` / `propertyNames`) now run against the project's
  VERIFIED regex engine (`Regex.XSDPattern.parse_xsd_pattern` +
  `Regex.Exec.search` / `matches_norm`). JSON-Schema patterns are ECMA-262
  regexes matched UNANCHORED; a leading `^` / trailing `$` is reconstructed
  at the string layer as prefix / suffix / whole-string matching (the
  XSD-flavor parser treats `^`/`$` as whole-string no-ops). A pattern
  outside the XSD-parseable subset short-circuits the subschema to a skip
  (never a wrong verdict) — no vendored pattern triggers this.
- **`$ref`** now resolves the full draft-07 base-URI algorithm the fixtures
  exercise: local JSON pointers, `$id`-relative and absolute URI refs,
  `#anchor` plain-name fragments (`$id:"#foo"`), percent-encoded pointer
  tokens, and cross-document refs. The vendored draft-07 meta-schema
  (`remotes/draft-07-schema.json`) is supplied to the validator by the
  runner as an external document, so `{"$ref":
  "http://json-schema.org/draft-07/schema#"}` (ref.json remote-ref group,
  definitions.json) resolves with no live HTTP.

## Standalone files still un-vendored

`pattern.json`, `patternProperties.json`, `format.json`, and `refRemote.json`
are not (yet) copied in as their own files — but this is now a vendoring gap,
not a capability gap: the `pattern` / `patternProperties` keywords and remote
`$ref` resolution are exercised by the copies embedded in
`additionalProperties.json`, `properties.json`, `propertyNames.json`,
`ref.json`, and `definitions.json`. `format` remains a skip source in the
validator (draft-07 treats it as an annotation; no vendored test asserts it).

The validator still returns a three-valued result
(`VPass`/`VFail`/`VUnsupported`) and `VUnsupported` maps to skip, so any future
construct outside the supported subset is reported as a skip, never a wrong
verdict.
