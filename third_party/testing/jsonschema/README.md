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

## Excluded from slice-1

Not vendored (regex / cross-document machinery outside the slice-1 scope):

- `pattern.json`, `patternProperties.json` — need a regex engine; no verified
  regex facility is exposed inside the F* boundary (iron rule #11).
- `format.json` — `format` is an annotation in draft-07; the suite tests it as
  an optional assertion, which again needs regex/format primitives.
- `refRemote.json` — remote `$ref` across documents; slice-1 resolves only
  local JSON pointers (`#`, `#/...`) within the same document.

Within the vendored files, individual tests whose schema uses an unsupported
assertion keyword (`pattern`/`patternProperties`/`format`) or an unresolvable
`$ref` (remote, or a `#anchor` id-ref) are reported by the runner as **skips**,
never as a wrong verdict: the validator returns a three-valued result
(`VPass`/`VFail`/`VUnsupported`) and `VUnsupported` maps to skip.
