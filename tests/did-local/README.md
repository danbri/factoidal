# tests/did-local — our own DID documents, for local testing

Sibling to [`tests/did/`](../did/), which holds *spec* did:key resolution
vectors in a strict `.did`/`.nt` pair format. This directory is for DID
documents we write ourselves while developing, in whatever shape the work
needs.

## Fixtures

| File | What it is |
|---|---|
| `fdid1.json` | A `did:example:` document with two verification methods (Ed25519VerificationKey2020, JsonWebKey2020). **Carries two independent faults** — see below. |
| `fdid1-syntax-fixed.json` | `fdid1.json` with fault 1 repaired, so fault 2 can be observed on its own. |

## fdid1.json carries two faults, and they must not be confused

**Fault 1 — it is not valid JSON.** The `verificationMethod` array is opened
and never closed: after the second verification-method object, `"name"`,
`"created"` and `"updated"` appear as key/value pairs *inside the array*.
Python's `json` and Node's `JSON.parse` both reject at line 37, char 1043,
with the same diagnosis (`Expecting ',' delimiter` / `Expected ',' or ']'
after array element`). The missing `]` belongs immediately before `"name"`.

**Fault 2 — every `@context` entry is a remote IRI.** `https://www.w3.org/ns/did/v1`
and the three `w3id.org` suites all have to be dereferenced. Neither the
`factoidal` CLI nor the npm bundle registers a document loader
(issue [#275](https://github.com/danbri/factoidal/issues/275); the
`assume val` is stubbed in
`minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh`),
so both refuse the document.

`fdid1-syntax-fixed.json` is valid JSON and **still fails**, which is what
isolates fault 2. Any real DID document will hit fault 2, because DID
documents essentially always use remote contexts.

## Measured behaviour (2026-07-31)

| Input | `factoidal jsonld --in` | npm `parseToDatasetJson(…,'jsonld',…)` |
|---|---|---|
| `fdid1.json` | rejected, rc=1 | rejected |
| `fdid1-syntax-fixed.json` | rejected, rc=1 | rejected |
| valid JSON-LD, inline `@context` | parses | parses |
| valid JSON-LD, one remote `@context` | rejected | rejected |

⚠️ **The two faults produce the same error string**, on both the native and
the JS path: *"invalid JSON-LD (parse or unsupported feature — remote
contexts need a loader this CLI does not have)"*. That message is a
disjunction, so a green-field user cannot tell a syntax error from a
missing loader. Rejecting malformed JSON is correct; reporting it
indistinguishably from an unimplemented feature is not. The control that
proves the parser really does catch malformed input independently is a
malformed document with an **inline** context — that is rejected too, so
the syntax check is real, it is only the reporting that is ambiguous.

## To make local DID documents parseable

One of:

1. Wire a document loader for the CLI and the npm entry (#275), or
2. vendor the four contexts and resolve them from disk.

Until then this directory can hold documents and record what happens to
them, but cannot turn them into triples.
