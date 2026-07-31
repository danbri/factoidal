# tests/did-local — our own DID documents, for local testing

Sibling to [`tests/did/`](../did/), which holds *spec* did:key resolution
vectors in a strict `.did`/`.nt` pair format. This directory is for DID
documents we write ourselves while developing, in whatever shape the work
needs.

## Fixtures

| File | What it is |
|---|---|
| `fdid1.json` | A `did:example:` document with two verification methods (Ed25519VerificationKey2020, JsonWebKey2020). Valid JSON. Does not yet yield triples — see below. |

## History: it arrived with a syntax error, now fixed

As first committed, `fdid1.json` was **not valid JSON**: the
`verificationMethod` array was opened and never closed, so `"name"`,
`"created"` and `"updated"` sat as key/value pairs *inside the array*.
Python's `json` and Node's `JSON.parse` both rejected it at line 37,
char 1043. Fixed 2026-07-31 by inserting the missing `]` before
`"name"`; both parsers now accept it and it carries two verification
methods as intended.

## What still blocks it: every `@context` entry is a remote IRI

`https://www.w3.org/ns/did/v1` and the three `w3id.org` suites all have to
be dereferenced. Neither the `factoidal` CLI nor the npm bundle registers a
document loader (issue
[#275](https://github.com/danbri/factoidal/issues/275); the `assume val` is
stubbed in
`minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh`),
so both still refuse the document — now for this reason alone.

Any real DID document hits this, because DID documents essentially always
use remote contexts.

## Measured behaviour (2026-07-31)

| Input | `factoidal jsonld --in` | npm `parseToDatasetJson(…,'jsonld',…)` |
|---|---|---|
| `fdid1.json` (valid JSON, remote contexts) | rejected, rc=1 | rejected |
| valid JSON-LD, inline `@context` | parses | parses |
| valid JSON-LD, one remote `@context` | rejected | rejected |
| malformed JSON-LD, inline `@context` | rejected | rejected |

⚠️ **A syntax error and a missing loader produce the same error string**, on
both the native and the JS path: *"invalid JSON-LD (parse or unsupported feature — remote
contexts need a loader this CLI does not have)"*. That message is a
disjunction, so a green-field user cannot tell a syntax error from a
missing loader. Rejecting malformed JSON is correct; reporting it
indistinguishably from an unimplemented feature is not. The last row of the
table above is the control that proves the parser really does catch
malformed input: a malformed document with an **inline** context is
rejected, so the syntax check is real — only the reporting is ambiguous.

## To make local DID documents parseable

One of:

1. Vendor the four contexts and resolve them from disk — no network, no
   semantic compromise, and enough to unblock this directory; or
2. wire a real document loader for the CLI and the npm entry (#275).

⚠️ **Not an option: defaulting the loader to return `{}`.** Measured
2026-07-31 on this document with its contexts replaced by `{}` — the CLI
exits 0 and emits **0 triples**, silently. Every DID term (`id`,
`controller`, `verificationMethod`, `alsoKnownAs`, `publicKeyMultibase`) is
an alias *defined by* `did/v1`, not a JSON-LD keyword, and expansion drops
keys with no IRI mapping. That turns an honest failure into a green result
meaning "we did not do the work" (anti-pattern #3). It would also give the
wrong answer on 11 W3C tests that expect a remote-context load or validity
error: 4 `recursive context inclusion`, 4 `invalid remote context`, 2
`loading remote context failed`, 1 `multiple context link headers`. If the
behaviour is ever wanted for triage, it belongs behind an explicit
`--empty-remote-contexts` flag with a stderr warning, never as the default.

Until one of those lands, this directory can hold documents and record what
happens to them, but cannot turn them into triples.
