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

## Reading of the document (2026-07-31, after the loader landed)

It now parses to **10 triples**. Five observations, in rough order of how
much they would matter if this were a real DID document.

**1. Three of the seven keys produce no triples at all.** `name`,
`created` and `updated` are not defined by `did/v1` and there is no
`@vocab`, so JSON-LD expansion drops them. This is *correct* JSON-LD —
and it means metadata the author clearly intended to state is invisible
to every consumer. If they are wanted, they need a context that defines
them (`dcterms:created`/`dcterms:modified` and `rdfs:label` are the
conventional choices).

**2. Relative verification-method IDs resolve against the wrong base
unless you say otherwise.** With no `--base`, `#ed25519-key-1` becomes
`file:///…/fdid1.json#ed25519-key-1`. DID Core says a relative ID in a
DID document resolves against the **DID subject**. Passing
`--base did:example:7d4f…` yields the correct
`did:example:7d4f…#ed25519-key-1`. Anything consuming a DID document must
set the base to the subject; the file path is never right.

**3. The Ed25519 key is not a well-formed multikey.** The multibase
string decodes to 34 bytes — the right length for a 2-byte multicodec
prefix plus a 32-byte key — but the prefix is `0416`, where
`ed25519-pub` is `ed01`. It is shaped like a real `z6Mk…` identifier and
is not one.

**4. The JWK coordinates are the wrong length.** P-256 `x` and `y` must
each be 32 bytes, i.e. 43 base64url characters. Here `x` is 39 and `y` is
40. Not decodable as a P-256 point.

**5. No verification relationships.** The document declares two
verification methods but no `authentication`, `assertionMethod`,
`keyAgreement`, `capabilityInvocation` or `capabilityDelegation`. Under
DID Core a verification method that no relationship references cannot be
used to authenticate, assert or delegate anything — the keys are present
but inert.

Points 3 and 4 are exactly what one expects of an illustrative example
and are not defects in the document's purpose. Points 1, 2 and 5 are the
ones that would bite a real deployment, and 2 is a property of *our*
processing that any DID consumer we build has to get right.

## Historical: what used to block it — every `@context` entry is a remote IRI

`https://www.w3.org/ns/did/v1` and the three `w3id.org` suites all have to
be dereferenced. Neither the `factoidal` CLI nor the npm bundle registers a
document loader (issue
[#275](https://github.com/danbri/factoidal/issues/275); the `assume val` is
stubbed in
`minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh`),
...which was true until the loader landed. `bin/factoidal-cli` now
resolves these four IRIs from `third_party/jsonld-context-cache/`
(see `skills/jsonld-context-cache/SKILL.md`), so the document parses
offline. Consumers that have not yet registered a loader — the npm
bundle among them — still refuse it.

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
