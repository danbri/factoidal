---
name: jsonld-context-cache
description: Resolve remote JSON-LD @context documents offline from third_party/jsonld-context-cache/ — a URL-keyed, content-addressed, versioned snapshot store. Use when a JSON-LD, DID, or VC document fails to parse because its @context is a remote IRI; when adding or refreshing a cached context; when wiring a documentLoader (issue #275); when auditing the licence or provenance of a vendored context; or when deciding between this cache and third_party/contexts/. Also covers why an empty-context fallback is forbidden.
---

# JSON-LD `@context` cache

Remote `@context` IRIs cannot be dereferenced by our binaries — no
documentLoader is registered (issue
[#275](https://github.com/danbri/factoidal/issues/275)). This cache holds
the bytes on disk so resolution needs no network.

Store: `third_party/jsonld-context-cache/`
Tool: `tools/jsonld-context-cache.sh` → `tools/jsonld_context_cache.py`

## Commands

```bash
tools/jsonld-context-cache.sh add URL...     # fetch + store, idempotent
tools/jsonld-context-cache.sh resolve URL    # print body — READ PATH, no network
tools/jsonld-context-cache.sh resolve URL --path-only
tools/jsonld-context-cache.sh refresh        # re-fetch all known URLs
tools/jsonld-context-cache.sh verify         # re-hash everything, offline
tools/jsonld-context-cache.sh list
```

In-process, for a consumer that should not shell out:

```python
from jsonld_context_cache import resolve_body, normalize_url
body = resolve_body(cache_dir, "https://www.w3.org/ns/did/v1")   # str | None
```

`resolve_body` is deliberately the shape of
`JSONLD.Loader.jsonld_load_document : string -> option string`, so a
documentLoader realisation maps onto it directly.

## Layout

```
third_party/jsonld-context-cache/
  index.json                              generated — never hand-edit
  <domain>/<sha256(normalized-url)>/v<N>.jsonld
```

## The five rules, and why each exists

**1. The key is the requested URL, never the redirect target.** `w3id.org`
is a redirector. A document citing `https://w3id.org/security/multikey/v1`
must resolve *under that IRI*; keying on where the bytes came from would
miss every such document. `final_url` is recorded as provenance only.

**2. URLs are normalized, but only where it cannot change the answer.**
Scheme and host lowercased (RFC 3986 says they are case-insensitive),
default port dropped, fragment stripped (never sent to a server). **Path
and query are left exactly alone** — they are case-sensitive and
percent-encoding is meaningful, so normalising them could alias two
different resources onto one entry.

**3. A new `v<N>` appears only when the bytes change.** `add` on unchanged
upstream prints `unchanged` and writes nothing. When a published context
*is* revised, the old bytes stay. That matters because a signed document
was signed against whichever revision was live when it was issued — see
`credentials-v2-20240720-8d0ee107.jsonld` in
`third_party/contexts/PROVENANCE.md` for a case where exactly that came up.

**4. Everything fails closed.** `store` refuses a body that is not
parseable JSON — an unparseable cached context poisons every consumer.
`resolve_body` re-hashes the file against the index before returning it,
so a tampered snapshot yields `None` rather than silently feeding a wrong
context into expansion. `verify` re-derives every URL hash and content
hash offline, and flags orphan files (on disk, not in the index) because
an orphan means something wrote into the cache without going through the
tool.

**5. Validate before fetching, not after.** `curl` dereferences `file://`
(local file read) and `ftp://`. The scheme, host and credential checks run
*before* the network call, and curl is additionally pinned with
`--proto =https --proto-redir =https`. This ordering was a real bug
found in testing, not a hypothetical.

## Diagnostics distinguish absent / missing / corrupt

```
not cached: <url>                          → never added
indexed but MISSING on disk: <path>        → index and disk disagree
CORRUPT: <path> does not match its sha256  → tampered or truncated
```

Do not collapse these. Telling someone "not cached" when the file is
corrupt sends them to re-fetch a URL whose real problem is on disk — the
same message-conflation defect recorded against the JSON-LD loader in
`tests/did-local/README.md`.

## Which store? This one or `third_party/contexts/`?

| | `third_party/contexts/` | this cache |
|---|---|---|
| Naming | human-readable | URL-keyed sha256 |
| Scope | contexts the **VC/VCDM** checkers need | any context any document cites |
| Consumers | `VC.Context.fst`, `build-ocaml.sh`, four CI path filters | general JSON-LD resolution |
| Provenance | prose `PROVENANCE.md` | generated `index.json` |

`third_party/contexts/` is load-bearing for verified code and its
filenames appear in F\* comments and CI path filters — **do not move or
rename anything in it** as a side effect of cache work. If a resource is
in both, the VC store is authoritative for VC code paths.

## ⚠️ Licence is per-URL, read it off `final_url`

`w3id.org` URLs do **not** all resolve to W3C documents. Measured
2026-07-31, the three cached `w3id.org` URLs resolve to three different
publishers, and `security/suites/ed25519-2020/v1` is served from
`digitalbazaar.github.io` under **BSD 3-Clause, © 2021 Digital Bazaar** —
not a W3C document. When adding a URL, check its `final_url` and record
the publisher in the cache README. Never extend an existing licence row to
a new URL by analogy.

## 🔴 Never default a documentLoader to `{}`

Returning an empty context for unresolvable IRIs looks like a cheap fix.
Measured on `tests/did-local/fdid1.json` with its contexts replaced by
`{}`: the CLI **exits 0 and emits 0 triples**, silently. Every DID term
(`id`, `controller`, `verificationMethod`, `alsoKnownAs`) is an alias
*defined by* `did/v1`, not a JSON-LD keyword, and expansion drops keys
with no IRI mapping. That converts an honest failure into a green result
meaning "we did not do the work" (anti-pattern #3).

It would also give the wrong answer on 11 W3C tests that expect a
remote-context load or validity error: 4 `recursive context inclusion`,
4 `invalid remote context`, 2 `loading remote context failed`, 1
`multiple context link headers`.

If that behaviour is ever wanted for triage, it belongs behind an explicit
`--empty-remote-contexts` flag with a stderr warning, never as a default,
and excluded from suite runs.

## Adding a context — the checklist

1. `tools/jsonld-context-cache.sh add <URL>`
2. `tools/jsonld-context-cache.sh verify` — expect `N of N intact`
3. Check `final_url` in the output or `index.json`; record the publisher
   and licence in `third_party/jsonld-context-cache/README.md`
4. Commit the snapshot, `index.json`, and the README change together —
   a snapshot without its index entry is an orphan and `verify` fails
