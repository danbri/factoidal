# third_party/jsonld-context-cache — offline JSON-LD `@context` snapshots

A URL-keyed, content-addressed, versioned cache of remote JSON-LD
`@context` documents, so parsing does not need the network.

Nothing here is hand-written. Add and refresh with
[`tools/jsonld-context-cache.sh`](../../tools/jsonld-context-cache.sh);
`index.json` is generated.

```
tools/jsonld-context-cache.sh add URL...   # fetch + store (idempotent)
tools/jsonld-context-cache.sh verify       # re-hash every snapshot, no network
tools/jsonld-context-cache.sh list         # print the index
```

## Layout

```
third_party/jsonld-context-cache/
  index.json                                     generated
  <domain>/<sha256(url)>.v<N>.jsonld
```

* **`<domain>`** — the host of the **requested** URL.
* **`<sha256(url)>`** — sha256 of the **requested** URL, full 64-hex.
* **`.v<N>`** — snapshot generation, from 1.

Example:

```
www.w3.org/a6e5bae7721672996bc597d40685cb6405734cde907c291024956a4c72c0e2f2.v1.jsonld
  = https://www.w3.org/ns/did/v1
```

### The key is the requested URL, never the redirect target

`https://w3id.org/security/multikey/v1` serves a redirect to
`https://www.w3.org/2025/credentials/vcdi/multikey/context/v1.jsonld`. A
document citing the `w3id.org` IRI must resolve **under that IRI** — a
cache keyed by the redirect target would miss every such document. The
final URL is recorded in `index.json` as provenance, and is not part of
the key.

Redirect targets also move over time and differ per URL, which is the
second reason not to key on them: the three `w3id.org` URLs cached today
resolve to **three different publishers** (see the licence section).

### A new `v<N>` means upstream changed

`add` mints a new version only when the fetched bytes differ from the
newest stored snapshot; otherwise it prints `unchanged` and writes
nothing. So re-running is cheap, and when a published context is revised
the older bytes stay on disk. That matters because a signed document is
signed against the context that was live when it was issued — see
`credentials-v2-20240720-8d0ee107.jsonld` in
[`../contexts/PROVENANCE.md`](../contexts/PROVENANCE.md) for a case where
exactly that came up.

### Every entry is self-authenticating

`verify` re-hashes each file and re-derives each URL hash from the URL
string, with no network access, so a corrupted or hand-edited snapshot is
caught. `store` also refuses to record a body that is not parseable JSON,
since an unparseable context poisons every consumer that resolves it.

## Relationship to `third_party/contexts/`

Two stores, deliberately, and they are not duplicates of each other:

| | `third_party/contexts/` | `third_party/jsonld-context-cache/` (here) |
|---|---|---|
| Naming | human-readable (`credentials-v2.jsonld`) | URL-keyed sha256 |
| Scope | the specific contexts the **VC/VCDM** checkers need | any context any document cites |
| Consumers | `VC.Context.fst`, `build-ocaml.sh`, four CI suite path-filters | general JSON-LD resolution |
| Provenance | prose, `PROVENANCE.md` | generated, `index.json` |

`third_party/contexts/` is load-bearing for verified code — `VC.Context.fst`
reads its bytes to build the protected-term map — and its filenames appear
in F\* comments and CI path filters. It is left exactly as it is.

⚠️ **One resource is currently in both.**
`https://w3id.org/security/multikey/v1` is `security-multikey-v1.jsonld`
there and `w3id.org/05a185db….v1.jsonld` here. Verified 2026-07-31: the
two files are **byte-identical**, sha256
`ba2c182de2d92f7e47184bcca8fcf0beaee6d3986c527bf664c195bbc7c58597`, so the
2026-07-10 vendoring and today's fetch agree and upstream has not moved.
If they ever diverge, the VC store is authoritative for VC code paths —
that is what its consumers are pinned to. Consolidating the two is
possible but would touch `VC.Context.fst`, `build-ocaml.sh` and four suite
YAMLs, so it is a separate piece of work, not a side effect of adding a
cache.

## Licence

Each cached document keeps the licence of its publisher; caching does not
change it. The snapshots are byte-identical, unmodified copies, stored
solely so offline parsing can resolve a context without a network fetch.

⚠️ **`w3id.org` is only a redirector, and its URLs do not all resolve to
the same publisher.** The licence follows the document that was actually
served, so it must be read off `final_url` in `index.json`, never assumed
from the requested URL. For the four snapshots cached today:

| Requested URL | Served by | Licence |
|---|---|---|
| `https://www.w3.org/ns/did/v1` | `www.w3.org` | W3C Document Licence / W3C Software and Document Notice and Licence |
| `https://w3id.org/security/multikey/v1` | `www.w3.org` | as above |
| `https://w3id.org/security/suites/jws-2020/v1` | `w3c.github.io` (w3c/vc-jws-2020) | as above |
| `https://w3id.org/security/suites/ed25519-2020/v1` | `digitalbazaar.github.io` | **BSD 3-Clause, Copyright (c) 2021 Digital Bazaar, Inc.** — not a W3C document |

W3C terms: <https://www.w3.org/copyright/document-license-2023/> and
<https://www.w3.org/copyright/software-license-2023/>. The Digital Bazaar
licence is at
<https://github.com/digitalbazaar/ed25519-signature-2020-context/blob/master/LICENSE>.

When adding a URL to this cache, check its `final_url` and record the
publisher here. Do not extend a row above to a new URL by analogy.

No warranty; see the upstream licences.

## Current contents

Run `tools/jsonld-context-cache.sh list` for the live view. As of
2026-07-31 — the four contexts `tests/did-local/fdid1.json` cites:

| URL | Domain | v | Bytes |
|---|---|---|---|
| `https://www.w3.org/ns/did/v1` | www.w3.org | 1 | 1474 |
| `https://w3id.org/security/suites/jws-2020/v1` | w3id.org | 1 | 2473 |
| `https://w3id.org/security/suites/ed25519-2020/v1` | w3id.org | 1 | 2976 |
| `https://w3id.org/security/multikey/v1` | w3id.org | 1 | 1010 |

Caching them does **not** by itself make that document parse: no consumer
resolves this cache yet. Wiring a document loader that reads it is
issue [#275](https://github.com/danbri/factoidal/issues/275).
