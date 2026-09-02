---
title: "Installed, not vendored"
description: "Loads the actual @factoidal/core package published to npmjs.com — not this site's own copy — from a public CDN, and cross-checks it against the same-origin engine: what you install is what this repo built."
layout: hub.njk
series: docs-hub
series_order: 37
vocab: none
status: published
tests: tests/hub/post37_test.mjs
hubAllowRegistryCdn: true
---

Every other page in this hub loads `@factoidal/core` the same way the
rest of this site does: same-origin, from `docs/npm/factoidal/`, built
by this repo's own CI. That proves the *engine* works. It does not
prove that what a stranger gets from `npm install @factoidal/core`
is the same thing — a publish step, a stale `files` list, or a CDN
mirror serving the wrong layout could all break that link silently.

This page closes that gap. It loads `@factoidal/core@0.1.0` **from
the public npm registry**, via a CDN that serves npm packages
verbatim, and runs it side by side with the same-origin copy.

**This page needs network access.** Every other hub page works
completely offline (same-origin only, by CSP). This one's whole point
is the opposite: it fetches real code from `cdn.jsdelivr.net` /
`unpkg.com`, so this post's Content-Security-Policy allows exactly
those two hosts and nothing else external. No other post carries the
carve-out. If both CDNs are unreachable, every cell reports "registry
unreachable" instead of failing outright.

## Loading the published package

```observable-js
registry = {
  try {
    return await fn.loadRegistryPackage("0.1.0");
  } catch (err) {
    return { unavailable: `could not load @factoidal/core@0.1.0 from a CDN: ${err.message}` };
  }
}
```

## Two versions, side by side

The version this *page* is running (same-origin, built by this repo's
CI for this deploy) and the version the *registry* served can differ —
that is the point of this page, not a bug to fix. A reader comparing
them sees exactly what "installed" vs. "vendored" means in practice.

```observable-js
return {
  siteBundleVersion: Factoidal.version,
  registryPackageVersion: registry.unavailable ? null : registry.version,
  registryStatus: registry.unavailable ? registry.unavailable : "loaded from the npm registry CDN",
};
```

## A small dataset, parsed by the registry module

```observable-js
DATA_TTL = `
  @prefix : <http://example.org/> .
  :alice :name "Alice" ; :age 30 .
  :bob   :name "Bob"   ; :age 7 .
`
```

```observable-js
registryDataset = {
  if (registry.unavailable) return { unavailable: registry.unavailable };
  return await registry.parse(DATA_TTL);
}
```

## SELECT, through the registry module

```observable-js
if (registry.unavailable) return { unavailable: registry.unavailable };
const rows = await registry.query(registryDataset, `
  # Every person and their age, sorted by subject.
  PREFIX : <http://example.org/>
  SELECT ?s ?age WHERE { ?s :age ?age } ORDER BY ?s`);
return pretty(rows);
```

## ASK, through the registry module

```observable-js
if (registry.unavailable) return { unavailable: registry.unavailable };
return await registry.query(registryDataset, `
  # Is anyone in the dataset 18 or older?
  PREFIX : <http://example.org/>
  ASK { ?s :age ?age . FILTER(?age >= 18) }`);
```

## RDFC-1.0 canonicalize, through the registry module

```observable-js
if (registry.unavailable) return { unavailable: registry.unavailable };
const canon = await registry.canonicalize(DATA_TTL, { format: "turtle" });
return canon;
```

## An extension function, registered on the registry module

The same SPARQL 1.1 §17.6 seam from
[post 34](./34-extension-functions.md), this time registered against
the code fetched from the registry, not this site's own copy:

```observable-js
if (registry.unavailable) return { unavailable: registry.unavailable };
await registry.registerExtensionFunction(
  "http://example.org/fn#isAdult",
  ([age]) => Number(age.value) >= 18
);
const rows = await registry.query(registryDataset, `
  # Everyone the custom fn:isAdult extension function accepts.
  PREFIX : <http://example.org/>
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE { ?s :age ?age . FILTER(fn:isAdult(?age)) }`);
return pretty(rows);
```

## Cross-check: same-origin and registry agree

Same query, same data, two independently-loaded copies of the engine —
one same-origin, one fetched fresh from the registry. Their answers
should be identical.

```observable-js
if (registry.unavailable) return { unavailable: registry.unavailable };
const q = `
  # Every person and their age, sorted by subject -- run through both
  # engine copies so their answers can be compared.
  PREFIX : <http://example.org/>
  SELECT ?s ?age WHERE { ?s :age ?age } ORDER BY ?s`;
const siteDataset = await fn.parse(DATA_TTL);
const siteRows = await fn.query(siteDataset, q);
const registryRows = await registry.query(registryDataset, q);
const norm = (rows) => rows.map((r) => ({ s: r.get("s").value, age: r.get("age").value }));
const a = norm(siteRows);
const b = norm(registryRows);
return { agree: JSON.stringify(a) === JSON.stringify(b), siteRows: a, registryRows: b };
```

## What this actually checks — and what it does not

- **It proves the published tarball is runnable, not just present.**
  `npm publish` can succeed while shipping a broken `files` list (a
  bundle missing, a relative path that only resolves same-origin); this
  page's Node-side test
  ([`tests/hub/post37_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post37_test.mjs))
  `npm pack`s the real tarball from `registry.npmjs.org` into a scratch
  directory and imports *that*, so a broken publish fails this test,
  not just a user's build.
- **It proves provenance, not correctness.** The Node test asserts the
  installed package's `version.json` `gitSha` is an ancestor of (or
  equal to) this repository's current commit — i.e. what you can `npm
  install` today was actually built from this history, not from a
  fork or a tampered mirror. It says nothing new about whether the
  *engine* is correct; that is every other post's and every W3C
  suite's job.
- **The CDN carve-out is this page's alone.** This is the one page in
  the hub whose whole purpose requires third-party code execution; its
  CSP allows the two npm CDN hosts (per-post front matter flag), and
  every other page's policy is unchanged — see
  `docs/_includes/hub.njk`'s CSP comment for the exact carve-out.

## Related

[Post 34](./34-extension-functions.md) is the extension-function seam
this page reuses. [Post 16](./16-the-verified-in-fstar-story.md) is
the verification story this page's provenance check is downstream of.
