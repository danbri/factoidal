# third_party/eleventy/

Vendored copy of Eleventy (`@11ty/eleventy@3.1.2`) and its full
dependency tree (134 packages, ~9.6 MB), so the site
(`docs/`, built with Eleventy — see `skills/site-and-dashboard/SKILL.md`)
builds without hitting `registry.npmjs.org`.

## What's vendored, and why this form

The vendored artifact is `npm-cache/` — a populated npm cache
directory (the same content-addressable tarball store `npm install`
normally writes under `~/.npm`), **not** a checked-in `node_modules/`
tree and **not** a folder of individually-`npm pack`ed `.tgz` files.

This is npm's own supported offline-install recipe:
`npm ci --offline --cache=<dir>` resolves every package named in
`package-lock.json` from a cache directory, verifies each against the
lockfile's `integrity` (sha512) hash, and never touches the network.
Given a choice between:

1. `npm pack`ing each of 134 packages individually and writing a
   from-scratch installer that reassembles `node_modules/` from loose
   tarballs (reimplementing what npm's installer already does), or
2. checking in a full built `node_modules/` snapshot (larger, and
   drifts from `package-lock.json` silently if anyone edits it by
   hand), or
3. populating npm's own cache format and using the installer npm
   ships for exactly this (`npm ci --offline`),

(3) was chosen: it's the smallest vendored artifact (9.6 MB vs 22 MB
for a `node_modules/` snapshot), it's literally the tarballs `npm
pack` would produce (same registry-hosted `.tgz` bytes,
content-addressed by npm's own hashing), and the "installer" is a
single well-tested npm flag rather than new code.

`package.json` / `package-lock.json` are **not** duplicated into this
directory — `docs/package.json` and `docs/package-lock.json` remain
the single source of truth for versions; this cache was built
directly from them (see "Re-vendoring" below) and must stay in sync
with them.

## Versions

- `@11ty/eleventy` 3.1.2 (top-level, pinned `^3.0.0` in
  `docs/package.json`, resolved via `docs/package-lock.json`)
- 133 further packages in the resolved dependency tree (dev
  dependencies of Eleventy itself: `chokidar`, `micromatch`,
  `markdown-it`, `liquidjs`, `luxon`, `@11ty/eleventy-dev-server`,
  etc.) — full list with per-package version and license in
  `manifest.json`.

Every package's exact version + sha512 integrity hash is already
recorded in `docs/package-lock.json` (npm's own lockfile format);
`manifest.json` here additionally records each package's declared
license for compliance review in one place.

## Licenses

`manifest.json` has 134 entries (matching npm's own "added 134
packages" count) because a handful of packages are installed twice at
different versions to satisfy conflicting ranges (nested
`node_modules/` under `markdown-it`, `nunjucks`, `anymatch`,
`gray-matter`, `htmlparser2`, `finalhandler`, `readdirp`,
`dom-serializer` — each holds one extra copy of a dependency). That's
124 distinct package **names**.

`licenses/<name-with-path>/LICENSE` holds the upstream license text
for 117 of the 124 distinct names (the remaining 7 — small `@11ty/*`
internal utilities and MIT-licensed one-file helpers such as
`array-differ`, `errno`, `esm-import-transformer` — ship no separate
LICENSE file upstream; their license identifier is still recorded in
`manifest.json` from `package.json`'s `license` field).

License distribution across all 134 resolved package instances:

| License | Count |
|---|---|
| MIT | 111 |
| ISC | 9 |
| BSD-2-Clause | 9 |
| BSD-3-Clause | 3 |
| Python-2.0 | 1 |
| BlueOak-1.0.0 | 1 |

No copyleft licenses anywhere in the tree.

## Installing offline

```sh
third_party/eleventy/install.sh docs   # or omit the arg; defaults to docs/
```

This runs `npm ci --offline --cache=third_party/eleventy/npm-cache`
inside the target directory. Verify with `npx @11ty/eleventy
--version` afterwards (should print `3.1.2`).

The site build (`docs/.eleventy.js` + CI) uses this instead of a bare
`npm ci` — see `.github/workflows/deploy-pages.yml`'s "Install
Eleventy" step and `skills/site-and-dashboard/SKILL.md`'s local-build
line.

## Re-vendoring / upgrading

When `docs/package.json`'s Eleventy version constraint changes (and
`docs/package-lock.json` is regenerated for it), refresh this cache
from a machine with network access:

```sh
cd docs
rm -rf node_modules
npm ci --cache=../third_party/eleventy/npm-cache
```

Then regenerate `manifest.json` and `licenses/` by walking
`docs/node_modules/*/package.json` **recursively** (some packages
nest a second `node_modules/` for a conflicting version — see
"Licenses" above; a non-recursive walk under-counts by ~10) and
update the version/license tables above. `third_party/observable/build.sh`
has the same walk-and-copy pattern for a flat (non-nested) tree.
