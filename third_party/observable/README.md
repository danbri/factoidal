# third_party/observable/

Vendored browser libraries for running Observable-style reactive
cells (and Observable Plot charts) on the documentation hub, served
same-origin from GitHub Pages — no CDN, no `npm install` at page-load
time. This is the same constraint that already governs
`npm/factoidal/browser.js` (see its header comment): fetching code
from `raw.githubusercontent.com` or `unpkg.com` at runtime is not
acceptable here, so every module the hub loads must be a plain file
under this repo's own Pages origin.

## What's vendored, and why bundled (not raw npm packages)

| File | Source package | Version | Why bundled |
|---|---|---|---|
| `dist/runtime.esm.js` | `@observablehq/runtime` | 6.0.0 | Ships an ESM `src/index.js` with only relative imports — already self-contained; re-emitted through esbuild for a stable single-file artifact. |
| `dist/inspector.esm.js` | `@observablehq/inspector` | 5.0.1 | Depends on `isoformat` (bare specifier) — bundled in. |
| `dist/stdlib.esm.js` | `@observablehq/stdlib` | 5.8.8 | Depends on `d3-array`, `d3-dsv`, `d3-require` (bare specifiers) — bundled in. **Caveat:** `d3-require`'s dynamic `require(...)` loader normally fetches modules from jsDelivr at runtime. The code is present (inert) in this bundle, but hub cells MUST NOT call it — that would reintroduce the CDN dependency this vendoring exists to avoid. Use the pure helpers (`Generators`, `Promises`, `now`, `width`, `FileAttachments`, ...) only. |
| `dist/plot.esm.js` | `@observablehq/plot` | 0.6.17 | Depends on `d3`, `isoformat`, `interval-tree-1d` (bare specifiers) — bundled in, including a full copy of d3. |
| `dist/d3.esm.js` | `d3` (meta-package) | 7.9.0 | Standalone bundle, for hub cells that want raw d3 (selections, scales, etc.) without pulling in all of Plot. **Note:** this is a second, independent copy of d3's code from the one inlined into `plot.esm.js` — two separate module realms, so `instanceof` checks spanning both won't unify. Acceptable for this first vendoring pass (see `build.sh`'s header comment for the import-map alternative if a future hub post needs both in one page). |

All five files are produced by `build.sh` with:

```
esbuild <entry> --bundle --format=esm --platform=browser --target=es2022 --legal-comments=eof
```

`build.sh` also asserts (`grep '^import'`) that no bare-specifier
import survives bundling — every `import` in the shipped files is
`./...`-relative or absolute-URL, so nothing needs an import map or
network fetch to resolve.

## Versions and integrity

| Bundle | sha256 |
|---|---|
| `dist/d3.esm.js` | `3b4a787e223e8e5352829cb4ad699c4480b5127ed6c36e08a6164abbdc902b8f` |
| `dist/inspector.esm.js` | `a037582ca45f38d859282f21106250dc07ad4ddd34c6aa257546241153a5c0d3` |
| `dist/plot.esm.js` | `fd7cdb3f20538d66e3a733d83e7569668c4b727590d5879c103d7de340f8137d` |
| `dist/runtime.esm.js` | `f8781e67bf7acec1a5865565206b609241aaecd84ab7cf5b37baedc34a6deb7a` |
| `dist/stdlib.esm.js` | `b665ef5c622a244789eeeda257b7b4c3bcebc760a77132d938505f8abde8f5a2` |

Recompute with `sha256sum third_party/observable/dist/*.esm.js` and
compare against this table before trusting a checkout.

`manifest.json` lists every npm package (46, including transitive d3
sub-packages) that fed into these five bundles, with its resolved
version and declared license.

## Licenses

`licenses/<package>/LICENSE` holds the upstream license text for
every package in `manifest.json` that ships one. All 46 packages are
permissively licensed:

- ISC — `@observablehq/runtime`, `@observablehq/inspector`,
  `@observablehq/stdlib`, `@observablehq/plot`, `d3` and most `d3-*`
  sub-packages, `d3-require`, `interval-tree-1d`'s transitive
  `binary-search-bounds`
- MIT — `interval-tree-1d`, `isoformat`, `internmap`
- BSD-3-Clause — `d3-ease`, `rw`

No copyleft licenses anywhere in the tree.

## Re-vendoring / upgrading

Run `third_party/observable/build.sh` (needs network access to
`registry.npmjs.org`). It re-downloads the pinned versions, re-bundles
with esbuild, and rewrites `dist/`, `licenses/`, and `manifest.json`.
Update the sha256 table above and the version pins in `build.sh`'s
header comment when you bump a version.

## How the hub loads these

The Eleventy hub layout (`docs/web/hub/`) passthrough-copies this
directory's `dist/` to `/factoidal/vendor/observable/` on Pages (see
`docs/.eleventy.js`) and imports the bundles same-origin:

```html
<script type="module">
  import { Runtime, Inspector } from '/factoidal/vendor/observable/runtime.esm.js';
  // ... Inspector is imported from inspector.esm.js separately, see below
</script>
```

(`Inspector` actually lives in `inspector.esm.js`, not `runtime.esm.js`
— split imports intentionally, matching upstream's package split.)
