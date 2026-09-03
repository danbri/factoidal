---
name: npm-release
description: Release the Factoidal npm packages — which artifacts each build script produces, which files each package ships, how the version and the WebAssembly digest are stamped into version.json, how trusted publishing through the OIDC workflow works and why a token or one-time password never will, the gates that must be green first, and the traps that have cost time. Use before publishing @factoidal/core, before bumping a package version, when a wasm rebuild has to reach the package, when npm publish fails on authentication, or when the four committed wasm copies disagree.
---

# Releasing the Factoidal npm packages

Two packages exist. Only one is current.

| Package | Directory | Status |
| --- | --- | --- |
| `@factoidal/core` | `npm/factoidal/` | current; carries both engines |
| `@factoidal/lean` | `npm/factoidal-lean/` | superseded by https://github.com/danbri/factoidal/issues/618; never published; a frozen manual-override copy |

`@factoidal/core` carries the F\* engine's JavaScript bundle AND the Lean
engine's WebAssembly module (under `l4-assets/`), so one `npm install`
gives a consumer both. Do not publish `@factoidal/lean` unless the owner
asks for the override channel by name; its workflow refuses to run
without a typed confirmation phrase.

## What builds what

### The Lean engine (WebAssembly)

```bash
bash formal/lean4/Wasm/build-wasm.sh          # about ten minutes
```

It compiles `L4Factoidal` to `l4factoidal.wasm`, writes Emscripten's glue
`l4factoidal.mjs` and the repository's own loader `l4factoidal.js`, then
installs **four byte-identical copies**:

| Copy | Directory | Who reads it |
| --- | --- | --- |
| 1 | `docs/web/hub/assets/l4/` | the GitHub Pages hub posts |
| 2 | `npm/factoidal/l4-assets/` | `npm install @factoidal/core` — the copy that ships |
| 3 | `npm/factoidal-lean/` | the superseded companion package |
| 4 | `docs/npm/lean/` | the Pages mirror of that companion |

Step 9 of the script compares all four against the freshly built
SHA-256 and exits 1 when one differs. Trust that check; do not copy
these files by hand. Copy 2 was missing from the script until
2026-08-26, and one rebuild left `l4-assets/` holding the previous wasm
while the other three carried the new one, with every suite green.

The loader carries the wasm's own digest: step 9 rewrites
`const WASM_VERSION = "<first 12 hex of the sha256>";` inside
`l4factoidal.js` before copying it anywhere, and the loader puts that
value in the `?v=` query of its wasm fetch. The Pages service worker
(`docs/sw.js`) caches by pathname, so without that stamp a fresh loader
can pair with a stale wasm for one page load after a deploy.

### The F\* engine (JavaScript bundle)

```bash
eval $(opam env --switch=fstar)               # iron rule 12, every shell
cd formal/fstar
./build-ocaml.sh js                           # build the js_of_ocaml bundles
./build-ocaml.sh npm                          # copy them into npm/factoidal/
```

`npm run build` inside `npm/factoidal/` is `build-ocaml.sh npm`. That
step copies only; it never re-extracts or recompiles, and it never calls
`fstar.exe`. If `factoidal.js` is missing it tells you to run the `js`
step first.

An incremental `js` build SKIPS the npm entry bundle. A landing that
adds a hub cell calling a new F\* feature is therefore not documentation
work: force the npm-entry rebuild, or the published bundle answers with
the old surface (anti-pattern 32).

## What each package ships

`files` in `npm/factoidal/package.json` is the list. Today it is the two
engines plus the command:

- F\* engine: `factoidal.js`, `factoidal.wasm.js`,
  `factoidal.wasm.assets/`, `factoidal-npm-entry.*`, `index.*`,
  `wasm.*`, `rdfjs.js`, `fn.*`, `select.*`, `browser*.js`, `lib/`
- Lean engine: `l4.js`, `l4-core.js`, `l4-assets/`
- Crypto: `hacl-init.js`, `hacl-wasm/`
- Store host and command: `store-host/`, `bin/`
- Metadata: `version.json`, `README.md`, `CHANGELOG.md`, `LICENSE`

`bin` maps the command `factoidal` to `./bin/factoidal.mjs`. A consumer
gets it on PATH from a global install and in `node_modules/.bin` from a
local one.

Check the list before every publish:

```bash
cd npm/factoidal && npm pack --dry-run
```

Anything absent from `files` is absent from the tarball, whatever the
working tree holds.

## How the version and the digests are stamped

Three `version.json` files, three writers. Do not merge them.

| File | Written by | Carries |
| --- | --- | --- |
| `npm/factoidal/version.json` | `build-ocaml.sh npm` | the F\* engine's package version, git SHA, build time, and a hand-authored `claims` block that the step preserves across rebuilds |
| `npm/factoidal/l4-assets/version.json` | `build-wasm.sh` step 9 | the Lean engine's provenance, refreshed in place so its `engine` and `note` members survive |
| `npm/factoidal-lean/version.json` | `build-wasm.sh` step 9 | the same provenance for the superseded companion |

The Lean provenance members are `version`, `gitSha`, `builtAt`,
`leanToolchain`, `emscripten`, `abiVersion`, `wasmSha256`, `wasmBytes`
and `claims`. `factoidal version` prints them, which is the quickest way
to see which engine an install actually holds.

The `claims` block in `npm/factoidal/version.json` is edited by hand and
cites `docs/theorem-registry.md` sections. Editing it is a deliberate act
with the registry open; the build only carries it forward.

Bumping the package version is a manual edit of `version` in
`npm/factoidal/package.json`, plus a `CHANGELOG.md` entry, plus a
rebuild so the stamped `version.json` files agree with it.

## How publishing works

`.github/workflows/npm-publish.yml`, trusted publishing through OIDC.
There are no npm tokens anywhere in this repository, and there is no way
to add one that would work.

**The owner's npmjs.com account is security-key-only. Publishing with a
token, or with a one-time password, always fails.** Do not suggest
`npm login`, `npm publish --otp`, an automation token or a CI secret;
each of those is a dead end for this account. The only path that
publishes is the workflow.

Trigger it in one of two ways:

- `gh workflow run npm-publish.yml --repo danbri/factoidal`
- push a tag matching `npm-v*`

What the workflow does, in order:

1. checks out with `submodules: recursive` — the package's own
   `prepublishOnly` runs `npm test`, and that suite reads vendored W3C
   fixtures from `third_party/testing/`. Without the submodules the
   suite dies on ENOENT and the publish aborts. That is how run 2 failed
   on 2026-08-27, 22 minutes after the drift check had passed.
2. installs opam, F\* and z3 4.13.3, with caches.
3. re-extracts the whole F\* corpus with
   `./build-ocaml.sh extract --force-full` and fails on any difference
   against the committed `.ml`. `--force-full` is what stops a manifest
   hit turning the check into a vacuous pass.
4. logs a provenance witness: F\* and z3 versions, the digest of the
   `.fst` input tree, the digest of the glue tree.
5. `npm publish` from `npm/factoidal`, with provenance generated
   automatically (Sigstore-signed, Rekor-logged; a consumer checks it
   with `npm audit signatures`).

The npmjs.com side was configured once by the owner: package Settings →
Trusted Publisher → GitHub Actions, organization `danbri`, repository
`factoidal`, workflow filename `npm-publish.yml`, environment blank,
allowed action `npm publish`. Those fields are case-sensitive and npm
validates them only at publish time, so a typo shows up as a failed
publish and nothing earlier.

Cost: five to ten minutes with warm caches; about two hours with a cold
`.checked` cache, because the tree re-verifies.

## The gates before a release

Run these from the repository root, with the numbers each one must
produce. A number that has moved is a finding to explain, not a number
to overwrite.

| Gate | Command | Expected, measured 2026-09-03 |
| --- | --- | --- |
| hub notebooks | `node --test tests/hub/*_test.mjs` | 414 pass, 0 fail, 1 skipped (out of 415) |
| package suite | `cd npm/factoidal && npm test` | 252 pass, 0 fail, 2 skipped (out of 254) |
| store host | `node tests/store-host/conformance.mjs` | 29 pass, 0 fail, 0 skipped (out of 29) under Node, and the same under Deno |
| tarball | `cd npm/factoidal && npm pack --dry-run` | the `files` list above, 59 files |
| wasm copies | the tail of `build-wasm.sh` | "all committed wasm copies agree" |
| Lean native | `bash formal/lean4/Wasm/native-smoke.sh` | see the script's own report |
| browser surface | `tests/web-demos/hub_browser_all.sh` | the node harness cannot see browser-only gaps; run this too |

The package suite runs again inside `npm publish` through
`prepublishOnly`, so a failure there aborts the publish after the
workflow has already spent its F\* re-extraction time.

Install the tarball somewhere else and run the command before
publishing. A `files` entry that names a directory which does not exist
produces a tarball that installs and then fails on first use:

```bash
cd npm/factoidal && npm pack --pack-destination /tmp
mkdir /tmp/probe && cd /tmp/probe && npm init -y
npm install /tmp/factoidal-core-<version>.tgz
./node_modules/.bin/factoidal --help
./node_modules/.bin/factoidal version
```

## Traps

1. **The four wasm copies drift when a file is copied by hand.** Let
   `build-wasm.sh` place them; its step 9 is the only thing that checks
   them. (Issue 618, 2026-08-26.)
2. **`npm pack` reports the `files` list, not the working tree.** A new
   directory is invisible to the tarball until it is added to `files`.
   Both `bin/` and `store-host/` needed an entry when they were added on
   2026-09-03; without them `npm pack --dry-run` listed 53 files and the
   `bin` mapping pointed at nothing.
3. **`bin` needs the executable bit and a shebang.** `bin/factoidal.mjs`
   starts with `#!/usr/bin/env node` and is committed with mode 755. npm
   sets the bit on install, but a source checkout that runs the file
   directly needs it too.
4. **Deno ignores the shebang.** Run the command under Deno as
   `deno run --allow-read --allow-write node_modules/@factoidal/core/bin/factoidal.mjs`.
   Grant only the permissions the subcommand needs; `inspect` and
   `version` need `--allow-read` alone.
5. **`.js` in `npm/factoidal/` is CommonJS.** The package sets no
   `"type"`, so ESM files carry the `.mjs` extension. `store-host/` and
   `bin/` are `.mjs` for that reason.
6. **Deno 2 removed the resource-id fsync calls.** `Deno.fsyncSync` no
   longer exists; the file-handle method `FsFile.syncSync()` is the one
   to call. Code written against Deno 1 fails at run time with
   "Deno.fsyncSync is not a function".
7. **A conformance run that finds no native binary reports a green
   skip.** `tests/store-host/conformance.mjs` prints the skipped count
   next to the passes for exactly that reason, and it raises rather than
   skips when `L4_BIN_DIR` names a directory with no `l4block-shard-pack`
   in it. Read the skipped column before quoting the score
   (anti-pattern 3).
8. **A git worktree has no `formal/lean4/.lake/build`.** Tools that need
   the committed native binaries must fall back to the main checkout
   (the conformance test reads the worktree's `.git` pointer file to
   find it) or take an `L4_BIN_DIR` override.
9. **The version in `package.json` and the versions in the three
   `version.json` files diverge silently.** Bump, then rebuild, then
   check `factoidal version` before tagging.

## Where the pieces are

- Lean wasm build and its mirrors: `formal/lean4/Wasm/build-wasm.sh`,
  and [`skills/lean4-wasm-export/SKILL.md`](../lean4-wasm-export/SKILL.md)
  for the toolchain and the export ABI.
- F\* bundle and package population: `formal/fstar/build-ocaml.sh`
  (`js`, `wasm`, `npm` steps), and
  [`skills/build-and-test/SKILL.md`](../build-and-test/SKILL.md).
- Publish workflows: `.github/workflows/npm-publish.yml` and
  `.github/workflows/npm-publish-lean.yml`.
- The persisted store the command drives:
  [`skills/shardborough-storage/SKILL.md`](../shardborough-storage/SKILL.md)
  and `docs/shardborough-storage-spec.md`.
- The milestone that adds the remaining subcommands:
  https://github.com/danbri/factoidal/issues/641, with the byte
  transport it depends on at
  https://github.com/danbri/factoidal/issues/640.
