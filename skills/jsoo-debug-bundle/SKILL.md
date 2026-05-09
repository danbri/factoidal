---
name: jsoo-debug-bundle
description: Build a source-mapped, pretty-printed js_of_ocaml bundle and wire it into the public demo so a browser-only crash gives a real OCaml stack trace. Use when a query works under the native binary or under Node but crashes only in the browser (e.g. `BatUChar.Out_of_range`, "use-js-string=true" UTF-16 mismatches), when a minified `factoidal.js` stack trace shows opaque single-letter function names like `aw`/`bb`/`cd`, or when the user asks to "build a debug bundle / get sourcemaps for the JS demo / step through the browser bundle". Pairs with build-and-test (which covers the production js_of_ocaml step) and workflow-gotchas-debugging.
---

# Debug js_of_ocaml bundle for browser-V8 crash repros

Production `docs/fstar-extracted/factoidal.js` is built without `-g`,
without `--pretty`, and with inlining on. When the public demo throws
something like `BatUChar.Out_of_range` from inside the bundle, the
browser stack trace is a soup of `aw`, `bb`, `cd` with no line
numbers that map to F\* / OCaml source. That's not enough to find
the throw site, let alone the caller chain.

The fix is to ship a **parallel** debug bundle with source maps and
opt the demo into it via `?jsoo-debug=1`. Production stays
untouched; the debug bundle costs ~7× the size (~3.7 MB vs ~560 KB)
plus a ~4 MB `.map` file, paid only by users who add the query
param.

## TL;DR

```bash
# Prereq: js_of_ocaml + zarith_stubs_js installed in the active
# opam switch. If not:
eval $(opam env --switch=fstar)
opam install js_of_ocaml js_of_ocaml-compiler zarith_stubs_js -y

# Prereq: F* extraction present in formal/fstar/ocaml-output/
# (most fresh clones already have this committed). If not:
./formal/fstar/build-ocaml.sh extract

# Build the debug bundle:
eval $(opam env)
cd formal/fstar
./build-jsoo-debug.sh
```

Outputs:

- `docs/fstar-extracted/factoidal.debug.js` (`--pretty --no-inline`,
  ~3.7 MB, with `/*<<src/file.ml:line:col>>*/` comments inline)
- `docs/fstar-extracted/factoidal.debug.map` (~4.2 MB, separate
  source map referenced from the bundle's tail)

Reload the demo with `?jsoo-debug=1`. The `<factoidal-sparql>`
custom element lives at `docs/fstar-extracted/index.html`, **not**
at the Pages root (`docs/index.md` is just a landing page that
links into `/fstar-extracted/`). The correct URL is:

```
https://danbri.github.io/factoidal/fstar-extracted/?jsoo-debug=1
```

Other demo pages under the same dir (`demo-lifesci.html`,
`demo-notebook.html`, `demo-remote-endpoint.html`) accept the
same query param — append `?jsoo-debug=1` to whichever one
reproduces the bug.

Open Chrome devtools → Sources → toggle **"Pause on uncaught
exceptions"**. Trigger the offending query. The break point lands
on a line annotated with the originating OCaml file:line:col, and
the call stack resolves to OCaml-named frames (`look`, `chr$0`,
`string_of_list`, …) instead of single letters.

## Why each flag matters

`build-jsoo-debug.sh` differs from the production js step
(`build-ocaml.sh js`) in exactly four places:

| Flag | Step | Effect on browser repro |
|---|---|---|
| `-g` | `ocamlfind ocamlc` | Embeds OCaml debug info into `factoidal.byte`. Without this, `js_of_ocaml --debug-info` has nothing to emit. |
| `--pretty` | `js_of_ocaml` | Multi-line JS with one statement per line — devtools can highlight individual instructions. |
| `--debug-info` | `js_of_ocaml` | Inserts `/*<<src/file.ml:line:col>>*/` comments before generated statements. Survives even without an external `.map`. |
| `--no-inline` | `js_of_ocaml` | Preserves call boundaries. Without this, callers and callees collapse into one anonymous function and the stack trace is one frame deep. |
| `--source-map` | `js_of_ocaml` | Emits the external `.map` file referenced by `//# sourceMappingURL=` so devtools can show OCaml source directly. |

## Hooking the demo (already done)

`docs/fstar-extracted/factoidal-sparql-client.js` (the
`<factoidal-sparql>` custom element) reads the URL query string
inside its `jsUrl` getter:

```js
get jsUrl() {
  try {
    const dbg = new URLSearchParams(globalThis.location?.search || '').get('jsoo-debug');
    if (dbg === '1') return './factoidal.debug.js';
  } catch (_) { /* non-browser host */ }
  return this.getAttribute('js-url') || './factoidal.js';
}
```

The Wasm path (`?wasm`) is independent. Production `factoidal.js`
is loaded by default for everyone who doesn't add the query param.

## Module-list drift to watch

`build-jsoo-debug.sh` carries its own `FSTAR_MODULES` array. Keep
it in sync with the **native** module list in `build-ocaml.sh`
(around the `COMMON_MODULES=` block, ~lines 387–429). The jsoo
list inside `build-ocaml.sh` itself is a smaller, older subset
(missing `RDF_CottasStore_PresenceWriter`, planner modules,
`RDF_Store_Combine`, etc.) — that's a separate stale-bundle
problem, not the debug bundle's concern.

If the build fails with `Module 'X' is unavailable (required by
'Y')`, the missing module is in the native list but not in the
debug script's array. Add it in extraction-order (alphabetical
within the same prefix is usually fine; bottom-up topological if
modules cross-depend).

## What the debug bundle has actually unlocked

The bundle was first cut to chase **#240** (bind+strings query
crashes only in browser-V8 with `BatUChar.Out_of_range`, runs
cleanly under Node-V8 and the native binary). The production
bundle's stack trace was unusable; the debug bundle exposed
`BatUChar.chr$0` at `src/batUChar.ml:55:7` as the throw site, and
preserved the `BatUTF8.look` / `next` / `string_of_list` frames
that fed it. That gave us a fixable culprit instead of a hash.

When you find a similar bug in another runtime asymmetry —
e.g. wasm-of-ocaml diverging from js-of-ocaml, or a Latin-1 vs
UTF-8 mismatch elsewhere in `FStar_String` — reach for this
skill first.

## Cleanup / when not to use

- The debug bundle is committed (Pages serves it). Do **not**
  remove it casually; the `?jsoo-debug=1` path is part of the
  public-demo debug surface now. If a future hardening pass wants
  to drop it, pull the bundle + map + `jsUrl` debug branch
  together in one commit.
- For a Node-only crash, skip this skill entirely. Build the
  debug bytecode (`build-ocaml-debug.sh`) and step under
  `ocamldebug` — that's the right tool when the bug already
  reproduces outside the browser.
- For a wasm-only crash, `build-jsoo-debug.sh` won't help (it
  builds the JS bundle). Track wasm-side debug story separately.

## Iron-rule fit

This is consumer-tooling: it lives in `bin/`-equivalent territory
(the public demo) and does not modify the verified F\* library
boundary. No new `assume val`. No glue patches. Scaffolding-only,
per CLAUDE.md rule #11.
