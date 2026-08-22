---
name: lean4-wasm-export
description: Compile the Lean 4 port (formal/lean4, library L4Factoidal) to a single WebAssembly module that runs in the browser, Node and Deno — the toolchain route chosen and why, the exact build commands, the Lean runtime flags, the C ABI and its memory rules, how to add an export, and the traps that produce a silently-wrong or silently-aborting artifact. Use when adding or changing a wasm export, when rebuilding after a Lean change, when the wasm aborts or returns nothing, when a hub post needs the Lean engine, or when evaluating a different C-to-wasm toolchain.
---

# Lean 4 → WebAssembly

Issue: https://github.com/danbri/factoidal/issues/466
Design decision (owner-approved 2026-08-22):
`docs/designissues/2026-08-22-lean4-external-dependencies.md` §4.

## What exists

| Path | Role |
|---|---|
| `formal/lean4/Wasm/Abi.lean` | JSON string-in / string-out ABI + a phase-1 JSON reader/writer shim |
| `formal/lean4/Wasm/Exports.lean` | the `@[export]` declarations (the C symbol names) |
| `formal/lean4/Wasm/Main.lean` | a NATIVE driver over the same ABI (`lake exe l4wasm-cli`) |
| `formal/lean4/Wasm/l4_shim.c` | the C boundary: init, `char *` ↔ Lean string, ownership |
| `formal/lean4/Wasm/l4_stubs.c` | one stub (`initialize_libuv`) — see "the purity evidence" below |
| `formal/lean4/Wasm/build-wasm.sh` | the whole pipeline, reproducible |
| `docs/web/hub/assets/l4/l4factoidal.wasm` | the committed module |
| `docs/web/hub/assets/l4/l4factoidal.mjs` | Emscripten's generated glue |
| `docs/web/hub/assets/l4/l4factoidal.js` | our ES-module loader (`loadL4()`) |
| `tests/hub/post36_test.mjs` | the gate: cells of hub post 36 + the error paths |

Measured on the first working build (2026-08-22, macOS arm64,
Emscripten 6.0.8, Lean v4.33.1):

| Quantity | Value |
|---|---|
| `l4factoidal.wasm` | 1,510,823 bytes (1.5 MB) |
| Emscripten glue `l4factoidal.mjs` | 62,242 bytes |
| Module instantiation, Node | ~41 ms |
| Module instantiation, Deno | ~60 ms |
| Lean module initialisers (`l4_init`) | ~36 ms, once |
| One 2-pattern BGP over a 4-triple graph | 2.7 ms (Node), 4.0 ms (Deno) |

## The problem, stated exactly

Lean's compiler emits C. Linking that C needs two things the elan
toolchain ships **only as native binaries**:

1. Lean's C++ runtime (`libleanrt`), and
2. Lean's compiled core library (`libInit.a`) — every `List`, `String`
   and `Option` function your code calls.

There is no `wasm32` release asset for Lean (checked: the v4.33.1
release publishes darwin/linux/windows only). So both must be rebuilt.

## The route chosen, and the three that were not

**Chosen: regenerate the core library's C with the native `lean`, then
Emscripten for everything.**

The insight that makes this cheap: `lean -R <srcdir> -c out.c <mod>.lean`
re-emits a module's C in about **one second**, because the toolchain
ships the core library's *sources* (`<toolchain>/src/lean/Init/**`) and
every import is already a compiled `.olean`. So "rebuild the Lean
standard library" is ~630 one-second jobs — about four minutes at
`-P 8` — not a stage build. Nothing needs to *elaborate* Lean inside the
browser; it only needs to *run* already-compiled Lean.

Rejected, with reasons:

- **lean4's own CMake Emscripten build** (`emcmake cmake`,
  `-DLEAN_EMSCRIPTEN`). This is the upstream-supported route and it
  works, but it builds the Lean *compiler* (`libleancpp`, the whole C++
  frontend) and cross-builds the stdlib through it, plus libuv as an
  ExternalProject. Hours of build for a capability we do not need
  (elaboration in the browser). Its flags were still worth reading —
  `-fwasm-exceptions` and the GMP-free option came from there.
- **`leanir`, the toolchain's IR-to-C tool.** Looked ideal: the
  toolchain ships per-module `.ir` files (252 KB for
  `Init.Data.List.Basic`, so the bodies really are there) and a
  `leanir <setup.json> <out.ir> <out.c>` binary. In practice its
  `setup.json` contract could not be reconstructed: with imports absent,
  with direct imports, and with all 1,114 core modules listed, it
  emitted the same **near-empty** module (3,529 bytes, 3 exports, no
  `l_List_reverse`) and exited 0 — and some modules failed with
  `missing data file for module Init.Grind.ToInt` even though both that
  module's `.olean` and `.ir` were listed. **It fails silently**, which
  is why it is recorded here rather than left for someone to rediscover.
  Setting `isModule: true` (Init uses Lean's new module system — the
  sources begin with `module`) did not change the output.
- **WASI (`wasi-sdk` / `clang --target=wasm32-wasi`) and `zig cc`.** Not
  attempted after Emscripten linked, per the brief's instruction to take
  the route that links first and document the rest. The blocking risk to
  check first if this is revisited: Lean's runtime throws C++ exceptions
  (`runtime/exception.cpp`), and wasi-sdk's libc++ exception support is
  the historic weak point; Emscripten's `-fwasm-exceptions` is
  well-trodden. The upside WASI would buy — no JS glue at all — is
  smaller than it looks here, because the glue is 62 KB and our loader
  already hides it behind one `loadL4()`.

## Build it

```bash
export PATH="$HOME/.elan/bin:$PATH"          # every shell, every time
brew install emscripten libuv                 # libuv: HEADERS only, see below
cd /path/to/factoidal
formal/lean4/Wasm/build-wasm.sh               # work dir defaults to /tmp/l4wasm-build
```

Incremental: the script skips a core `.c`/`.o` that already exists, so a
re-run after a change to *our* Lean code only redoes steps 0, 6 and 7
(seconds). To force a clean build, delete the work directory.

Prerequisites and how much they cost:

| Thing | Size | Note |
|---|---|---|
| Emscripten | ~919 MB (`brew install emscripten`) | pulls its own node |
| lean4 source, sparse+blobless | ~3.3 MB | only `src/runtime` + `src/include` |
| generated core C | ~32 MB | in the work dir |
| core wasm objects | ~17 MB | in the work dir |

## What the build actually does

0. `lake build l4wasm` — also writes our modules' C into `.lake/build/ir/`.
1. `git clone --filter=blob:none --sparse --depth 1 --branch <tag>` of
   lean4, then `git sparse-checkout set src/runtime src/include`. Only
   3.3 MB is ever downloaded. **Do not clone the full tree** — it is
   large enough to matter on a constrained machine.
2. Write the CMake-generated headers by hand:
   - `lean/config.h` — deliberately WITHOUT `LEAN_MIMALLOC` (no mimalloc
     for wasm32) and WITHOUT `LEAN_USE_GMP`, so `runtime/mpz.cpp` falls
     back to `runtime/mpn.cpp`. **This is what makes the artifact
     GMP-free**, which was one of the owner's selection criteria.
   - `lean/version.h` — copied from the toolchain.
   - `githash.h` — `#define LEAN_GITHASH "$(lean --githash)"`.
3. Regenerate the core library's C (~631 modules, `-P 8`).
4. Compile that C to wasm objects.
5. Compile Lean's runtime `.cpp` to wasm objects (24 of the 34 files).
6. Compile our library's C, `l4_shim.c` and `l4_stubs.c`.
7. `em++` link.

## The flags, and why each one is load-bearing

```
-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions
```

- **`-DNDEBUG` is not an optimisation, it is a correctness requirement.**
  Lake compiles Lean-generated C with `-O3 -DNDEBUG` natively, and Lean's
  core C is only ever built that way upstream. Built WITHOUT it, the
  wasm module aborted with
  `LEAN ASSERTION VIOLATION … i < lean_ctor_num_objs(o)` (`lean.h:779`,
  inside `lean_ctor_get`) on the **first decode-error path**, while the
  happy path was perfectly fine. That asymmetry is what makes it
  dangerous: a smoke test that only queries successfully ships a module
  that dies the first time a user sends malformed input.
  `tests/hub/post36_test.mjs` pins the error path for exactly this
  reason. (Confirmed wasm-specific: rebuilding the native library with
  `moreLeancArgs = ["-UNDEBUG"]` did *not* reproduce it, because the
  native build still links the shipped, NDEBUG-built `libInit.a`.)
- **`-fwasm-exceptions`**: Lean's runtime throws. Native wasm exception
  handling needs Chrome 95+, Firefox 131+, Safari 18.4+, Node 18+. Same
  choice lean4's CMake makes. `-fexceptions` (JS-based) is the fallback
  if an older browser must be supported; it is larger and slower.
- **NO `-pthread`**, deliberately, even though lean4's own Emscripten
  build uses it. A pthread build needs `SharedArrayBuffer`, which needs
  COOP/COEP response headers, which **GitHub Pages does not send** — so
  the hub demo would be dead on arrival. Safe here because the shim
  calls `lean_initialize_runtime_module()`, not the full
  `lean_initialize()`, so no Lean task-manager thread is ever spawned.
- **`em++`, not `emcc`, for the LINK step.** The C driver does not link
  libc++, and Lean's runtime is C++. Symptom of getting this wrong: a
  wall of undefined `std::__2::…`, `__cxa_throw`, `typeinfo for …`.
- **`-std=c++20`** for the runtime `.cpp` only: `runtime/object.cpp`
  uses `std::memory_order::relaxed` and `std::bit_cast`. C++17 fails.

Runtime files deliberately NOT compiled: `libuv.cpp`, `uv/*.cpp`,
`openssl.cpp`. `uv.h` is still needed on the include path because
`runtime/io.cpp` includes it — **declarations only**; no libuv code is
linked.

### The purity evidence

After excluding those files, `wasm-ld` reported **exactly one** undefined
symbol: `initialize_libuv`. That is the whole of `l4_stubs.c`. The
smallness of that list is the measured evidence that the exported ABI
really is a pure computation — nothing reachable from the exports
touches Lean's IO, socket, DNS or task layers. If that list ever grows,
something impure got exported; treat a new stub as a design question,
not a build fix.

## The C ABI and its memory rules

Lean side (`Wasm/Exports.lean`):

```lean
@[export l4_version]   def l4VersionExport (_ : Unit) : String
@[export l4_bgp_query] def l4BgpQueryExport (dataJson bgpJson : String) : String
```

C prototypes Lean generates:

```c
lean_object *l4_version   (lean_object *unit);
lean_object *l4_bgp_query (lean_object *data_json, lean_object *bgp_json);
```

`l4_version` takes `Unit` rather than being a nullary constant: an
exported nullary Lean definition compiles to a closed thunk that C
cannot portably call. Pass `lean_box(0)`.

The JS-facing surface is `Wasm/l4_shim.c`:

```c
int   l4_init(void);                                    /* idempotent */
char *l4_version_c(void);
char *l4_bgp_query_c(const char *data_json, const char *bgp_json);
void  l4_free_result(char *p);
```

Ownership, in full:

1. Lean's convention for `@[export]`ed functions is **owned arguments**:
   the callee consumes every `lean_object *` you pass. Never `lean_dec`
   an argument you already handed over — that is a double free.
2. The returned `lean_object *` is **owned by the caller**; the shim
   copies its bytes with `strdup` and then `lean_dec`s it.
3. The `char *` returned to JavaScript is **owned by JavaScript** and
   must go back to `l4_free_result` exactly once. The loader does this in
   a `finally`, so a throwing `JSON.parse` cannot leak.
4. Returned strings are NUL-terminated UTF-8. Lean strings contain no
   interior NUL, so this is lossless.
5. Errors never cross as exceptions. A Lean-side failure comes back as
   a JSON document with an `"error"` key; the loader turns that into a
   JS `Error`. A NULL return means allocation failure only.

The module initialiser symbol is
`initialize_<package>_<Module_Path>` — here
`initialize_l4factoidal_Wasm_Exports(uint8_t builtin)`. Note it takes
only `builtin` in Lean 4.33 (no world argument), and it chains through
every import including `Init`. `lean_initialize_runtime_module` and
`lean_io_mark_end_initialization` are **not declared in `lean.h`**;
declare them yourself, as Lean's own generated `main` does.

## Loading it: browser, Node, Deno

One artifact, one loader:

```js
import { loadL4 } from './assets/l4/l4factoidal.js';
const l4 = await loadL4();
l4.version();
l4.bgpQuery(triples, bgp);   // -> SPARQL Query Results JSON
```

- **Browser** — the glue `fetch`es the sidecar `.wasm` from the same
  origin. No headers needed (no `SharedArrayBuffer`).
- **Node** — the glue reads it with `node:fs`.
- **Deno** — takes the Node path through `node:` compatibility. Needs
  `--allow-read` for a `file:` URL.

**The naming trap.** Emscripten 6 resolves the sidecar from the *glue
file's own basename* (`findWasmBinary()` does
`new URL("l4factoidal.wasm", import.meta.url)`), and it **ignores a
`wasmBinary` option passed to the factory**. So the glue must be named
`l4factoidal.mjs` for it to find `l4factoidal.wasm`. Rename one without
the other and every runtime fails with `ENOENT` / a failed fetch. An
earlier version of the loader read the bytes itself and passed
`wasmBinary` — that silently did nothing.

## Adding a new export

1. Write the Lean function in `Wasm/Abi.lean` as a pure
   `String → … → String`. Keep the boundary at JSON strings; do not
   invent a struct-passing convention.
2. Add `@[export l4_<name>]` in `Wasm/Exports.lean`.
3. Add the `char *`-level wrapper in `l4_shim.c`, following the
   ownership rules above.
4. Add `_l4_<name>_c` to `-sEXPORTED_FUNCTIONS` in `build-wasm.sh`.
5. Add a method in `docs/web/hub/assets/l4/l4factoidal.js`.
6. Add an `async <name>(…)` wrapper to the `fn` object in
   `docs/_includes/hub.njk` **before** any hub post calls it —
   `tests/hub/fn_surface_parity_test.mjs` enforces this, because the
   node harness binds `fn` to the node package and cannot see a missing
   browser wrapper.
7. Extend `tests/hub/post36_test.mjs`, including an error path.
8. Rerun `build-wasm.sh` and commit the rebuilt `.wasm` (binaries are
   committed in this repo, iron rule #9).

## Rebuilding after a Lean change

`build-wasm.sh` re-runs `lake build l4wasm` first, so a change to any
`L4Factoidal` or `Wasm` module is picked up. The core library and
runtime objects are cached in the work dir and are NOT recompiled — that
is the fast path (seconds, not minutes). Delete the work dir only when
the Lean toolchain version changes.

**A Lean toolchain bump is a wasm rebuild.** `lean-toolchain` pins both
the compiler and the core sources the wasm objects are generated from;
bumping it without re-running this script leaves an artifact built
against the old core library.

## Traps, each one paid for

1. **`leanir` fails silently** — emits a near-empty module and exits 0.
   Do not use it. (Above.)
2. **Building the core C without `-DNDEBUG`** aborts the module on error
   paths only. (Above.)
3. **`emcc` instead of `em++` at link time** — undefined libc++.
4. **Renaming the glue or the wasm independently** — ENOENT everywhere.
5. **Deriving the toolchain directory from the tag.** elan spells it
   `leanprover--lean4---v4.33.1` (tag and all), and `command -v lean`
   points at elan's *shim* in `~/.elan/bin`, whose grandparent is
   `~/.elan`, not the toolchain. Use `lean --print-prefix`. Getting this
   wrong resolved to `~/.elan` and the build failed 40 lines later with
   a confusing "toolchain does not ship core sources".
6. **`lean.h` needs `lean/config.h`**, which CMake generates and the
   source tree does not contain. Write it (step 2).
7. **`brew cleanup --prune=all` can break `emcc`.** It removes superseded
   kegs, and Emscripten runs on Homebrew's `node`; a stale
   `llhttp` dependency left `node` unable to start
   (`Library not loaded: libllhttp.9.3.dylib`), so `emcc --version`
   failed with a dyld error that looks nothing like a toolchain problem.
   Fix: `brew reinstall node`.
8. **`pretty()` in a hub cell returns a DOM element in the browser and a
   plain object in the node harness.** Never read `.rows` off a
   `pretty()` result in a later cell — keep raw values in their own named
   cells and call `pretty` only in display cells. (Anti-pattern #28.)

## Gates

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd formal/lean4 && lake build            # #guards + theorems + the ABI
lake exe l4wasm-cli version              # the ABI, natively
node --test tests/hub/post36_test.mjs tests/hub/fn_surface_parity_test.mjs
PLAYWRIGHT_PKG=<dir> bash tests/web-demos/hub_browser_all.sh   # browser sweep
```

The native driver (`l4wasm-cli`) exists so an ABI bug and a wasm bug are
never confused: if `lake exe l4wasm-cli bgp data.json bgp.json` and the
wasm disagree, the problem is in the build, not in the Lean.

## Scope of the current ABI (phase 1)

`l4_bgp_query` only. No SPARQL string parsing, no Turtle/N-Triples
reading, no §18.5 operators across the boundary. The JSON reader/writer
in `Wasm/Abi.lean`'s `L4Wasm.Json` namespace is a **shim marked for
deletion** once `L4Factoidal.JSON` and the N-Triples parser land from
`lean4/json` and `lean4/syntax-ntriples-nquads`; the exported C symbols
and the wire format do not change when it goes. Say this plainly
wherever the Lean engine is demonstrated — hub post 36 does.

The Lean side keeps its proof policy across this boundary: no `sorry`,
no `axiom`, no `partial`, no `native_decide`. The JSON reader recurses
on an explicit `Nat` fuel precisely so it is structurally recursive and
total without well-founded-recursion obligations.
