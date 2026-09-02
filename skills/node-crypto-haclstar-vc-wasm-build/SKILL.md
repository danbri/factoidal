---
name: node-crypto-haclstar-vc-wasm-build
description: How Factoidal's Verifiable-Credentials crypto (VC Data Integrity, eddsa-rdfc-2022) runs OFF the native binary — in Node and the browser — by realising VC.DataIntegrity.fst's four crypto assume vals with HACL*'s official WebAssembly build. Use when VC verify/sign must work without a native binary, when a js_of_ocaml/wasm_of_ocaml build crashes inside a digest/signature primitive, when wiring or landing the hacl-wasm stubs, when adding a new crypto assume val that must reach the browser, or when auditing the crypto provenance/licence chain. Pairs with crypto-policy (the sourcing rule) — this is the concrete build.
---

# HACL\* wasm VC crypto — verify/sign in Node and the browser, no native binary

## The problem this solves

`formal/fstar/VC.DataIntegrity.fst` (eddsa-rdfc-2022 Data Integrity
proofs) has **four crypto `assume val`s**: SHA-256, and Ed25519
`secret_to_public` / `sign` / `verify`. Natively these are realised by
vendored HACL\* **C**. That C **does not link under js_of_ocaml or
wasm_of_ocaml**, so before #286 VC verify/sign was native-only — the
whole VC pipeline went dark in Node and the browser. This skill is how
the *same* F\*-extracted VC pipeline runs off-native: the crypto
primitives are backed by HACL\*'s own verified WebAssembly build.

Landed in **#286** (`3c303a8`, "VC verify works off-native"). This is
preference (1) of the `crypto-policy` adoption order — HACL\*'s
**official** wasm, not a hand-written fallback digest, and not (yet) the
self-built `krml -wasm` route (#71, an alternative not on the critical
path).

## Iron rule that governs this

Never write our own crypto. Every primitive here is HACL\*'s verified
output (F\*/Low\*/KaRaMeL → wasm), vendored **unmodified**. The OCaml/JS
we add is *glue that calls it* — realising an `assume val`, which is the
one thing hand-written OCaml/JS is allowed to do (repo rule #11,
`ASSUME-CRYPTO`). No byte-layout, no algorithm, no "just hash it
ourselves for now".

## The three realisation paths (one F\* spec, three backends)

| Target | Realisation | File |
|---|---|---|
| Native OCaml | vendored HACL\* **C** | `formal/fstar/ocaml-output/fstar_hacl_crypto.ml` (+ the C under `third_party/hacl/`) |
| js_of_ocaml (Node + browser) | HACL\* **wasm** via `//Provides:` JS stubs | `formal/fstar/ocaml-output/hacl_stubs.js` + `hacl_stubs_jsoo.c` |
| wasm_of_ocaml | same JS stubs | same |

All three satisfy the **identical byte contract** — the js stubs'
header documents the exact hex-string signatures the C stub also honours:

```
caml_hacl_sha256(msg_bytes)                       -> 64-char hex digest
caml_hacl_ed25519_secret_to_public(sk_hex)        -> pk_hex (64) | ""
caml_hacl_ed25519_sign(sk_hex, msg_hex)           -> sig_hex (128) | ""
caml_hacl_ed25519_verify(pk_hex, msg_hex, sig_hex)-> bool (0/1)
```

## The safety contract — verify NEVER silently succeeds

The wasm backend must be **initialised first**. `hacl_stubs.js`'s
`caml_hacl_backend()` reads `globalThis.__factoidalHacl`; if it's unset,
**every primitive THROWS** — it never returns a fake success. A `verify`
that returns `true` without a real signature check is a security hole,
not a graceful degradation. So:

- Node: `const { initHacl } = require('.../hacl-init.js'); await initHacl();`
- Browser: serve the `hacl-wasm/` dir next to the page and
  `await initHacl({ apiUrl: '/path/to/hacl-wasm/api.js' })`.

`initHacl` loads HACL\*'s wasm modules once (async) and stashes the ready
API object on `globalThis.__factoidalHacl`; after that the primitives run
**synchronously** — no await on the hot path. `npm/factoidal/hacl-init.js`
is the loader; it probes `./hacl-wasm/api.js` (packaged) then
`../../third_party/hacl-wasm/api.js` (repo).

## Vendored artifacts + provenance (licence-critical)

- `third_party/hacl-wasm/` — the Ed25519 + SHA-2 module closure of
  **`hacl-wasm@1.4.0`** (the official npm package published by the HACL\*
  team, project-everest/hacl-star), **Apache-2.0**. ~520 KB. Keep
  `PROVENANCE.md` + `INFO.txt` (records the F\*/KaRaMeL/Vale commit
  hashes that produced the `.wasm`) + `LICENSE-APACHE`.
- `npm/factoidal/hacl-wasm/` — a **mirror** of the same closure so the
  published npm package is self-contained (no repo-relative path at
  runtime).
- Both are pure vendored artifacts: when landing, `git checkout <commit>
  -- third_party/hacl-wasm/ npm/factoidal/hacl-wasm/` wholesale is safe.

## Build wiring (`formal/fstar/build-ocaml.sh`, the `js` step)

Four edits, all inside the `"$STEP" == "js"` block:

1. `FSTAR_MODULES` array += `fstar_hacl_crypto.ml` and `VC_DataIntegrity.ml`.
2. The **three** `ocamlc ... -custom` byte-link lines (w3c_runner.byte,
   factoidal.byte, npm_entry.byte) += `hacl_stubs_jsoo.c` (after
   `parquet_zstd_stubs_jsoo.c`).
3. `JS_TARGETS` array += `hacl_stubs.js` (so the change-detection guard
   sees it).
4. The final `js_of_ocaml` link inputs += `hacl_stubs.js`.

The sanctioned patch that realises the native side lives at
`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/286_vc_hacl_ed25519_sha256_stubs.sh`
(rule #3: one patch per assume-val gap, mapped to issue #286).

## npm ABI surface (`bin/npm-entry/entry_jsoo.ml`)

Six string-in/string-out consumer wrappers over `VC_DataIntegrity.*`,
each a `guarded (fun () -> ...)` returning `{"ok":true,...}` JSON,
registered in the `Js.export "factoidalNpmEntry"` object:

```
vcSha256Hex, vcEd25519SecretToPublic, vcEd25519Sign, vcEd25519Verify,
vcEddsaCreateFromCanonical, vcEddsaVerifyFromCanonical
```

These are consumer glue (rule #11) — no crypto logic; they delegate to
the F\*-extracted `VC_DataIntegrity` functions.

## The gate

`node --test npm/factoidal/test/vc-crypto.test.js` — runs `await
initHacl()` then exercises Ed25519 + SHA-256 against **FIPS 180-4 / RFC
8032 vectors** (correctness proven, not asserted), and REQUIRES the
negative cases (wrong key, tampered signature, tampered proof, different
document) all report `false`. A green run is the proof VC works
off-native.

## Landing recipe (when bringing this from an off-main branch)

The #286 commit was built on an old base, so its regenerated
`docs/fstar-extracted/*.js` bundle is **stale** — never reuse it. Land
the source, rebuild the bundle fresh (hazard #28):

1. `git checkout <commit> --` the vendored dirs + `hacl-init.js` +
   `vc-crypto.test.js` + the `286_...sh` patch + `hacl_stubs.js` +
   `hacl_stubs_jsoo.c` + `fstar_hacl_crypto.ml` (all safe wholesale).
2. **3-way merge** (not wholesale checkout — main drifts) the crypto
   hunks into `bin/npm-entry/entry_jsoo.ml` (6 fns + 6 exports),
   `build-ocaml.sh` (the four edits above), `npm/factoidal/factoidal-npm-entry.js`,
   `package.json`. Get exact hunks with `git diff <commit>^..<commit> -- <file>`.
3. Re-extract + `./build-ocaml.sh js`, **forcing** the npm-entry
   rebuild (the `JS_NEEDS_REBUILD` guard skips unchanged targets — see
   hazard #28). Confirm js_of_ocaml actually re-ran the npm-entry target.
4. Gate: `vc-crypto.test.js` green + `node --test tests/hub/*.mjs` still
   green — 181 pass, 0 fail at the time of writing; 408 pass, 0 fail
   (out of 409) on 2026-09-02 (a broken bundle breaks every hub cell).

## The other wasm route (don't confuse them)

There are two ways to get HACL\* into wasm:

- **Official `hacl-wasm` npm artifact** — what #286 uses, what this skill
  documents. Fastest, published+versioned by the HACL\* team.
- **Self-built via `krml -wasm`** (#71) — reproduce the wasm ourselves
  from HACL\*'s F\*/C source rather than trusting the upstream binary.
  An assurance upgrade, not on the VC critical path. If you adopt it,
  it drops in behind the *same* `caml_hacl_*` byte contract and
  `initHacl` seam — only the `.wasm` provenance changes.

See also: [`crypto-policy`](../crypto-policy/SKILL.md) (the sourcing
rule + adoption order + the wasm compatibility gate that is the whole
reason the C route can't serve the browser).
