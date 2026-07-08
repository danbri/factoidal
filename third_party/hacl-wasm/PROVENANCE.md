# Vendored HACL\* WebAssembly build (`hacl-wasm`)

Source: npm package [`hacl-wasm@1.4.0`](https://www.npmjs.com/package/hacl-wasm)
(`dist.tarball`
`https://registry.npmjs.org/hacl-wasm/-/hacl-wasm-1.4.0.tgz`), the
official JavaScript/WebAssembly bindings for the KaRaMeL-extracted HACL\*
cryptographic library, published by the HACL\* team
(project-everest/hacl-star).

Toolchain that produced the `.wasm` (see `INFO.txt`):

- F\* `e617752a1b014a16892f7d8772d62e5c234f06c1`
- KaRaMeL `2cf2974007f4103dba5619e4eb9e3eaeefad533b`
- Vale `0.3.19`

License: Apache-2.0 (`LICENSE-APACHE`), same license as the native
vendored HACL\* C under `../hacl/`.

## Why this is here

The native VC Data Integrity crypto (`eddsa-rdfc-2022`) links the
vendored HACL\* **C** (`third_party/hacl/`) into the native binary. That C
does not link under `js_of_ocaml` / `wasm_of_ocaml`, so VC crypto was
native-only (GitHub #286). This directory holds HACL\*'s own official
**WebAssembly** build so the same F\*/Low\*-verified Ed25519 + SHA-2
primitives run in Node and the browser, wired at the npm-entry layer per
`skills/crypto-policy/SKILL.md` (preference: "HACL\*'s own official
WebAssembly build (the `hacl-wasm` artifacts) wired in at the npm-entry
layer").

No cryptographic logic is hand-written anywhere in this integration: the
`.wasm` modules are HACL\*'s verified output; `api.js` / `loader.js` /
`shell.js` are HACL\*'s own KaRaMeL-generated bindings, vendored
**unmodified**; `api.json` / `layouts.json` are HACL\*'s API descriptors.

## Minimal module subset

Only the modules in the transitive closure of Ed25519 + SHA-2 are
vendored (the upstream package ships ~60 `.wasm` modules for the full
EverCrypt surface). Closure, in load order:

    WasmSupport  FStar  LowStar_Endianness
    Hacl_Hash_Base  Hacl_Hash_SHA2
    Hacl_IntTypes_Intrinsics  Hacl_Bignum_Base  Hacl_Bignum
    Hacl_Bignum25519_51  Hacl_Curve25519_51
    Hacl_Ed25519_PrecompTable  Hacl_Ed25519

This subset is the argument passed to
`HaclWasm.getInitializedHaclModule(modules)` in
`npm/factoidal/hacl-init.js`. If a future consumer needs more primitives
(e.g. P-256, HMAC), add the corresponding `.wasm` files here and extend
that module list.

## Updating

Re-run `npm pack hacl-wasm@<version>`, copy the same file set, and update
the version + toolchain hashes above. Keep `api.js` / `loader.js` /
`shell.js` byte-for-byte from upstream — they are not modified.
