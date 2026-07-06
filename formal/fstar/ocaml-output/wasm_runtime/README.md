# Vendored + hand-written wasm_of_ocaml runtime bindings

`zarith_stubs_js` v0.17+ ships both a JS runtime (for js_of_ocaml) and a
wasm-side runtime (`runtime.wat` + `runtime_wasm.js`, for
wasm_of_ocaml). The official opam switch here has v0.16.1, which only
installs the JS files, so the wasm build otherwise hits throwing
"`ml_z_* not implemented`" stubs at the wasm/JS boundary.

We vendor the wasm files straight from
https://github.com/janestreet/zarith_stubs_js master (2025-12-16, commit
58891805 "Add missing WASM primitives (ml_z_*_unsigned)"):

- `zarith_runtime.wat` — wasm module with `(import "js" "wasm_z_*" ...)`
  declarations that export the OCaml-facing `ml_z_*` primitives.
- `zarith_runtime_wasm.js` — companion JS (`//Provides: wasm_z_*`) that
  normalises BigInt results to 31-bit JS `Number` when they fit,
  matching wasm_of_ocaml's i31 expectation (js_of_ocaml cuts at 32-bit).

`build-ocaml.sh wasm` passes both files to `wasm_of_ocaml compile`.
With these in place and stdint/sha/digestif identity-shimmed by
`wasm_stub_shims.py`, the wasm binary passes the W3C SPARQL suites
that don't touch SHA/MD5 identically to the native runner.

Upstream: https://github.com/janestreet/zarith_stubs_js

## `stdint_uint32_runtime.wat` — hand-written, not vendored

Closes the same class of gap for `Stdint.Uint32` (the OCaml realisation
`FStar_UInt32` uses for F*'s `u32`, e.g. Parquet.Footer's magic-number
and length parsing, HDT's CRC32c). A plain `//Provides: uint32_*` JS
file (`../fstar_int_stubs.js`) already gives js_of_ocaml correct
semantics, but wasm_of_ocaml does not consume that mechanism the same
way zarith does not: confirmed by disassembling a previously built
`factoidal.wasm.js` with `wasm-dis` and finding every `uint32_*` import
wired to `wasm_stub_shims.py`'s blanket identity stub instead of
`fstar_int_stubs.js`'s real bodies. Unlike Zarith, a uint32 fits
natively in Wasm's `i32`, so this file needs no companion JS runtime —
it's pure Wasm-GC struct boxing over the standard i32 arithmetic/
bitwise/unsigned-division instructions, with a custom-block shape
(compare/hash/serialize/deserialize/fixed_length) that mirrors native
stdint's `uint32_ops` (`uint32_stubs.c`) field-for-field. See the file's
own header comment for the full rationale and scope (only `uint32_*` —
the wider stdint fixed-width types are unused for real arithmetic
anywhere in this project's extracted OCaml and stay identity-shimmed).
