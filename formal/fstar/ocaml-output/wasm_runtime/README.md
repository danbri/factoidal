# Vendored wasm_of_ocaml runtime bindings

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
