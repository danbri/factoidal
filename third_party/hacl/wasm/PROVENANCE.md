# Self-hosted HACL\* wasm — provenance & status

This directory holds the recipe for rebuilding HACL\*'s Ed25519 + SHA-2
(+ Curve25519) **WebAssembly** ourselves via KaRaMeL's wasm backend,
instead of trusting the upstream prebuilt `hacl-wasm@1.4.0` npm binary.

Full write-up: `docs/designissues/2026-07-08-self-hosted-hacl-wasm.md`.
Policy: `skills/crypto-policy/SKILL.md`. Issues: #63, #286.

## Status (2026-07-08): recipe + toolchain-pin blocker

- **Byte-identical rebuild: BLOCKED on the pinned toolchain.**
  `hacl-wasm@1.4.0` was built with F\* `e617752`, KaRaMeL `2cf2974`,
  Vale `0.3.19` (from the tarball's own `INFO.txt`). This environment
  has KaRaMeL `11bb8e1` + F\* `2025.12.15` — both newer. KaRaMeL's wasm
  codegen is not byte-stable across versions, so identical Low\* input
  yields different bytes. Demonstrated: a `WasmSupport.wasm` built here
  is 1131 B vs upstream 1135 B, byte-identical through offset 394 then
  divergent.
- **Pipeline itself: PROVEN with our tools.** `fstar --codegen krml`
  then `krml -backend wasm` runs every codegen pass and emits the full
  hacl-wasm-shaped artifact set (`*.wasm` + `loader.js` + `shell.js` +
  `layouts.json`). The missing input is HACL\*'s crypto `.krml`, which
  is an F\* extraction output (gitignored `obj/`), not shipped by
  upstream and not regenerated this pass (multi-GB, multi-hour verified
  build).
- **Shipping artifact stays the vendored binary** (companion commit
  `3c303a8`, verified sha256-identical to the npm tarball) until a run
  with the pinned toolchain produces a self-built `.wasm` to swap in.

## Files

- `reproduce-hacl-wasm.sh` — runs the upstream `dist/wasm` build in
  `byte-identical` (pinned toolchain) or `functional` (installed
  toolchain) mode; diffs against reference bytes and points at the
  RFC-vector functional check.

## Not vendored here (and why)

- The crypto `.krml` bundles: they require the pinned/heavy F\*
  extraction of HACL\*'s Low\* source. Capturing them is the recommended
  next step so `krml -backend wasm` can run without re-extracting.
- Any `.wasm`: none self-built for the crypto modules yet (see blocker).

## Never

Do not hand-edit anything here into crypto logic. This is a build recipe
around HACL\*'s verified sources; primitives come only from HACL\*.
