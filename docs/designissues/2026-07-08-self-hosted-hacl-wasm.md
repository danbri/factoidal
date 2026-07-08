# Self-hosted HACL\* WebAssembly build (reproduce `hacl-wasm` from source)

Status: **recipe + toolchain-pin blocker documented; pipeline proven
end-to-end with our tools; byte-identical rebuild blocked on the pinned
toolchain.** Research+build spike, 2026-07-08. Relates to #63 (crypto
assume vals) and #286 (vendored HACL\* Ed25519/SHA-256).

## Goal

Own a verified-to-wasm crypto artifact instead of trusting the upstream
prebuilt `hacl-wasm@1.4.0` npm binary. Rebuild the SAME Ed25519 + SHA-2
(+ Curve25519) WebAssembly ourselves through KaRaMeL's wasm backend (the
*Formally Verified Cryptography for WebAssembly* / "WASM\*" pipeline) and
diff against the vendored bytes.

## What the vendored artifact actually is

The prebuilt `.wasm` files (`Hacl_Ed25519.wasm`, `Hacl_Hash_SHA2.wasm`,
`Hacl_Curve25519_51.wasm`, plus the runtime modules `FStar.wasm`,
`WasmSupport.wasm`, `LowStar_Endianness.wasm`,
`Hacl_IntTypes_Intrinsics.wasm`, `Hacl_Hash_Base.wasm`, the Bignum
modules, and the `loader.js` / `shell.js` / `api.js` / `api.json` /
`layouts.json` glue) are the classic per-module KaRaMeL wasm output: one
`.wasm` per F\* module, linked at load time by a generated JS loader.

Verified byte-identical to the npm tarball this pass: the bytes vendored
by the companion agent (branch `worktree-agent-ac00a74895d1e9c53`,
`npm/factoidal/hacl-wasm/*.wasm`) are `sha256`-identical to
`https://registry.npmjs.org/hacl-wasm/-/hacl-wasm-1.4.0.tgz`
(Hacl_Ed25519, Hacl_Hash_SHA2, Hacl_Curve25519_51, FStar, WasmSupport
all MATCH).

## The exact toolchain pin (authoritative)

`hacl-wasm@1.4.0`'s tarball ships `INFO.txt`, written by the wasm build
rule itself:

```
This code was generated with the following toolchain.
F* version:      e617752a1b014a16892f7d8772d62e5c234f06c1
Karamel version: 2cf2974007f4103dba5619e4eb9e3eaeefad533b
Vale version:    0.3.19
```

What we have in this environment:

| Tool     | hacl-wasm@1.4.0 pin                         | Ours (this env)                            | Match |
|----------|---------------------------------------------|--------------------------------------------|-------|
| F\*      | `e617752a1b014a16892f7d8772d62e5c234f06c1`  | `2025.12.15` (opam `fstar` switch)         | no    |
| KaRaMeL  | `2cf2974007f4103dba5619e4eb9e3eaeefad533b`  | `11bb8e1ac2f720fb7144b9b768c7251526caa149` (2026-06-14) | no |
| Vale     | `0.3.19`                                    | not installed (not needed for the wasm subset) | n/a |

Both of our tools are NEWER than the pins. This is the blocker for a
**byte-identical** rebuild: KaRaMeL's wasm codegen changed between
`2cf2974` (~2024) and our `11bb8e1` (2026-06), so the emitted bytes
differ even from identical Low\* input (demonstrated below).

`.krml` binary-format note: our KaRaMeL's `InputAst.current_version = 32`
and it accepts any `.krml` with `version <= 32` (rejects only *newer*).
The pinned older KaRaMeL emits `version <= 32`, so our `krml` could in
principle *read* `.krml` produced by the pinned extractor — the format
is backward-compatible; the *codegen* is not byte-stable.

## What we proved this pass (pipeline works with our tools)

Our installed toolchain runs the entire
`F\* --codegen krml` -> `krml -backend wasm` pipeline and emits the
hacl-wasm-shaped artifact set. Reproduced here from a trivial Low\*
module plus KaRaMeL's own `krmllib/runtime/WasmSupport.fst`:

- `fstar.exe --codegen krml` produced `out.krml`.
- `krml -backend wasm -minimal -bundle 'FStar.*' -bundle 'LowStar.*'
  -bundle Prims -bundle 'C.*' -bundle TestLib -tmpdir wout
  -skip-compilation out/*.krml` ran every wasm codegen pass
  (Monomorphization, Inlining, AstToCFlat, CFlatToWasm, OptimizeWasm)
  and wrote the full artifact set:
  `WasmSupport.wasm`, `WasmSupport.wast`, `loader.js`, `shell.js`,
  `layouts.json`, `main.js`, `main.html` — the same file kinds
  `hacl-wasm` ships.

So the tool (`krml -wasm`) is not the missing input. The missing input
is HACL\*'s Low\* / `.krml` for the crypto modules.

### Byte diff vs upstream (WasmSupport.wasm, the one module both builds share)

| build                                 | size (bytes) |
|---------------------------------------|--------------|
| ours (krml `11bb8e1`, F\* 2025.12.15) | 1131         |
| `hacl-wasm@1.4.0` (krml `2cf2974`)    | 1135         |

Byte-identical through offset 394 (identical wasm magic + version +
the entire type section: `01 b1 80 80 80 00 09` = 9 function types,
identical), then diverges. `cmp -l` reports ~645 differing byte
positions in the back half. Conclusion: **structurally the same module,
not byte-identical** — exactly the karamel-version delta, as predicted.
This is the concrete evidence that byte-identical reproduction requires
the pinned `2cf2974` KaRaMeL, and that functional reproduction (correct
crypto, non-identical bytes) is what our current toolchain can deliver.

## The remaining gap (why the crypto `.krml` isn't here yet)

`krml -backend wasm` consumes `.krml` bundles. For the crypto modules
those come from running F\* over HACL\*'s Low\* source:

```
HACL* Low* (.fst in code/, specs/, lib/, vale/)
   --[ fstar.exe --codegen krml ]-->  obj/*.krml
   --[ krml -backend wasm ... ]-->    dist/wasm/*.wasm + loader.js
```

hacl-star does **not** check the `.krml` into git (they are gitignored
`obj/` build outputs), and they are not in the npm package. Generating
them requires the full HACL\* F\* extraction: a multi-GB source checkout
and a multi-hour verified build, and it is gated on the pinned F\*.
That build was **not** run this pass (disk + time discipline; the
outcome tier was already settled by the evidence above).

### The exact upstream wasm build rule (from hacl-star Makefile, HEAD `504c298`)

```make
WASM_STANDALONE = Prims LowStar.Endianness C.Endianness C.String TestLib
WASM_FLAGS = $(patsubst %,-bundle %,$(WASM_STANDALONE)) \
  -bundle FStar.* -bundle LowStar.* \
  -bundle Lib.RandomBuffer.System -bundle Lib.Memzero \
  -minimal -wasm ./test.js

dist/%/Makefile.basic: $(ALL_KRML_FILES) ...
	for f in $(filter %.krml,$^); do echo $$f; done > $@.rsp
	$(KRML) -fstar $(FSTAR_EXE) $(DEFAULT_FLAGS) \
	  -tmpdir $(dir $@) -skip-compilation @$@.rsp -silent ...
```

`$(ALL_KRML_FILES)` is the F\* extraction output. `DEFAULT_FLAGS` for
the wasm target folds in `WASM_FLAGS` and drops all Vale/intrinsic/
EverCrypt bundles ("we disable anything that is not pure Low\*").

## Reproduction recipe (shipped)

`third_party/hacl/wasm/reproduce-hacl-wasm.sh` runs the upstream build
in one of two modes:

- `byte-identical` — checks out F\* `e617752`, KaRaMeL `2cf2974`, Vale
  `0.3.19`, builds `hacl-star`'s `dist/wasm`, and diffs against the
  vendored bytes. This is the path a future run with the pinned
  toolchain finishes. Expected result: byte-identical `.wasm`.
- `functional` — uses the installed (newer) F\*/KaRaMeL, builds
  `dist/wasm`, and validates the result against the RFC 8032 Ed25519 /
  FIPS 180-4 SHA-256 vectors (the same ones the vc-crypto tests use).
  Expected result: functionally-correct `.wasm`, NOT byte-identical to
  `hacl-wasm@1.4.0` (the WasmSupport diff above is the proof of why).

## Recommendation / next steps

1. Keep the vendored-binary path (companion commit `3c303a8`) as the
   shipping artifact for now — it is verified byte-identical to upstream
   `hacl-wasm@1.4.0`, which is itself the KaRaMeL wasm output of the
   HACL\* verified sources.
2. To retire the trusted binary, run
   `reproduce-hacl-wasm.sh byte-identical` on a machine with the pinned
   toolchain (Everest image or explicit F\* `e617752` + KaRaMeL
   `2cf2974` + Vale `0.3.19`). If the diff is clean, repoint the
   npm-entry at our self-built `.wasm` and delete the upstream
   dependency.
3. Alternatively, accept `functional` mode: rebuild with our current
   toolchain, gate on the RFC vectors, and vendor our-built `.wasm`
   with provenance stating "self-built, functionally validated, not
   byte-identical to hacl-wasm@1.4.0 (newer KaRaMeL)". This owns the
   pipeline without pinning an old toolchain, at the cost of giving up
   the byte-for-byte cross-check against upstream.
4. Either way the `.krml` for the Ed25519+SHA-2+Curve25519 closure
   should be captured as a build artifact (they are the real
   "self-hosted" input); vendoring them alongside the recipe would let
   `krml -backend wasm` run without re-running the F\* extraction.

## Hard-rule note

No crypto was hand-rolled anywhere in this spike. Every primitive is
HACL\*'s verified code; the work is rebuilding HACL\*'s verified wasm,
not writing crypto. The existing vc-crypto tests are untouched.
