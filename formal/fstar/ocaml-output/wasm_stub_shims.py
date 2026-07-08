#!/usr/bin/env python3
"""
Post-process the wasm_of_ocaml-generated .wasm.js loader to replace the
remaining throwing-stub implementations for missing C primitives with
identity/pass-through shims.

Why: fstar.lib transitively depends on stdint, zarith, sha, and
digestif. wasm_of_ocaml emits dummy `() => { throw Error("X not
implemented") }` stubs for any external primitive without a
wasm-side binding.

Zarith is handled separately by linking
ocaml-output/wasm_runtime/{zarith_runtime.wat,zarith_runtime_wasm.js}
during `wasm_of_ocaml compile` (see build-ocaml.sh). That covers
~14 ml_z_* primitives and makes the Turtle parser actually work.

This script handles what remains:
- stdint fixed-width ops (int40_of_int, uint64_of_int, int40_min_int,
  …). Identity pass-through: stdint is linked for its module init
  but the F*-extracted hot path doesn't use fixed-width ints, so
  returning the argument unchanged is enough to keep Wasm-GC's
  (ref eq) conversion happy without semantic correctness.
- SHA/digestif (stub_sha*, caml_digestif_*). Also identity. These
  ARE used when a SPARQL test calls MD5()/SHA1()/SHA256() — those
  tests crash with "illegal cast" until real bindings are written.

With those two tweaks, most SPARQL suites run identically to native
(bind 10/10, bindings 10/10, aggregates 46/46, syntax-query 93/94,
…). The `functions` suite crashes because it tests hash builtins.

Usage:
  python3 wasm_stub_shims.py path/to/w3c-runner.wasm.js
"""
import re
import sys


# Map from primitive name to a JS expression that replaces
# `()=>{throw new\nError("X not implemented")}` in the loader.
IMPLS = {}

# VC Data Integrity crypto (Ed25519 + SHA-256) — the SAME four primitives
# that hacl_stubs.js realises over HACL*'s wasm build under js_of_ocaml.
# wasm_of_ocaml does NOT consume the js_of_ocaml-style `//Provides:` JS FFI
# in hacl_stubs.js, so these land in the missing-primitives set here. We
# must NOT let the DEFAULT_STUB (identity pass-through) apply to
# caml_hacl_ed25519_verify: identity would return a truthy value and make
# `verify` appear to SUCCEED without a signature check — a security hole.
# Fail SAFE instead: throw, so VC.DataIntegrity's caller (entry_jsoo's
# `guarded`) surfaces {"ok":false,...} and verify is never a false `true`.
# Real VC crypto off-native runs on the js_of_ocaml/Node bundle (see
# skills/crypto-policy/SKILL.md "VC crypto off-native", #286). The
# wasm_of_ocaml target awaits a wasm-native HACL* FFI binding.
_HACL_UNAVAILABLE = (
    '()=>{throw new Error("factoidal VC crypto: HACL* is not wired for the '
    'wasm_of_ocaml target yet (GitHub #286); js_of_ocaml/Node bundle has it. '
    'Refusing to run VC crypto without the verified backend.")}'
)
for _hacl_prim in (
    'caml_hacl_sha256',
    'caml_hacl_ed25519_secret_to_public',
    'caml_hacl_ed25519_sign',
    'caml_hacl_ed25519_verify',
):
    IMPLS[_hacl_prim] = _HACL_UNAVAILABLE

# Fallback: pass the first argument through unchanged. This keeps
# Wasm-GC (ref eq) values round-tripping cleanly because V8 sees
# the exact same reference returned.
DEFAULT_STUB = '(...a)=>a[0]!==undefined?a[0]:0'

# Digestif/sha size getters: return a plausible size so the digestif
# module's constructor doesn't throw an OCaml-level Failure (e.g.
# "Invalid digest_size:64 to make a BLAKE2{S,B}").
SIZE_STUB = '()=>256'
OUTLEN_STUB = '()=>64'
KEY_STUB = '()=>64'


def stub_for(name: str) -> str:
    if name in IMPLS:
        return IMPLS[name]
    if name.endswith('_ctx_size'):
        return SIZE_STUB
    if name.endswith('_max_outlen'):
        return OUTLEN_STUB
    if name.endswith('_key_size'):
        return KEY_STUB
    return DEFAULT_STUB


def patch(path: str) -> int:
    with open(path, 'r') as f:
        content = f.read()
    pattern = re.compile(
        r'("([a-zA-Z_0-9]+)":)\(\)=>\{throw new\s+Error\("[a-zA-Z_0-9]+ not implemented"\)\}'
    )
    replaced = 0

    def repl(m):
        nonlocal replaced
        replaced += 1
        return m.group(1) + stub_for(m.group(2))

    content = pattern.sub(repl, content)
    with open(path, 'w') as f:
        f.write(content)
    return replaced


if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.stderr.write('Usage: wasm_stub_shims.py path/to/w3c-runner.wasm.js\n')
        sys.exit(1)
    n = patch(sys.argv[1])
    print(f'Replaced {n} throwing stubs with shims in {sys.argv[1]}')
