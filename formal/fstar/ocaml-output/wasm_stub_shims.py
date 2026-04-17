#!/usr/bin/env python3
"""
Post-process the wasm_of_ocaml-generated .wasm.js loader to replace the
throwing-stub implementations for missing C primitives with
best-effort JavaScript shims.

Why: fstar.lib transitively depends on stdint, sha, digestif, zarith.
Their C primitives have no wasm_of_ocaml runtime implementation, so
wasm_of_ocaml emits dummy `() => { throw Error("X not implemented") }`
stubs into the loader. Calling any of them crashes the program at init.

This script patches the generated loader.

Current state of the shims (honest):
- Identity/pass-through for everything. This is enough to survive
  *initialization* (int40_of_int etc. are called during stdint module
  init with small numbers, and returning those numbers back through
  keeps Wasm-GC's (ref eq) conversion happy).
- It is NOT enough to make code that actually USES these primitives
  work: ml_z_add(a,b) returns `a`, so zarith arithmetic is wrong;
  SHA/MD5 hash functions return the wrong thing; etc.
- Consequence: `./w3c_runner.wasm.js --list` prints all suites
  (works — no arithmetic needed). Running test suites does NOT work
  — the Turtle manifest parser needs real integer math, so it
  returns 0 triples and reports 0/0/0/0 per suite.
- Real implementations for zarith/stdint were attempted but hit
  Wasm-GC type-representation issues: returning plain JS numbers for
  a `(result (ref eq))` import sometimes works (for values that
  round-trip as i31) and sometimes doesn't (type incompatibility
  from-JS conversion failure). Proper shims likely require
  reverse-engineering wasm_of_ocaml's value representation for Z.t,
  or cross-compiling the whole OCaml link to drop these dependencies.

Usage:
  python3 wasm_stub_shims.py path/to/w3c-runner.wasm.js
"""
import re
import sys


# Map from primitive name to a JS expression that replaces
# `()=>{throw new\nError("X not implemented")}` in the loader.
IMPLS = {}

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
