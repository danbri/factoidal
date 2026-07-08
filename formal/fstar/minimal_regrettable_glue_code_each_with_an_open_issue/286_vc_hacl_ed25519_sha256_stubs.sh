#!/bin/bash
# Issue #286: VC Data Integrity crypto assume-val stubs for VC_DataIntegrity.ml
# https://github.com/danbri/factoidal/issues/286  (the #63 assume-val family)
#
# Crypto sourcing policy: skills/crypto-policy/SKILL.md — "Dont roll our own
# crypto!", "pursue HACL*".  Routes the four crypto assume-vals of
# VC.DataIntegrity.fst (eddsa-rdfc-2022 pipeline) to the vendored, F*/Low*-
# verified HACL* extracted C (third_party/hacl/, commit 05c3d8fb, Apache-2.0),
# via the hand-written realiser ocaml-output/fstar_hacl_crypto.ml + the CAMLprim
# FFI experimental_ocaml_glue/hacl_stubs.c.
#
# There is NO pure-OCaml/F* signature fallback: Ed25519 sign+verify come from
# HACL* only.  This patch is the NATIVE seam (vendored HACL* C).  The
# browser/Node (js_of_ocaml) seam realises the SAME four assume vals over
# HACL*'s OWN official WebAssembly build (third_party/hacl-wasm/) via
# ocaml-output/hacl_stubs.js + npm/factoidal/hacl-init.js — VC.DataIntegrity
# is now in the js module list too (see skills/crypto-policy/SKILL.md
# "VC crypto off-native", #286).  wasm_of_ocaml target: tracked in #286.
#
# Replaces F*-extracted failwith stubs for:
#   - hash_sha256_hex        -> Fstar_hacl_crypto.sha256_hex
#   - ed25519_secret_to_public -> Fstar_hacl_crypto.ed25519_secret_to_public
#   - ed25519_sign           -> Fstar_hacl_crypto.ed25519_sign
#   - ed25519_verify         -> Fstar_hacl_crypto.ed25519_verify

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/VC_DataIntegrity.ml"
if [[ ! -f "$FILE" ]]; then
  # VC_DataIntegrity.ml is only extracted for the native build; skip silently
  # when it is absent (e.g. a js/wasm-only extraction run).
  echo "  (286) $FILE not present — skipping (native-only crypto seam)."
  exit 0
fi

echo "  Patching $FILE (VC HACL* Ed25519 + SHA-256 crypto stubs)..."

python3 - "$FILE" <<'PYEOF'
import sys
path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

repls = [
    ('''let hash_sha256_hex (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: VC.DataIntegrity.hash_sha256_hex"''',
     '''let hash_sha256_hex (s : Prims.string) : Prims.string=
  Fstar_hacl_crypto.sha256_hex s'''),

    ('''let ed25519_secret_to_public (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: VC.DataIntegrity.ed25519_secret_to_public"''',
     '''let ed25519_secret_to_public (sk : Prims.string) : Prims.string=
  Fstar_hacl_crypto.ed25519_secret_to_public sk'''),

    ('''let ed25519_sign (uu___ : Prims.string) (uu___1 : Prims.string) :
  Prims.string= failwith "Not yet implemented: VC.DataIntegrity.ed25519_sign"''',
     '''let ed25519_sign (sk : Prims.string) (msg : Prims.string) :
  Prims.string= Fstar_hacl_crypto.ed25519_sign sk msg'''),

    ('''let ed25519_verify (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string) : Prims.bool=
  failwith "Not yet implemented: VC.DataIntegrity.ed25519_verify"''',
     '''let ed25519_verify (pk : Prims.string) (msg : Prims.string)
  (sg : Prims.string) : Prims.bool=
  Fstar_hacl_crypto.ed25519_verify pk msg sg'''),
]

missing = []
for old, new in repls:
    if old in content:
        content = content.replace(old, new)
    elif new.split('\n')[1].strip() in content:
        pass  # already patched (idempotent re-run)
    else:
        missing.append(old.split('\n')[0])

if missing:
    sys.stderr.write("  ERROR: VC_DataIntegrity.ml crypto stub(s) matched neither "
                     "failwith form nor patched form:\n")
    for m in missing:
        sys.stderr.write("    - " + m + "\n")
    sys.stderr.write("  eddsa-rdfc-2022 sign/verify will raise failwith. "
                     "Inspect VC_DataIntegrity.ml head and update patch 286.\n")
    sys.exit(2)

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  VC crypto stubs wired to Fstar_hacl_crypto (HACL* Ed25519 + SHA-256)."
