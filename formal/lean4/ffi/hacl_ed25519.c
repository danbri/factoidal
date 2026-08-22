/* hacl_ed25519.c — Lean 4 <-> C binding for the vendored HACL* Ed25519
 * primitives (third_party/hacl/, Apache-2.0, hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see third_party/hacl/
 * PROVENANCE.md).  Realises the three `@[extern]` opaques of
 * L4Factoidal/Crypto/Ed25519.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md, "Lean 4 tree
 * amendment" — signatures come from HACL* via FFI ONLY; this is the Lean
 * tree's single permitted extern family.  There is NO cryptographic logic
 * in this file: every primitive is a call into the F-star/Low-star-verified
 * HACL* extracted C, which is vendored UNMODIFIED.  (Written "F-star"
 * because a star-slash pair would close this comment.)  The only logic here is
 * length checking around Lean's ByteArray (a `lean_sarray` of uint8).
 *
 * Boundary contract (mirrors formal/fstar/experimental_ocaml_glue/
 * hacl_stubs.c, but over raw bytes instead of hex strings):
 *   l4_hacl_ed25519_secret_to_public(sk[32])          -> pk[32]  | empty
 *   l4_hacl_ed25519_sign(sk[32], msg)                 -> sig[64] | empty
 *   l4_hacl_ed25519_verify(pk[32], msg, sig[64])      -> 0 / 1
 * An EMPTY result (or 0 from verify) on a wrong-length input is a
 * refusal, never a crypto verdict; the Lean side documents the same.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side), so nothing
 * is dec-ref'd here; results are fresh Lean objects owned by the caller.
 * HACL* takes non-const `uint8_t *` for its inputs but does not write
 * through them.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_Ed25519.h"

static lean_obj_res l4_empty_bytes(void) {
  return lean_alloc_sarray(1, 0, 0);
}

LEAN_EXPORT lean_obj_res l4_hacl_ed25519_secret_to_public(b_lean_obj_arg sk) {
  if (lean_sarray_size(sk) != 32) return l4_empty_bytes();
  lean_obj_res pk = lean_alloc_sarray(1, 32, 32);
  Hacl_Ed25519_secret_to_public(lean_sarray_cptr(pk), lean_sarray_cptr(sk));
  return pk;
}

LEAN_EXPORT lean_obj_res l4_hacl_ed25519_sign(b_lean_obj_arg sk, b_lean_obj_arg msg) {
  if (lean_sarray_size(sk) != 32) return l4_empty_bytes();
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return l4_empty_bytes();
  lean_obj_res sig = lean_alloc_sarray(1, 64, 64);
  Hacl_Ed25519_sign(lean_sarray_cptr(sig), lean_sarray_cptr(sk),
                    (uint32_t)n, lean_sarray_cptr(msg));
  return sig;
}

LEAN_EXPORT uint8_t l4_hacl_ed25519_verify(b_lean_obj_arg pk, b_lean_obj_arg msg,
                                           b_lean_obj_arg sig) {
  if (lean_sarray_size(pk) != 32) return 0;
  if (lean_sarray_size(sig) != 64) return 0;
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return 0;
  return Hacl_Ed25519_verify(lean_sarray_cptr(pk), (uint32_t)n,
                             lean_sarray_cptr(msg), lean_sarray_cptr(sig)) ? 1 : 0;
}
