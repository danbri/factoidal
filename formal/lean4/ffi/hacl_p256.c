/* hacl_p256.c — Lean 4 <-> C binding for the vendored HACL* NIST P-256
 * ECDSA verification primitive (third_party/hacl/, Apache-2.0,
 * hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see
 * third_party/hacl/PROVENANCE.md).  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/P256Native.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md, "Lean 4 tree
 * amendment" — signature primitives come from HACL* via FFI ONLY.  There
 * is NO cryptographic logic in this file.  The only logic is length
 * checking around Lean's ByteArray (a `lean_sarray` of uint8) and the
 * split of a JWS 64-byte r||s signature into the two 32-byte halves
 * HACL* takes.
 *
 * Calling convention match (JWS ES256, RFC 7518 section 3.4):
 *   JWS ES256 signature = R || S, each the 32-byte big-endian
 *   fixed-length integer.  HACL* takes signature_r and signature_s as
 *   two separate 32-byte big-endian buffers.  So the conversion is one
 *   pointer offset, not a re-encoding: there is no DER here.
 *   The public key is x || y, 64 raw bytes, which is what a JWK
 *   `{"kty":"EC","crv":"P-256","x":...,"y":...}` gives after base64url
 *   decoding both members.  Hacl_P256_ecdsa_verif_p256_sha2 itself
 *   hashes the message with SHA-256 and validates the public key.
 *
 * Boundary contract:
 *   l4_hacl_p256_verify_sha256(pubXY[64], msg, sig[64]) -> 0 / 1
 * Every length refusal is 0.  There is no "unknown" answer and no
 * success-by-default path.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side), so nothing
 * is dec-ref'd here.  HACL* takes non-const `uint8_t *` for its inputs
 * but does not write through them.
 */
#include <lean/lean.h>
#include <stdint.h>

#include "Hacl_P256.h"

LEAN_EXPORT uint8_t l4_hacl_p256_verify_sha256(b_lean_obj_arg pub_xy,
                                               b_lean_obj_arg msg,
                                               b_lean_obj_arg sig) {
  if (lean_sarray_size(pub_xy) != 64) return 0;
  if (lean_sarray_size(sig) != 64) return 0;
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return 0;
  uint8_t *s = lean_sarray_cptr(sig);
  return Hacl_P256_ecdsa_verif_p256_sha2((uint32_t)n, lean_sarray_cptr(msg),
                                         lean_sarray_cptr(pub_xy),
                                         s, s + 32) ? 1 : 0;
}

/* Point validity of a raw x||y public key (HACL* checks the point is on
 * the curve and is not the point at infinity).  Exposed so the Lean JWK
 * layer can refuse a malformed EC key at parse time rather than at
 * verification time.  Not a cryptographic decision made here: the whole
 * body is one HACL* call. */
LEAN_EXPORT uint8_t l4_hacl_p256_validate_public_key(b_lean_obj_arg pub_xy) {
  if (lean_sarray_size(pub_xy) != 64) return 0;
  return Hacl_P256_validate_public_key(lean_sarray_cptr(pub_xy)) ? 1 : 0;
}
