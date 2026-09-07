/* hacl_kdf.c — Lean 4 <-> C binding for the vendored HACL* HMAC-SHA-256
 * (RFC 2104) and HKDF-SHA-256 (RFC 5869), and for X25519 (RFC 7748).
 * third_party/hacl/, Apache-2.0, hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see
 * third_party/hacl/PROVENANCE.md.  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/Hkdf.lean and L4Factoidal/Crypto/X25519.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md.  There is NO
 * cryptographic logic in this file: length checks and lean_sarray
 * plumbing only.
 *
 * Boundary contract, EMPTY on every length refusal:
 *   l4_hacl_hmac_sha256(key, msg)              -> mac[32]
 *   l4_hacl_hkdf_extract_sha256(salt, ikm)     -> prk[32]
 *   l4_hacl_hkdf_expand_sha256(prk, info, len) -> okm[len]
 *   l4_hacl_x25519_scalarmult(scalar[32], point[32]) -> shared[32]
 *   l4_hacl_x25519_base(scalar[32])            -> point[32]
 *
 * The X25519 all-zero result is NOT filtered here.  RFC 7748 section 6.1
 * says a shared secret of all zeros (the low-order-point outcome) MUST
 * be rejected by protocols that need contributory behaviour; that is a
 * PROTOCOL decision, so `Crypto/X25519.lean` makes it in Lean where it
 * is visible and testable, and this shim reports what the curve
 * computed.  Wycheproof's `x25519_test.json` marks those vectors
 * `acceptable` for exactly this reason.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side); results
 * are fresh Lean objects owned by the caller.
 */
#include <lean/lean.h>
#include <stdint.h>

#include "Hacl_HMAC.h"
#include "Hacl_HKDF.h"
#include "Hacl_Curve25519_51.h"

static lean_obj_res l4_kdf_empty(void) { return lean_alloc_sarray(1, 0, 0); }

LEAN_EXPORT lean_obj_res l4_hacl_hmac_sha256(b_lean_obj_arg key,
                                             b_lean_obj_arg msg) {
  size_t kn = lean_sarray_size(key), mn = lean_sarray_size(msg);
  if (kn > UINT32_MAX || mn > UINT32_MAX) return l4_kdf_empty();
  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  Hacl_HMAC_compute_sha2_256(lean_sarray_cptr(out), lean_sarray_cptr(key),
                             (uint32_t)kn, lean_sarray_cptr(msg), (uint32_t)mn);
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_hkdf_extract_sha256(b_lean_obj_arg salt,
                                                     b_lean_obj_arg ikm) {
  size_t sn = lean_sarray_size(salt), in = lean_sarray_size(ikm);
  if (sn > UINT32_MAX || in > UINT32_MAX) return l4_kdf_empty();
  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  Hacl_HKDF_extract_sha2_256(lean_sarray_cptr(out), lean_sarray_cptr(salt),
                             (uint32_t)sn, lean_sarray_cptr(ikm), (uint32_t)in);
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_hkdf_expand_sha256(b_lean_obj_arg prk,
                                                    b_lean_obj_arg info,
                                                    size_t len) {
  size_t pn = lean_sarray_size(prk), fn = lean_sarray_size(info);
  if (pn > UINT32_MAX || fn > UINT32_MAX) return l4_kdf_empty();
  /* RFC 5869 section 2.3: L must be at most 255 * HashLen, and the PRK
   * must be at least HashLen.  HACL* requires the same; asking outside
   * that range is a refusal, not a derivation. */
  if (pn < 32) return l4_kdf_empty();
  if (len == 0 || len > 255u * 32u) return l4_kdf_empty();
  lean_obj_res out = lean_alloc_sarray(1, len, len);
  Hacl_HKDF_expand_sha2_256(lean_sarray_cptr(out), lean_sarray_cptr(prk),
                            (uint32_t)pn, lean_sarray_cptr(info), (uint32_t)fn,
                            (uint32_t)len);
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_x25519_scalarmult(b_lean_obj_arg scalar,
                                                   b_lean_obj_arg point) {
  if (lean_sarray_size(scalar) != 32) return l4_kdf_empty();
  if (lean_sarray_size(point) != 32) return l4_kdf_empty();
  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  Hacl_Curve25519_51_scalarmult(lean_sarray_cptr(out), lean_sarray_cptr(scalar),
                                lean_sarray_cptr(point));
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_x25519_base(b_lean_obj_arg scalar) {
  if (lean_sarray_size(scalar) != 32) return l4_kdf_empty();
  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  Hacl_Curve25519_51_secret_to_public(lean_sarray_cptr(out),
                                      lean_sarray_cptr(scalar));
  return out;
}
