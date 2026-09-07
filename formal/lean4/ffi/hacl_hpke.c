/* hacl_hpke.c — Lean 4 <-> C binding for the vendored HACL* HPKE
 * (RFC 9180) single-shot BASE mode with DHKEM(X25519, HKDF-SHA256),
 * HKDF-SHA256 and ChaCha20-Poly1305 — the RFC 9180 Appendix A.1
 * ciphersuite, and MLS ciphersuite 3's KEM/KDF/AEAD triple.
 * third_party/hacl/, Apache-2.0, hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see
 * third_party/hacl/PROVENANCE.md.  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/Hpke.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md.  There is NO
 * cryptographic logic in this file.  The only logic is length checking
 * and the concatenation of HACL*'s two seal outputs (`enc` and `ct`)
 * into the single `enc || ciphertext || tag` buffer RFC 9180 callers
 * transmit, plus the matching split on the open path.
 *
 * Boundary contract:
 *   l4_hacl_hpke_seal_base(skE[32], pkR[32], info, aad, plain)
 *       -> enc[32] || ciphertext || tag   (32 + plain.size + 16 bytes)
 *          or EMPTY on a length refusal or a HACL* failure (an invalid
 *          recipient key).
 *   l4_hacl_hpke_open_base(skR[32], info, aad, enc_ct)
 *       -> plaintext || status, status the single LAST byte, 1 on
 *          success and 0 on failure; EMPTY on a length refusal.
 *          `enc_ct` is the buffer seal produced.
 *
 * The status-byte convention is the same as ffi/hacl_chachapoly.c and
 * for the same reason: it keeps the shim to plumbing and puts the
 * Option wrapper in Lean, where the compiler checks it.
 *
 * BASE MODE ONLY.  The vendored translation unit
 * Hacl_HPKE_Curve51_CP32_SHA256.c exports setupBaseS, setupBaseR,
 * sealBase and openBase and nothing else: the release has no PSK,
 * auth or auth-PSK entry point for this ciphersuite, and none is
 * emulated here.  A caller that needs mode_psk or mode_auth must not
 * pretend this module provides it.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side); results
 * are fresh Lean objects owned by the caller.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_HPKE_Curve51_CP32_SHA256.h"

static lean_obj_res l4_hpke_empty(void) { return lean_alloc_sarray(1, 0, 0); }

LEAN_EXPORT lean_obj_res l4_hacl_hpke_seal_base(b_lean_obj_arg skE,
                                                b_lean_obj_arg pkR,
                                                b_lean_obj_arg info,
                                                b_lean_obj_arg aad,
                                                b_lean_obj_arg plain) {
  if (lean_sarray_size(skE) != 32) return l4_hpke_empty();
  if (lean_sarray_size(pkR) != 32) return l4_hpke_empty();
  size_t in = lean_sarray_size(info), an = lean_sarray_size(aad);
  size_t pn = lean_sarray_size(plain);
  if (in > UINT32_MAX || an > UINT32_MAX) return l4_hpke_empty();
  if (pn > UINT32_MAX - 16u) return l4_hpke_empty();
  lean_obj_res out = lean_alloc_sarray(1, 32 + pn + 16, 32 + pn + 16);
  uint8_t *o = lean_sarray_cptr(out);
  uint32_t err = Hacl_HPKE_Curve51_CP32_SHA256_sealBase(
      lean_sarray_cptr(skE), lean_sarray_cptr(pkR), (uint32_t)in,
      lean_sarray_cptr(info), (uint32_t)an, lean_sarray_cptr(aad),
      (uint32_t)pn, lean_sarray_cptr(plain), o, o + 32);
  if (err != 0u) {
    lean_free_object(out);
    return l4_hpke_empty();
  }
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_hpke_open_base(b_lean_obj_arg skR,
                                                b_lean_obj_arg info,
                                                b_lean_obj_arg aad,
                                                b_lean_obj_arg enc_ct) {
  if (lean_sarray_size(skR) != 32) return l4_hpke_empty();
  size_t in = lean_sarray_size(info), an = lean_sarray_size(aad);
  size_t n = lean_sarray_size(enc_ct);
  if (in > UINT32_MAX || an > UINT32_MAX) return l4_hpke_empty();
  if (n < 32 + 16) return l4_hpke_empty();
  size_t ctn = n - 32;              /* ciphertext || tag */
  size_t pn = ctn - 16;             /* plaintext */
  if (ctn > UINT32_MAX) return l4_hpke_empty();
  lean_obj_res out = lean_alloc_sarray(1, pn + 1, pn + 1);
  uint8_t *o = lean_sarray_cptr(out);
  uint8_t *b = lean_sarray_cptr(enc_ct);
  uint32_t err = Hacl_HPKE_Curve51_CP32_SHA256_openBase(
      b, lean_sarray_cptr(skR), (uint32_t)in, lean_sarray_cptr(info),
      (uint32_t)an, lean_sarray_cptr(aad), (uint32_t)ctn, b + 32, o);
  if (err != 0u) {
    memset(o, 0, pn);
    o[pn] = 0;
  } else {
    o[pn] = 1;
  }
  return out;
}
