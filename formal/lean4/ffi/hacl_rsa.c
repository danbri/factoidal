/* hacl_rsa.c — Lean 4 <-> C binding for the RSA PUBLIC operation over the
 * vendored HACL* generic 64-bit bignum field (third_party/hacl/,
 * Apache-2.0, hacl-packages commit
 * 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see third_party/hacl/
 * PROVENANCE.md).  Realises the `@[extern]` opaque of
 * L4Factoidal/Crypto/RsaNative.lean.
 *
 * WHAT IS EXPOSED, AND WHAT IS NOT.  Only RSAVP1 (RFC 8017 section 5.2.2),
 * the PUBLIC verification primitive s^e mod n.  There is no private
 * operation, no key generation and no signing entry point in this file,
 * so no secret ever reaches this translation unit.
 *
 * WHY VARIABLE TIME IS ACCEPTABLE.  Hacl_Bignum64_mod_exp_vartime is not
 * constant time in the exponent.  Here the exponent is the RSA PUBLIC
 * exponent e and the base is the signature s; both are published values
 * carried in the JWS and the JWK.  A timing observer learns nothing that
 * is not already in the token.  The constant-time variant
 * (mod_exp_consttime) is the one to use if a private exponent is ever
 * added, which this file forbids by construction.
 *
 * NO PADDING LOGIC HERE.  EMSA-PKCS1-v1_5 encoding and the comparison
 * against it are pure Lean (L4Factoidal/JOSE/Pkcs1.lean), where they
 * carry theorems.  This file returns the raw k-byte integer and makes no
 * decision about whether a signature is valid.  That split is deliberate:
 * the Bleichenbacher 2006 forgery class comes from LENIENT PARSING of the
 * padding, so the padding is never parsed anywhere — it is generated and
 * compared for full-length byte equality in Lean.
 *
 * Boundary contract:
 *   l4_hacl_rsa_public_op(n, e, s) -> res[k] | empty
 * where k = n.size.  The EMPTY ByteArray is a refusal, never a result:
 *   * k not 256, 384 or 512 bytes (2048, 3072 or 4096 bits);
 *   * s.size != k, or e empty, or e longer than k;
 *   * e with no set bit;
 *   * allocation failure;
 *   * HACL* rejecting its own preconditions (n even, n <= 1, or s >= n —
 *     the last is RFC 8017's "signature representative out of range").
 * A successful result is always exactly k bytes, so a caller
 * distinguishes a refusal by size.
 *
 * Memory: arguments are BORROWED; the three heap bignums allocated by
 * Hacl_Bignum64_new_bn_from_bytes_be and the result limb array are freed
 * on every exit path.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Bignum64.h"

static lean_obj_res l4_rsa_empty(void) { return lean_alloc_sarray(1, 0, 0); }

/* Number of significant bits of a big-endian byte string.  Byte counting,
 * not arithmetic on a secret: e is public. */
static uint32_t l4_be_bit_length(const uint8_t *b, size_t n) {
  size_t i = 0;
  while (i < n && b[i] == 0) i++;
  if (i == n) return 0;
  uint32_t bits = (uint32_t)((n - i - 1) * 8);
  uint8_t top = b[i];
  while (top != 0) { bits++; top >>= 1; }
  return bits;
}

LEAN_EXPORT lean_obj_res l4_hacl_rsa_public_op(b_lean_obj_arg n_ba,
                                               b_lean_obj_arg e_ba,
                                               b_lean_obj_arg s_ba) {
  size_t k = lean_sarray_size(n_ba);
  if (k != 256 && k != 384 && k != 512) return l4_rsa_empty();
  if (lean_sarray_size(s_ba) != k) return l4_rsa_empty();
  size_t elen = lean_sarray_size(e_ba);
  if (elen == 0 || elen > k) return l4_rsa_empty();

  uint32_t e_bits = l4_be_bit_length(lean_sarray_cptr(e_ba), elen);
  if (e_bits == 0) return l4_rsa_empty();

  uint32_t n_limbs = (uint32_t)(k / 8);
  uint32_t e_limbs = (e_bits + 63U) / 64U;

  /* Right-align e in a limb-multiple big-endian buffer so that
   * new_bn_from_bytes_be yields exactly e_limbs limbs. */
  size_t e_pad = (size_t)e_limbs * 8U;
  uint8_t *e_buf = (uint8_t *)calloc(e_pad, 1);
  if (e_buf == NULL) return l4_rsa_empty();
  memcpy(e_buf + (e_pad - elen), lean_sarray_cptr(e_ba), elen);

  uint64_t *bn_n = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(n_ba));
  uint64_t *bn_s = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)k, lean_sarray_cptr(s_ba));
  uint64_t *bn_e = Hacl_Bignum64_new_bn_from_bytes_be((uint32_t)e_pad, e_buf);
  uint64_t *bn_r = (uint64_t *)calloc(n_limbs, sizeof(uint64_t));

  lean_obj_res out;
  if (bn_n == NULL || bn_s == NULL || bn_e == NULL || bn_r == NULL) {
    out = l4_rsa_empty();
  } else if (!Hacl_Bignum64_mod_exp_vartime(n_limbs, bn_n, bn_s, e_bits, bn_e, bn_r)) {
    out = l4_rsa_empty();
  } else {
    out = lean_alloc_sarray(1, k, k);
    Hacl_Bignum64_bn_to_bytes_be((uint32_t)k, bn_r, lean_sarray_cptr(out));
  }

  free(e_buf);
  free(bn_n);
  free(bn_s);
  free(bn_e);
  free(bn_r);
  return out;
}
