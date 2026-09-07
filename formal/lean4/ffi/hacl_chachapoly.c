/* hacl_chachapoly.c — Lean 4 <-> C binding for the vendored HACL*
 * ChaCha20-Poly1305 AEAD (RFC 8439), third_party/hacl/, Apache-2.0,
 * hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see
 * third_party/hacl/PROVENANCE.md.  Realises the `@[extern]` opaques of
 * L4Factoidal/Crypto/ChaChaPoly.lean.
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md.  There is NO
 * cryptographic logic in this file.  The only logic is length checking
 * around Lean's ByteArray (a `lean_sarray` of uint8) and the split of a
 * combined `ciphertext || tag` buffer, which is the shape every AEAD
 * caller in this tree uses (OMEMO, MLS and HPKE all carry the tag
 * appended to the ciphertext) while HACL* takes the tag separately.
 * That split is a pointer offset, not a re-encoding.
 *
 * Boundary contract:
 *   l4_hacl_chachapoly_seal(key[32], nonce[12], aad, plain)
 *       -> ciphertext || tag  (plain.size + 16 bytes), or EMPTY on a
 *          length refusal.
 *   l4_hacl_chachapoly_open(key[32], nonce[12], aad, ct_with_tag)
 *       -> ByteArray of size plaintext.size + 1, whose LAST byte is 1
 *          on success and 0 on authentication failure, or EMPTY on a
 *          length refusal.
 *
 * Why `open` returns a success flag inside the buffer rather than an
 * Option: Lean's C FFI for a sum type over ByteArray needs a constructor
 * allocation the shim would have to build by hand.  A trailing status
 * byte keeps the shim to plumbing, and `Crypto/ChaChaPoly.lean` turns it
 * back into an `Option ByteArray` in Lean, where the wrapper is checked
 * by the compiler.  A refusal (EMPTY) and a failed tag (last byte 0) are
 * distinguishable, and NEITHER can be mistaken for a plaintext: an empty
 * result never carries a status byte at all.
 *
 * The tag comparison is HACL*'s own (Hacl_AEAD_Chacha20Poly1305_decrypt),
 * which returns 1 on failure without writing the output buffer.  This
 * file does not compare tags and must never grow a comparison: a
 * hand-written one would not be constant time.
 *
 * Memory: every argument is BORROWED (`@&` on the Lean side), so nothing
 * is dec-ref'd here; results are fresh Lean objects owned by the caller.
 * HACL* takes non-const `uint8_t *` for its inputs but does not write
 * through them.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"

static lean_obj_res l4_cp_empty(void) { return lean_alloc_sarray(1, 0, 0); }

LEAN_EXPORT lean_obj_res l4_hacl_chachapoly_seal(b_lean_obj_arg key,
                                                 b_lean_obj_arg nonce,
                                                 b_lean_obj_arg aad,
                                                 b_lean_obj_arg plain) {
  if (lean_sarray_size(key) != 32) return l4_cp_empty();
  if (lean_sarray_size(nonce) != 12) return l4_cp_empty();
  size_t pn = lean_sarray_size(plain);
  size_t an = lean_sarray_size(aad);
  if (pn > UINT32_MAX - 16u) return l4_cp_empty();
  if (an > UINT32_MAX) return l4_cp_empty();
  lean_obj_res out = lean_alloc_sarray(1, pn + 16, pn + 16);
  uint8_t *o = lean_sarray_cptr(out);
  Hacl_AEAD_Chacha20Poly1305_encrypt(o, o + pn, lean_sarray_cptr(plain),
                                     (uint32_t)pn, lean_sarray_cptr(aad),
                                     (uint32_t)an, lean_sarray_cptr(key),
                                     lean_sarray_cptr(nonce));
  return out;
}

LEAN_EXPORT lean_obj_res l4_hacl_chachapoly_open(b_lean_obj_arg key,
                                                 b_lean_obj_arg nonce,
                                                 b_lean_obj_arg aad,
                                                 b_lean_obj_arg ct) {
  if (lean_sarray_size(key) != 32) return l4_cp_empty();
  if (lean_sarray_size(nonce) != 12) return l4_cp_empty();
  size_t cn = lean_sarray_size(ct);
  size_t an = lean_sarray_size(aad);
  if (cn < 16) return l4_cp_empty();
  if (an > UINT32_MAX) return l4_cp_empty();
  size_t pn = cn - 16;
  if (pn > UINT32_MAX) return l4_cp_empty();
  lean_obj_res out = lean_alloc_sarray(1, pn + 1, pn + 1);
  uint8_t *o = lean_sarray_cptr(out);
  uint8_t *c = lean_sarray_cptr(ct);
  uint32_t err = Hacl_AEAD_Chacha20Poly1305_decrypt(
      o, c, (uint32_t)pn, lean_sarray_cptr(aad), (uint32_t)an,
      lean_sarray_cptr(key), lean_sarray_cptr(nonce), c + pn);
  if (err != 0u) {
    /* HACL* leaves `o` unchanged on failure; zero it so a caller that
     * ignores the status byte cannot read uninitialised memory. */
    memset(o, 0, pn);
    o[pn] = 0;
  } else {
    o[pn] = 1;
  }
  return out;
}
