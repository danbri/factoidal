/* hacl_ed25519.c — Lean 4 <-> C binding for the vendored HACL* Ed25519
 * and SHA-256 primitives (third_party/hacl/, Apache-2.0, hacl-packages
 * commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — see third_party/hacl/
 * PROVENANCE.md).  Realises the three `@[extern]` opaques of
 * L4Factoidal/Crypto/Ed25519.lean and the one of
 * L4Factoidal/Crypto/SHA2Native.lean.
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
 *   l4_hacl_sha256(msg)                               -> digest[32] | empty
 *   l4_hacl_sha256_blocks(state[32], data, offset, blocks) -> state[32] | empty
 * An EMPTY result (or 0 from verify) on a wrong-length input is a
 * refusal, never a crypto verdict; the Lean side documents the same.
 * For l4_hacl_sha256 the only refusal is a message longer than
 * UINT32_MAX bytes, which HACL*'s uint32_t length parameter cannot
 * express; the digest of a message it DOES accept is always 32 bytes,
 * so an empty result is unambiguously a refusal.
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
#include "Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA2.h"

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

/* SHA-256 (FIPS 180-4) for L4Factoidal/Crypto/SHA2Native.lean.  The pure
 * Lean sha256 in Crypto/SHA2.lean remains the specification and is what
 * every build-time guard and every theorem uses; this entry exists only
 * so a host can hash tens of megabytes of PUBLIC block bytes at C speed.
 * No cryptographic logic here: one length check, then HACL*. */
LEAN_EXPORT lean_obj_res l4_hacl_sha256(b_lean_obj_arg msg) {
  size_t n = lean_sarray_size(msg);
  if (n > UINT32_MAX) return l4_empty_bytes();
  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  Hacl_Hash_SHA2_hash_256(lean_sarray_cptr(out), lean_sarray_cptr(msg),
                          (uint32_t)n);
  return out;
}

/* The SHA-256 compression walk over `blocks` complete 64-byte blocks of
 * `data` starting at byte `offset`.  `st` is the eight-word chaining value
 * as 32 big-endian bytes and the result is the next chaining value in the
 * same form; HACL* keeps that value in HOST word order, so the two loops
 * below are the only arithmetic in this function and they are byte order
 * conversion, not hashing.  Refusals (empty result): a state that is not 32
 * bytes, a block run that leaves `data`, or a run above HACL*'s uint32_t
 * length.
 */
LEAN_EXPORT lean_obj_res l4_hacl_sha256_blocks(b_lean_obj_arg st,
                                               b_lean_obj_arg data,
                                               size_t offset, size_t blocks) {
  if (lean_sarray_size(st) != 32) return l4_empty_bytes();
  if (blocks > (size_t)(UINT32_MAX / 64U)) return l4_empty_bytes();
  size_t span = blocks * 64U;
  size_t n = lean_sarray_size(data);
  if (offset > n || span > n - offset) return l4_empty_bytes();

  uint32_t h[8];
  const uint8_t *sp = lean_sarray_cptr(st);
  for (int i = 0; i < 8; i++) {
    h[i] = ((uint32_t)sp[4 * i] << 24) | ((uint32_t)sp[4 * i + 1] << 16) |
           ((uint32_t)sp[4 * i + 2] << 8) | (uint32_t)sp[4 * i + 3];
  }

  Hacl_Hash_SHA2_sha256_update_nblocks((uint32_t)span,
                                       lean_sarray_cptr(data) + offset, h);

  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  uint8_t *op = lean_sarray_cptr(out);
  for (int i = 0; i < 8; i++) {
    op[4 * i] = (uint8_t)(h[i] >> 24);
    op[4 * i + 1] = (uint8_t)(h[i] >> 16);
    op[4 * i + 2] = (uint8_t)(h[i] >> 8);
    op[4 * i + 3] = (uint8_t)h[i];
  }
  return out;
}
