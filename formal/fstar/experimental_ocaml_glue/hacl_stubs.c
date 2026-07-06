/* hacl_stubs.c — OCaml <-> C FFI for the vendored HACL* Ed25519 + SHA-256
 * primitives (third_party/hacl/).  Realises the crypto assume-vals of
 * VC.DataIntegrity.fst (Verifiable Credentials eddsa-rdfc-2022 pipeline).
 *
 * Crypto sourcing policy: skills/crypto-policy/SKILL.md — "Dont roll our
 * own crypto!", "pursue HACL*".  This file contains NO cryptographic
 * logic: every primitive (Ed25519 sign/verify/keygen, SHA-256) is a call
 * into the vendored, F-star/Low-star-verified HACL* extracted C.  The only
 * logic here is hex <-> byte marshalling around the OCaml string boundary, the
 * same shape as experimental_ocaml_glue/parquet_zstd_stubs.c.
 *
 * Boundary contract (all hex is lowercase, no 0x prefix):
 *   caml_hacl_sha256(msg_bytes)                -> 64-char hex digest
 *   caml_hacl_ed25519_secret_to_public(sk_hex) -> pk_hex (64 chars) | ""
 *   caml_hacl_ed25519_sign(sk_hex, msg_hex)    -> sig_hex (128 chars) | ""
 *   caml_hacl_ed25519_verify(pk_hex,msg_hex,sig_hex) -> bool
 * An empty-string return signals a malformed-length/odd-hex input (the
 * F* wrapper treats that as failure); it never signals a crypto verdict.
 */
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

#include "Hacl_Ed25519.h"
#include "Hacl_Hash_SHA2.h"

static const char HEXD[] = "0123456789abcdef";

static int hex_nibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
  if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
  return -1;
}

/* Decode a hex OCaml string into a freshly malloc'd byte buffer.
 * Returns 1 on success (sets *out and *out_len), 0 on odd length or a
 * non-hex digit. Caller frees *out on success. */
static int hex_decode(value v_hex, unsigned char **out, size_t *out_len) {
  const char *hex = String_val(v_hex);
  size_t hex_len = caml_string_length(v_hex);
  if ((hex_len % 2) != 0) return 0;
  size_t n = hex_len / 2;
  unsigned char *buf = (unsigned char *)malloc(n ? n : 1);
  if (buf == NULL) caml_failwith("hacl_stubs: allocation failure");
  for (size_t i = 0; i < n; i++) {
    int hi = hex_nibble(hex[2 * i]);
    int lo = hex_nibble(hex[2 * i + 1]);
    if (hi < 0 || lo < 0) { free(buf); return 0; }
    buf[i] = (unsigned char)((hi << 4) | lo);
  }
  *out = buf;
  *out_len = n;
  return 1;
}

/* Encode raw bytes into a fresh OCaml hex string. */
static value hex_encode(const unsigned char *bytes, size_t len) {
  CAMLparam0();
  CAMLlocal1(v_out);
  v_out = caml_alloc_string(len * 2);
  unsigned char *dst = Bytes_val(v_out);
  for (size_t i = 0; i < len; i++) {
    dst[2 * i]     = (unsigned char)HEXD[(bytes[i] >> 4) & 0xF];
    dst[2 * i + 1] = (unsigned char)HEXD[bytes[i] & 0xF];
  }
  CAMLreturn(v_out);
}

/* SHA-256 of the raw bytes of the OCaml string argument. */
CAMLprim value caml_hacl_sha256(value v_msg) {
  CAMLparam1(v_msg);
  CAMLlocal1(v_out);
  uint8_t digest[32];
  /* HACL takes a non-const uint8_t*; String_val is safe to read from. */
  Hacl_Hash_SHA2_hash_256(digest, (uint8_t *)String_val(v_msg),
                          (uint32_t)caml_string_length(v_msg));
  v_out = hex_encode(digest, 32);
  CAMLreturn(v_out);
}

/* Ed25519 private key (32 bytes, hex) -> public key (32 bytes, hex). */
CAMLprim value caml_hacl_ed25519_secret_to_public(value v_sk_hex) {
  CAMLparam1(v_sk_hex);
  CAMLlocal1(v_out);
  unsigned char *sk = NULL; size_t sk_len = 0;
  if (!hex_decode(v_sk_hex, &sk, &sk_len) || sk_len != 32) {
    if (sk) free(sk);
    CAMLreturn(caml_copy_string(""));
  }
  uint8_t pk[32];
  Hacl_Ed25519_secret_to_public(pk, sk);
  free(sk);
  v_out = hex_encode(pk, 32);
  CAMLreturn(v_out);
}

/* Ed25519 sign: (sk_hex[32B], msg_hex) -> signature hex (64 bytes). */
CAMLprim value caml_hacl_ed25519_sign(value v_sk_hex, value v_msg_hex) {
  CAMLparam2(v_sk_hex, v_msg_hex);
  CAMLlocal1(v_out);
  unsigned char *sk = NULL, *msg = NULL; size_t sk_len = 0, msg_len = 0;
  if (!hex_decode(v_sk_hex, &sk, &sk_len) || sk_len != 32) {
    if (sk) free(sk);
    CAMLreturn(caml_copy_string(""));
  }
  if (!hex_decode(v_msg_hex, &msg, &msg_len)) {
    free(sk);
    CAMLreturn(caml_copy_string(""));
  }
  uint8_t sig[64];
  Hacl_Ed25519_sign(sig, sk, (uint32_t)msg_len, msg);
  free(sk); free(msg);
  v_out = hex_encode(sig, 64);
  CAMLreturn(v_out);
}

/* Ed25519 verify: (pk_hex[32B], msg_hex, sig_hex[64B]) -> bool. */
CAMLprim value caml_hacl_ed25519_verify(value v_pk_hex, value v_msg_hex,
                                        value v_sig_hex) {
  CAMLparam3(v_pk_hex, v_msg_hex, v_sig_hex);
  unsigned char *pk = NULL, *msg = NULL, *sig = NULL;
  size_t pk_len = 0, msg_len = 0, sig_len = 0;
  int ok = 0;
  if (hex_decode(v_pk_hex, &pk, &pk_len) && pk_len == 32 &&
      hex_decode(v_msg_hex, &msg, &msg_len) &&
      hex_decode(v_sig_hex, &sig, &sig_len) && sig_len == 64) {
    ok = Hacl_Ed25519_verify(pk, (uint32_t)msg_len, msg, sig) ? 1 : 0;
  }
  if (pk) free(pk);
  if (msg) free(msg);
  if (sig) free(sig);
  CAMLreturn(Val_bool(ok));
}
