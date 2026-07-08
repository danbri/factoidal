/* Placeholder C stubs for js_of_ocaml bytecode linking of the VC crypto
 * primitives (fstar_hacl_crypto.ml's `external caml_hacl_*`).
 *
 * The ocamlc bytecode linker insists every `external ... = "caml_hacl_*"`
 * resolve to a real symbol at link time — even when the resulting .byte is
 * only fed to js_of_ocaml, which then replaces each primitive with the JS
 * shim in hacl_stubs.js (HACL* wasm backend) at bundle time.
 *
 * This file exists purely to satisfy that link-time check. If the bytecode
 * is ever run directly (outside js_of_ocaml), these return the failure
 * sentinels the F* wrapper VC.DataIntegrity already understands: "" for the
 * hex-producing entry points and false for verify. verify NEVER returns
 * true here — a bytecode missing its JS crypto runtime must not appear to
 * validate a signature.
 *
 * The *native* build (build-ocaml.sh compile) links the real
 * experimental_ocaml_glue/hacl_stubs.c (vendored HACL* C). This file must
 * NOT be compiled into the native binary — the symbols would collide.
 */
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

CAMLprim value caml_hacl_sha256(value v_msg) {
  (void)v_msg;
  return caml_copy_string("");
}

CAMLprim value caml_hacl_ed25519_secret_to_public(value v_sk_hex) {
  (void)v_sk_hex;
  return caml_copy_string("");
}

CAMLprim value caml_hacl_ed25519_sign(value v_sk_hex, value v_msg_hex) {
  (void)v_sk_hex;
  (void)v_msg_hex;
  return caml_copy_string("");
}

CAMLprim value caml_hacl_ed25519_verify(value v_pk_hex, value v_msg_hex,
                                        value v_sig_hex) {
  (void)v_pk_hex;
  (void)v_msg_hex;
  (void)v_sig_hex;
  return Val_bool(0);
}
