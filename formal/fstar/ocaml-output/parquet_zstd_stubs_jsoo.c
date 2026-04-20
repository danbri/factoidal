/* Placeholder C stub for js_of_ocaml bytecode linking.
 *
 * The ocamlc bytecode linker insists that every external primitive
 * declared via `external ... = "caml_parquet_zstd_decompress_hex"` be
 * bound to a real symbol at link time — even when the resulting .byte
 * is only going to be fed to js_of_ocaml, which then replaces the
 * primitive with the JS shim in parquet_zstd_stubs.js at bundle time.
 *
 * This file exists purely to satisfy that link-time check. It returns
 * OCaml None unconditionally; if the bytecode is ever executed
 * directly (outside js_of_ocaml / the browser), Parquet_Footer will
 * observe None and surface "Could not read COTTAS row count" up the
 * stack, which is honest behaviour for a bytecode missing its JS
 * runtime.
 *
 * The *native* build (build-ocaml.sh compile) links the real
 * experimental_ocaml_glue/parquet_zstd_stubs.c, which calls into
 * libzstd. This file must NOT be compiled into the native binary —
 * the symbol would collide at link time.
 */

#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

CAMLprim value caml_parquet_zstd_decompress_hex(value v_hex, value v_expected_size) {
  (void)v_hex;
  (void)v_expected_size;
  /* OCaml None encoding is the int 0. */
  return Val_int(0);
}
