#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <string.h>
#include <stdlib.h>
#include <zstd.h>

static int hex_nibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
  if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
  return -1;
}

CAMLprim value caml_parquet_zstd_decompress_hex(value v_hex, value v_expected_size) {
  CAMLparam2(v_hex, v_expected_size);
  CAMLlocal2(v_some, v_out);

  const char *hex = String_val(v_hex);
  mlsize_t hex_len = caml_string_length(v_hex);
  if ((hex_len % 2) != 0) CAMLreturn(Val_int(0));

  size_t compressed_len = (size_t)(hex_len / 2);
  char *expected_end = NULL;
  unsigned long expected_ul = strtoul(String_val(v_expected_size), &expected_end, 10);
  size_t expected_size = (size_t)expected_ul;
  if (expected_end == String_val(v_expected_size) || *expected_end != '\0') {
    CAMLreturn(Val_int(0));
  }
  unsigned char *compressed = (unsigned char *)malloc(compressed_len);
  unsigned char *out = (unsigned char *)malloc(expected_size);
  char *out_hex = NULL;

  if (compressed == NULL || out == NULL) {
    free(compressed);
    free(out);
    caml_failwith("parquet_zstd_decompress_hex: allocation failure");
  }

  for (size_t i = 0; i < compressed_len; i++) {
    int hi = hex_nibble(hex[i * 2]);
    int lo = hex_nibble(hex[i * 2 + 1]);
    if (hi < 0 || lo < 0) {
      free(compressed);
      free(out);
      CAMLreturn(Val_int(0));
    }
    compressed[i] = (unsigned char)((hi << 4) | lo);
  }

  size_t actual = ZSTD_decompress(out, expected_size, compressed, compressed_len);
  free(compressed);
  if (ZSTD_isError(actual) || actual != expected_size) {
    free(out);
    CAMLreturn(Val_int(0));
  }

  out_hex = (char *)malloc(actual * 2);
  if (out_hex == NULL) {
    free(out);
    caml_failwith("parquet_zstd_decompress_hex: output allocation failure");
  }

  static const char hexdigits[] = "0123456789ABCDEF";
  for (size_t i = 0; i < actual; i++) {
    out_hex[i * 2] = hexdigits[(out[i] >> 4) & 0xF];
    out_hex[i * 2 + 1] = hexdigits[out[i] & 0xF];
  }
  free(out);

  v_out = caml_alloc_string(actual * 2);
  memcpy(Bytes_val(v_out), out_hex, actual * 2);
  free(out_hex);

  v_some = caml_alloc(1, 0);
  Store_field(v_some, 0, v_out);
  CAMLreturn(v_some);
}
