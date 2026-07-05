/* Hand-written C realisations for the extern symbols left open by the
 * KaRaMeL pilot bundle (Factoidal_Pilot.c). Mirrors the OCaml glue that
 * realises the same `assume val`s on the OCaml extraction path.
 *
 * Two groups:
 *   1. Parser.FastString byte primitives (assume val in
 *      formal/fstar/Parser.FastString.fst — same trust boundary as the
 *      OCaml realisation, patch 89).
 *   2. FStar.String ulib primitives that krmllib's dist/generic does not
 *      implement (lowercase, sub, string_of_list).
 *
 * Caveats (pilot-grade, documented rather than hidden):
 *   - FStar_String_lowercase lowercases ASCII bytes only. The F* ulib
 *     spec is codepoint-based; every string RDF.Format compares against
 *     is ASCII, for which this is byte-identical.
 *   - FStar_String_sub indexes by byte, not codepoint. Callers in this
 *     bundle (SPARQL.HTTP.StaticFiles.ends_with) only pass ASCII.
 *   - FStar_String_string_of_list encodes codepoints as UTF-8.
 *   - Strings are malloc'd and never freed — same GC-less compatibility
 *     mode the rest of the krml -warn-error +2 pilot runs in.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "krmllib.h"
#include "krml/internal/compat.h"

/* ---- Group 1: Parser.FastString byte primitives ---- */

krml_checked_int_t Parser_FastString_fs_byte_length(Prims_string s) {
  return (krml_checked_int_t)strlen(s);
}

krml_checked_int_t Parser_FastString_fs_byte_at(Prims_string s,
                                                krml_checked_int_t i) {
  return (krml_checked_int_t)(uint8_t)s[i];
}

Prims_string Parser_FastString_fs_byte_sub(Prims_string s,
                                           krml_checked_int_t start,
                                           krml_checked_int_t len) {
  char *out = KRML_HOST_MALLOC((size_t)len + 1);
  memcpy(out, s + start, (size_t)len);
  out[len] = '\0';
  return out;
}

/* ---- Group 2: FStar.String primitives missing from krmllib ---- */

Prims_string FStar_String_lowercase(Prims_string s) {
  size_t n = strlen(s);
  char *out = KRML_HOST_MALLOC(n + 1);
  for (size_t i = 0; i < n; i++) {
    char c = s[i];
    out[i] = (c >= 'A' && c <= 'Z') ? (char)(c + 32) : c;
  }
  out[n] = '\0';
  return out;
}

Prims_string FStar_String_sub(Prims_string s, krml_checked_int_t i,
                              krml_checked_int_t l) {
  char *out = KRML_HOST_MALLOC((size_t)l + 1);
  memcpy(out, s + i, (size_t)l);
  out[l] = '\0';
  return out;
}

/* The generated code's list__FStar_Char_char is a tagged cons cell;
 * declare a structurally identical local copy (the generated definition
 * lives inside Factoidal_Pilot.c, not its header). */
typedef struct demo_char_list_s {
  uint8_t tag; /* 0 = Nil, 1 = Cons */
  uint32_t hd; /* FStar_Char_char = uint32 codepoint */
  struct demo_char_list_s *tl;
} demo_char_list;

static size_t utf8_encode(uint32_t cp, char *out) {
  if (cp < 0x80) {
    out[0] = (char)cp;
    return 1;
  } else if (cp < 0x800) {
    out[0] = (char)(0xC0 | (cp >> 6));
    out[1] = (char)(0x80 | (cp & 0x3F));
    return 2;
  } else if (cp < 0x10000) {
    out[0] = (char)(0xE0 | (cp >> 12));
    out[1] = (char)(0x80 | ((cp >> 6) & 0x3F));
    out[2] = (char)(0x80 | (cp & 0x3F));
    return 3;
  } else {
    out[0] = (char)(0xF0 | (cp >> 18));
    out[1] = (char)(0x80 | ((cp >> 12) & 0x3F));
    out[2] = (char)(0x80 | ((cp >> 6) & 0x3F));
    out[3] = (char)(0x80 | (cp & 0x3F));
    return 4;
  }
}

Prims_string FStar_String_string_of_list(void *l) {
  /* Worst case 4 bytes per codepoint. */
  size_t count = 0;
  for (demo_char_list *p = l; p != NULL && p->tag == 1; p = p->tl) count++;
  char *out = KRML_HOST_MALLOC(4 * count + 1);
  size_t pos = 0;
  for (demo_char_list *p = l; p != NULL && p->tag == 1; p = p->tl)
    pos += utf8_encode(p->hd, out + pos);
  out[pos] = '\0';
  return out;
}
