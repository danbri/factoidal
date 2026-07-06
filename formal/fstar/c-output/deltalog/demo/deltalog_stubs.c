/* Hand-written C realisations for the krmllib string/char primitives
 * that karamel's dist/generic/{fstar_string,fstar_char}.c do not
 * implement — the same gap the Group A pilot hit
 * (c-output/demo/factoidal_pilot_stubs.c), just a different subset of
 * missing functions (this module calls `String.list_of_string`,
 * `String.string_of_list`, `String.index`, and `FStar.Char.u32_of_char`
 * rather than the pilot's `lowercase`/`sub`).
 *
 * ASCII-first, UTF-8-correct decode: `FStar_String_strlen` (krmllib's
 * own implementation, unmodified) counts codepoints by skipping UTF-8
 * continuation bytes, so `list_of_string`/`index` decode multi-byte
 * sequences properly rather than assuming one byte per codepoint —
 * every real caller in this bundle (IRIs, RDF literals) is ASCII in
 * practice, but a non-ASCII string would decode correctly here rather
 * than silently mis-splitting.
 *
 * Strings/lists are malloc'd and never freed — same GC-less
 * compatibility mode the Group A pilot demo runs in (short-lived CLI
 * process, not a library).
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "krmllib.h"
#include "krml/internal/compat.h"
#include "Factoidal_DeltaLog.h"

/* Same layout as the generated `Prims_list__FStar_Char_char` cons cell
 * (Factoidal_DeltaLog.h) — aliased locally as `fc_list` so this file's
 * loop/build logic can use plain field names without the generated
 * struct's longer type name at every site. Included from the real
 * header (not redeclared) so there is exactly one struct definition,
 * no layout-mismatch risk between this stub and the generated code. */
typedef struct Prims_list__FStar_Char_char_s fc_list;

/* Decode one UTF-8 codepoint starting at s[i]; returns the codepoint
 * and advances *consumed by its byte width (1-4). Malformed leading
 * bytes are treated as a single raw byte (never crashes on bad input;
 * this bundle only ever feeds it well-formed F* string literals /
 * ASCII IRIs). */
static uint32_t utf8_decode_one(const unsigned char *s, size_t i, size_t len,
                                 size_t *consumed) {
  unsigned char b0 = s[i];
  if (b0 < 0x80) {
    *consumed = 1;
    return b0;
  } else if ((b0 & 0xE0) == 0xC0 && i + 1 < len) {
    *consumed = 2;
    return ((uint32_t)(b0 & 0x1F) << 6) | (s[i + 1] & 0x3F);
  } else if ((b0 & 0xF0) == 0xE0 && i + 2 < len) {
    *consumed = 3;
    return ((uint32_t)(b0 & 0x0F) << 12) | ((uint32_t)(s[i + 1] & 0x3F) << 6) |
           (s[i + 2] & 0x3F);
  } else if ((b0 & 0xF8) == 0xF0 && i + 3 < len) {
    *consumed = 4;
    return ((uint32_t)(b0 & 0x07) << 18) | ((uint32_t)(s[i + 1] & 0x3F) << 12) |
           ((uint32_t)(s[i + 2] & 0x3F) << 6) | (s[i + 3] & 0x3F);
  }
  *consumed = 1;
  return b0;
}

Prims_list__FStar_Char_char *FStar_String_list_of_string(Prims_string s) {
  size_t len = strlen(s);
  /* Decode all codepoints into a scratch array first (unknown count
   * ahead of time for multi-byte input), then build the linked list
   * tail-to-head so the final list is in forward (first-codepoint-
   * first) order. */
  uint32_t *cps = KRML_HOST_MALLOC(sizeof(uint32_t) * (len + 1));
  size_t n = 0;
  size_t i = 0;
  while (i < len) {
    size_t consumed;
    cps[n++] = utf8_decode_one((const unsigned char *)s, i, len, &consumed);
    i += consumed;
  }
  /* krml represents Nil as a real allocated node (tag = Prims_Nil),
   * never a bare NULL pointer (confirmed by grepping the generated
   * `Factoidal_DeltaLog.c` for its own `[]` literals: `(Prims_list...){
   * .tag = Prims_Nil }`) — every list must terminate in one of these,
   * including a non-empty one, or the generated recursive walkers
   * (`FStar_List_Tot_Base_length`, `parse_lstring`'s byte consumption,
   * etc.) dereference NULL/garbage past the true end and crash. This
   * bug was caught by exactly that: the very first demo run segfaulted
   * inside `length__FStar_Char_char` recursing off the end of a
   * `serialize_lstring`-produced list built by an earlier, buggy
   * version of this function that left the last cons cell's `tl` as a
   * bare NULL. */
  fc_list *acc = KRML_HOST_MALLOC(sizeof(fc_list));
  acc->tag = 0;
  for (size_t k = n; k > 0; k--) {
    fc_list *node = KRML_HOST_MALLOC(sizeof(fc_list));
    node->tag = 1;
    node->hd = cps[k - 1];
    node->tl = acc;
    acc = node;
  }
  return (Prims_list__FStar_Char_char *)acc;
}

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

Prims_string FStar_String_string_of_list(Prims_list__FStar_Char_char *l) {
  size_t count = 0;
  for (fc_list *p = (fc_list *)l; p != NULL && p->tag == 1; p = p->tl) count++;
  char *out = KRML_HOST_MALLOC(4 * count + 1);
  size_t pos = 0;
  for (fc_list *p = (fc_list *)l; p != NULL && p->tag == 1; p = p->tl)
    pos += utf8_encode(p->hd, out + pos);
  out[pos] = '\0';
  return out;
}

/* nth (0-based) codepoint of s, decoding UTF-8 correctly rather than
 * assuming byte-per-codepoint — matches `FStar_String_strlen`'s own
 * continuation-byte-aware count so `index`/`length` agree. Precondition
 * (n < String.length s) is the caller's, per the F* signature; this
 * stub does not re-check it (same trust boundary as krmllib's own
 * `FStar_String_index_of`/`substring`, which also don't bounds-check). */
FStar_Char_char FStar_String_index(Prims_string s, krml_checked_int_t n) {
  size_t len = strlen(s);
  size_t i = 0;
  krml_checked_int_t cp_idx = 0;
  while (i < len) {
    size_t consumed;
    uint32_t cp = utf8_decode_one((const unsigned char *)s, i, len, &consumed);
    if (cp_idx == n) return cp;
    cp_idx++;
    i += consumed;
  }
  return 0;
}

/* FStar_Char_char IS already the uint32 codepoint representation
 * (krml/internal/types.h: `typedef uint32_t FStar_Char_char`) — same
 * identity krmllib's own `FStar_Char_char_of_u32` gives in the other
 * direction (fstar_char.c: `return x;`). */
uint32_t FStar_Char_u32_of_char(FStar_Char_char c) { return c; }
