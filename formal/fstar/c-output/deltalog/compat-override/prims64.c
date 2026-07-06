/* Factoidal-local replacement for karamel's krmllib/dist/generic/prims.c,
 * recompiled against this directory's widened compat.h (__int128
 * `krml_checked_int_t` instead of the stock int32_t) — see compat.h's
 * banner for why. Function bodies are otherwise identical to upstream
 * karamel's prims.c; only the parameter/return types changed from
 * `int32_t` to `krml_checked_int_t` (which this same translation unit's
 * compat.h now defines as `__int128`) so the two match.
 *
 * `Prims_string_of_int`/`Prims_string_of_bool` (upstream prims.c's
 * other exports) are omitted: RDF.Store.Columnar.DeltaLog's extracted
 * C never calls them (grepped the generated header/`.c` — only
 * `__eq__Prims_string`, `Prims_strcat` (transitively, via krmllib's own
 * `fstar_string.c`), and the arithmetic/comparison ops below are
 * referenced), so there is nothing to widen for those and pulling in
 * FStar_Int32.h's own object just to satisfy an unused extern would add
 * a second recompiled copy of that module for no reason.
 */

#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#include "krmllib.h"

bool __eq__Prims_string(Prims_string s1, Prims_string s2) {
  return (strcmp(s1, s2) == 0);
}

/* Pulled in transitively by krmllib's own fstar_string.c
 * (`FStar_String_strcat` delegates to this) even though this bundle's
 * call graph never reaches it — included so the link succeeds without
 * needing `--gc-sections` bookkeeping. */
Prims_string Prims_strcat(Prims_string s0, Prims_string s1) {
  size_t len = strlen(s0) + strlen(s1) + 1;
  char *dest = KRML_HOST_CALLOC(len, 1);
  strcat(dest, s0);
  strcat(dest, s1);
  return (Prims_string)dest;
}

bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) {
  return x >= y;
}

bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) {
  return x <= y;
}

bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y) {
  return x > y;
}

bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y) {
  return x < y;
}

krml_checked_int_t Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((__int128)x * (__int128)y);
}

krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((__int128)x + (__int128)y);
}

krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((__int128)x - (__int128)y);
}

krml_checked_int_t Prims_op_Division(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((__int128)x / (__int128)y);
}

krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((__int128)x % (__int128)y);
}

krml_checked_int_t Prims_op_Minus(krml_checked_int_t x) {
  RETURN_OR(-(__int128)x);
}
