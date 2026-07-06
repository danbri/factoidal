/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 and MIT Licenses.

   Factoidal-local override of karamel's krml/internal/compat.h.

   Why this exists: RDF.Store.Columnar.DeltaLog.fst is written against
   F*'s unbounded mathematical `nat`/`int` (not machine `FStar.UInt32.t`/
   `UInt64.t`) for its wire-format magic numbers, u32 length fields, the
   byte-shift decomposition in `write_u64_le`/`parse_u64_le` (divisors up
   to 2^56), AND `delta_batch_ok`'s own `db_seq < 2^64 && db_epoch < 2^64`
   well-formedness bound. krml's stock `compat.h` (the "porting shim" for
   non-Low* code) types `Prims.nat`/`Prims.int` as `int32_t`, which
   silently truncates any C literal >= 2^31 the generated code passes to
   a `Prims_op_*` call. Confirmed empirically two ways
   (tools/karamel-c-build.sh --group-c dry runs, 2026-07-06):

     1. With the stock int32_t width: the `4294967296` (2^32)
        overflow-guard literal in `serialize_lstring`/
        `serialize_delta_entry` narrows to `0` at the call site, turning
        `n >= 2^32` into `n >= 0` (always true — every string would hit
        the "too long" branch and serialize to `[]`); `write_u64_le`'s
        `n / 4294967296`-style divisions become divide-by-zero traps.
     2. Widening only to int64_t is NOT enough: `delta_batch_ok`'s
        `db_seq < 18446744073709551616` (2^64) literal still exceeds
        int64_t's range (max ~9.2e18 vs the literal's ~1.8e19) — gcc's
        own "-Woverflow"/"integer constant is too large for its type"
        warnings on that build confirmed the truncation was still live;
        the demo's `delta_batch_ok` check failed for exactly this reason.

   Fix: widen `krml_checked_int_t` (and the `Prims.{pos,nat,nonzero,
   int}` aliases) to `__int128` (gcc/clang x86_64 extension), which
   comfortably represents every literal this module's generated C
   actually contains, including the 2^64 bound check — no C integer
   literal in this bundle exceeds __int128's ~1.7e38 range. This header
   is used ONLY for the DeltaLog C-build group
   (tools/karamel-c-build.sh's `-I` precedence puts this directory ahead
   of $KRML_HOME/include) — it does not touch karamel's own installed
   copy, and every object file linked into the DeltaLog demo binary is
   recompiled fresh against this header (never mixed with the
   int32-width objects the Group A pilot demo uses).

   A residual friction point remains even at this width: the literal
   `18446744073709551615` (2^64 - 1, `u64_max_nat` in the .fst) is
   itself ULLONG_MAX — gcc's front end still stamps it as `unsigned
   long long` (the widest STANDARD C integer type any literal without
   an explicit `__int128`-producing expression can have) and warns
   "integer constant is so large that it is unsigned" at the point
   where it initializes the `krml_checked_int_t` (signed __int128)
   global, then converts. The VALUE survives the conversion correctly
   (unsigned long long -> signed __int128 is always exact — __int128
   has far more range), so this is a benign, disclosed warning, not a
   truncation bug like the two above. */

#ifndef KRML_COMPAT_H
#define KRML_COMPAT_H

#include <inttypes.h>

typedef struct {
  uint32_t length;
  const char *data;
} FStar_Bytes_bytes;

typedef __int128 Prims_pos, Prims_nat, Prims_nonzero, Prims_int,
    krml_checked_int_t;

/* No narrowing occurs at this width (every value this module's
   generated C computes is astronomically far from __int128's own
   range limit), so RETURN_OR is just a plain return — kept as a macro
   only so prims64.c's bodies read identically to upstream karamel's
   prims.c convention. */
#define RETURN_OR(x) return (x)

#endif
