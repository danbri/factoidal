# Issue #252 — `lemma_parse_write_u64_le_inverse` proof sketch (and verified proof)

**Date:** 2026-05-10
**Tracker:** GitHub issue #252
**Module:** `formal/fstar/RDF.Bytes.fst`
**Status (as of this doc):** the lemma is `admit ()` in production. This
note documents a fully verified replacement, exercised end-to-end via the
`fstar-mcp` daemon and a batch `fstar.exe` rerun
(`real 0m8.764s`, `--z3version 4.13.3`, no `--lax`, no admits).

The work below is a research/MCP-iteration artefact only. **No edits have
been made to `RDF.Bytes.fst`** — landing the proof is a follow-up the
tracker issue should request explicitly so the writer-family checked-file
cascade is scheduled.

---

## 1. The proof goal

From `formal/fstar/RDF.Bytes.fst:221-225`:

```fstar
let lemma_parse_write_u64_le_inverse
  (n : nat{n < 18446744073709551616}) (rest : bytes)
  : Lemma (ensures parse_u64_le (FStar.List.Tot.append (write_u64_le n) rest)
                   == Some (n, rest))
  = admit ()
```

`write_u64_le n` returns the 8-byte LE encoding
`[n%256; (n/256)%256; ...; (n/2^56)%256]` (each `byte_of_int`-wrapped).
`parse_u64_le` is the inverse: it pattern-matches 8 bytes and computes the
LE integer sum
`b0 + b1·2^8 + b2·2^16 + b3·2^24 + b4·2^32 + b5·2^40 + b6·2^48 + b7·2^56`.

The bare-SMT failure mode (per #252 comment): z3 4.13.3 stalls in a
quantifier matching loop at 0% CPU for 20+ minutes even at rlimit 200.
The 4-byte u32 sibling, structurally identical, discharges in
`lemma_parse_write_u32_le_inverse` with `()`.

Preconditions: `n < 2^64`. No requires beyond the type refinement.
`rest` is universally quantified.

---

## 2. The decomposition sub-lemma

Decompose `n = lo + hi * 2^32` with `lo = n % 2^32`, `hi = n / 2^32`.
Then `write_u64_le n` is byte-equal to
`write_u32_le lo @ write_u32_le hi`.

The **F\* code that verified** (in `/tmp/U64_attempt.fst` via the
fstar-mcp daemon, and re-verified by direct `fstar.exe` invocation
in 8.7 s):

```fstar
let lemma_write_u64_le_decompose (n : nat{n < 18446744073709551616})
  : Lemma (requires True)
          (ensures (
            let lo : nat = n % 4294967296 in
            let hi : nat = n / 4294967296 in
            lo < 4294967296 /\ hi < 4294967296 /\
            write_u64_le n == append (write_u32_le lo) (write_u32_le hi)))
  = lemma_lo_byte0 n;
    lemma_lo_byte1 n;
    lemma_lo_byte2 n;
    lemma_lo_byte3 n;
    lemma_hi_byte1 n;
    lemma_hi_byte2 n;
    lemma_hi_byte3 n
```

The seven calls hand z3 the seven non-trivial per-byte equalities
(`lemma_hi_byte0` is `(n/2^32) % 256 == (n/2^32) % 256`, syntactically
true). With those in scope, the list-equality
`write_u64_le n == append (write_u32_le lo) (write_u32_le hi)` reduces
by `cons`/`nil` unfolding plus `byte_of_int` injectivity (a
syntactically obvious step that z3 handles in milliseconds; the
quantifier-loop pathology is gone because we never ask SMT to derive the
modulo identity itself — only to combine seven discrete equalities).

---

## 3. The 8-byte byte-equality chain

Each per-byte sub-lemma is one application of a foundation lemma from
`FStar.Math.Lemmas`. All seven verified individually via MCP and as a
batch.

### LO half (lo = `n % 2^32`, four sub-lemmas):

```fstar
let lemma_lo_byte0 (n : nat{n < 18446744073709551616})
  : Lemma (ensures (n % 4294967296) % 256 == n % 256)
  = modulo_modulo_lemma n 256 16777216
  // a % (b*c) % b == a % b, with b=256, c=2^24, b*c=2^32

let lemma_lo_byte1 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 256) % 256 == (n / 256) % 256)
  = modulo_division_lemma n 256 16777216;     // (n%(b*c))/b = (n/b)%c
    modulo_modulo_lemma (n / 256) 256 65536    // ((n/256)%2^24)%256 = (n/256)%256

let lemma_lo_byte2 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 65536) % 256 == (n / 65536) % 256)
  = modulo_division_lemma n 65536 65536;       // 2^32 = 2^16 * 2^16
    modulo_modulo_lemma (n / 65536) 256 256

let lemma_lo_byte3 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 16777216) % 256 == (n / 16777216) % 256)
  = modulo_division_lemma n 16777216 256       // 2^32 = 2^24 * 256
```

The pattern: `modulo_division_lemma` walks the `%` past one `/`, then
`modulo_modulo_lemma` collapses the residual `% 2^k % 256` (which is
`% 256` whenever `k >= 8`).

### HI half (hi = `n / 2^32`, three non-trivial sub-lemmas):

```fstar
let lemma_hi_byte1 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 256) % 256 == (n / 1099511627776) % 256)
  = division_multiplication_lemma n 4294967296 256
  // a / (b*c) = (a/b)/c, with 2^32 * 2^8 = 2^40

let lemma_hi_byte2 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 65536) % 256 == (n / 281474976710656) % 256)
  = division_multiplication_lemma n 4294967296 65536    // 2^32 * 2^16 = 2^48

let lemma_hi_byte3 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 16777216) % 256 == (n / 72057594037927936) % 256)
  = division_multiplication_lemma n 4294967296 16777216 // 2^32 * 2^24 = 2^56
```

`hi_byte0` (i.e. `hi % 256 == (n / 2^32) % 256`) is reflexive after
substituting the definition of `hi`.

---

## 4. The composition

The naive idea ("plug the byte equalities into the parse_u64_le sum and
let z3 close") still stalls — confirmed in MCP. The reason: even with
all seven per-byte equalities discharged, z3 still has to recognise the
8-term arithmetic identity
`n == b0 + b1·256 + b2·2^16 + b3·2^24 + b4·2^32 + b5·2^40 + b6·2^48 + b7·2^56`,
which is the original quantifier-loop pathology.

The clean composition routes around this by **introducing two
parse_u32_le calls explicitly** so the arithmetic the solver has to
discharge is just `n == lo + hi * 2^32` (one application of
`lemma_div_mod`).

### Auxiliary: `parse_u64_le` decomposes into two `parse_u32_le` calls

Given any 8 bytes, parsing them as u64 equals first-4-as-u32 plus
last-4-as-u32 times 2^32. Pure pattern-matching identity, z3 closes it
in milliseconds:

```fstar
let lemma_parse_u64_decompose
  (b0 b1 b2 b3 b4 b5 b6 b7 : byte) (rest : bytes)
  : Lemma (ensures (
      match parse_u32_le [b0; b1; b2; b3] with
      | Some (lo, _) ->
        match parse_u32_le [b4; b5; b6; b7] with
        | Some (hi, _) ->
          parse_u64_le (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)
            == Some (lo + hi `op_Multiply` 4294967296, rest)
        | None -> False
      | None -> False))
  = ()
```

### The final lemma (verified, no admits)

```fstar
let lemma_parse_write_u64_le_inverse
  (n : nat{n < 18446744073709551616}) (rest : bytes)
  : Lemma (ensures parse_u64_le (FStar.List.Tot.append (write_u64_le n) rest)
                   == Some (n, rest))
  = let lo : nat = n % 4294967296 in
    let hi : nat = n / 4294967296 in
    (* Decompose write_u64_le into the two write_u32_le slabs. *)
    lemma_write_u64_le_decompose n;
    (* (write_u64_le n) @ rest
        = (write_u32_le lo @ write_u32_le hi) @ rest
        = write_u32_le lo @ (write_u32_le hi @ rest)
       Without the explicit append_assoc rewrite the SMT match-pattern
       sees the wrong cons-spine, so this hint is load-bearing. *)
    FStar.List.Tot.Properties.append_assoc
      (write_u32_le lo) (write_u32_le hi) rest;
    (* Two applications of the existing u32 lemma — first peel lo off
       the front (yielding the 4-byte hi slab + rest as the residual),
       then peel hi off. *)
    lemma_parse_write_u32_le_inverse lo (append (write_u32_le hi) rest);
    lemma_parse_write_u32_le_inverse hi rest;
    (* Bridge: parse_u64_le's 8-byte sum factors as parse_u32_le-on-lo
       + parse_u32_le-on-hi * 2^32. *)
    (match write_u32_le lo, write_u32_le hi with
     | [b0;b1;b2;b3], [b4;b5;b6;b7] ->
        lemma_parse_u64_decompose b0 b1 b2 b3 b4 b5 b6 b7 rest
     | _ -> ());
    (* Closing arithmetic: n = (n%2^32) + (n/2^32)*2^32 = lo + hi*2^32. *)
    lemma_div_mod n 4294967296
```

The `match write_u32_le lo, write_u32_le hi with` block looks
suspicious because both sides are statically 4-element lists, but
without it the SMT instantiation of `lemma_parse_u64_decompose` has no
witness for the byte values; binding the eight names lets the solver
unify the parse_u64_le pattern.

---

## 5. What worked, what didn't

**Verified via MCP (and re-confirmed by batch `fstar.exe` in 8.7 s):**
the **entire proof above**, no `admit ()`, no `--lax`, no rlimit bump
(default 5). Specifically these definitions, in order:

| Sub-lemma                              | Status   | Foundation             |
|----------------------------------------|----------|------------------------|
| `lemma_lo_byte0`                       | verified | `modulo_modulo_lemma`   |
| `lemma_lo_byte1`                       | verified | `modulo_division_lemma + modulo_modulo_lemma` |
| `lemma_lo_byte2`                       | verified | same                    |
| `lemma_lo_byte3`                       | verified | `modulo_division_lemma` |
| `lemma_hi_byte1`                       | verified | `division_multiplication_lemma` |
| `lemma_hi_byte2`                       | verified | same                    |
| `lemma_hi_byte3`                       | verified | same                    |
| `lemma_write_u64_le_decompose`         | verified | composes the 7 above    |
| `lemma_parse_u64_decompose`            | verified | pattern unfolding only  |
| `lemma_parse_write_u64_le_inverse`     | **verified** | composes everything + `lemma_div_mod` |

Reproduce: copy the contents of `/tmp/U64_attempt.fst` (or rebuild it
from the snippets above), run
`fstar.exe /tmp/U64_attempt.fst --z3version 4.13.3`. Expect:

```
Verified module: U64_attempt
All verification conditions discharged successfully

real    0m8.764s
user    0m8.648s
sys     0m0.180s
```

**What didn't work:**

1. *Naive byte-equalities only* — passing all 7 per-byte sub-lemmas
   in scope of the final lemma without the decomposition step **still
   stalls** (post-condition fails after a long search). Confirmed:
   the SMT struggles with the 8-term u64 polynomial identity per se,
   not with the modulo arithmetic.
2. *Asserting the 8-byte arithmetic identity directly*
   (`assert (n == b0 + b1*256 + ... + b7*2^56)`) reproduces the original
   `admit ()` pathology — z3 enters the quantifier-loop.
3. *Decomposition + `lemma_div_mod` without `append_assoc`* — fails:
   the LHS spine is `(write_u32_le lo @ write_u32_le hi) @ rest` but
   the `parse_u64_le` pattern needs the right-associated form, and z3
   does not auto-rewrite list `append`.
4. *Decomposition + composition without the explicit
   `match write_u32_le lo, write_u32_le hi with ... -> lemma_parse_u64_decompose ...`
   bridge* — fails: SMT cannot pick byte witnesses to instantiate
   `lemma_parse_u64_decompose`'s universally-quantified bytes.

The four "didn't works" pinned the load-bearing parts of the working
proof.

---

## 6. Estimated remaining effort

**Effectively zero — the proof is done.** The remaining task is
mechanical:

1. Copy the seven sub-lemmas, the decomposition lemma, the
   `parse_u64_decompose` auxiliary, and the new body of
   `lemma_parse_write_u64_le_inverse` into `RDF.Bytes.fst`,
   replacing the `admit ()`.
2. Add `open FStar.Math.Lemmas` at the top of the module (currently it
   only opens `FStar.List.Tot`).
3. `make verify` in `formal/fstar/`.
4. Recheck downstream writer-family `.fst.checked` files — none of them
   import the lemma's *body*, only its statement, so the cascade should
   be a no-op (`make verify` should regenerate the checked file in
   ~10 s and leave the rest alone). Worth confirming on a clean run.

Wall-clock estimate including review and PR: **half a day**.

---

## 7. Recommendation

**Go with strategy (a) — the decomposition.** Rationale:

- **It works.** A complete, verified proof is in hand.
  No `Tactics.V2`, no `--rlimit` bump, no `compute()`, no
  bit-vector encoding. Stays inside the same SMT toolchain that
  discharges the rest of the module.
- **Footprint is local.** Seven small `Math.Lemmas` calls + two
  composing lemmas + one final body. ~80 lines added. The proof
  decomposes cleanly into pieces that are independently meaningful
  (each per-byte equality is reusable; the decomposition lemma is
  reusable for any future byte-layout that needs a u64-as-2×u32 view).
- **No new dependency surface.** `FStar.Math.Lemmas` is already on the
  default include path; nothing to add to the build.
- **Avoids the `Tactics.V2 + BV` cliff.** That route would have brought
  in `FStar.Tactics.V2`, `FStar.Tactics.BV`, `FStar.UInt64`, plus a
  `compute()` invocation whose extraction story is murkier (the
  writer family extracts to OCaml; tactic-discharged lemmas have
  no extracted code so this is benign in principle, but adds a
  reviewable surface and a new dependency in the `.depend` graph).
  None of that is needed.
- **Composes in the future.** When the same proof is needed for u128
  or u256 layouts (Parquet stat headers, future #200 writers), the
  same lo/hi decomposition with `pow2 64`/`pow2 128` re-uses the
  identical foundation lemmas. Strategy (b) would have to re-derive
  per-bitwidth.

The only argument for (b) was insurance against (a) failing. Since
(a) succeeded end-to-end, (b) is unjustified.

---

## Critical files for the follow-up landing PR

- `/home/user/factoidal/formal/fstar/RDF.Bytes.fst` — the only file
  that needs editing (replace `admit ()` body and add the new
  helpers/lemmas above it; add `open FStar.Math.Lemmas`).
- `/home/user/factoidal/formal/fstar/RDF.Bytes.fst.checked` — will
  regenerate on `make verify`.
- `/home/user/factoidal/formal/fstar/Makefile` — no changes; existing
  `verify` target picks up the regenerated checked file.
- `/tmp/U64_attempt.fst` — the working scratch file with the verified
  proof in standalone form, kept under `/tmp/` per the planning-task
  scratch-file policy. Lift its body verbatim into `RDF.Bytes.fst`
  during the landing PR.
- `/root/.opam/fstar/lib/fstar/ulib/FStar.Math.Lemmas.fsti` — reference
  for the four foundation lemmas used (`modulo_modulo_lemma`,
  `modulo_division_lemma`, `division_multiplication_lemma`,
  `lemma_div_mod`).
