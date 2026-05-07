# 2026-05-07 — I/O verification + third-party crypto/format vendoring

Companion to
[`2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md).
Phase 0 of the recovery plan demands a boundary audit; this doc
gives the audit its taxonomy for each remaining `assume val` and
each system-I/O bridge.

## The hash-based round-trip pattern

For every companion file the project writes, the byte layout
must be defined in F\*. We can't verify the OS `write(2)` itself
— that's outside any feasible verification target — but we can
build a **round-trip witness** that proves byte-equivalence of
what F\* asked to write and what's actually on disk.

The pattern:

```fstar
// In F*: byte-level format spec.
val serialize : data -> Tot (list u8)
val parse     : list u8 -> Tot (option data)
val serialize_parse_roundtrip
  (d : data) :
  Lemma (parse (serialize d) == Some d)

// Hash the F*-side byte representation.
val expected_digest : data -> Tot sha256_digest
let expected_digest d = sha256 (serialize d)

// In OCaml: pure I/O realisations. No decisions.
assume val write_bytes : path:string -> bytes:list u8 -> ML unit
assume val read_bytes  : path:string -> ML (list u8)

// Test in F*: the on-disk file matches the F*-computed bytes.
val verify_file_matches : data -> path:string -> ML bool
let verify_file_matches d p =
  let actual_digest = sha256 (read_bytes p) in
  expected_digest d = actual_digest
```

The CI gate is a unit test, not a verification proof: for every
companion-file format defined in F\*, the test generates sample
data, calls `write_bytes`, reads it back, hashes both sides, and
asserts equality.

What this catches:

- Byte-level corruption from a bug in the OCaml writer (e.g.
  off-by-one, endian mistake, truncated buffer).
- Drift between the F\* serializer and the OCaml writer if anyone
  re-introduces semantic logic on the OCaml side.
- Reader/writer mismatch (parse roundtrip property is checked
  separately by the F\* lemma).

What it doesn't catch:

- Corruption introduced by the filesystem after the test passes.
- Storage-medium failures (bad sectors, etc.).

Both of those are out of scope for any practical verification
strategy. The hash check is the strongest property we can claim
short of formal modelling of the OS.

## SHA-256 — vendor HACL\*

For the round-trip pattern above we need a hash function inside
F\* with proven correctness. HACL\* is the obvious choice.

[HACL\*](https://github.com/hacl-star/hacl-star) is a verified
cryptographic library written in F\*, compiled to C via KaRaMeL,
with OCaml bindings available as the `hacl-star` opam package. It
implements SHA-224/256/384/512, BLAKE2, ChaCha20, AES, Curve25519,
Ed25519, and more — verified for memory safety, constant-time
behaviour, and functional correctness. Production deployments
include Mozilla Firefox NSS, the Linux kernel, mbedTLS, the
Tezos blockchain, ElectionGuard, and Wireguard.

For our use case (file-integrity hashing in tests) we only need
SHA-256.

### Integration plan

Two modes:

**Mode A — opam dependency (start here).**
- Add `hacl-star` (currently 0.6.x) to the project's opam deps in
  CLAUDE.md and CI.
- Declare in F\*:
  ```fstar
  module ThirdParty.HACL

  // SHA-256 over a list of bytes.
  // Realised by an OCaml binding to HACL*'s verified C
  // implementation. We trust HACL*'s upstream proof here; we
  // don't reverify in our own F* tree.
  assume val sha256 : list FStar.UInt8.t -> Tot (digest:list FStar.UInt8.t {length digest = 32})

  // (Add other primitives as needed.)
  ```
- OCaml realisation patch: `let sha256 = Hacl_star.Hacl.SHA2_256.hash`
  (with the bytes ↔ list-u8 marshalling shim).

**Mode B — vendor the F\* sources (when stricter trust required).**
- Place HACL\*'s relevant `.fst` files in
  `formal/third_party/hacl-star/sha2/`.
- Verify and extract them in our own toolchain.
- Pin the upstream commit in `formal/third_party/hacl-star/VERSION`.

Mode A is fine for the round-trip witness use. Mode B becomes
necessary if a compliance audit demands an end-to-end verified
chain inside our repo.

### Why not write our own SHA-256

We could. It's a few hundred lines of F\*. But:

- HACL\*'s SHA-256 is verified for **constant-timeness** in
  addition to functional correctness — a property our hand-roll
  would not have.
- Reimplementing means our hash differs from the de-facto F\*
  community hash, with no benefit.
- The C extraction route via KaRaMeL is the same either way; HACL\*
  is exactly the kind of code KaRaMeL was designed for.

## EverParse — keep an eye on, don't depend on yet

[EverParse](https://github.com/project-everest/everparse)
generates verified, secure parsers for binary formats from
declarative DSLs (LowParse + 3D + QuackyDucky). Used in production
by Windows Hyper-V to validate every Azure network packet.

It's the right tool for **future** companion-file formats and for
the SPARQL Protocol-over-the-wire stack (TLS already uses it via
miTLS). Not necessary for the current recovery work, which sticks
to bespoke byte layouts in plain F\*.

When we add a new on-disk file format (e.g. for the offset-index
in the recovery plan's Phase 6), reach for EverParse rather than
hand-rolling — it gives parser/formatter pairs with the
serialize-parse-roundtrip lemma for free.

## UUID — implement RFC 4122 in F\*

No verified F\* UUID library exists. RFC 4122 is small (16 bytes
with specific bit patterns); we implement it ourselves.

```fstar
module ThirdParty.UUID

module U8 = FStar.UInt8

// 16-byte UUID. All UUIDs are 16 bytes by definition.
type uuid = bs:list U8.t {length bs = 16}

// UUID v4 (random) per RFC 4122 §4.4:
//   octet 6 high nibble = 0100  (version 4)
//   octet 8 high two bits = 10  (variant DCE 1.1)
val uuid_v4_format : uuid -> bool
let uuid_v4_format bs =
  let octet6 = index bs 6 in
  let octet8 = index bs 8 in
  U8.((octet6 &^ 0xF0uy) = 0x40uy) &&
  U8.((octet8 &^ 0xC0uy) = 0x80uy)

// Construct a v4 UUID from 16 random bytes by setting the
// version+variant bits. This is the byte-format conversion;
// randomness comes from outside.
val mk_v4 : raw:list U8.t {length raw = 16} -> Tot (u:uuid {uuid_v4_format u})
let mk_v4 raw =
  let raw6 = index raw 6 in
  let raw8 = index raw 8 in
  // (set high nibble of raw6 to 4, top two bits of raw8 to 10)
  // ...byte mutation via list update; F* helper code...

// Source of randomness — realised by OCaml's Random or HACL*'s
// CSPRNG depending on whether crypto-strength is required.
assume val random_bytes : n:nat -> ML (bs:list U8.t {length bs = n})

val gen_v4 : unit -> ML uuid
let gen_v4 () = mk_v4 (random_bytes 16)
```

The format function `uuid_v4_format` is decidable; we can prove
`mk_v4 raw` produces a `uuid` satisfying it for any 16-byte input.
The OCaml side is one realisation: `random_bytes` calls
`Random.bits` (non-crypto) or `Hacl_star.Hacl.RandomBuffer`
(CSPRNG), depending on the use site.

CLAUDE.md issue #63 (`63_regex_hash_uuid_stubs.sh`) currently
realises UUID via OCaml; this design replaces that patch with a
verified F\* byte-format function plus a single `assume val
random_bytes` realisation.

## Regex — keep `assume val regex_match`

Regex matching is **explicitly host-defined** by the SPARQL 1.1
spec. The pattern language and matching semantics are deferred
to the implementation's regex engine, with a small subset
mandated. Verifying the regex semantics ourselves is therefore
not just hard but **wrong** — it would create a divergence from
what every other SPARQL engine does.

The right pattern:

```fstar
// SPARQL REGEX call-out. Pattern flags: "i" (case-insensitive),
// "s" (dot matches newline), etc. Semantics defined by the host
// regex engine; no F* proof obligations on the matcher itself.
assume val regex_match
  (pattern : string)
  (input   : string)
  (flags   : string)
  : ML bool
```

The OCaml side calls `Str.regexp_string` / `Str.string_match` (or
better, `Re` for PCRE compatibility). Other targets:
- C extraction: link against POSIX `<regex.h>` or PCRE2.
- WASM: ship a regex engine with the WASM bundle (or use the
  host's via JS interop).

This is rule #11(a) — an `assume val` realisation of pure I/O
(in this case, "I/O" with the regex engine as the foreign service).
It is correctly **not** in scope for migration into F\*.

CLAUDE.md issue #63 covers this. Resolution for the issue: drop
the migration goal; accept that regex semantics are externally
defined.

## Random — `assume val` per quality tier

Two distinct uses:

**Cryptographic randomness** (used by UUID v4, future
challenge/nonce flows):
```fstar
assume val random_bytes_csprng : n:nat -> ML (bs:list U8.t {length bs = n})
```
OCaml realisation: `Hacl_star.Hacl.RandomBuffer.randombytes`.
Same on C-extraction (HACL\* native).

**Non-crypto randomness** (test data, blank-node naming where
collision-resistance ≠ security):
```fstar
assume val random_bytes_weak : n:nat -> ML (bs:list U8.t {length bs = n})
```
OCaml realisation: `Random.bits`. C-extraction: `arc4random` or
similar.

Two distinct `assume val`s rather than one parameterized by a
quality flag, because mistakenly reaching for the weak source in
a security context would be a silent vulnerability.

## `formal/third_party/` — vendoring directory pattern

```
formal/third_party/
├── README.md                        -- vendoring policy
├── hacl-star/                       -- (vendored when Mode B kicks in)
│   ├── VERSION                      -- upstream commit pin
│   ├── LICENSE                      -- HACL*'s Apache 2.0
│   └── sha2/                        -- only the SHA-256 .fst files we use
└── (future) everparse/              -- when an on-disk format wants verified parsing
    └── ...
```

Policy (in `formal/third_party/README.md`):

1. Each dependency lives in its own subdirectory.
2. Each subdir has `VERSION` (upstream commit + date),
   `LICENSE` (verbatim from upstream), and just-enough `.fst`
   files for our actual usage.
3. **No editing.** If a vendored file needs to change, propose
   the change upstream first; if blocked, document the local
   deviation in `LOCAL_PATCHES.md` next to the file.
4. Bumping a dependency is a single PR with the new VERSION,
   the new `.fst` content, and any forced re-extractions.
5. The main extract step in `build-ocaml.sh` includes
   `formal/third_party/<dep>/*.fst` automatically.

For now (Mode A) only the README is needed; the actual vendoring
waits until we want a closed-loop verification chain.

## Boundary audit taxonomy update

Phase 0 of the recovery plan classifies every OCaml-side function.
Add these categories to the audit's classification scheme:

| Category | Example | Status |
|---|---|---|
| `assume val` realisation — pure I/O | `write_bytes`, `read_bytes`, system clock | ALLOWED |
| `assume val` realisation — host-engine call-out | `regex_match` | ALLOWED (semantics deferred to host) |
| `assume val` realisation — vendored crypto | `sha256` via HACL\* | ALLOWED (Mode A) |
| `assume val` realisation — randomness | `random_bytes_csprng`, `random_bytes_weak` | ALLOWED (per quality tier) |
| Companion-file writer with byte-layout logic | (current Vav3 reality TBD by audit) | VIOLATION — migrate to F\* serialise + `write_bytes` realisation |
| Consumer / binding | `factoidal_cli.ml`, runners | OUT OF SCOPE — relocate to `bin/` |
| Semantic shadow | Yod6/Tet3/Lamed3/Mem5/Pe5/Bet7/Tav5/Heth3 | VIOLATION — migrate per recovery plan |

The hash-based round-trip witness applies to every "companion-file
writer" entry: once the byte layout moves to F\* and the OCaml
side becomes a `write_bytes` realisation, we run a CI test that
hashes the F\*-computed bytes against the on-disk bytes. Passing
the test is the proof the boundary holds.

## What this gives the recovery plan

- **Phase 0 (boundary audit)** classifies every OCaml file
  against the table above. The "VIOLATION" rows enumerate the
  remaining migration work.
- **Phases 1-7** retire violations. Each companion-file writer
  migration adds:
  - F\* `serialize` + parse + roundtrip lemma
  - `assume val write_bytes` realisation
  - CI test using `expected_digest` ↔ `sha256 (read_bytes path)`
- **Phase 8 (consumer relocation)** physically separates the
  things that aren't in scope (CLI, runners) from the verified
  library proper.
- **Phase 9 (drop the qualifier)** — when the audit shows zero
  VIOLATION rows and the round-trip tests are green in CI, the
  rule #11 caveat comes off and the project can call itself
  "verified RDF/SPARQL" without footnotes.

## Summary of the third-party policy

| Need | Source | Trust model |
|---|---|---|
| SHA-256 | `hacl-star` opam package (Mode A) → vendored `.fst` (Mode B) | Trust HACL\* upstream proof; verify locally via Mode B if compliance demands |
| Verified parsers (future) | EverParse | Trust upstream; vendor when used |
| UUID format | Implement in F\* (RFC 4122 byte assembly) | Self-verified |
| Regex matching | `assume val regex_match` realised by host (`Str` / PCRE2 / JS) | Host-engine-defined per SPARQL 1.1 |
| Crypto random bytes | HACL\* `RandomBuffer` realisation of `assume val random_bytes_csprng` | HACL\* upstream |
| Weak random bytes | OCaml `Random.bits` realisation of `assume val random_bytes_weak` | Non-crypto by design |

Under this policy the project never silently mixes verified and
unverified code paths. Every external dependency is named, its
trust model documented, and the migration target known.

## References

- [HACL\* — formally verified cryptographic library](https://github.com/hacl-star/hacl-star)
- [HACL\*/EverCrypt manual](https://hacl-star.github.io/index.html)
- [`hacl-star` opam package (0.6.x)](https://ocaml.org/p/hacl-star/0.6.1)
- [EverParse — verified secure parsers](https://github.com/project-everest/everparse)
- [Project Everest](https://project-everest.github.io/)
- [RFC 4122 — UUID URN Namespace](https://datatracker.ietf.org/doc/html/rfc4122)
- [Brzozowski-derivative regex — verified Idris implementation](https://github.com/MathiasVP/idris-regex)
  (reference for if/when we want a fully F\*-verified regex)
