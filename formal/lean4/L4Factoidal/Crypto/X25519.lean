/-
L4Factoidal.Crypto.X25519 — the X25519 Diffie-Hellman function
(RFC 7748 §5) bound to HACL* through Lean's C FFI.

`third_party/hacl/src/Hacl_Curve25519_51.c` was already vendored and
already linked into every target, because Ed25519 uses its field
arithmetic. Until now nothing in the Lean tree could CALL it. This
module exposes it, for the KEM half of HPKE (`Crypto/Hpke.lean`), for
OMEMO's X3DH, and for MLS ciphersuite 3's DHKEM(X25519, HKDF-SHA256).

## Crypto policy

`skills/crypto-policy/SKILL.md`: HACL* only. A scalar multiplication
touches a SECRET scalar, so there is no pure-Lean variant of this
function anywhere in the tree and none may be added.

## Trust statement

`scalarmult` and `basePoint` are `opaque`: Lean knows their TYPE and
nothing about their VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT THEY
COMPUTE.

Trusted: X25519 as implemented by HACL*
(`Hacl_Curve25519_51_scalarmult` and `_secret_to_public`), extracted by
KaRaMeL from F*/Low* code proved by Project Everest, vendored unmodified
from cryspen/hacl-packages commit
05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 — `third_party/hacl/PROVENANCE.md`.
And `ffi/hacl_kdf.c`, which is two length checks per entry point.

HACL* CLAMPS the scalar itself, as RFC 7748 §5 requires (`decodeScalar25519`:
clear the low three bits of the first byte, clear the top bit and set the
second-highest bit of the last). The caller passes the raw 32 bytes and
must not clamp them again.

## The all-zero output, and why it is not filtered in C

RFC 7748 §6.1: "Both [parties] MAY check, without leaking extra
information about the value of K, whether K is the all-zero value and
abort if so". An all-zero shared secret is what a LOW-ORDER input point
produces, and accepting it destroys the contributory property some
protocols need. It is a PROTOCOL decision, not a curve one, so
`ffi/hacl_kdf.c` reports what the curve computed and the decision is
made here, in Lean, where it is visible:

  * `scalarmult` returns the raw result, all-zero included.
  * `dh?` returns `none` on an all-zero result — the RFC 7748 §6.1
    abort — and is what protocol code should call.

Wycheproof's `x25519_test.json` marks the low-order-point vectors
`acceptable` for exactly this reason: neither answer is a defect, so
`lake exe l4crypto-probe` counts them in their own bucket and names
them, rather than folding them into pass or fail.

## Contract

  * `scalarmult scalar point` → the 32-byte result, or the EMPTY
    `ByteArray` if either argument is not 32 bytes. A shared secret is
    always 32 bytes, so an empty result is unambiguously a refusal.
  * `basePoint scalar` → the 32-byte public key `X25519(scalar, 9)`, or
    EMPTY on a wrong length.
  * `dh? scalar point` → `some k` when both are 32 bytes and `k` is not
    all zero; `none` otherwise.
-/

namespace L4Factoidal.Crypto.X25519

/-- Both the scalar and the u-coordinate are 32 bytes (RFC 7748 §5). -/
def keyBytes : Nat := 32

/-- X25519 scalar multiplication (RFC 7748 §5) via HACL*
`Hacl_Curve25519_51_scalarmult`. HACL* clamps the scalar; do not clamp
it again. The all-zero low-order-point result is RETURNED, not filtered
— see `dh?`. EMPTY on a wrong length. -/
@[extern "l4_hacl_x25519_scalarmult"]
opaque scalarmult (scalar : @& ByteArray) (point : @& ByteArray) : ByteArray

/-- The X25519 public key of a secret scalar, `X25519(scalar, 9)`, via
HACL* `Hacl_Curve25519_51_secret_to_public`. EMPTY on a wrong length. -/
@[extern "l4_hacl_x25519_base"]
opaque basePoint (scalar : @& ByteArray) : ByteArray

/-- `true` when every byte is zero. Used only for the RFC 7748 §6.1
check; a shared secret that reaches this point is about to be discarded
either way, so the non-constant-time short circuit of `Array.all` leaks
nothing an attacker does not already control. -/
def isAllZero (b : ByteArray) : Bool := b.data.all (· == 0)

/-- X25519 with the RFC 7748 §6.1 contributory check applied: `none` on
a wrong length AND on an all-zero shared secret. Protocol code should
call this rather than `scalarmult`. -/
def dh? (scalar point : ByteArray) : Option ByteArray :=
  if scalar.size ≠ keyBytes ∨ point.size ≠ keyBytes then none
  else
    let k := scalarmult scalar point
    if k.size ≠ keyBytes ∨ isAllZero k then none else some k

/-- The public key of a secret scalar; `none` on a wrong length. -/
def publicKey? (scalar : ByteArray) : Option ByteArray :=
  if scalar.size ≠ keyBytes then none
  else
    let p := basePoint scalar
    if p.size = keyBytes then some p else none

end L4Factoidal.Crypto.X25519
