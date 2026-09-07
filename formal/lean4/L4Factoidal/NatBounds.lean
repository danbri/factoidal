/-
L4Factoidal.NatBounds — the `Nat` bounds the on-disk codecs and the
parsers compare against, held as `@[noinline]` definitions.

WHY THESE ARE DEFINITIONS AND WHY THEY CARRY `@[noinline]`

A `Nat` literal at or above 2 ^ 31 does not fit a boxed scalar on a
32-bit target, so the WebAssembly module (wasm32, GMP-free) builds an
arbitrary-precision object for it. The code generator emits such a
literal INLINE in the function body --

    v___x_122_ = lean_cstr_to_nat("4294967296");
    v___x_123_ = lean_nat_dec_lt(v_n_121_, v___x_122_);
    return v___x_123_;

-- and `lean_nat_dec_lt` borrows both arguments, so nothing releases
the object: each call leaks one. A TOP-LEVEL definition is built once
in the module's initialiser and marked persistent
(`lean_mark_persistent`), and the call site then reads a global. The
`@[noinline]` attribute is what stops the compiler folding the
definition back into the call site: without it the emitted code is the
inline literal again, measured.

Measured on 2026-09-07, before this module existed: a 109,804-row pack
of N-Quads through the wasm module retained 1,709,007 such objects,
52.2 MiB, and the count grew by exactly that per repeated pack in one
module instance. Every retained value was 2 ^ 32 (1,646,462 of them)
or 2 ^ 32 - 1 (62,525). Design record:
`docs/designissues/2026-09-07-wasm-packer-memory.md`.

On a 64-bit target each of these values is an unboxed scalar and the
attribute costs one load from a global.

`@[reducible]` sits beside `@[noinline]` so that a proof about a
function which uses one of these sees the literal transparently: with a
plain definition, `simp [fitsU32]` stops at
`decide (n < 4294967296) = true` and no longer closes a goal of
`n < 4294967296` (measured on eight proofs in
`PagedTermDictionaryCoreTheorems` and `TermCodecTheorems`). Reducibility
is an elaboration-time transparency and does not reach the code
generator, so the emitted call site still reads the global.

Use these in EXECUTABLE code. A theorem statement may say
`n < UInt32.size` or `n < 4294967296` as before.
-/

namespace L4Factoidal

/-- `2 ^ 32` — the exclusive upper bound of a `UInt32` wire field. -/
@[reducible, noinline] def two32 : Nat := 4294967296

theorem two32_eq : two32 = 4294967296 := rfl

theorem two32_eq_uint32Size : two32 = UInt32.size := rfl

/-- `2 ^ 32 - 1` — the `xsd:unsignedInt` inclusive upper bound
(XSD 1.1 §3.4.19). Used by the `Nat`-typed callers. -/
@[reducible, noinline] def two32m1 : Nat := 4294967295

theorem two32m1_eq : two32m1 = 4294967295 := rfl

/-- `2 ^ 32 - 1` as an `Int`, for the `xsd:unsignedInt` facet checks
that compare against an `Int` lexical value (`XSD.Facets.baseIntervalFor`,
`SHACL.Validation.literalIllFormed`). -/
@[reducible, noinline] def two32m1Int : Int := 4294967295

theorem two32m1Int_eq : two32m1Int = 4294967295 := rfl

end L4Factoidal
