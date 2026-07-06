;; Hand-written for this repo (not vendored) -- Wasm-of-ocaml realization
;; of Stdint.Uint32's C-stub primitives (the `uint32_*` names), which is
;; the OCaml-side backing FStar_UInt32 uses for F*'s `u32` (see F*'s
;; installed ulib/ml/FStar_UInt32.ml: `module M = Stdint.Uint32`).
;;
;; Why this exists: native OCaml gets these via stdint's own C stubs
;; (uint32_stubs.c, struct custom_operations "uint.uint32"). js_of_ocaml
;; gets them via this directory's ../fstar_int_stubs.js, a plain-JS
;; `//Provides: uint32_*` file using raw JS Numbers (`x >>> 0`) as the
;; representation. wasm_of_ocaml does NOT pick up that same JS file for
;; these primitives even though it's passed to `wasm_of_ocaml compile`
;; alongside it (confirmed 2026-07-06 by disassembling the previously
;; built factoidal.wasm.js with `wasm-dis`: every `uint32_*` import was
;; wired to wasm_stub_shims.py's blanket identity stub
;; `(...a)=>a[0]!==undefined?a[0]:0`, never to fstar_int_stubs.js's real
;; bodies) -- a plain `//Provides:` JS stub file is a js_of_ocaml
;; mechanism; wasm_of_ocaml needs actual Wasm-module exports under these
;; names, resolved by `wasm-merge` at `wasm_of_ocaml compile` time. This
;; is exactly the gap `wasm_runtime/zarith_runtime.wat` (vendored from
;; janestreet/zarith_stubs_js) already closes for Zarith's `ml_z_*`
;; primitives -- see that file's header and this directory's README.md.
;;
;; Unlike Zarith (arbitrary precision, needs JS BigInt on the other side
;; of the import), a uint32 fits natively in Wasm's `i32` value type, so
;; no companion JS runtime file is needed here: every operation below is
;; plain Wasm-GC struct boxing plus the standard i32 arithmetic/bitwise/
;; unsigned-division instructions. The custom-block shape (id string,
;; compare/hash/serialize/deserialize/fixed_length) mirrors native
;; stdint's `uint32_ops` in uint32_stubs.c field-for-field (id
;; "uint.uint32", 4-byte fixed length, unsigned compare, raw-bits hash)
;; so a value's *meaning* is identical across native/js/wasm even though
;; each target boxes it differently. `dup` is left null, matching
;; native's C initializer (which doesn't set it either).
;;
;; Scope: only the uint32_* primitives are realized here. Wider stdint
;; fixed-width types (Int40/48/56/128, Uint40/48/56/64/128) are touched
;; only via eager OCaml module-init calls (`zero = of_int 0`, `max_int =
;; max_int_fun ()`, `init_custom_ops ()`) and never used for real
;; arithmetic anywhere in this project's extracted OCaml (confirmed by
;; grepping ocaml-output/*.ml for `FStar_UInt64.`/`FStar_UInt16.` etc:
;; no hits) -- wasm_stub_shims.py's existing identity-stub fallback
;; remains correct and sufficient for those, and is left untouched.
;;
;; The type-section boilerplate (custom_operations/custom struct shapes,
;; the `$string` byte-array type) follows the same pattern already
;; vendored in `zarith_runtime.wat` so the two auxiliary Wasm modules
;; merge cleanly via `wasm-merge`'s structural type canonicalization.

(module
   (type $string (array (mut i8)))
   (type $compare
      (func (param (ref eq)) (param (ref eq)) (param i32) (result i32)))
   (type $hash (func (param (ref eq)) (result i32)))
   (type $fixed_length (struct (field $bsize_32 i32) (field $bsize_64 i32)))
   (type $serialize
      (func (param (ref eq)) (param (ref eq)) (result i32) (result i32)))
   (type $deserialize (func (param (ref eq)) (result (ref eq)) (result i32)))
   (type $dup (func (param (ref eq)) (result (ref eq))))
   (type $custom_operations
      (struct
         (field $id (ref $string))
         (field $compare (ref null $compare))
         (field $compare_ext (ref null $compare))
         (field $hash (ref null $hash))
         (field $fixed_length (ref null $fixed_length))
         (field $serialize (ref null $serialize))
         (field $deserialize (ref null $deserialize))
         (field $dup (ref null $dup))))
   (type $custom (sub (struct (field (ref $custom_operations)))))
   (type $u32box
      (sub final $custom
         (struct
            (field (ref $custom_operations))
            (field $v i32))))

   (import "env" "caml_invalid_argument"
      (func $caml_invalid_argument (param (ref eq))))
   (import "env" "caml_raise_zero_divide" (func $caml_raise_zero_divide))
   (import "env" "caml_hash_mix_int"
      (func $caml_hash_mix_int (param i32) (param i32) (result i32)))
   (import "env" "caml_register_custom_operations"
      (func $caml_register_custom_operations
         (param (ref $custom_operations))))
   (import "env" "caml_serialize_int_4"
      (func $caml_serialize_int_4 (param (ref eq)) (param i32)))
   (import "env" "caml_deserialize_int_4"
      (func $caml_deserialize_int_4 (param (ref eq)) (result i32)))

   (func $wrap_u32 (param $v i32) (result (ref eq))
      (struct.new $u32box (global.get $u32_custom_ops) (local.get $v)))

   (func $unwrap_u32 (param $x (ref eq)) (result i32)
      (struct.get $u32box $v (ref.cast (ref $u32box) (local.get $x))))

   ;; Matches native stdint's `uint32_cmp`: unsigned comparison of the
   ;; two raw 32-bit bit patterns, tri-state result. Used generically by
   ;; OCaml's polymorphic `=`/`<`/`compare` on this custom-block type
   ;; (e.g. Stdint's Str_conv-based `of_string`/`to_string`, which drive
   ;; Parquet.Footer's `FStar_UInt32.uint_to_t`/`.v`).
   (func $u32_compare
      (param $a (ref eq)) (param $b (ref eq)) (param $total i32)
      (result i32)
      (local $za i64) (local $zb i64)
      (local.set $za (i64.extend_i32_u (call $unwrap_u32 (local.get $a))))
      (local.set $zb (i64.extend_i32_u (call $unwrap_u32 (local.get $b))))
      (if (i64.lt_u (local.get $za) (local.get $zb))
         (then (return (i32.const -1))))
      (if (i64.gt_u (local.get $za) (local.get $zb))
         (then (return (i32.const 1))))
      (i32.const 0))

   ;; Matches native's `uint32_hash`: the raw bits, unmixed (OCaml's
   ;; generic hash mixer folds this in itself).
   (func $u32_hash (param $a (ref eq)) (result i32)
      (call $caml_hash_mix_int (i32.const 0) (call $unwrap_u32 (local.get $a))))

   (func $u32_serialize
      (param $s (ref eq)) (param $a (ref eq)) (result i32) (result i32)
      (call $caml_serialize_int_4 (local.get $s) (call $unwrap_u32 (local.get $a)))
      (i32.const 4) (i32.const 4))

   (func $u32_deserialize (param $s (ref eq)) (result (ref eq)) (result i32)
      (call $wrap_u32 (call $caml_deserialize_int_4 (local.get $s)))
      (i32.const 4))

   (global $u32_custom_ops (ref $custom_operations)
      (struct.new $custom_operations
         (array.new_fixed $string 11 ;; "uint.uint32"
            (i32.const 117) (i32.const 105) (i32.const 110) (i32.const 116)
            (i32.const 46) (i32.const 117) (i32.const 105) (i32.const 110)
            (i32.const 116) (i32.const 51) (i32.const 50))
         (ref.func $u32_compare)
         (ref.func $u32_compare)
         (ref.func $u32_hash)
         (struct.new $fixed_length (i32.const 4) (i32.const 4))
         (ref.func $u32_serialize)
         (ref.func $u32_deserialize)
         (ref.null $dup)))

   ;; OCaml source: `let () = init_custom_ops ()` at Uint32 module load.
   (func (export "uint32_init_custom_ops")
      (param (ref eq)) (result (ref eq))
      (call $caml_register_custom_operations (global.get $u32_custom_ops))
      (ref.i31 (i32.const 0)))

   (func (export "uint32_of_int") (param $x (ref eq)) (result (ref eq))
      (return_call $wrap_u32 (i31.get_s (ref.cast (ref i31) (local.get $x)))))

   (data $to_int_range "int_of_uint32: value out of OCaml int range")

   ;; wasm_of_ocaml's plain `int` is a 31-bit signed i31ref (same
   ;; representable range as OCaml `int` on a 32-bit host), unlike
   ;; native's 63-bit int which fits any uint32 without loss. Values
   ;; needing bit 30 or 31 of the u32 can't round-trip through `int`
   ;; here; raise rather than silently truncate/misrepresent, mirroring
   ;; how this same auxiliary-module pattern already handles the
   ;; analogous case in zarith_runtime.wat's `ml_z_to_int`.
   (func (export "int_of_uint32") (param $x (ref eq)) (result (ref eq))
      (local $v i32)
      (local.set $v (call $unwrap_u32 (local.get $x)))
      (if (i32.and (local.get $v) (i32.const 0xC0000000))
         (then
            (call $caml_invalid_argument
               (array.new_data $string $to_int_range
                  (i32.const 0) (i32.const 45)))))
      (ref.i31 (local.get $v)))

   (func (export "uint32_max_int") (param (ref eq)) (result (ref eq))
      (return_call $wrap_u32 (i32.const -1)))

   (func (export "uint32_add")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.add (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   (func (export "uint32_sub")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.sub (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   (func (export "uint32_mul")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.mul (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   ;; Matches native's `uint32_div`/`uint32_mod`: raise Division_by_zero
   ;; rather than the JS shim's silent-0 (fstar_int_stubs.js); this is a
   ;; fresh realization, so it can match native exactly instead of
   ;; inheriting that pre-existing JS-target deviation.
   (func (export "uint32_div")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (local $bv i32)
      (local.set $bv (call $unwrap_u32 (local.get $b)))
      (if (i32.eqz (local.get $bv)) (then (call $caml_raise_zero_divide)))
      (return_call $wrap_u32
         (i32.div_u (call $unwrap_u32 (local.get $a)) (local.get $bv))))

   (func (export "uint32_mod")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (local $bv i32)
      (local.set $bv (call $unwrap_u32 (local.get $b)))
      (if (i32.eqz (local.get $bv)) (then (call $caml_raise_zero_divide)))
      (return_call $wrap_u32
         (i32.rem_u (call $unwrap_u32 (local.get $a)) (local.get $bv))))

   (func (export "uint32_and")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.and (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   (func (export "uint32_or")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.or (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   (func (export "uint32_xor")
      (param $a (ref eq)) (param $b (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.xor (call $unwrap_u32 (local.get $a))
            (call $unwrap_u32 (local.get $b)))))

   ;; The shift amount is a plain OCaml `int` (i31), not a boxed uint32:
   ;; FStar_UInt32.shift_left/shift_right (ulib/ml/FStar_UInt32.ml) do
   ;; `M.shift_left n (Stdint.Uint32.to_int i)` before calling the
   ;; external, and Stdint.Uint32.Base.shift_left's OCaml type is
   ;; `uint32 -> int -> uint32` -- confirmed against the compiled
   ;; program's own import signature (`wasm-dis` on factoidal.wasm.js
   ;; shows `uint32_shift_left : (ref eq, ref eq) -> ref eq` like every
   ;; other binary op here, but the *value* on the OCaml side is an
   ;; `int`, so it must be unboxed as `i31`, not `$u32box`).
   (func (export "uint32_shift_left")
      (param $a (ref eq)) (param $amt (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.shl (call $unwrap_u32 (local.get $a))
            (i32.and (i31.get_s (ref.cast (ref i31) (local.get $amt)))
               (i32.const 31)))))

   (func (export "uint32_shift_right")
      (param $a (ref eq)) (param $amt (ref eq)) (result (ref eq))
      (return_call $wrap_u32
         (i32.shr_u (call $unwrap_u32 (local.get $a))
            (i32.and (i31.get_s (ref.cast (ref i31) (local.get $amt)))
               (i32.const 31)))))
)
