(* fstar_pure_hashes.ml — pure OCaml implementations of MD5/SHA-1/SHA-2.
 *
 * Why this file exists:
 *   - SPARQL11.Algebra.fst declares `hash_md5`, `hash_sha1`, `hash_sha256`,
 *     `hash_sha384`, `hash_sha512` as `assume val`.
 *   - The `ocaml-patches.sh` glue used to wire these to `Digest`, `Sha1`,
 *     `Sha256`, `Sha512`, and `Digestif.SHA384`, which pull in C
 *     primitives. Those primitives have no binding under `wasm_of_ocaml`,
 *     so the W3C `functions` suite crashed with `WebAssembly.Exception`.
 *   - Pure OCaml implementations work uniformly on native, js_of_ocaml,
 *     and wasm_of_ocaml with no runtime stubs.
 *
 * Hashes aren't hot paths in the SPARQL engine; clarity matters more than
 * micro-optimisation. All five functions take a UTF-8 byte string and
 * return the lowercase hex digest.
 *
 * References:
 *   - MD5:     RFC 1321
 *   - SHA-1:   RFC 3174 / FIPS 180-4 section 6.1
 *   - SHA-256: FIPS 180-4 section 6.2
 *   - SHA-384 / SHA-512: FIPS 180-4 sections 6.4 / 6.5
 *)

(* ------------------------------------------------------------------ *)
(* Common helpers                                                     *)
(* ------------------------------------------------------------------ *)

let hex_of_bytes (b : Bytes.t) : string =
  let n = Bytes.length b in
  let buf = Buffer.create (n * 2) in
  for i = 0 to n - 1 do
    Buffer.add_string buf (Printf.sprintf "%02x" (Char.code (Bytes.get b i)))
  done;
  Buffer.contents buf

(* ------------------------------------------------------------------ *)
(* MD5  (RFC 1321)                                                    *)
(* ------------------------------------------------------------------ *)

module MD5 = struct
  (* Per-round shift amounts *)
  let s = [|
    7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22;
    5;  9; 14; 20; 5;  9; 14; 20; 5;  9; 14; 20; 5;  9; 14; 20;
    4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23;
    6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21
  |]

  (* K[i] = floor(2^32 * |sin(i + 1)|) for i = 0..63. Hardcoded from RFC 1321. *)
  let k = [|
    0xd76aa478l; 0xe8c7b756l; 0x242070dbl; 0xc1bdceeel;
    0xf57c0fafl; 0x4787c62al; 0xa8304613l; 0xfd469501l;
    0x698098d8l; 0x8b44f7afl; 0xffff5bb1l; 0x895cd7bel;
    0x6b901122l; 0xfd987193l; 0xa679438el; 0x49b40821l;
    0xf61e2562l; 0xc040b340l; 0x265e5a51l; 0xe9b6c7aal;
    0xd62f105dl; 0x02441453l; 0xd8a1e681l; 0xe7d3fbc8l;
    0x21e1cde6l; 0xc33707d6l; 0xf4d50d87l; 0x455a14edl;
    0xa9e3e905l; 0xfcefa3f8l; 0x676f02d9l; 0x8d2a4c8al;
    0xfffa3942l; 0x8771f681l; 0x6d9d6122l; 0xfde5380cl;
    0xa4beea44l; 0x4bdecfa9l; 0xf6bb4b60l; 0xbebfbc70l;
    0x289b7ec6l; 0xeaa127fal; 0xd4ef3085l; 0x04881d05l;
    0xd9d4d039l; 0xe6db99e5l; 0x1fa27cf8l; 0xc4ac5665l;
    0xf4292244l; 0x432aff97l; 0xab9423a7l; 0xfc93a039l;
    0x655b59c3l; 0x8f0ccc92l; 0xffeff47dl; 0x85845dd1l;
    0x6fa87e4fl; 0xfe2ce6e0l; 0xa3014314l; 0x4e0811a1l;
    0xf7537e82l; 0xbd3af235l; 0x2ad7d2bbl; 0xeb86d391l
  |]

  let rotl32 (x : int32) (n : int) : int32 =
    let open Int32 in
    logor (shift_left x n) (shift_right_logical x (32 - n))

  (* Process the already-padded message (length multiple of 64 bytes). *)
  let process (msg : Bytes.t) : int32 array =
    let a0 = ref 0x67452301l in
    let b0 = ref 0xefcdab89l in
    let c0 = ref 0x98badcfel in
    let d0 = ref 0x10325476l in
    let len = Bytes.length msg in
    let nblocks = len / 64 in
    let m = Array.make 16 0l in
    for blk = 0 to nblocks - 1 do
      let base = blk * 64 in
      for j = 0 to 15 do
        let p = base + j * 4 in
        let b0' = Int32.of_int (Char.code (Bytes.get msg p)) in
        let b1' = Int32.of_int (Char.code (Bytes.get msg (p + 1))) in
        let b2' = Int32.of_int (Char.code (Bytes.get msg (p + 2))) in
        let b3' = Int32.of_int (Char.code (Bytes.get msg (p + 3))) in
        m.(j) <-
          Int32.logor b0'
            (Int32.logor (Int32.shift_left b1' 8)
              (Int32.logor (Int32.shift_left b2' 16) (Int32.shift_left b3' 24)))
      done;
      let a = ref !a0 in
      let b = ref !b0 in
      let c = ref !c0 in
      let d = ref !d0 in
      for i = 0 to 63 do
        let f, g =
          if i < 16 then
            Int32.logor (Int32.logand !b !c) (Int32.logand (Int32.lognot !b) !d),
            i
          else if i < 32 then
            Int32.logor (Int32.logand !d !b) (Int32.logand (Int32.lognot !d) !c),
            (5 * i + 1) mod 16
          else if i < 48 then
            Int32.logxor !b (Int32.logxor !c !d),
            (3 * i + 5) mod 16
          else
            Int32.logxor !c (Int32.logor !b (Int32.lognot !d)),
            (7 * i) mod 16
        in
        let tmp = !d in
        let sum = Int32.add (Int32.add !a f) (Int32.add k.(i) m.(g)) in
        d := !c;
        c := !b;
        b := Int32.add !b (rotl32 sum s.(i));
        a := tmp
      done;
      a0 := Int32.add !a0 !a;
      b0 := Int32.add !b0 !b;
      c0 := Int32.add !c0 !c;
      d0 := Int32.add !d0 !d
    done;
    [| !a0; !b0; !c0; !d0 |]

  (* MD5 padding: 0x80, zero padding, then 64-bit little-endian length in
     bits. *)
  let pad (s : string) : Bytes.t =
    let len = String.length s in
    let bit_len = Int64.mul (Int64.of_int len) 8L in
    let rem = len mod 64 in
    (* need (len + 1 + pad_zeros + 8) % 64 == 0 *)
    let pad_zeros =
      if rem < 56 then 55 - rem
      else 119 - rem
    in
    let total = len + 1 + pad_zeros + 8 in
    let b = Bytes.make total '\x00' in
    Bytes.blit_string s 0 b 0 len;
    Bytes.set b len '\x80';
    let off = len + 1 + pad_zeros in
    for i = 0 to 7 do
      let byte =
        Int64.to_int
          (Int64.logand
             (Int64.shift_right_logical bit_len (i * 8))
             0xffL)
      in
      Bytes.set b (off + i) (Char.chr byte)
    done;
    b

  let hex (s : string) : string =
    let padded = pad s in
    let state = process padded in
    (* Little-endian output per RFC 1321 *)
    let out = Bytes.make 16 '\x00' in
    for i = 0 to 3 do
      let w = state.(i) in
      for j = 0 to 3 do
        let byte =
          Int32.to_int
            (Int32.logand
               (Int32.shift_right_logical w (j * 8))
               0xffl)
        in
        Bytes.set out (i * 4 + j) (Char.chr byte)
      done
    done;
    hex_of_bytes out
end

(* ------------------------------------------------------------------ *)
(* SHA-1  (FIPS 180-4 section 6.1)                                    *)
(* ------------------------------------------------------------------ *)

module SHA1 = struct
  let rotl32 (x : int32) (n : int) : int32 =
    let open Int32 in
    logor (shift_left x n) (shift_right_logical x (32 - n))

  (* Big-endian padding: 0x80, zero padding, then 64-bit BE length in bits. *)
  let pad (s : string) : Bytes.t =
    let len = String.length s in
    let bit_len = Int64.mul (Int64.of_int len) 8L in
    let rem = len mod 64 in
    let pad_zeros =
      if rem < 56 then 55 - rem
      else 119 - rem
    in
    let total = len + 1 + pad_zeros + 8 in
    let b = Bytes.make total '\x00' in
    Bytes.blit_string s 0 b 0 len;
    Bytes.set b len '\x80';
    let off = len + 1 + pad_zeros in
    for i = 0 to 7 do
      let byte =
        Int64.to_int
          (Int64.logand
             (Int64.shift_right_logical bit_len ((7 - i) * 8))
             0xffL)
      in
      Bytes.set b (off + i) (Char.chr byte)
    done;
    b

  let process (msg : Bytes.t) : int32 array =
    let h0 = ref 0x67452301l in
    let h1 = ref 0xefcdab89l in
    let h2 = ref 0x98badcfel in
    let h3 = ref 0x10325476l in
    let h4 = ref 0xc3d2e1f0l in
    let len = Bytes.length msg in
    let nblocks = len / 64 in
    let w = Array.make 80 0l in
    for blk = 0 to nblocks - 1 do
      let base = blk * 64 in
      for j = 0 to 15 do
        let p = base + j * 4 in
        let b0 = Int32.of_int (Char.code (Bytes.get msg p)) in
        let b1 = Int32.of_int (Char.code (Bytes.get msg (p + 1))) in
        let b2 = Int32.of_int (Char.code (Bytes.get msg (p + 2))) in
        let b3 = Int32.of_int (Char.code (Bytes.get msg (p + 3))) in
        w.(j) <-
          Int32.logor (Int32.shift_left b0 24)
            (Int32.logor (Int32.shift_left b1 16)
              (Int32.logor (Int32.shift_left b2 8) b3))
      done;
      for j = 16 to 79 do
        let t = Int32.logxor (Int32.logxor w.(j-3) w.(j-8))
                  (Int32.logxor w.(j-14) w.(j-16)) in
        w.(j) <- rotl32 t 1
      done;
      let a = ref !h0 in
      let b = ref !h1 in
      let c = ref !h2 in
      let d = ref !h3 in
      let e = ref !h4 in
      for i = 0 to 79 do
        let f, k =
          if i < 20 then
            Int32.logor (Int32.logand !b !c)
              (Int32.logand (Int32.lognot !b) !d),
            0x5a827999l
          else if i < 40 then
            Int32.logxor !b (Int32.logxor !c !d), 0x6ed9eba1l
          else if i < 60 then
            Int32.logor
              (Int32.logor (Int32.logand !b !c) (Int32.logand !b !d))
              (Int32.logand !c !d),
            0x8f1bbcdcl
          else
            Int32.logxor !b (Int32.logxor !c !d), 0xca62c1d6l
        in
        let tmp =
          Int32.add (Int32.add (rotl32 !a 5) f)
            (Int32.add (Int32.add !e k) w.(i))
        in
        e := !d;
        d := !c;
        c := rotl32 !b 30;
        b := !a;
        a := tmp
      done;
      h0 := Int32.add !h0 !a;
      h1 := Int32.add !h1 !b;
      h2 := Int32.add !h2 !c;
      h3 := Int32.add !h3 !d;
      h4 := Int32.add !h4 !e
    done;
    [| !h0; !h1; !h2; !h3; !h4 |]

  let hex (s : string) : string =
    let padded = pad s in
    let state = process padded in
    let out = Bytes.make 20 '\x00' in
    for i = 0 to 4 do
      let w = state.(i) in
      for j = 0 to 3 do
        let byte =
          Int32.to_int
            (Int32.logand
               (Int32.shift_right_logical w ((3 - j) * 8))
               0xffl)
        in
        Bytes.set out (i * 4 + j) (Char.chr byte)
      done
    done;
    hex_of_bytes out
end

(* ------------------------------------------------------------------ *)
(* SHA-256  (FIPS 180-4 section 6.2)                                  *)
(* ------------------------------------------------------------------ *)

module SHA256 = struct
  let k = [|
    0x428a2f98l; 0x71374491l; 0xb5c0fbcfl; 0xe9b5dba5l;
    0x3956c25bl; 0x59f111f1l; 0x923f82a4l; 0xab1c5ed5l;
    0xd807aa98l; 0x12835b01l; 0x243185bel; 0x550c7dc3l;
    0x72be5d74l; 0x80deb1fel; 0x9bdc06a7l; 0xc19bf174l;
    0xe49b69c1l; 0xefbe4786l; 0x0fc19dc6l; 0x240ca1ccl;
    0x2de92c6fl; 0x4a7484aal; 0x5cb0a9dcl; 0x76f988dal;
    0x983e5152l; 0xa831c66dl; 0xb00327c8l; 0xbf597fc7l;
    0xc6e00bf3l; 0xd5a79147l; 0x06ca6351l; 0x14292967l;
    0x27b70a85l; 0x2e1b2138l; 0x4d2c6dfcl; 0x53380d13l;
    0x650a7354l; 0x766a0abbl; 0x81c2c92el; 0x92722c85l;
    0xa2bfe8a1l; 0xa81a664bl; 0xc24b8b70l; 0xc76c51a3l;
    0xd192e819l; 0xd6990624l; 0xf40e3585l; 0x106aa070l;
    0x19a4c116l; 0x1e376c08l; 0x2748774cl; 0x34b0bcb5l;
    0x391c0cb3l; 0x4ed8aa4al; 0x5b9cca4fl; 0x682e6ff3l;
    0x748f82eel; 0x78a5636fl; 0x84c87814l; 0x8cc70208l;
    0x90befffal; 0xa4506cebl; 0xbef9a3f7l; 0xc67178f2l
  |]

  let rotr32 (x : int32) (n : int) : int32 =
    let open Int32 in
    logor (shift_right_logical x n) (shift_left x (32 - n))

  let shr32 (x : int32) (n : int) : int32 = Int32.shift_right_logical x n

  let pad = SHA1.pad  (* same BE padding scheme *)

  let process (msg : Bytes.t) (h : int32 array) : unit =
    let len = Bytes.length msg in
    let nblocks = len / 64 in
    let w = Array.make 64 0l in
    for blk = 0 to nblocks - 1 do
      let base = blk * 64 in
      for j = 0 to 15 do
        let p = base + j * 4 in
        let b0 = Int32.of_int (Char.code (Bytes.get msg p)) in
        let b1 = Int32.of_int (Char.code (Bytes.get msg (p + 1))) in
        let b2 = Int32.of_int (Char.code (Bytes.get msg (p + 2))) in
        let b3 = Int32.of_int (Char.code (Bytes.get msg (p + 3))) in
        w.(j) <-
          Int32.logor (Int32.shift_left b0 24)
            (Int32.logor (Int32.shift_left b1 16)
              (Int32.logor (Int32.shift_left b2 8) b3))
      done;
      for j = 16 to 63 do
        let w15 = w.(j - 15) in
        let w2 = w.(j - 2) in
        let s0 = Int32.logxor (rotr32 w15 7)
                   (Int32.logxor (rotr32 w15 18) (shr32 w15 3)) in
        let s1 = Int32.logxor (rotr32 w2 17)
                   (Int32.logxor (rotr32 w2 19) (shr32 w2 10)) in
        w.(j) <- Int32.add (Int32.add w.(j - 16) s0)
                   (Int32.add w.(j - 7) s1)
      done;
      let a = ref h.(0) in
      let b = ref h.(1) in
      let c = ref h.(2) in
      let d = ref h.(3) in
      let e = ref h.(4) in
      let f = ref h.(5) in
      let g = ref h.(6) in
      let hh = ref h.(7) in
      for i = 0 to 63 do
        let s1 = Int32.logxor (rotr32 !e 6)
                   (Int32.logxor (rotr32 !e 11) (rotr32 !e 25)) in
        let ch = Int32.logxor (Int32.logand !e !f)
                   (Int32.logand (Int32.lognot !e) !g) in
        let t1 = Int32.add (Int32.add !hh s1)
                   (Int32.add (Int32.add ch k.(i)) w.(i)) in
        let s0 = Int32.logxor (rotr32 !a 2)
                   (Int32.logxor (rotr32 !a 13) (rotr32 !a 22)) in
        let maj =
          Int32.logxor (Int32.logand !a !b)
            (Int32.logxor (Int32.logand !a !c) (Int32.logand !b !c))
        in
        let t2 = Int32.add s0 maj in
        hh := !g;
        g := !f;
        f := !e;
        e := Int32.add !d t1;
        d := !c;
        c := !b;
        b := !a;
        a := Int32.add t1 t2
      done;
      h.(0) <- Int32.add h.(0) !a;
      h.(1) <- Int32.add h.(1) !b;
      h.(2) <- Int32.add h.(2) !c;
      h.(3) <- Int32.add h.(3) !d;
      h.(4) <- Int32.add h.(4) !e;
      h.(5) <- Int32.add h.(5) !f;
      h.(6) <- Int32.add h.(6) !g;
      h.(7) <- Int32.add h.(7) !hh
    done

  let initial_h () = [|
    0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
    0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l
  |]

  let hex (s : string) : string =
    let padded = pad s in
    let h = initial_h () in
    process padded h;
    let out = Bytes.make 32 '\x00' in
    for i = 0 to 7 do
      let w = h.(i) in
      for j = 0 to 3 do
        let byte =
          Int32.to_int
            (Int32.logand
               (Int32.shift_right_logical w ((3 - j) * 8))
               0xffl)
        in
        Bytes.set out (i * 4 + j) (Char.chr byte)
      done
    done;
    hex_of_bytes out
end

(* ------------------------------------------------------------------ *)
(* SHA-512 / SHA-384  (FIPS 180-4 sections 6.4 and 6.5)               *)
(* ------------------------------------------------------------------ *)

module SHA512 = struct
  let k = [|
    0x428a2f98d728ae22L; 0x7137449123ef65cdL;
    0xb5c0fbcfec4d3b2fL; 0xe9b5dba58189dbbcL;
    0x3956c25bf348b538L; 0x59f111f1b605d019L;
    0x923f82a4af194f9bL; 0xab1c5ed5da6d8118L;
    0xd807aa98a3030242L; 0x12835b0145706fbeL;
    0x243185be4ee4b28cL; 0x550c7dc3d5ffb4e2L;
    0x72be5d74f27b896fL; 0x80deb1fe3b1696b1L;
    0x9bdc06a725c71235L; 0xc19bf174cf692694L;
    0xe49b69c19ef14ad2L; 0xefbe4786384f25e3L;
    0x0fc19dc68b8cd5b5L; 0x240ca1cc77ac9c65L;
    0x2de92c6f592b0275L; 0x4a7484aa6ea6e483L;
    0x5cb0a9dcbd41fbd4L; 0x76f988da831153b5L;
    0x983e5152ee66dfabL; 0xa831c66d2db43210L;
    0xb00327c898fb213fL; 0xbf597fc7beef0ee4L;
    0xc6e00bf33da88fc2L; 0xd5a79147930aa725L;
    0x06ca6351e003826fL; 0x142929670a0e6e70L;
    0x27b70a8546d22ffcL; 0x2e1b21385c26c926L;
    0x4d2c6dfc5ac42aedL; 0x53380d139d95b3dfL;
    0x650a73548baf63deL; 0x766a0abb3c77b2a8L;
    0x81c2c92e47edaee6L; 0x92722c851482353bL;
    0xa2bfe8a14cf10364L; 0xa81a664bbc423001L;
    0xc24b8b70d0f89791L; 0xc76c51a30654be30L;
    0xd192e819d6ef5218L; 0xd69906245565a910L;
    0xf40e35855771202aL; 0x106aa07032bbd1b8L;
    0x19a4c116b8d2d0c8L; 0x1e376c085141ab53L;
    0x2748774cdf8eeb99L; 0x34b0bcb5e19b48a8L;
    0x391c0cb3c5c95a63L; 0x4ed8aa4ae3418acbL;
    0x5b9cca4f7763e373L; 0x682e6ff3d6b2b8a3L;
    0x748f82ee5defb2fcL; 0x78a5636f43172f60L;
    0x84c87814a1f0ab72L; 0x8cc702081a6439ecL;
    0x90befffa23631e28L; 0xa4506cebde82bde9L;
    0xbef9a3f7b2c67915L; 0xc67178f2e372532bL;
    0xca273eceea26619cL; 0xd186b8c721c0c207L;
    0xeada7dd6cde0eb1eL; 0xf57d4f7fee6ed178L;
    0x06f067aa72176fbaL; 0x0a637dc5a2c898a6L;
    0x113f9804bef90daeL; 0x1b710b35131c471bL;
    0x28db77f523047d84L; 0x32caab7b40c72493L;
    0x3c9ebe0a15c9bebcL; 0x431d67c49c100d4cL;
    0x4cc5d4becb3e42b6L; 0x597f299cfc657e2aL;
    0x5fcb6fab3ad6faecL; 0x6c44198c4a475817L
  |]

  let rotr64 (x : int64) (n : int) : int64 =
    let open Int64 in
    logor (shift_right_logical x n) (shift_left x (64 - n))

  let shr64 (x : int64) (n : int) : int64 = Int64.shift_right_logical x n

  (* SHA-512 padding: message bit length encoded as a 128-bit big-endian
     integer. We don't support messages of length >= 2^61 bytes (≈2 EB);
     the high 64 bits are always zero. *)
  let pad (s : string) : Bytes.t =
    let len = String.length s in
    let bit_len = Int64.mul (Int64.of_int len) 8L in
    let rem = len mod 128 in
    let pad_zeros =
      if rem < 112 then 111 - rem
      else 239 - rem
    in
    let total = len + 1 + pad_zeros + 16 in
    let b = Bytes.make total '\x00' in
    Bytes.blit_string s 0 b 0 len;
    Bytes.set b len '\x80';
    let off = len + 1 + pad_zeros + 8 (* skip the high 64 bits (zero) *) in
    for i = 0 to 7 do
      let byte =
        Int64.to_int
          (Int64.logand
             (Int64.shift_right_logical bit_len ((7 - i) * 8))
             0xffL)
      in
      Bytes.set b (off + i) (Char.chr byte)
    done;
    b

  let process (msg : Bytes.t) (h : int64 array) : unit =
    let len = Bytes.length msg in
    let nblocks = len / 128 in
    let w = Array.make 80 0L in
    for blk = 0 to nblocks - 1 do
      let base = blk * 128 in
      for j = 0 to 15 do
        let p = base + j * 8 in
        let acc = ref 0L in
        for b_idx = 0 to 7 do
          acc := Int64.logor
                   (Int64.shift_left !acc 8)
                   (Int64.of_int (Char.code (Bytes.get msg (p + b_idx))))
        done;
        w.(j) <- !acc
      done;
      for j = 16 to 79 do
        let w15 = w.(j - 15) in
        let w2 = w.(j - 2) in
        let s0 = Int64.logxor (rotr64 w15 1)
                   (Int64.logxor (rotr64 w15 8) (shr64 w15 7)) in
        let s1 = Int64.logxor (rotr64 w2 19)
                   (Int64.logxor (rotr64 w2 61) (shr64 w2 6)) in
        w.(j) <- Int64.add (Int64.add w.(j - 16) s0)
                   (Int64.add w.(j - 7) s1)
      done;
      let a = ref h.(0) in
      let b = ref h.(1) in
      let c = ref h.(2) in
      let d = ref h.(3) in
      let e = ref h.(4) in
      let f = ref h.(5) in
      let g = ref h.(6) in
      let hh = ref h.(7) in
      for i = 0 to 79 do
        let s1 = Int64.logxor (rotr64 !e 14)
                   (Int64.logxor (rotr64 !e 18) (rotr64 !e 41)) in
        let ch = Int64.logxor (Int64.logand !e !f)
                   (Int64.logand (Int64.lognot !e) !g) in
        let t1 = Int64.add (Int64.add !hh s1)
                   (Int64.add (Int64.add ch k.(i)) w.(i)) in
        let s0 = Int64.logxor (rotr64 !a 28)
                   (Int64.logxor (rotr64 !a 34) (rotr64 !a 39)) in
        let maj =
          Int64.logxor (Int64.logand !a !b)
            (Int64.logxor (Int64.logand !a !c) (Int64.logand !b !c))
        in
        let t2 = Int64.add s0 maj in
        hh := !g;
        g := !f;
        f := !e;
        e := Int64.add !d t1;
        d := !c;
        c := !b;
        b := !a;
        a := Int64.add t1 t2
      done;
      h.(0) <- Int64.add h.(0) !a;
      h.(1) <- Int64.add h.(1) !b;
      h.(2) <- Int64.add h.(2) !c;
      h.(3) <- Int64.add h.(3) !d;
      h.(4) <- Int64.add h.(4) !e;
      h.(5) <- Int64.add h.(5) !f;
      h.(6) <- Int64.add h.(6) !g;
      h.(7) <- Int64.add h.(7) !hh
    done

  let initial_h_512 () = [|
    0x6a09e667f3bcc908L; 0xbb67ae8584caa73bL;
    0x3c6ef372fe94f82bL; 0xa54ff53a5f1d36f1L;
    0x510e527fade682d1L; 0x9b05688c2b3e6c1fL;
    0x1f83d9abfb41bd6bL; 0x5be0cd19137e2179L
  |]

  let initial_h_384 () = [|
    0xcbbb9d5dc1059ed8L; 0x629a292a367cd507L;
    0x9159015a3070dd17L; 0x152fecd8f70e5939L;
    0x67332667ffc00b31L; 0x8eb44a8768581511L;
    0xdb0c2e0d64f98fa7L; 0x47b5481dbefa4fa4L
  |]

  let digest_bytes (h : int64 array) (nwords : int) : Bytes.t =
    let out = Bytes.make (nwords * 8) '\x00' in
    for i = 0 to nwords - 1 do
      let w = h.(i) in
      for j = 0 to 7 do
        let byte =
          Int64.to_int
            (Int64.logand
               (Int64.shift_right_logical w ((7 - j) * 8))
               0xffL)
        in
        Bytes.set out (i * 8 + j) (Char.chr byte)
      done
    done;
    out

  let hex_512 (s : string) : string =
    let padded = pad s in
    let h = initial_h_512 () in
    process padded h;
    hex_of_bytes (digest_bytes h 8)

  let hex_384 (s : string) : string =
    let padded = pad s in
    let h = initial_h_384 () in
    process padded h;
    (* SHA-384 outputs only the first 6 words (48 bytes) *)
    hex_of_bytes (digest_bytes h 6)
end

(* ------------------------------------------------------------------ *)
(* Public API used by ocaml-patches.sh                                *)
(* ------------------------------------------------------------------ *)

let md5 (s : string) : string = MD5.hex s
let sha1 (s : string) : string = SHA1.hex s
let sha256 (s : string) : string = SHA256.hex s
let sha384 (s : string) : string = SHA512.hex_384 s
let sha512 (s : string) : string = SHA512.hex_512 s
