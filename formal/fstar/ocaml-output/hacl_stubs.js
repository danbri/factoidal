// hacl_stubs.js — js_of_ocaml / Node runtime realisation of the four VC
// crypto primitives that the NATIVE build realises in
// experimental_ocaml_glue/hacl_stubs.c over the vendored HACL* C.
//
// Crypto sourcing policy: skills/crypto-policy/SKILL.md — "Dont roll our own
// crypto!", "pursue HACL*".  These stubs contain NO cryptographic logic:
// every primitive (Ed25519 sign/verify/keygen, SHA-256/384) is a call into
// HACL*'s OWN official WebAssembly build (third_party/hacl-wasm/, the
// `hacl-wasm` npm artifacts), loaded by npm/factoidal/hacl-init.js.  The only
// logic here is the hex <-> byte marshalling around the OCaml string
// boundary — byte-for-byte the same contract as the native C stub:
//
//   caml_hacl_sha256(msg_bytes)                -> 64-char hex digest
//   caml_hacl_ed25519_secret_to_public(sk_hex) -> pk_hex (64 chars) | ""
//   caml_hacl_ed25519_sign(sk_hex, msg_hex)    -> sig_hex (128 chars) | ""
//   caml_hacl_ed25519_verify(pk_hex,msg_hex,sig_hex) -> bool (0/1)
//
// An empty-string return signals a malformed-length/odd-hex input (the F*
// wrapper VC.DataIntegrity treats that as failure); it NEVER signals a
// crypto verdict.  `verify` returns the HACL* verdict unchanged.
//
// This is a rule #11 assume-val realisation (a host-engine call-out to the
// SAME assume vals the native C realises), not new semantics.  It is loaded
// into the bundle by build-ocaml.sh's js_of_ocaml step, exactly like
// parquet_zstd_stubs.js.
//
// SECURITY: if the HACL* wasm module has not been initialised
// (globalThis.__factoidalHacl is unset), every primitive THROWS.  verify
// must never silently succeed when the crypto backend is missing — a
// verify that returns true without checking a signature is a security hole.
// Consumers MUST `await require('.../hacl-init.js').initHacl()` (Node) or
// call the browser initialiser before invoking any VC verify/sign path.

//Provides: caml_hacl_backend
function caml_hacl_backend() {
  var H = (typeof globalThis !== "undefined") ? globalThis.__factoidalHacl : undefined;
  if (!H) {
    throw new Error(
      "factoidal VC crypto: HACL* wasm backend not initialised. " +
      "Call `await require('./hacl-init.js').initHacl()` (Node) or the " +
      "browser initHacl() before any vcVerify/vcSign. Refusing to run " +
      "crypto without the verified backend (would be a security hole).");
  }
  return H;
}

// Normalise an OCaml-string argument that js_of_ocaml may hand us as a plain
// JS string (use-js-string=true) or as an MlBytes-like object, into a
// byte-string (each code unit is a byte value 0..255).  Matches the native
// stub's String_val: raw bytes, NOT a UTF-8 re-encoding.
//Provides: caml_hacl_bytestr
function caml_hacl_bytestr(s) {
  if (s && typeof s === "object") {
    if (typeof s.c === "string") return s.c;                 // MlBytes { c, l, t }
    if (typeof s.toString === "function") return s.toString();
  }
  return String(s);
}

// Byte-string -> Uint8Array (raw bytes; charCode & 0xff).
//Provides: caml_hacl_str_to_u8
//Requires: caml_hacl_bytestr
function caml_hacl_str_to_u8(s) {
  var bs = caml_hacl_bytestr(s);
  var n = bs.length;
  var out = new Uint8Array(n);
  for (var i = 0; i < n; i++) out[i] = bs.charCodeAt(i) & 0xff;
  return out;
}

// Hex OCaml string -> Uint8Array, or null on odd length / non-hex digit.
//Provides: caml_hacl_hex_to_u8
//Requires: caml_hacl_bytestr
function caml_hacl_hex_to_u8(hex) {
  var h = caml_hacl_bytestr(hex);
  if ((h.length % 2) !== 0) return null;
  var n = h.length / 2;
  var out = new Uint8Array(n);
  for (var i = 0; i < n; i++) {
    var hi = h.charCodeAt(2 * i);
    var lo = h.charCodeAt(2 * i + 1);
    var hv = hi >= 48 && hi <= 57 ? hi - 48
           : hi >= 97 && hi <= 102 ? hi - 87
           : hi >= 65 && hi <= 70 ? hi - 55 : -1;
    var lv = lo >= 48 && lo <= 57 ? lo - 48
           : lo >= 97 && lo <= 102 ? lo - 87
           : lo >= 65 && lo <= 70 ? lo - 55 : -1;
    if (hv < 0 || lv < 0) return null;
    out[i] = (hv << 4) | lv;
  }
  return out;
}

// Uint8Array -> lowercase hex string (no separators), matching the C stub.
//Provides: caml_hacl_u8_to_hex
function caml_hacl_u8_to_hex(bytes) {
  var hexd = "0123456789abcdef";
  var n = bytes.length;
  var out = new Array(n);
  for (var i = 0; i < n; i++) {
    var b = bytes[i] & 0xff;
    out[i] = hexd.charAt(b >> 4) + hexd.charAt(b & 0xf);
  }
  return out.join("");
}

// SHA-256 of the raw bytes of the OCaml string -> 64-char lowercase hex.
//Provides: caml_hacl_sha256
//Requires: caml_hacl_backend, caml_hacl_str_to_u8, caml_hacl_u8_to_hex
function caml_hacl_sha256(v_msg) {
  var H = caml_hacl_backend();
  var digest = H.SHA2.hash_256(caml_hacl_str_to_u8(v_msg))[0];
  return caml_hacl_u8_to_hex(digest);
}

// SHA-384 (exposed for parity with the SHA-2 family; VC uses SHA-256, but
// RDFC-1.0 / the SHA-2 assume vals want 384 too). 96-char lowercase hex.
//Provides: caml_hacl_sha384
//Requires: caml_hacl_backend, caml_hacl_str_to_u8, caml_hacl_u8_to_hex
function caml_hacl_sha384(v_msg) {
  var H = caml_hacl_backend();
  var digest = H.SHA2.hash_384(caml_hacl_str_to_u8(v_msg))[0];
  return caml_hacl_u8_to_hex(digest);
}

// Ed25519 secret key (32 bytes, hex) -> public key (32 bytes, hex), or ""
// on a malformed-length / non-hex secret key.
//Provides: caml_hacl_ed25519_secret_to_public
//Requires: caml_hacl_backend, caml_hacl_hex_to_u8, caml_hacl_u8_to_hex
function caml_hacl_ed25519_secret_to_public(v_sk_hex) {
  var H = caml_hacl_backend();
  var sk = caml_hacl_hex_to_u8(v_sk_hex);
  if (sk === null || sk.length !== 32) return "";
  var pk = H.Ed25519.secret_to_public(sk)[0];
  return caml_hacl_u8_to_hex(pk);
}

// Ed25519 sign: (sk_hex[32B], msg_hex) -> signature hex (64 bytes), or ""
// on a malformed secret key / non-hex input.
//Provides: caml_hacl_ed25519_sign
//Requires: caml_hacl_backend, caml_hacl_hex_to_u8, caml_hacl_u8_to_hex
function caml_hacl_ed25519_sign(v_sk_hex, v_msg_hex) {
  var H = caml_hacl_backend();
  var sk = caml_hacl_hex_to_u8(v_sk_hex);
  if (sk === null || sk.length !== 32) return "";
  var msg = caml_hacl_hex_to_u8(v_msg_hex);
  if (msg === null) return "";
  var sig = H.Ed25519.sign(sk, msg)[0];
  return caml_hacl_u8_to_hex(sig);
}

// Ed25519 verify: (pk_hex[32B], msg_hex, sig_hex[64B]) -> bool (0/1).
// A malformed-length / non-hex input is a verdict of false, never true.
//Provides: caml_hacl_ed25519_verify
//Requires: caml_hacl_backend, caml_hacl_hex_to_u8
function caml_hacl_ed25519_verify(v_pk_hex, v_msg_hex, v_sig_hex) {
  var H = caml_hacl_backend();
  var pk = caml_hacl_hex_to_u8(v_pk_hex);
  var msg = caml_hacl_hex_to_u8(v_msg_hex);
  var sig = caml_hacl_hex_to_u8(v_sig_hex);
  if (pk === null || pk.length !== 32) return 0;
  if (msg === null) return 0;
  if (sig === null || sig.length !== 64) return 0;
  var ok = H.Ed25519.verify(pk, msg, sig)[0];
  return ok ? 1 : 0;
}
