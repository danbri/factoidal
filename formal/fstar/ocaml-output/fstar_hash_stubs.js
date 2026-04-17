// JS shims for the C primitives the `sha` and `digestif` opam packages
// register at module load. fstar.lib pulls these in transitively; without
// the shim, js_of_ocaml emits throwing stubs and top-level init crashes
// with "stub_sha512_init not implemented".
//
// Strategy:
//   - Hash state is an opaque JS object ({ algo, data } accumulator).
//   - init returns a fresh state.
//   - update appends input (as a UTF-8 string).
//   - finalize computes the digest using the environment's crypto API:
//       * Node: require('node:crypto').createHash(algo).update(input).digest()
//       * Browser: not supported yet (SubtleCrypto is async; factoidal's
//         hash_* path is sync). Returns a placeholder; MD5/SHA queries
//         will be wrong in the browser until we add a sync implementation
//         or migrate to an async path.
//   - to_hex renders the digest as a lowercase hex string.
//   - ctx_size / max_outlen / key_size return plausible constants so the
//     digestif module's constructor doesn't throw.
//
// Most factoidal users don't touch hash built-ins. This shim exists to
// make top-level init succeed so non-hashing queries work in the browser.

//Provides: ffactoidal_hash_digest_hex
function ffactoidal_hash_digest_hex(algo, data) {
  if (typeof process !== "undefined" && process.versions && process.versions.node) {
    var crypto = require("node:crypto");
    return crypto.createHash(algo).update(data, "utf8").digest("hex");
  }
  // Browser fallback — not async-safe. Use a tiny pure-JS MD5/SHA later.
  return "";
}

// ---- sha (vincenthz/ocaml-sha) ------------------------------------------

//Provides: stub_sha1_init
function stub_sha1_init() { return { algo: "sha1", data: "" }; }
//Provides: stub_sha1_update
function stub_sha1_update(ctx, buf, off, len) {
  // OCaml passes an MlBytes; approximate by concatenating the whole buffer.
  var s = (typeof buf === "object" && buf.c) ? buf.c : String(buf);
  ctx.data += (off !== undefined && len !== undefined) ? s.substr(off, len) : s;
  return 0;
}
//Provides: stub_sha1_finalize
//Requires: ffactoidal_hash_digest_hex
function stub_sha1_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha1", ctx.data); return ctx; }
//Provides: stub_sha1_to_hex
function stub_sha1_to_hex(ctx) { return ctx.hex || ""; }

//Provides: stub_sha256_init
function stub_sha256_init() { return { algo: "sha256", data: "" }; }
//Provides: stub_sha256_update
//Requires: stub_sha1_update
function stub_sha256_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: stub_sha256_finalize
//Requires: ffactoidal_hash_digest_hex
function stub_sha256_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha256", ctx.data); return ctx; }
//Provides: stub_sha256_to_hex
function stub_sha256_to_hex(ctx) { return ctx.hex || ""; }

//Provides: stub_sha512_init
function stub_sha512_init() { return { algo: "sha512", data: "" }; }
//Provides: stub_sha512_update
//Requires: stub_sha1_update
function stub_sha512_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: stub_sha512_finalize
//Requires: ffactoidal_hash_digest_hex
function stub_sha512_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha512", ctx.data); return ctx; }
//Provides: stub_sha512_to_hex
function stub_sha512_to_hex(ctx) { return ctx.hex || ""; }

// ---- digestif (mirage-crypto heritage) ----------------------------------
// Only the algorithms we actually use elsewhere (MD5, SHA1, SHA256,
// SHA384, SHA512). The rest (blake2, sha3, whirlpool, rmd160, keccak)
// get init/update/finalize wired the same way but will produce empty
// hashes in browser mode; the F*-extracted code doesn't invoke them.

//Provides: caml_digestif_size_stub
function caml_digestif_size_stub() { return 64; }
//Provides: caml_digestif_max_outlen_stub
function caml_digestif_max_outlen_stub() { return 64; }
//Provides: caml_digestif_key_size_stub
function caml_digestif_key_size_stub() { return 64; }

// A generic digestif algorithm ctx factory.
//Provides: caml_digestif_make_ctx
function caml_digestif_make_ctx(algo) {
  return function () { return { algo: algo, data: "" }; };
}

//Provides: caml_digestif_md5_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_md5_st_init = caml_digestif_make_ctx("md5");
//Provides: caml_digestif_md5_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_md5_ba_init = caml_digestif_make_ctx("md5");
//Provides: caml_digestif_md5_st_update
//Requires: stub_sha1_update
function caml_digestif_md5_st_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: caml_digestif_md5_ba_update
//Requires: stub_sha1_update
function caml_digestif_md5_ba_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: caml_digestif_md5_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_md5_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("md5", ctx.data); return ctx; }
//Provides: caml_digestif_md5_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_md5_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("md5", ctx.data); return ctx; }
//Provides: caml_digestif_md5_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_md5_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha1_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha1_st_init = caml_digestif_make_ctx("sha1");
//Provides: caml_digestif_sha1_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha1_ba_init = caml_digestif_make_ctx("sha1");
//Provides: caml_digestif_sha1_st_update
//Requires: stub_sha1_update
function caml_digestif_sha1_st_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: caml_digestif_sha1_ba_update
//Requires: stub_sha1_update
function caml_digestif_sha1_ba_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: caml_digestif_sha1_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha1_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha1", ctx.data); return ctx; }
//Provides: caml_digestif_sha1_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha1_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha1", ctx.data); return ctx; }
//Provides: caml_digestif_sha1_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha1_ctx_size = caml_digestif_size_stub;

// The remaining digestif algorithms (sha224/256/384/512, sha3_*, blake2*,
// whirlpool, rmd160, keccak_256) follow the same pattern. For brevity
// just wire them to shared init/update/finalize with the algo name — the
// algorithms we can't hand off to Node crypto will return empty.
//Provides: caml_digestif_noop_ctx
function caml_digestif_noop_ctx() { return { algo: "noop", data: "" }; }
//Provides: caml_digestif_noop_update
//Requires: stub_sha1_update
function caml_digestif_noop_update(ctx, buf, off, len) { return stub_sha1_update(ctx, buf, off, len); }
//Provides: caml_digestif_noop_finalize
function caml_digestif_noop_finalize(ctx) { ctx.hex = ""; return ctx; }

//Provides: caml_digestif_sha224_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha224_st_init = caml_digestif_make_ctx("sha224");
//Provides: caml_digestif_sha224_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha224_ba_init = caml_digestif_make_ctx("sha224");
//Provides: caml_digestif_sha224_st_update
//Requires: stub_sha1_update
function caml_digestif_sha224_st_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha224_ba_update
//Requires: stub_sha1_update
function caml_digestif_sha224_ba_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha224_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha224_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha224", ctx.data); return ctx; }
//Provides: caml_digestif_sha224_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha224_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha224", ctx.data); return ctx; }
//Provides: caml_digestif_sha224_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha224_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha256_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha256_st_init = caml_digestif_make_ctx("sha256");
//Provides: caml_digestif_sha256_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha256_ba_init = caml_digestif_make_ctx("sha256");
//Provides: caml_digestif_sha256_st_update
//Requires: stub_sha1_update
function caml_digestif_sha256_st_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha256_ba_update
//Requires: stub_sha1_update
function caml_digestif_sha256_ba_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha256_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha256_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha256", ctx.data); return ctx; }
//Provides: caml_digestif_sha256_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha256_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha256", ctx.data); return ctx; }
//Provides: caml_digestif_sha256_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha256_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha384_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha384_st_init = caml_digestif_make_ctx("sha384");
//Provides: caml_digestif_sha384_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha384_ba_init = caml_digestif_make_ctx("sha384");
//Provides: caml_digestif_sha384_st_update
//Requires: stub_sha1_update
function caml_digestif_sha384_st_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha384_ba_update
//Requires: stub_sha1_update
function caml_digestif_sha384_ba_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha384_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha384_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha384", ctx.data); return ctx; }
//Provides: caml_digestif_sha384_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha384_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha384", ctx.data); return ctx; }
//Provides: caml_digestif_sha384_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha384_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha512_st_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha512_st_init = caml_digestif_make_ctx("sha512");
//Provides: caml_digestif_sha512_ba_init
//Requires: caml_digestif_make_ctx
var caml_digestif_sha512_ba_init = caml_digestif_make_ctx("sha512");
//Provides: caml_digestif_sha512_st_update
//Requires: stub_sha1_update
function caml_digestif_sha512_st_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha512_ba_update
//Requires: stub_sha1_update
function caml_digestif_sha512_ba_update(a,b,c,d) { return stub_sha1_update(a,b,c,d); }
//Provides: caml_digestif_sha512_st_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha512_st_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha512", ctx.data); return ctx; }
//Provides: caml_digestif_sha512_ba_finalize
//Requires: ffactoidal_hash_digest_hex
function caml_digestif_sha512_ba_finalize(ctx) { ctx.hex = ffactoidal_hash_digest_hex("sha512", ctx.data); return ctx; }
//Provides: caml_digestif_sha512_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha512_ctx_size = caml_digestif_size_stub;

// blake2 / sha3 / whirlpool / rmd160 / keccak — init/update/finalize noops.
// F*-extracted hash_md5/hash_sha1/hash_sha256/hash_sha384/hash_sha512 don't
// hit these. If the digestif module's top-level registration invokes them
// at load, the *_ctx_size / *_max_outlen / *_key_size constants keep the
// OCaml-side validation happy.
//Provides: caml_digestif_blake2b_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2b_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2b_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2b_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2b_st_init_with_outlen_and_key
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2b_st_init_with_outlen_and_key = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2b_ba_init_with_outlen_and_key
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2b_ba_init_with_outlen_and_key = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2b_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_blake2b_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_blake2b_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_blake2b_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_blake2b_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_blake2b_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_blake2b_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_blake2b_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_blake2b_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_blake2b_ctx_size = caml_digestif_size_stub;
//Provides: caml_digestif_blake2b_max_outlen
//Requires: caml_digestif_max_outlen_stub
var caml_digestif_blake2b_max_outlen = caml_digestif_max_outlen_stub;
//Provides: caml_digestif_blake2b_key_size
//Requires: caml_digestif_key_size_stub
var caml_digestif_blake2b_key_size = caml_digestif_key_size_stub;

//Provides: caml_digestif_blake2s_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2s_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2s_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2s_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2s_st_init_with_outlen_and_key
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2s_st_init_with_outlen_and_key = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2s_ba_init_with_outlen_and_key
//Requires: caml_digestif_noop_ctx
var caml_digestif_blake2s_ba_init_with_outlen_and_key = caml_digestif_noop_ctx;
//Provides: caml_digestif_blake2s_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_blake2s_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_blake2s_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_blake2s_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_blake2s_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_blake2s_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_blake2s_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_blake2s_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_blake2s_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_blake2s_ctx_size = caml_digestif_size_stub;
//Provides: caml_digestif_blake2s_max_outlen
//Requires: caml_digestif_max_outlen_stub
var caml_digestif_blake2s_max_outlen = caml_digestif_max_outlen_stub;
//Provides: caml_digestif_blake2s_key_size
//Requires: caml_digestif_key_size_stub
var caml_digestif_blake2s_key_size = caml_digestif_key_size_stub;

// sha3_224/256/384/512 + rmd160 + whirlpool + keccak_256 — boilerplate.
//Provides: caml_digestif_sha3_224_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_224_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_224_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_224_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_224_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_224_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_224_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_224_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_224_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_224_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_224_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_224_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_224_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha3_224_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha3_256_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_256_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_256_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_256_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_256_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_256_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_256_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_256_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_256_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_256_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_256_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_256_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_256_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha3_256_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha3_384_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_384_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_384_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_384_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_384_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_384_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_384_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_384_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_384_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_384_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_384_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_384_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_384_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha3_384_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_sha3_512_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_512_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_512_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_sha3_512_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_sha3_512_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_512_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_512_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_sha3_512_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_sha3_512_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_512_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_512_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_sha3_512_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_sha3_512_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_sha3_512_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_keccak_256_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_keccak_256_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_keccak_256_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_keccak_256_ba_finalize = caml_digestif_noop_finalize;

//Provides: caml_digestif_rmd160_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_rmd160_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_rmd160_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_rmd160_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_rmd160_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_rmd160_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_rmd160_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_rmd160_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_rmd160_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_rmd160_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_rmd160_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_rmd160_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_rmd160_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_rmd160_ctx_size = caml_digestif_size_stub;

//Provides: caml_digestif_whirlpool_st_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_whirlpool_st_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_whirlpool_ba_init
//Requires: caml_digestif_noop_ctx
var caml_digestif_whirlpool_ba_init = caml_digestif_noop_ctx;
//Provides: caml_digestif_whirlpool_st_update
//Requires: caml_digestif_noop_update
var caml_digestif_whirlpool_st_update = caml_digestif_noop_update;
//Provides: caml_digestif_whirlpool_ba_update
//Requires: caml_digestif_noop_update
var caml_digestif_whirlpool_ba_update = caml_digestif_noop_update;
//Provides: caml_digestif_whirlpool_st_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_whirlpool_st_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_whirlpool_ba_finalize
//Requires: caml_digestif_noop_finalize
var caml_digestif_whirlpool_ba_finalize = caml_digestif_noop_finalize;
//Provides: caml_digestif_whirlpool_ctx_size
//Requires: caml_digestif_size_stub
var caml_digestif_whirlpool_ctx_size = caml_digestif_size_stub;
