// js_of_ocaml runtime shims for the Parquet/Zstd primitives used by
// Parser.BallyhooCOTTAS (via Parquet.Footer).
//
// Two primitives are exported here:
//
//   caml_parquet_zstd_decompress_hex(compressed_hex, expected_size_string)
//     Mirrors experimental_ocaml_glue/parquet_zstd_stubs.c. Takes a hex
//     string of the compressed bytes + the expected decompressed size
//     (as a decimal string) and returns either [0, out_hex] (OCaml
//     Some out_hex) or 0 (OCaml None) on any failure.
//     JS backend: fzstd.decompress (vendored under vendor/fzstd.umd.js,
//     concatenated into the factoidal.js bundle so globalThis.fzstd is
//     available at load time).
//
//   caml_parquet_fetch_range_hex(path, start_string, count_string)
//     Optional fast path for the runtime glue: given a path-or-URL and
//     a byte range, return Some hex or None. Currently unreferenced by
//     the F*-extracted OCaml (the patched Parquet_Footer.ml uses
//     open_in_bin/seek_in, which js_of_ocaml routes through the
//     pseudo-filesystem). Exposed so the demo page and future URL-aware
//     OCaml shims can delegate remote reads to this primitive rather
//     than preloading the whole file.
//
// Hex encoding matches the C stub: uppercase, two hex digits per byte,
// no separators. OCaml [Prims.nat] values arrive as zarith bigints;
// we convert them to JS numbers via [.toString()] for safety with
// multi-MB files (ordinary [Number] is enough for single-page reads
// but [Prims.string_of_int] is what the OCaml side passes in anyway).

//Provides: caml_parquet_hex_to_bytes
function caml_parquet_hex_to_bytes(hex) {
  // Accepts MlBytes or plain JS string. The OCaml-extracted code passes
  // Prims.string which js_of_ocaml represents as either a plain JS
  // string or an MlBytes depending on build flags; handle both.
  if (hex && typeof hex === "object" && typeof hex.c === "string") hex = hex.c;
  if (typeof hex !== "string") return null;
  if ((hex.length % 2) !== 0) return null;
  var n = hex.length / 2;
  var out = new Uint8Array(n);
  for (var i = 0; i < n; i++) {
    var hi = hex.charCodeAt(2 * i);
    var lo = hex.charCodeAt(2 * i + 1);
    var hv = hi >= 48 && hi <= 57 ? hi - 48
           : hi >= 65 && hi <= 70 ? hi - 55
           : hi >= 97 && hi <= 102 ? hi - 87 : -1;
    var lv = lo >= 48 && lo <= 57 ? lo - 48
           : lo >= 65 && lo <= 70 ? lo - 55
           : lo >= 97 && lo <= 102 ? lo - 87 : -1;
    if (hv < 0 || lv < 0) return null;
    out[i] = (hv << 4) | lv;
  }
  return out;
}

//Provides: caml_parquet_bytes_to_hex
function caml_parquet_bytes_to_hex(bytes) {
  var hex_digits = "0123456789ABCDEF";
  var n = bytes.length;
  var out = new Array(n);
  for (var i = 0; i < n; i++) {
    var b = bytes[i] & 0xFF;
    out[i] = hex_digits.charAt(b >> 4) + hex_digits.charAt(b & 0xF);
  }
  return out.join("");
}

//Provides: caml_parquet_str
// Normalize an OCaml-string argument that js_of_ocaml might hand us
// either as a plain JS string or as an MlBytes-like object.
function caml_parquet_str(s) {
  if (typeof s === "string") return s;
  if (s && typeof s === "object" && typeof s.c === "string") return s.c;
  return String(s);
}

//Provides: caml_parquet_zstd_decompress_hex
//Requires: caml_parquet_hex_to_bytes, caml_parquet_bytes_to_hex, caml_parquet_str
function caml_parquet_zstd_decompress_hex(v_hex, v_expected_size) {
  try {
    var hex = caml_parquet_str(v_hex);
    var expected_str = caml_parquet_str(v_expected_size);
    var expected = parseInt(expected_str, 10);
    if (!isFinite(expected) || expected < 0) return 0;
    var compressed = caml_parquet_hex_to_bytes(hex);
    if (compressed === null) return 0;

    var fzstd_ns = (typeof globalThis !== "undefined" && globalThis.fzstd)
                 || (typeof self !== "undefined" && self.fzstd)
                 || (typeof window !== "undefined" && window.fzstd)
                 || null;
    if (fzstd_ns === null) {
      // Try Node require() fallback for `fzstd` installed from npm.
      try {
        if (typeof require === "function") fzstd_ns = require("fzstd");
      } catch (_e) { fzstd_ns = null; }
    }
    if (fzstd_ns === null || typeof fzstd_ns.decompress !== "function") {
      // No zstd library reachable — return None rather than crashing.
      // The caller (Parquet_Footer) will surface this as "Could not
      // read COTTAS row count" up the stack.
      return 0;
    }

    var decompressed = fzstd_ns.decompress(compressed);
    // fzstd may return a Uint8Array that is trimmed to the real size;
    // accept any length equal to or less than expected.
    if (decompressed.length !== expected) {
      // Mirror the C stub: require exact match.
      return 0;
    }
    var out_hex = caml_parquet_bytes_to_hex(decompressed);
    // OCaml [Some x] is [0, x] in js_of_ocaml's representation.
    return [0, out_hex];
  } catch (_e) {
    return 0;
  }
}

//Provides: caml_parquet_fetch_range_hex_node
//Requires: caml_parquet_bytes_to_hex, caml_parquet_str
function caml_parquet_fetch_range_hex_node(path_str, start, count) {
  // Node.js fast path: use node:fs for local paths. Not currently wired
  // into the OCaml-side Parquet_Footer (which uses open_in_bin/seek_in
  // through the js_of_ocaml pseudo-FS), but exposed so Node-side
  // callers can pick it up cheaply.
  try {
    var fs = require("node:fs");
    var fd = fs.openSync(path_str, "r");
    try {
      var buf = Buffer.alloc(count);
      var got = fs.readSync(fd, buf, 0, count, start);
      if (got !== count) return 0;
      return [0, caml_parquet_bytes_to_hex(buf)];
    } finally {
      fs.closeSync(fd);
    }
  } catch (_e) {
    return 0;
  }
}

//Provides: caml_parquet_fetch_range_hex
//Requires: caml_parquet_bytes_to_hex, caml_parquet_str, caml_parquet_fetch_range_hex_node
function caml_parquet_fetch_range_hex(v_path, v_start, v_count) {
  // Synchronous wrapper around a byte-range read. Returns OCaml
  // Some hex or None. Supports:
  //   * http://, https:// URLs via Fetch + Range header (browser/Node 22).
  //     Must be called from a place where synchronous XHR is allowed
  //     (browser main thread) OR the bytes must already be in a
  //     globalThis.factoidalFetchCache[url]: Uint8Array table (a
  //     pre-warm the demo page populates before calling into factoidal).
  //   * node:fs for local paths (delegates to Node fast path).
  //   * js_of_ocaml pseudo-FS for /-rooted paths under Node test harnesses.
  try {
    var path_str = caml_parquet_str(v_path);
    var start_str = caml_parquet_str(v_start);
    var count_str = caml_parquet_str(v_count);
    var start = parseInt(start_str, 10);
    var count = parseInt(count_str, 10);
    if (!isFinite(start) || !isFinite(count) || start < 0 || count < 0) return 0;

    var is_http = /^https?:\/\//i.test(path_str);
    if (is_http) {
      var cache = (typeof globalThis !== "undefined" && globalThis.factoidalFetchCache) || null;
      if (cache && cache[path_str] instanceof Uint8Array) {
        var full = cache[path_str];
        if (start + count > full.length) return 0;
        return [0, caml_parquet_bytes_to_hex(full.subarray(start, start + count))];
      }
      // No prewarmed cache. Synchronous fetch is not portable (browser
      // main-thread XHR is deprecated; Workers can't sync; Node fetch
      // is async). The demo page warms globalThis.factoidalFetchCache
      // before calling factoidal, so this branch is expected to be
      // unreachable in the shipped demo flow. Return None and let the
      // caller report.
      return 0;
    }

    // Local path.
    if (typeof process !== "undefined" && process.versions && process.versions.node) {
      return caml_parquet_fetch_range_hex_node(path_str, start, count);
    }

    // Browser + pseudo-FS: js_of_ocaml's FS has its own primitives.
    // Not wiring that path here — demo.html preloads via MlBytes into
    // globalThis.factoidalFetchCache keyed on the virtual path. The
    // OCaml side reaches local /tmp/foo.parquet via open_in_bin/seek_in
    // and does not call this primitive.
    return 0;
  } catch (_e) {
    return 0;
  }
}
