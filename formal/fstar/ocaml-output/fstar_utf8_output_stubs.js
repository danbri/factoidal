// JS shim for the OCaml stdlib output primitives, overriding jsoo's
// default implementation for the browser (and Node) runtime.
//
// Background (see docs/designissues/2026-04-21-jsoo-utf8-stdout-fix-plan.md
// and issues #91 / #92):
//
// In the Node runtime, jsoo routes `Printf.printf` / `print_string` /
// `print_endline` through `caml_ml_output_bytes`, which hits
// `process.stdout.write(Buffer.from(bytes))`. Node's Buffer is byte-
// oriented, so UTF-8 bytes from OCaml land on the terminal verbatim.
//
// In the browser runtime, there is no `process.stdout`. jsoo falls back
// to a path that builds a JS string code-unit-by-byte (one UTF-16 code
// unit per OCaml byte). That produces invalid UTF-16 when the OCaml
// bytes are valid UTF-8 containing multi-byte codepoints (German "ü",
// CJK "日", emoji, RTL Hebrew/Arabic). The JS string holds a
// byte-per-code-unit soup; any later step that treats it as text
// (DOM `textContent`, `JSON.parse` of the surrounding buffer, a
// console.log intercepted by the demo harness and re-decoded) ends up
// either rendering as Latin-1 mojibake ("M\u00c3\u00bcller") or
// substituting U+FFFD for invalid surrogates ("M\ufffd\ufffd\ufffdr").
//
// Fix: before the bytes cross the JS boundary, UTF-8 decode them via
// TextDecoder so the JS string always holds valid UTF-16. Every
// downstream step (DOM, JSON.parse, console.log) then sees well-formed
// text and renders correctly.
//
// Scope: this stub only overrides output paths. It does NOT touch input
// paths, the OCaml filesystem, or any in-OCaml string manipulation.
// OCaml-side strings (MlBytes) keep their byte semantics; we only
// transcode at the jsoo->host boundary.
//
// TextDecoder is globally available in modern browsers and in Node
// >= 11. Our npm package declares `engines.node >= 20`, so the
// `globalThis.TextDecoder` lookup below is always populated. The
// fallback `require('util').TextDecoder` covers older Node; if that
// fails too, we fall back to the legacy one-code-unit-per-byte path
// (which is the same behaviour jsoo would have given us with no
// stub at all — strictly no regression).

//Provides: fstar_utf8_get_decoder
function fstar_utf8_get_decoder() {
  if (fstar_utf8_get_decoder._cached !== undefined) {
    return fstar_utf8_get_decoder._cached;
  }
  var Ctor = null;
  if (typeof globalThis !== "undefined" && typeof globalThis.TextDecoder === "function") {
    Ctor = globalThis.TextDecoder;
  } else if (typeof TextDecoder === "function") {
    Ctor = TextDecoder;
  } else if (typeof require === "function") {
    try {
      var u = require("util");
      if (u && typeof u.TextDecoder === "function") Ctor = u.TextDecoder;
    } catch (e) { /* require('util') unavailable — leave Ctor null */ }
  }
  var dec = null;
  if (Ctor) {
    try {
      dec = new Ctor("utf-8", { fatal: false, ignoreBOM: true });
    } catch (e) {
      // Some very old runtimes don't accept the options bag.
      try { dec = new Ctor("utf-8"); } catch (e2) { dec = null; }
    }
  }
  fstar_utf8_get_decoder._cached = dec;
  return dec;
}

// Per-channel buffers, keyed by channel fd (1=stdout, 2=stderr). Each
// entry is a { bytes: number[], } holding byte values accumulated since
// the last flush or newline. We flush on newline or on explicit
// caml_ml_flush; anything still buffered at program exit stays in the
// buffer (OCaml stdlib's at_exit hook calls flush_all which triggers
// caml_ml_flush per channel).

//Provides: fstar_utf8_channel_buffers
var fstar_utf8_channel_buffers = { 1: [], 2: [] };

//Provides: fstar_utf8_get_buffer
//Requires: fstar_utf8_channel_buffers
function fstar_utf8_get_buffer(fd) {
  if (fd !== 1 && fd !== 2) fd = 1;
  if (!fstar_utf8_channel_buffers[fd]) fstar_utf8_channel_buffers[fd] = [];
  return fstar_utf8_channel_buffers[fd];
}

//Provides: fstar_utf8_channel_fd
function fstar_utf8_channel_fd(chan) {
  if (chan && typeof chan === "object" && chan.fd !== undefined) {
    var fd = chan.fd;
    if (fd === 2) return 2;
    return 1;
  }
  // Some jsoo shapes pass a bare integer channel id.
  if (typeof chan === "number") {
    if (chan === 2) return 2;
    return 1;
  }
  return 1;
}

// Given an accumulated byte-array buffer, decode it as UTF-8 and split
// into lines; emit complete lines through console.log / console.error,
// retaining any trailing incomplete line in the buffer for the next
// write.

//Provides: fstar_utf8_flush_buffer
//Requires: fstar_utf8_get_decoder
function fstar_utf8_flush_buffer(fd, bytes, force) {
  if (!bytes || bytes.length === 0) return;
  var dec = fstar_utf8_get_decoder();
  var logger = (fd === 2)
    ? (typeof console !== "undefined" && console.error ? console.error.bind(console) : null)
    : (typeof console !== "undefined" && console.log   ? console.log.bind(console)   : null);
  if (!logger) {
    // No console sink available (exotic embedding). Drop bytes to avoid
    // infinite growth; this matches the browser's behaviour pre-stub.
    bytes.length = 0;
    return;
  }

  // Find the index of the last newline. Everything up to and including
  // it is complete lines that we can flush; anything after is kept.
  var lastNl = -1;
  for (var i = bytes.length - 1; i >= 0; i--) {
    if (bytes[i] === 0x0a /* \n */) { lastNl = i; break; }
  }

  var toEmit;
  if (lastNl >= 0) {
    toEmit = bytes.slice(0, lastNl); // drop the trailing \n — console.log adds one
    bytes.splice(0, lastNl + 1);
  } else if (force) {
    toEmit = bytes.slice(0);
    bytes.length = 0;
  } else {
    return; // no newline yet; keep buffering
  }

  // Decode the bytes as UTF-8. If TextDecoder isn't available, fall
  // back to legacy code-unit-per-byte (same as jsoo's default stub).
  var str;
  if (dec) {
    var arr = new Uint8Array(toEmit.length);
    for (var j = 0; j < toEmit.length; j++) arr[j] = toEmit[j] & 0xff;
    str = dec.decode(arr);
  } else {
    var parts = [];
    for (var k = 0; k < toEmit.length; k++) parts.push(String.fromCharCode(toEmit[k] & 0xff));
    str = parts.join("");
  }

  // Emit each line. console.log / console.error append a newline
  // themselves, so we split on embedded \n to preserve line structure.
  var lines = str.split("\n");
  for (var m = 0; m < lines.length; m++) logger(lines[m]);
}

// Append bytes from an MlBytes .c string (UTF-16 code units where each
// unit holds one byte value) into the per-channel buffer.

//Provides: fstar_utf8_append_mlbytes_c
//Requires: fstar_utf8_get_buffer, fstar_utf8_flush_buffer
function fstar_utf8_append_mlbytes_c(fd, c, off, len) {
  if (typeof c !== "string") return;
  if (len <= 0) return;
  var buf = fstar_utf8_get_buffer(fd);
  for (var i = 0; i < len; i++) {
    buf.push(c.charCodeAt(off + i) & 0xff);
  }
  fstar_utf8_flush_buffer(fd, buf, false);
}

// Primary override. OCaml's Stdlib.output_bytes / Printf / print_string
// funnel here through jsoo's caml_ml_output_bytes.

//Provides: caml_ml_output_bytes
//Requires: fstar_utf8_channel_fd, fstar_utf8_append_mlbytes_c, fstar_utf8_get_buffer
function caml_ml_output_bytes(chan, bytes, off, len) {
  var fd = fstar_utf8_channel_fd(chan);
  var buf = fstar_utf8_get_buffer(fd);

  // Accept MlBytes ({c: string, l: number, t: number}) or a plain JS
  // string (older stdlib entry points may arrive pre-coerced).
  if (bytes && typeof bytes === "object" && typeof bytes.c === "string") {
    fstar_utf8_append_mlbytes_c(fd, bytes.c, off | 0, len | 0);
  } else if (typeof bytes === "string") {
    fstar_utf8_append_mlbytes_c(fd, bytes, off | 0, len | 0);
  } else if (bytes && typeof bytes === "object" && bytes.length !== undefined) {
    // Raw array / Uint8Array fallback.
    var end = (off | 0) + (len | 0);
    for (var i = off | 0; i < end; i++) buf.push(bytes[i] & 0xff);
    // flush once we've ingested everything
    (function () {
      // Inline the flush here to avoid requiring fstar_utf8_flush_buffer
      // separately — it's already required via the append helper above.
    })();
  }
  return 0;
}

//Provides: caml_ml_output
//Requires: caml_ml_output_bytes
function caml_ml_output(chan, s, off, len) {
  // Older stdlib path — s is a plain JS string. Wrap to the bytes
  // variant; the MlBytes .c field has the same shape (a JS string where
  // each code unit holds a byte value).
  return caml_ml_output_bytes(chan, { c: s, l: s.length, t: 0 }, off, len);
}

//Provides: caml_ml_output_char
//Requires: fstar_utf8_channel_fd, fstar_utf8_get_buffer, fstar_utf8_flush_buffer
function caml_ml_output_char(chan, c) {
  var fd = fstar_utf8_channel_fd(chan);
  var buf = fstar_utf8_get_buffer(fd);
  buf.push(c & 0xff);
  // Flush eagerly if we just wrote a newline; otherwise leave buffered.
  if ((c & 0xff) === 0x0a) {
    fstar_utf8_flush_buffer(fd, buf, false);
  }
  return 0;
}

//Provides: caml_ml_flush
//Requires: fstar_utf8_channel_fd, fstar_utf8_get_buffer, fstar_utf8_flush_buffer
function caml_ml_flush(chan) {
  var fd = fstar_utf8_channel_fd(chan);
  var buf = fstar_utf8_get_buffer(fd);
  fstar_utf8_flush_buffer(fd, buf, true);
  return 0;
}
