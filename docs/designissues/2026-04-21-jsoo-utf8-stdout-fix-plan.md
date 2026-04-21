# js_of_ocaml UTF-8 stdout fix plan — 2026-04-21

Tracking: [#91](https://github.com/danbri/factoidal/issues/91) (UI symptom) and
[#92](https://github.com/danbri/factoidal/issues/92) (architectural write-up).

This is the concrete fix plan for the js-only UTF-8 corruption in the
browser demo. Everything here is orthogonal to the Parser.FastString
workstream (#89) — those are separate issues that happened to surface
together in the same QA pass.

## What the evidence says

From the triage under #92, and the probe performed this morning
(2026-04-21T07:30Z), the corruption is **exclusively present in the
browser**. Specifically:

- `bin/darwin-arm64/factoidal -o json` emits correct UTF-8 bytes for
  a literal containing `Müller` — bytes `4d c3 bc 6c` (M, ü, l).
- `node docs/fstar-extracted/factoidal.js -o json` emits the
  identical bytes `4d c3 bc 6c`. Node stdout capture is clean.
- `tests/unit/utf8_roundtrip.ml` asserts parse → SPARQL eval →
  `print_results_json` → byte-compare — 12 of 12 assertions pass
  natively over six UTF-8 cases (German, French, CJK, emoji).
- In a browser, the same factoidal.js run via the demo's
  `console.log` override produces strings like `"Eve M����r"` where
  the `����` is U+FFFD replacement characters.

That rules out:

- Hypothesis #1 from #92 (post-extraction patches differ between
  js and wasm) — `build-ocaml.sh` applies `ocaml-patches.sh` once
  in `extract`; both js and wasm consume the same patched output.
- Hypothesis #3 (result serializer slicing mid-codepoint) — the
  native binary goes through the same `print_results_json` and the
  bytes survive verbatim.

Which leaves hypothesis #2: js_of_ocaml's **stdout/console bridge
under the browser runtime** is the point of corruption.

## The mechanism, in concrete terms

js_of_ocaml's OCaml `string` is an MlBytes object. In the **Node
runtime**, `Printf.printf` / `print_string` / `print_endline`
eventually call `caml_ml_output_bytes` which writes to
`process.stdout.write(Buffer.from(bytes))`. Node's Buffer is
byte-oriented; the bytes hit the terminal as-is.

In the **browser runtime**, there is no `process.stdout`. jsoo
falls back to a path that goes through `console.log`. Depending on
the jsoo version, this is one of two shapes:

1. **Passing the MlBytes directly to `console.log`.** In that case
   the browser's default `console.log` formatter calls
   `MlBytes.prototype.toString()`, which — if jsoo was compiled in
   `--use-js-string=no` mode (our default) — maps each OCaml byte
   to a JS string element of code unit = byte value. Byte `0xC3`
   becomes U+00C3 (`Ã`), byte `0xBC` becomes U+00BC (`¼`). That
   would display as `M¼ller` mojibake, NOT as `M����r`.
2. **Passing a string built from `String.fromCharCode(byte)`
   concatenation.** Same shape as (1).

Neither (1) nor (2) produces U+FFFD replacement characters by
itself. U+FFFD only appears when **something downstream treats a
JS string as UTF-16 and tries to re-decode it as UTF-8**, hits an
invalid continuation byte, and substitutes U+FFFD.

That downstream is almost certainly the demo harness's
`args.join(' ')` / `buf.join('\n')` followed by `JSON.parse(slice)`.
Actually `JSON.parse` on a JS string is codepoint-aware and won't
re-decode — it consumes UTF-16 code units. But the **subsequent**
`textContent = value` assignment on a DOM node goes through the
browser's internal UTF-8 handling, and if any of the "bytes" in
the JS string were non-scalar (e.g. a high-surrogate followed by
a non-low-surrogate, or an unpaired high surrogate — which you
get if you map byte `0xED` to U+00ED then a byte `0xA0` to U+00A0,
combinations that coincidentally line up to form an invalid UTF-16
sequence), `textContent` replaces those with U+FFFD.

The test literals in the QA report include mixed-script strings
with Hebrew `ש` (U+05E9) and CJK `日` (U+65E5) — each encoded as
multi-byte UTF-8 that, once mapped byte-per-code-unit into JS,
forms a random-looking sequence of BMP code units that may
accidentally include unpaired surrogates. That would explain why
some characters come through as Latin-1 mojibake (`Ã¼`) and others
as U+FFFD (`����`).

## Proposed fix: a `caml_ml_output_bytes` override stub

jsoo's runtime exposes output primitives via the same
`//Provides:` annotation mechanism we already use for the hash
stubs (see `formal/fstar/ocaml-output/fstar_hash_stubs.js`).
Override the output path so that before the bytes cross the
JS boundary, they are decoded via `TextDecoder('utf-8')` into a
proper JS string. Then when the output is joined, JSON.parse'd,
and eventually DOM-rendered, every step sees valid UTF-16 — no
U+FFFD substitution.

Concrete stub (`formal/fstar/ocaml-output/fstar_utf8_output_stubs.js`,
new file):

```javascript
// In the browser, jsoo's default output path emits OCaml bytes
// as JS strings where each byte is a separate UTF-16 code unit.
// That produces invalid-UTF-16 sequences when the OCaml bytes are
// valid UTF-8 containing multibyte codepoints — and DOM rendering
// substitutes U+FFFD. In Node, the default path uses Buffer which
// is already byte-clean. Override in both environments to route
// through TextDecoder, so the JS string always contains valid
// UTF-16 corresponding to a UTF-8 decode of the OCaml bytes.

//Provides: caml_ml_output_bytes
//Requires: caml_raise_sys_error
var _utf8_decoder = null;
function caml_ml_output_bytes(chan, bytes, off, len) {
  if (!_utf8_decoder) {
    _utf8_decoder = (typeof TextDecoder === 'function')
      ? new TextDecoder('utf-8', { fatal: false, ignoreBOM: true })
      : null;
  }
  var s;
  if (_utf8_decoder && bytes && bytes.c !== undefined) {
    // bytes.c is the OCaml MlBytes string representation — a JS
    // string where each code unit is a byte. Extract as a
    // Uint8Array and UTF-8-decode into a proper JS string.
    var arr = new Uint8Array(len);
    for (var i = 0; i < len; i++) arr[i] = bytes.c.charCodeAt(off + i);
    s = _utf8_decoder.decode(arr);
  } else if (typeof bytes === 'string') {
    s = bytes.substr(off, len);  // already a JS string; passthrough
  } else {
    caml_raise_sys_error('caml_ml_output_bytes: unsupported bytes shape');
    return 0;
  }
  // Dispatch on the channel — 1 = stdout, 2 = stderr in OCaml.
  // jsoo's default runtime keeps a channel table; we short-circuit
  // to console.log / console.error based on the channel's fd.
  var fd = (chan && chan.fd !== undefined) ? chan.fd : 1;
  if (fd === 2) { console.error(s); } else { console.log(s); }
  return 0;
}

//Provides: caml_ml_output
//Requires: caml_ml_output_bytes
function caml_ml_output(chan, s, off, len) {
  // Older OCaml stdlib paths go through caml_ml_output (string
  // variant). Wrap to the bytes variant — the MlBytes .c field
  // is the same shape.
  return caml_ml_output_bytes(chan, { c: s }, off, len);
}
```

Wire into `build-ocaml.sh` js step alongside the existing
`fstar_int_stubs.js` / `fstar_hash_stubs.js` / `parquet_zstd_stubs.js`:

```
js_of_ocaml \
  +zarith_stubs_js/biginteger.js \
  +zarith_stubs_js/runtime.js \
  fstar_int_stubs.js \
  fstar_hash_stubs.js \
  fstar_utf8_output_stubs.js \   # NEW
  parquet_zstd_stubs.js \
  factoidal.byte \
  -o ../../../docs/fstar-extracted/factoidal.js
```

And the same for the `w3c-runner.js` build line.

## Validation

Three layers:

1. **Unit tests** — extend `tests/unit/utf8_roundtrip.ml` with one
   assertion that writes to stdout and reads back, but we can't do
   that portably under OCaml without spawning a subprocess, so this
   stays as it is (the assertion at OCaml layer already passes).

2. **Node-level**: run `node docs/fstar-extracted/factoidal.js
   -d tmp.ttl -e '...' -o json` on a multibyte literal and grep
   the output. Should continue to show correct bytes (Node runtime
   path was already clean).

3. **Browser-level**: Playwright script that opens
   `docs/fstar-extracted/index.html`, picks the People dataset
   (which contains `Eve Müller`@de), runs the default query, and
   asserts the DOM text for the `?o` column equals `"Eve Müller"@de`
   byte-for-byte. This is the acceptance test for the fix.

Add the Playwright test under `tests/browser/` as a new test
directory, separate from `tests/unit/`.

## Scope

Fix only the output path. Do NOT touch:

- The SPARQL evaluator or any F* code — the F* is correct.
- The result JSON serializer — bytes-clean per the native test.
- `factoidal_cli.ml` output functions — correct.
- Any non-jsoo runtime (native, wasm).

## Risks

- `TextDecoder` is available in every modern browser and Node 11+.
  Our `engines: node >= 20` in the npm package covers it.
- The override MAY not catch every output path. If OCaml code
  calls `print_char` byte-by-byte into an internal buffer and then
  flushes via a different primitive, we may also need to override
  `caml_ml_flush` and `caml_ml_output_char`. Start minimal; extend
  if the browser smoke test still shows corruption.
- The JSON output path writes a single `print_string` call per
  result row via `Printf.printf "%s"`. That routes through
  `caml_ml_output` / `caml_ml_output_bytes`, both of which we
  override. Should suffice.

## Out of scope (separate tickets)

- UCASE / LCASE Unicode-awareness (#91 finding 2) — pre-existing
  ASCII-only limitation per anti-pattern #10. Not caused by jsoo
  runtime; would need a Unicode-aware case-folding primitive.
- REPLACE regex byte-vs-codepoint (#10 again) — same family.
- ORDER BY / DISTINCT collapsing rows with corrupted bytes
  (the "5 of 6 rows returned" from the demo review) — will
  self-resolve once the bytes stop getting corrupted.

## Sequencing

This lands **after** Parser.FastString Pass 3 (bnode-label scanner
migration) so we don't tangle two workstreams in one commit. A
single subagent commit: new `fstar_utf8_output_stubs.js` + one-line
edit in `build-ocaml.sh` + rebuilt `factoidal.js` + `w3c-runner.js`
+ a Playwright smoke test committed under `tests/browser/`.
