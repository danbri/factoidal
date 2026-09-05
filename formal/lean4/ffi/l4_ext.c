/* Host call-out for caller-registered SPARQL 1.1 section 17.6 extension
 * functions.  It owns no RDF/SPARQL logic: Lean decides which IRIs may
 * reach the host (Wasm/Ops/ExtFns.lean consults its registry first, and
 * the built-in and geof: families are answered before it), encodes the
 * arguments as SRJ binding-value objects, and decodes the answer.  This
 * file only carries two strings across the boundary.
 *
 * Design: docs/designissues/2026-09-04-lean-extension-functions.md
 *
 * Under Emscripten the body is an EM_JS thunk that calls
 * globalThis.__factoidalExtCall(iri, argsJson), which the JavaScript host
 * installs (npm/factoidal/bin/ext.mjs).  On every other target there is no
 * host, so the answer is the empty string, which Lean reads as "no value"
 * -- the section 17.6 error.  A native build therefore behaves exactly as
 * it did before this file existed.
 */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>

EM_JS(char *, l4_ext_call_js, (const char *iri, const char *args), {
  var bridge = globalThis.__factoidalExtCall;
  if (typeof bridge !== 'function') return 0;
  var out;
  try {
    out = bridge(UTF8ToString(iri), UTF8ToString(args));
  } catch (e) {
    return 0;
  }
  if (typeof out !== 'string' || out.length === 0) return 0;
  var len = lengthBytesUTF8(out) + 1;
  var buf = _malloc(len);
  stringToUTF8(out, buf, len);
  return buf;
});
#else
static char *l4_ext_call_js(const char *iri, const char *args) {
  (void)iri;
  (void)args;
  return 0;
}
#endif

LEAN_EXPORT lean_obj_res l4_ext_call(b_lean_obj_arg iri, b_lean_obj_arg args) {
  char *out = l4_ext_call_js(lean_string_cstr(iri), lean_string_cstr(args));
  if (out == 0) return lean_mk_string("");
  lean_obj_res r = lean_mk_string(out);
  free(out);
  return r;
}
