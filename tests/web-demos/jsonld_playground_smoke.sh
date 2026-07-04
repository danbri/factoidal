#!/usr/bin/env bash
# tests/web-demos/jsonld_playground_smoke.sh
#
# Smoke test for docs/fstar-extracted/demo-jsonld-playground.html: runs
# the exact same toRdf()/canonicalize() calls the page makes on its
# preloaded example, through the shared engine-call module
# (docs/fstar-extracted/jsonld-playground-client.mjs) driven by the
# js_of_ocaml bundle mirrored to docs/npm/foafos/ (the Pages tree) --
# the same artifact the browser page loads, so a pass here is evidence
# the Pages-mirrored package actually runs the JSON-LD pipeline, not
# just that the SPARQL query path works.
#
# Also asserts the honest-failure path: a remote-context @context (a
# bare URL string) must be REJECTED with a non-zero exit and a message
# from the engine -- Parser.JSONLD.fst has no JSONLD.Loader/fetch step,
# so this is not a bug to paper over, it's the documented Phase 1-3b
# boundary (CLAUDE.md's "remote contexts NOT yet supported" note).
#
# Usage:
#   tests/web-demos/jsonld_playground_smoke.sh
#
# Exit code: 0 iff toRdf + canonicalize both produce non-empty,
# parseable N-Quads for the sample document AND the remote-context
# document is rejected.
#
# Requirements: node >= 20 (global fetch/ESM; only node:fs is actually
# used here, via lib/engine-js.js's fs-based CLI driver).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

MIRROR_DIR="docs/npm/foafos"
CLIENT_MODULE="docs/fstar-extracted/jsonld-playground-client.mjs"

for f in "$MIRROR_DIR/factoidal.js" "$MIRROR_DIR/lib/engine-js.js" "$CLIENT_MODULE"; do
  [ -f "$f" ] || {
    echo "Missing $f -- run 'formal/fstar/build-ocaml.sh npm' first." >&2
    exit 2
  }
done
command -v node >/dev/null 2>&1 || { echo "Missing node" >&2; exit 2; }

timeout 60 node --input-type=module -e "
import { runCli } from '$REPO_ROOT/$MIRROR_DIR/lib/engine-js.js';
import { buildJsonLdPlayground, parseNQuadsToRows, SAMPLE_JSONLD, SAMPLE_JSONLD_REMOTE_CONTEXT }
  from '$REPO_ROOT/$CLIENT_MODULE';

process.env.FACTOIDAL_JS_BUNDLE = '$REPO_ROOT/$MIRROR_DIR/factoidal.js';

const playground = buildJsonLdPlayground({ runCli });
let failures = 0;

function check(label, cond) {
  if (cond) { console.log('  PASS  ' + label); }
  else { console.log('  FAIL  ' + label); failures++; }
}

console.log('=== toRdf(SAMPLE_JSONLD) ===');
const rdf = await playground.toRdf(SAMPLE_JSONLD);
check('non-empty N-Quads', rdf.nquads.trim().length > 0);
const rows = parseNQuadsToRows(rdf.nquads);
check('rows parsed (expect 6)', rows.length === 6);
check('base-relative IRI resolved (alice)',
  rows.some(r => r.subject === '<http://example.org/alice>'));
check('container @set (knows bob AND carol)',
  rows.some(r => r.object === '<http://example.org/bob>') &&
  rows.some(r => r.object === '<http://example.org/carol>'));
check('@reverse swapped subject/object (eve knows alice)',
  rows.some(r => r.subject === '<http://example.org/eve>' &&
                 r.object === '<http://example.org/alice>'));
console.log('  (' + rdf.ms.toFixed(1) + ' ms, ' + rows.length + ' rows)');

console.log('=== canonicalize(SAMPLE_JSONLD) ===');
const canon = await playground.canonicalize(SAMPLE_JSONLD);
check('non-empty canonical N-Quads', canon.nquads.trim().length > 0);
check('same triple count as toRdf (no bnodes in this sample)',
  parseNQuadsToRows(canon.nquads).length === rows.length);
console.log('  (' + canon.ms.toFixed(1) + ' ms)');

console.log('=== toRdf(SAMPLE_JSONLD_REMOTE_CONTEXT) -- must FAIL honestly ===');
let remoteThrew = null;
try {
  await playground.toRdf(SAMPLE_JSONLD_REMOTE_CONTEXT);
} catch (e) {
  remoteThrew = e;
}
check('remote-context input rejected (not silently empty-output)', remoteThrew !== null);
if (remoteThrew) {
  check('error carries engine diagnostic text',
    /invalid JSON-LD|JSON-LD/i.test(remoteThrew.message));
  console.log('  (engine said: ' + remoteThrew.message.trim().slice(0, 120) + ')');
}

console.log('===');
if (failures === 0) {
  console.log('jsonld playground smoke: ALL PASS');
  process.exit(0);
} else {
  console.error('jsonld playground smoke: ' + failures + ' FAILED -- see above');
  process.exit(1);
}
"
