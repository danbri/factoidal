#!/usr/bin/env bash
# tests/web-demos/rif_demo_smoke.sh
#
# Smoke test for docs/fstar-extracted/demo-rif.html: runs the exact
# same rifSmoke()/rifEval() calls the page makes, through the shared
# engine-call module (docs/fstar-extracted/rif-demo-client.mjs), driven
# by a require()-based Node loader for the persistent npm-entry ABI
# bundle (factoidal-npm-entry.js, built from bin/npm-entry/entry_jsoo.ml)
# -- the same artifact the browser page loads via
# npm/factoidal/browser.js's loadNpmEntry() (fetch-based). Node's
# global fetch does not support file: URLs the way a browser's fetch
# resolves a same-origin relative path, so this test uses require()
# directly instead, mirroring npm/factoidal/index.js's own
# loadEntry(). Either way the call lands on the SAME
# factoidalNpmEntry.{rifSmoke,rifEval} exports, which call the SAME
# verified F* functions (RIF_Core_Eval.fixpoint / RIF_Core_Eval.
# one_round / Parser_RIFXML.parse_rif_program) -- so a pass here is
# real evidence the browser page computes the correct saturated graph.
#
# Also asserts the honest-failure path: malformed RIF-XML must be
# REJECTED by rifEval with a non-ok envelope carrying an engine
# diagnostic -- Parser.RIFXML.fst's parse_rif_program returns None on
# anything outside its grammar, and RIF_Core_Tests.
# lemma_parse_none_yields_false is the F*-side proof that this
# short-circuits cleanly; this test is the runtime-observable half of
# that same fact.
#
# Usage:
#   tests/web-demos/rif_demo_smoke.sh
#
# Requirements: node >= 20 (global URL/fetch/ESM; only node:fs, node:path
# and a require() shim via node:module are actually used here -- no
# network fetch happens in this test).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

CLIENT_MODULE="docs/fstar-extracted/rif-demo-client.mjs"
ENTRY_CANDIDATES=(
  "docs/npm/foafos/factoidal-npm-entry.js"
  "docs/fstar-extracted/factoidal-npm-entry.js"
  "npm/factoidal/factoidal-npm-entry.js"
)

[ -f "$CLIENT_MODULE" ] || {
  echo "Missing $CLIENT_MODULE" >&2
  exit 2
}
command -v node >/dev/null 2>&1 || { echo "Missing node" >&2; exit 2; }

FOUND_ENTRY=""
for c in "${ENTRY_CANDIDATES[@]}"; do
  if [ -f "$c" ]; then FOUND_ENTRY="$c"; break; fi
done
if [ -z "$FOUND_ENTRY" ]; then
  echo "Missing factoidal-npm-entry.js in any of: ${ENTRY_CANDIDATES[*]}" >&2
  echo "Run 'formal/fstar/build-ocaml.sh js && formal/fstar/build-ocaml.sh npm' first." >&2
  exit 2
fi

timeout 60 node --input-type=module -e "
import { createRequire } from 'node:module';
import fs from 'node:fs';
import path from 'node:path';
import { buildRifDemo, parseNQuadsToRows, diffSaturatedRows,
         SAMPLE_RIF_XML, SAMPLE_DATA_TTL }
  from '$REPO_ROOT/$CLIENT_MODULE';

const require = createRequire(import.meta.url);

const candidates = [
  process.env.FACTOIDAL_NPM_ENTRY,
  '$REPO_ROOT/docs/npm/foafos/factoidal-npm-entry.js',
  '$REPO_ROOT/docs/fstar-extracted/factoidal-npm-entry.js',
  '$REPO_ROOT/npm/factoidal/factoidal-npm-entry.js',
].filter(Boolean);

function loadAbi() {
  for (const p of candidates) {
    if (!fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
    if (abi && typeof abi.rifSmoke === 'function' && typeof abi.rifEval === 'function') {
      return { abi, path: p };
    }
  }
  return null;
}

const loaded = loadAbi();
let failures = 0;
function check(label, cond) {
  if (cond) { console.log('  PASS  ' + label); }
  else { console.log('  FAIL  ' + label); failures++; }
}

if (!loaded) {
  console.error(
    'No factoidal-npm-entry.js with rifSmoke/rifEval found in: ' +
    candidates.join(', '));
  console.error(
    'Rebuild with formal/fstar/build-ocaml.sh js (and npm) after adding' +
    ' the RIF exports to bin/npm-entry/entry_jsoo.ml.');
  process.exit(2);
}
console.log('Loaded ABI from: ' + loaded.path);
const abi = loaded.abi;

const driver = {
  rifSmoke: async () => {
    const parsed = JSON.parse(abi.rifSmoke());
    if (!parsed.ok) throw new Error(parsed.error || 'rifSmoke failed');
    return parsed;
  },
  rifEval: async (rifXml, dataNQuads) => {
    const parsed = JSON.parse(abi.rifEval(rifXml, dataNQuads));
    if (!parsed.ok) throw new Error(parsed.error || 'rifEval failed');
    return parsed;
  },
  toNQuads: async (ttl) => {
    const parsed = JSON.parse(abi.parseToDatasetJson(ttl, 'turtle', ''));
    if (!parsed.ok) throw new Error(parsed.error || 'Turtle parse failed');
    return parsed.nquads;
  },
};
const demo = buildRifDemo(driver);

// Expected saturated set per RIF.Core.Eval.fst's smoke_saturated
// assert_norm checks: the 3 input triples plus exactly 3 derived ones.
const RDF_TYPE = '<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>';
const SUBCLASSOF = '<http://www.w3.org/2000/01/rdf-schema#subClassOf>';
function hasDerivedTriple(rows, s, p, o) {
  return rows.some((r) =>
    r.derived && r.subject === s && r.predicate === p && r.object === o);
}

console.log('=== rifSmoke() -- live re-run of RIF.Core.Eval.fst smoke_program ===');
const smoke = await demo.runSmoke();
check('ok', smoke.ok === true || smoke.inputCount !== undefined);
check('inputCount === 3', smoke.inputCount === 3);
check('derivedCount === 3', smoke.derivedCount === 3);
check('fuel === 8', smoke.fuel === 8);
check('rounds within (0, fuel]', smoke.rounds > 0 && smoke.rounds <= smoke.fuel);
check('engineMs is a number', typeof smoke.engineMs === 'number');
const smokeRows = diffSaturatedRows(smoke.inputNquads, smoke.saturatedNquads);
check('6 total rows (3 input + 3 derived)', smokeRows.length === 6);
check('derived: Student subClassOf Agent (transitivity)',
  hasDerivedTriple(smokeRows, '<ex:Student>', SUBCLASSOF, '<ex:Agent>'));
check('derived: alice type Person (1-step propagation)',
  hasDerivedTriple(smokeRows, '<ex:alice>', RDF_TYPE, '<ex:Person>'));
check('derived: alice type Agent (2-step propagation)',
  hasDerivedTriple(smokeRows, '<ex:alice>', RDF_TYPE, '<ex:Agent>'));
console.log('  (engine ' + smoke.engineMs.toFixed(3) + ' ms, wall ' +
  smoke.wallMs.toFixed(1) + ' ms, ' + smoke.rounds + '/' + smoke.fuel + ' rounds)');

console.log('=== rifEval(SAMPLE_RIF_XML, SAMPLE_DATA_TTL) -- general pipeline, same program ===');
const custom = await demo.runCustom(SAMPLE_RIF_XML, SAMPLE_DATA_TTL);
check('inputCount === 3', custom.inputCount === 3);
check('derivedCount === 3', custom.derivedCount === 3);
check('fuel === 100', custom.fuel === 100);
const customRows = diffSaturatedRows(custom.inputNquads, custom.saturatedNquads);
check('custom pipeline reaches the SAME saturated set as rifSmoke (6 rows)',
  customRows.length === 6);
check('custom: derived Student subClassOf Agent',
  hasDerivedTriple(customRows, '<ex:Student>', SUBCLASSOF, '<ex:Agent>'));
check('custom: derived alice type Person',
  hasDerivedTriple(customRows, '<ex:alice>', RDF_TYPE, '<ex:Person>'));
check('custom: derived alice type Agent',
  hasDerivedTriple(customRows, '<ex:alice>', RDF_TYPE, '<ex:Agent>'));
console.log('  (engine ' + custom.engineMs.toFixed(3) + ' ms, wall ' +
  custom.wallMs.toFixed(1) + ' ms, ' + custom.rounds + '/' + custom.fuel + ' rounds)');

console.log('=== rifEval(malformed RIF-XML) -- must FAIL honestly ===');
let malformedThrew = null;
try {
  await demo.runCustom('not RIF-XML at all', SAMPLE_DATA_TTL);
} catch (e) {
  malformedThrew = e;
}
check('malformed RIF-XML rejected (not silently empty-output)', malformedThrew !== null);
if (malformedThrew) {
  check('error carries an engine diagnostic',
    /RIF-XML|parse/i.test(malformedThrew.message));
  console.log('  (engine said: ' + malformedThrew.message.trim().slice(0, 120) + ')');
}

console.log('===');
if (failures === 0) {
  console.log('rif demo smoke: ALL PASS');
  process.exit(0);
} else {
  console.error('rif demo smoke: ' + failures + ' FAILED -- see above');
  process.exit(1);
}
"
