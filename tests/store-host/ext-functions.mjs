// Caller-registered SPARQL 1.1 §17.6 extension functions against the Lean
// engine, including a persisted store.
// Design: docs/designissues/2026-09-04-lean-extension-functions.md
//
//   node tests/store-host/ext-functions.mjs [STORE_ROOT]
//
// STORE_ROOT defaults to $FACTOIDAL_SKOSGRAPHS, then
// ../factoidal-skosgraphs beside this checkout. Without it the store
// checks are SKIPPED and say so; the in-memory checks still run.
//
// WHAT IT GATES THAT NOTHING ELSE DOES
// That a JavaScript function registered by IRI is reachable from a SPARQL
// query the Lean engine evaluates, through a STORE HANDLE and not only
// through an in-memory dataset. Every row-content check compares the ROWS
// against the same query written WITHOUT the extension function, so a
// registration that changes which rows come back — not how many — is
// visible here (anti-pattern 34).
//
// Scores are printed as "N pass, M fail, S skipped (out of T)".

import { loadEngine } from '../../npm/factoidal/bin/engine.mjs'
import { openStore, openStoreHandle } from '../../npm/factoidal/bin/store.mjs'
import {
  registerExtensionFunction, unregisterExtensionFunction,
  clearExtensionFunctions, listExtensionFunctions, withFreshMemo
} from '../../npm/factoidal/bin/ext.mjs'
import { fileUrlToPath, joinPath } from '../../npm/factoidal/store-host/paths.mjs'
import { readWhole } from '../../npm/factoidal/store-host/index.mjs'

const EX = 'http://example.org/fn/'
const GEOF = 'http://www.opengis.net/def/function/geosparql/'
const XSD = 'http://www.w3.org/2001/XMLSchema#'

let pass = 0
let fail = 0
let skipped = 0

function check (name, condition, detail = '') {
  if (condition) {
    pass += 1
    console.log(`  pass  ${name}`)
  } else {
    fail += 1
    console.log(`  FAIL  ${name}${detail ? ' - ' + detail : ''}`)
  }
}

function skip (name, why) {
  skipped += 1
  console.log(`  skip  ${name} - ${why}`)
}

/** The bindings of an envelope, as comparable JSON strings, sorted. */
function rowsOf (envelope) {
  return envelope.srj.results.bindings
    .map((row) => JSON.stringify(Object.keys(row).sort().map((k) => [k, row[k]])))
    .sort()
}

function exists (path) {
  try { readWhole(path); return true } catch (_error) { return false }
}

function storeRoot (argv) {
  if (argv[0]) return argv[0]
  const env = globalThis.process?.env?.FACTOIDAL_SKOSGRAPHS
  if (env) return env
  const here = fileUrlToPath(new URL('.', import.meta.url).href)
  const beside = joinPath(here, '../../../factoidal-skosgraphs')
  return exists(joinPath(beside, 'CURRENT')) ? beside : null
}

async function main () {
  const argv = globalThis.process.argv.slice(2)
  const engine = await loadEngine()

  console.log('extension functions - in-memory dataset handle')

  const turtle = [
    '@prefix : <http://example.org/> .',
    ':a :label "alpha" ; :footprint "POINT(1 1)"^^<http://www.opengis.net/ont/geosparql#wktLiteral> .',
    ':b :label "beta"  ; :footprint "POINT(9 9)"^^<http://www.opengis.net/ont/geosparql#wktLiteral> .',
    ':c :label "apple" ; :footprint "POINT(0.5 0.5)"^^<http://www.opengis.net/ont/geosparql#wktLiteral> .'
  ].join('\n')
  const handle = engine.call('datasetOpen', [turtle, 'turtle', 'http://example.org/']).handle

  const q = (sparql) => withFreshMemo(() =>
    engine.call('datasetQuery', [handle, sparql]))

  // ---- 1. a registered SYNC function in FILTER position ----------------
  registerExtensionFunction(engine, EX + 'startsWithA', (args) => {
    const v = args[0]
    return !!(v && typeof v.value === 'string' && v.value.startsWith('a'))
  })
  check('extList reports the registration',
    listExtensionFunctions(engine).includes(EX + 'startsWithA'))

  const withExt = q(
    `PREFIX ex: <${EX}> SELECT ?s ?l WHERE { ?s <http://example.org/label> ?l ` +
    'FILTER(ex:startsWithA(?l)) } ORDER BY ?s')
  const reference = q(
    'SELECT ?s ?l WHERE { ?s <http://example.org/label> ?l ' +
    'FILTER(STRSTARTS(?l, "a")) } ORDER BY ?s')
  check('FILTER over a registered function answers the reference rows',
    JSON.stringify(rowsOf(withExt)) === JSON.stringify(rowsOf(reference)),
    `${JSON.stringify(rowsOf(withExt))} vs ${JSON.stringify(rowsOf(reference))}`)
  check('and the rows are not empty', rowsOf(withExt).length === 2,
    `${rowsOf(withExt).length} rows`)

  // ---- 2. a registered function in BIND position -----------------------
  registerExtensionFunction(engine, EX + 'shout', (args) =>
    String(args[0]?.value ?? '').toUpperCase())
  const bound = q(
    `PREFIX ex: <${EX}> SELECT ?l ?u WHERE { ?s <http://example.org/label> ?l ` +
    'BIND(ex:shout(?l) AS ?u) } ORDER BY ?l')
  check('BIND over a registered function binds the value',
    bound.srj.results.bindings.every((r) => r.u && r.u.value === r.l.value.toUpperCase()),
    JSON.stringify(bound.srj.results.bindings))

  // ---- 3. §17.6: an unregistered IRI in FILTER drops the row -----------
  const unregisteredFilter = q(
    'PREFIX ex: <http://example.org/nosuch/> SELECT ?s WHERE ' +
    '{ ?s <http://example.org/label> ?l FILTER(ex:nope(?l)) }')
  check('§17.6 unregistered IRI in FILTER drops every row',
    unregisteredFilter.srj.results.bindings.length === 0,
    `${unregisteredFilter.srj.results.bindings.length} rows`)

  // ---- 4. §17.6: an unregistered IRI in SELECT is unbound --------------
  const unregisteredSelect = q(
    'PREFIX ex: <http://example.org/nosuch/> SELECT ?s (ex:nope(?s) AS ?v) WHERE ' +
    '{ ?s <http://example.org/label> ?l } ORDER BY ?s')
  check('§17.6 unregistered IRI in SELECT keeps the row',
    unregisteredSelect.srj.results.bindings.length === 3,
    `${unregisteredSelect.srj.results.bindings.length} rows`)
  check('§17.6 unregistered IRI in SELECT leaves the variable unbound',
    unregisteredSelect.srj.results.bindings.every((r) => r.v === undefined),
    JSON.stringify(unregisteredSelect.srj.results.bindings))

  // ---- 5. §17.6: a registration never overrides a built-in -------------
  registerExtensionFunction(engine, XSD + 'integer', () => 999)
  registerExtensionFunction(engine, GEOF + 'sfWithin', () => false)
  const builtin = q(
    'PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> ' +
    'SELECT (xsd:integer("42") AS ?n) WHERE { } ')
  check('a registration does not override the xsd: cast family',
    builtin.srj.results.bindings[0]?.n?.value === '42',
    JSON.stringify(builtin.srj.results.bindings))

  // ---- 6. geof: keeps answering, registration or not -------------------
  const geo = q(
    `PREFIX geof: <${GEOF}> PREFIX geo: <http://www.opengis.net/ont/geosparql#> ` +
    'SELECT ?s WHERE { ?s <http://example.org/footprint> ?w ' +
    'FILTER(geof:sfWithin(?w, "POLYGON((0 0,0 2,2 2,2 0,0 0))"^^geo:wktLiteral)) } ORDER BY ?s')
  check('geof:sfWithin answers from the built-in table, not the registration',
    geo.srj.results.bindings.length === 2,
    `${geo.srj.results.bindings.length} rows`)

  // ---- 7. clearing returns the engine to the built-in table ------------
  clearExtensionFunctions(engine)
  check('extClear empties the registry',
    listExtensionFunctions(engine).length === 0)
  const afterClear = q(
    `PREFIX ex: <${EX}> SELECT ?s WHERE { ?s <http://example.org/label> ?l ` +
    'FILTER(ex:startsWithA(?l)) }')
  check('after extClear the IRI is the §17.6 error again',
    afterClear.srj.results.bindings.length === 0,
    `${afterClear.srj.results.bindings.length} rows`)

  engine.call('datasetClose', [handle])

  // ---- 8. the STORE handle path ---------------------------------------
  console.log('extension functions - persisted store handle')
  const root = storeRoot(argv)
  if (root === null || !exists(joinPath(root, 'CURRENT'))) {
    skip('store handle checks', 'no store root (pass one, or set FACTOIDAL_SKOSGRAPHS)')
  } else {
    const store = openStore(root)
    const sparql =
      `PREFIX ex: <${EX}> PREFIX skos: <http://www.w3.org/2004/02/skos/core#> ` +
      'SELECT ?c ?l WHERE { GRAPH ?g { ?c skos:prefLabel ?l } ' +
      'FILTER(ex:endsWithZed(?l)) } ORDER BY ?c ?l LIMIT 8'
    const referenceSparql =
      'PREFIX skos: <http://www.w3.org/2004/02/skos/core#> ' +
      'SELECT ?c ?l WHERE { GRAPH ?g { ?c skos:prefLabel ?l } ' +
      'FILTER(STRENDS(STR(?l), "z")) } ORDER BY ?c ?l LIMIT 8'
    // Scope the handle with the UNFILTERED pattern. The reference query's
    // STRENDS can be served by the LGI1 literal index, which narrows the
    // plan; the extension-function query cannot use the index and needs
    // every prefLabel block. A handle scoped by the narrower plan does not
    // retain what the wider one asks for, and refuses by name.
    const scopeSparql =
      'PREFIX skos: <http://www.w3.org/2004/02/skos/core#> ' +
      'SELECT ?c ?l WHERE { GRAPH ?g { ?c skos:prefLabel ?l } }'
    const sh = openStoreHandle(engine, store, { sparql: scopeSparql })
    try {
      let calls = 0
      registerExtensionFunction(engine, EX + 'endsWithZed', (args) => {
        calls += 1
        const v = args[0]
        return !!(v && typeof v.value === 'string' && v.value.endsWith('z'))
      })
      const storeExt = withFreshMemo(() => sh.query(sparql))
      const storeRef = withFreshMemo(() => sh.query(referenceSparql))
      check('store handle: the registered function is reached',
        calls > 0, `${calls} calls`)
      check('store handle: FILTER over a registered function answers the reference rows',
        JSON.stringify(rowsOf(storeExt)) === JSON.stringify(rowsOf(storeRef)),
        `${rowsOf(storeExt).length} vs ${rowsOf(storeRef).length} rows`)
      check('store handle: and the rows are not empty',
        rowsOf(storeExt).length > 0, `${rowsOf(storeExt).length} rows`)

      // §17.6 on the store path too.
      const storeUnregistered = withFreshMemo(() => sh.query(
        'PREFIX ex: <http://example.org/nosuch/> PREFIX skos: <http://www.w3.org/2004/02/skos/core#> ' +
        'SELECT (COUNT(*) AS ?n) WHERE { ?c skos:prefLabel ?l FILTER(ex:nope(?l)) }'))
      check('store handle: §17.6 unregistered IRI in FILTER drops every row',
        storeUnregistered.srj.results.bindings[0]?.n?.value === '0',
        JSON.stringify(storeUnregistered.srj.results.bindings))

      unregisterExtensionFunction(engine, EX + 'endsWithZed')
    } finally {
      sh.close()
      clearExtensionFunctions(engine)
    }
  }

  // ---- 9. cost of crossing to JavaScript ------------------------------
  // A function called once per row is on the hot path, so the per-call
  // overhead is measured, not assumed. Both queries answer the SAME rows
  // over the SAME dataset and differ only in whether the always-true
  // filter is a registered JavaScript function or a built-in, so the
  // difference is the boundary crossing plus the SRJ encode/decode.
  console.log('extension functions - per-call cost')
  const rows = 20000
  const lines = ['@prefix : <http://example.org/> .']
  for (let i = 0; i < rows; i += 1) lines.push(`:s${i} :label "v${i}" .`)
  const big = engine.call('datasetOpen',
    [lines.join('\n'), 'turtle', 'http://example.org/']).handle
  registerExtensionFunction(engine, EX + 'always', () => true)
  const timed = (sparql, repeats) => {
    let best = Infinity
    for (let r = 0; r < repeats; r += 1) {
      const t0 = performance.now()
      const env = withFreshMemo(() => engine.call('datasetQuery', [big, sparql]))
      const dt = performance.now() - t0
      if (env.srj.results.bindings.length !== rows) {
        throw new Error(`cost bench: ${env.srj.results.bindings.length} rows, expected ${rows}`)
      }
      if (dt < best) best = dt
    }
    return best
  }
  const baseline = timed(
    'SELECT ?s WHERE { ?s <http://example.org/label> ?l FILTER(STRLEN(?l) > 0) }', 3)
  const crossing = timed(
    `PREFIX ex: <${EX}> SELECT ?s WHERE { ?s <http://example.org/label> ?l ` +
    'FILTER(ex:always(?l)) }', 3)
  const perCall = (crossing - baseline) * 1000 / rows
  console.log(`  ${rows} rows: built-in filter ${baseline.toFixed(0)} ms, ` +
    `registered function ${crossing.toFixed(0)} ms, ` +
    `${perCall.toFixed(2)} us per call`)
  engine.call('datasetClose', [big])
  clearExtensionFunctions(engine)

  const total = pass + fail + skipped
  console.log(`\n${pass} pass, ${fail} fail, ${skipped} skipped (out of ${total})`)
  globalThis.process.exit(fail === 0 ? 0 : 1)
}

await main()
