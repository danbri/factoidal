// Our Solid client driven against a server this process did not write:
// Community Solid Server, started by tools/solid-client-interop.sh.
// https://github.com/danbri/factoidal/issues/659
//
//   node tests/solid/client/against-community-server.mjs --origin http://127.0.0.1:3000
//
// WHAT THIS GATES THAT against-own-server.mjs CANNOT
// `against-own-server.mjs` puts our client and our server on the two ends
// of one socket, so a shared misreading of the Solid Protocol passes it.
// This file replaces the far end with the reference implementation, so
// only a request our engine builds correctly is answered.
//
// Node only: it is one arm of an interop script, not a runtime-parity
// suite. Scores are printed as "N pass, M fail, S skipped (out of T)".

const argv = process.argv.slice(2)

function option (name) {
  const flag = `--${name}`
  for (let index = 0; index < argv.length; index += 1) {
    if (argv[index] === flag) return argv[index + 1]
    if (argv[index].startsWith(`${flag}=`)) return argv[index].slice(flag.length + 1)
  }
  return null
}

let passed = 0
let failed = 0
let skipped = 0
const failures = []

async function check (name, body) {
  try {
    await body()
    passed += 1
    console.log(`  ok   ${name}`)
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : String(error)}`)
    console.log(`  FAIL ${name}`)
  }
}

function skip (name, reason) {
  skipped += 1
  console.log(`  skip ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const CHECKS = [
  'discoverStorage finds the storage of a resource',
  'replace writes a data resource',
  'read reads it back',
  'create posts into a container and reports the assigned name',
  'delete removes the resource'
]

const TURTLE = 'text/turtle'
const NOTE = '<#it> <http://www.w3.org/2000/01/rdf-schema#label> "one" .'

function statusOf (answer) {
  assert(answer !== null && typeof answer === 'object', 'the client answered nothing')
  assert(answer.response !== undefined, 'the client answered no response record')
  return answer.response.status
}

async function main (base) {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { createSolidClient, solidClientOpsAvailable } =
    await import('../../../npm/factoidal/solid/client/index.mjs')

  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }
  const probe = await solidClientOpsAvailable(engine)
  if (!probe.available) {
    for (const name of CHECKS) skip(name, probe.reason)
    return
  }

  const client = await createSolidClient({ engine, baseIri: base })
  // A directory of this run's own, so a re-run does not meet its own
  // leftovers on a server that keeps state between runs.
  const container = `/factoidal-interop-${Date.now()}/`
  const target = `${container}one`

  await check(CHECKS[0], async () => {
    const seed = await client.replace(target, NOTE, TURTLE)
    assert(statusOf(seed) >= 200 && statusOf(seed) < 300,
      `the seed write answered ${statusOf(seed)}`)
    const answer = await client.discoverStorage(target)
    assert(answer.interpretation !== null,
      'discoverStorage returned no interpretation')
    assert(typeof answer.interpretation.storage === 'string' &&
           answer.interpretation.storage.length > 0,
      'the storage interpretation named no storage: ' +
      JSON.stringify(answer.interpretation).slice(0, 200))
  })

  await check(CHECKS[1], async () => {
    const answer = await client.replace(target, NOTE, TURTLE)
    const status = statusOf(answer)
    assert(status >= 200 && status < 300, `replace answered ${status}, expected a 2xx`)
  })

  await check(CHECKS[2], async () => {
    const answer = await client.read(target)
    assert(statusOf(answer) === 200, `read answered ${statusOf(answer)}, expected 200`)
    assert(answer.response.body.indexOf('one') >= 0,
      `read did not return what replace wrote: ${answer.response.body.slice(0, 120)}`)
  })

  await check(CHECKS[3], async () => {
    const answer = await client.create(container, NOTE, TURTLE)
    const status = statusOf(answer)
    assert(status === 201, `create answered ${status}, expected 201`)
    const location = answer.response.headers
      .filter((pair) => String(pair[0]).toLowerCase() === 'location')
    assert(location.length === 1,
      `create reported ${location.length} Location headers, expected one`)
  })

  await check(CHECKS[4], async () => {
    const answer = await client.delete(target)
    const status = statusOf(answer)
    assert(status >= 200 && status < 300, `delete answered ${status}, expected a 2xx`)
    const gone = await client.read(target)
    assert(statusOf(gone) === 404,
      `read after delete answered ${statusOf(gone)}, expected 404`)
  })
}

const origin = option('origin')
if (origin === null) {
  console.error('against-community-server: --origin URL is required')
  process.exitCode = 2
} else {
  await main(origin)
}

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`solid-client vs community-solid-server: ${passed} pass, ${failed} fail, ` +
  `${skipped} skipped (out of ${total})`)
// A run where nothing passed is a run that proved nothing: exit 2 (could
// not run), never 0. A skip is never a pass (anti-pattern 3).
if (failed > 0) process.exitCode = 1
else if (passed === 0) process.exitCode = 2
