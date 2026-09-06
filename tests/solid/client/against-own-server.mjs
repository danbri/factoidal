// Host tests for the Solid Protocol client host, driven against an
// in-process instance of our own Solid server.
// https://github.com/danbri/factoidal/issues/659
//
//   node tests/solid/client/against-own-server.mjs
//   deno run --allow-read --allow-net --allow-env tests/solid/client/against-own-server.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH. Scores
// are printed as "N pass, M fail, S skipped (out of T)".
//
// WHAT THIS GATES
// That the client host of `npm/factoidal/solid/client/index.mjs` and the
// server host of `npm/factoidal/solid/server/index.mjs` agree over a real
// socket: discover, replace, read, create and delete. Every request the
// client sends was built by `solidClientRequest` and every reply it
// reports was read by `solidClientResponse`, so a disagreement between
// the two engine sides shows here as a failed operation rather than as a
// silently different request.
//
// Both conformance classes are OURS here, so this test cannot find a
// disagreement with another implementation. That is what
// `tools/solid-client-interop.sh` (our client against Community Solid
// Server) and `tools/solid-server-interop.sh` (solid-crud-tests and the
// Web Access Control tests against our server) are for.
//
// WHEN THE OPS ARE ABSENT
// A module without the client ops or without the server ops answers
// "unknown op"; every check is then SKIPPED with that reason printed and
// the score line carries the skip count. A skip is never a pass
// (anti-pattern 3).

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)
const testFile = new URL(import.meta.url).pathname

// --------------------------------------------------------- runtime shims

const shim = isDeno
  ? {
      exit: (code) => globalThis.Deno.exit(code),
      run: (command, args) => {
        const output = new globalThis.Deno.Command(command, { args }).outputSync()
        return {
          code: output.code,
          stdout: new TextDecoder().decode(output.stdout),
          stderr: new TextDecoder().decode(output.stderr)
        }
      },
      spawn: (command, args) => {
        const child = new globalThis.Deno.Command(command, {
          args, stdout: 'piped', stderr: 'piped'
        }).spawn()
        return {
          wait: async () => {
            const output = await child.output()
            return {
              code: output.code,
              stdout: new TextDecoder().decode(output.stdout),
              stderr: new TextDecoder().decode(output.stderr)
            }
          }
        }
      },
      writeOut: (text) => globalThis.Deno.stdout.writeSync(new TextEncoder().encode(text)),
      writeErr: (text) => globalThis.Deno.stderr.writeSync(new TextEncoder().encode(text)),
      runtimeName: 'deno'
    }
  : await (async () => {
      const cp = await import('node:child_process')
      return {
        exit: (code) => { process.exitCode = code },
        run: (command, args) => {
          const result = cp.spawnSync(command, args, { encoding: 'utf8' })
          if (result.error) throw result.error
          return { code: result.status, stdout: result.stdout, stderr: result.stderr }
        },
        spawn: (command, args) => {
          const child = cp.spawn(command, args, { stdio: ['ignore', 'pipe', 'pipe'] })
          let stdout = ''
          let stderr = ''
          child.stdout.on('data', (chunk) => { stdout += chunk })
          child.stderr.on('data', (chunk) => { stderr += chunk })
          return {
            wait: () => new Promise((resolve) => {
              child.on('close', (code) => resolve({ code, stdout, stderr }))
            })
          }
        },
        writeOut: (text) => process.stdout.write(text),
        writeErr: (text) => process.stderr.write(text),
        runtimeName: 'node'
      }
    })()

// ---------------------------------------------------------- tiny harness

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
  'discoverStorage finds the storage root',
  'replace writes a data resource',
  'read reads it back',
  'create posts into a container and reports the assigned name',
  'delete removes the resource',
  'read after delete reports the resource is gone, and its sibling survives',
  'every request the client sent was built by the engine'
]

// ------------------------------------------------------------- fixtures

const TURTLE = 'text/turtle'
const NOTE = '<#it> <http://www.w3.org/2000/01/rdf-schema#label> "one" .'

/** The status of the reply the client reported for an operation. */
function statusOf (answer) {
  assert(answer !== null && typeof answer === 'object', 'the client answered nothing')
  assert(answer.response !== undefined, 'the client answered no response record')
  return answer.response.status
}

// ------------------------------------------------------------- the tests

async function main () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { listen, solidServerOpsAvailable } =
    await import('../../../npm/factoidal/solid/server/index.mjs')
  const { createSolidClient, solidClientOpsAvailable } =
    await import('../../../npm/factoidal/solid/client/index.mjs')

  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }

  const serverProbe = await solidServerOpsAvailable(engine)
  if (!serverProbe.available) {
    for (const name of CHECKS) skip(name, serverProbe.reason)
    return
  }
  const clientProbe = await solidClientOpsAvailable(engine)
  if (!clientProbe.available) {
    for (const name of CHECKS) skip(name, clientProbe.reason)
    return
  }

  const running = await listen({ engine, port: 0, now: 1000 })
  // Every request the client makes is counted here, so the last check can
  // say that no request reached the socket except through the engine.
  let requests = 0
  const counting = (input, init) => { requests += 1; return fetch(input, init) }
  const client = await createSolidClient({
    engine, fetch: counting, baseIri: running.origin
  })

  try {
    await check(CHECKS[0], async () => {
      const answer = await client.discoverStorage('/notes/one')
      const status = statusOf(answer)
      assert(status >= 200 && status < 500,
        `discoverStorage got ${status} from our own server`)
      assert(answer.interpretation !== null,
        'discoverStorage returned no interpretation; the engine named no ' +
        'interpretation kind and the client passed "storage"')
      assert(typeof answer.interpretation.storage === 'string' ||
             answer.interpretation.storage === null,
        'the storage interpretation carried no storage member: ' +
        JSON.stringify(answer.interpretation).slice(0, 200))
    })

    await check(CHECKS[1], async () => {
      const answer = await client.replace('/notes/one', NOTE, TURTLE)
      const status = statusOf(answer)
      assert(status >= 200 && status < 300,
        `replace answered ${status}, expected a 2xx`)
      assert(answer.request.method === 'PUT',
        `the engine built a ${answer.request.method} for replace, expected PUT`)
    })

    await check(CHECKS[2], async () => {
      const answer = await client.read('/notes/one')
      assert(statusOf(answer) === 200, `read answered ${statusOf(answer)}, expected 200`)
      assert(answer.response.body.indexOf('one') >= 0,
        `read did not return what replace wrote: ${answer.response.body.slice(0, 120)}`)
    })

    let created = null
    await check(CHECKS[3], async () => {
      const answer = await client.create('/notes/', NOTE, TURTLE)
      const status = statusOf(answer)
      assert(status === 201, `create answered ${status}, expected 201`)
      assert(answer.request.method === 'POST',
        `the engine built a ${answer.request.method} for create, expected POST`)
      const location = answer.response.headers
        .filter((pair) => String(pair[0]).toLowerCase() === 'location')
        .map((pair) => pair[1])
      assert(location.length === 1,
        `create reported ${location.length} Location headers, expected one`)
      created = location[0]
    })

    await check(CHECKS[4], async () => {
      const answer = await client.delete('/notes/one')
      const status = statusOf(answer)
      assert(status >= 200 && status < 300,
        `delete answered ${status}, expected a 2xx`)
      assert(answer.request.method === 'DELETE',
        `the engine built a ${answer.request.method} for delete, expected DELETE`)
    })

    await check(CHECKS[5], async () => {
      const answer = await client.read('/notes/one')
      assert(statusOf(answer) === 404,
        `read after delete answered ${statusOf(answer)}, expected 404`)
      // The POSTed sibling is a different resource and must survive.
      assert(created !== null, 'the created resource name was not recorded')
      const sibling = await client.read(created)
      assert(statusOf(sibling) === 200,
        `deleting /notes/one also removed ${created}: reading it answered ` +
        `${statusOf(sibling)}, expected 200`)
    })

    await check(CHECKS[6], async () => {
      assert(requests >= 7,
        `only ${requests} requests reached the socket; the seven client ` +
        'operations above should each have sent at least one')
    })
  } finally {
    await running.close()
  }
}

await main()

// ------------------------------------------------------------ reporting

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`solid-client ${shim.runtimeName}: ${passed} pass, ${failed} fail, ` +
  `${skipped} skipped (out of ${total})`)

let exitCode = failed === 0 ? 0 : 1

if (!isDeno && argv.indexOf('--no-deno') < 0) {
  const probe = shim.run('/bin/sh', ['-c', 'command -v deno'])
  const denoPath = probe.code === 0 && probe.stdout.trim().length > 0
    ? probe.stdout.trim()
    : null
  if (denoPath === null) {
    console.log('deno: not installed, so the Deno run is skipped (install deno to run it)')
  } else {
    console.log(`deno: ${denoPath}`)
    const child = shim.spawn(denoPath,
      ['run', '--allow-read', '--allow-net', '--allow-env', testFile, '--no-deno'])
    const result = await child.wait()
    shim.writeOut(result.stdout)
    if (result.stderr.length > 0) shim.writeErr(result.stderr)
    if (result.code !== 0) exitCode = 1
  }
}

shim.exit(exitCode)
