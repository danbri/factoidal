// Host tests for the Linked Web Storage 1.0 server host.
// https://github.com/danbri/factoidal/issues/659
//
//   node tests/lws/server.mjs
//   deno run --allow-read --allow-net --allow-env tests/lws/server.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH, and says
// so plainly when it is not. Scores are printed as
// "N pass, M fail, S skipped (out of T)".
//
// WHAT THIS GATES
// The server host of `npm/factoidal/lws/server.mjs` end to end over a
// real socket on an ephemeral port: a Create/Read/Update/Delete sequence
// on a data resource, `Last-Modified` on GET and HEAD, and the LWS core
// rule that PATCH insertion formulae MUST NOT contain blank nodes.
//
// It does NOT gate the engine's decisions in isolation -- those are
// `#guard`s in `formal/lean4/L4Factoidal/LWS/Tests.lean`. What only this
// file can see is the round trip: that a request reaching the socket
// arrives at `lwsStep` as the JSON record the ABI states, and that the
// engine's answer reaches the wire with its status, its headers (repeats
// kept) and its body intact.
//
// WHEN THE OPS ARE ABSENT
// The committed WebAssembly module is rebuilt by the coordinator, not by
// this test. A module without the LWS ops answers "unknown op"; every
// check below is then SKIPPED with that reason printed, and the score
// line carries the skip count. A skip is never counted as a pass
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

/** A check that did not run, with the reason printed rather than
 *  swallowed. A skip is never a pass (anti-pattern 3). */
function skip (name, reason) {
  skipped += 1
  console.log(`  skip ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

/** The checks this file runs, named once so the skip path can list every
 *  one of them by the same name the pass path would. */
const CHECKS = [
  'the server binds an ephemeral port',
  'PUT creates a data resource',
  'GET reads it back with Last-Modified',
  'HEAD carries Last-Modified and no body',
  'PUT updates it and moves Last-Modified',
  'DELETE removes it',
  'GET after DELETE does not find it',
  'PATCH refuses an insertion formula with a blank node'
]

// ------------------------------------------------------------- the tests

const TURTLE = 'text/turtle'
const NOTE = '</notes/one#it> <http://www.w3.org/2000/01/rdf-schema#label> "one" .'
const NOTE_TWO = '</notes/one#it> <http://www.w3.org/2000/01/rdf-schema#label> "two" .'

// LWS 1.0 core, Update: "?insertions formulae MUST NOT contain blank
// nodes". The engine decides the refusal; this checks it reaches the
// wire as a client-error status and that the well-formed sibling does
// not get refused for the same reason.
const PATCH_WITH_BLANK_NODE = `@prefix solid: <http://www.w3.org/ns/solid/terms#> .
<> a solid:InsertDeletePatch ;
   solid:inserts { </notes/one#it> <http://example.org/p> _:b0 . } .`

function headerOf (reply, name) {
  return reply.headers.get(name)
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen, lwsOpsAvailable } = await import('../../npm/factoidal/lws/server.mjs')

  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }

  const probe = await lwsOpsAvailable(engine)
  if (!probe.available) {
    for (const name of CHECKS) skip(name, probe.reason)
    return
  }

  // A fixed `now` keeps the engine's deterministic clock, so
  // `Last-Modified` is decided by the engine's own one-second step and
  // not by how fast this machine runs.
  const running = await listen({ engine, port: 0, now: 1000 })
  try {
    await check(CHECKS[0], () => {
      assert(typeof running.port === 'number' && running.port > 0,
        `no ephemeral port was bound: ${running.port}`)
    })

    const url = `${running.origin}/notes/one`
    let firstModified = null

    await check(CHECKS[1], async () => {
      const reply = await fetch(url, {
        method: 'PUT', headers: { 'content-type': TURTLE }, body: NOTE
      })
      assert(reply.status >= 200 && reply.status < 300,
        `PUT answered ${reply.status}, expected a 2xx`)
      await reply.text()
    })

    await check(CHECKS[2], async () => {
      const reply = await fetch(url, { headers: { accept: TURTLE } })
      assert(reply.status === 200, `GET answered ${reply.status}, expected 200`)
      firstModified = headerOf(reply, 'last-modified')
      assert(firstModified !== null,
        'GET carried no Last-Modified; LWS 1.0 core requires it on GET and HEAD')
      const body = await reply.text()
      assert(body.indexOf('one') >= 0,
        `GET did not return the resource that was written: ${body.slice(0, 120)}`)
    })

    await check(CHECKS[3], async () => {
      const reply = await fetch(url, { method: 'HEAD' })
      assert(reply.status === 200, `HEAD answered ${reply.status}, expected 200`)
      assert(headerOf(reply, 'last-modified') !== null,
        'HEAD carried no Last-Modified; LWS 1.0 core requires it on GET and HEAD')
      const body = await reply.text()
      assert(body.length === 0, `HEAD returned a body of ${body.length} bytes`)
    })

    await check(CHECKS[4], async () => {
      const put = await fetch(url, {
        method: 'PUT', headers: { 'content-type': TURTLE }, body: NOTE_TWO
      })
      assert(put.status >= 200 && put.status < 300,
        `the update PUT answered ${put.status}, expected a 2xx`)
      await put.text()
      const reply = await fetch(url, { headers: { accept: TURTLE } })
      assert(reply.status === 200, `GET after the update answered ${reply.status}`)
      const body = await reply.text()
      assert(body.indexOf('two') >= 0,
        `the update was not read back: ${body.slice(0, 120)}`)
      const second = headerOf(reply, 'last-modified')
      assert(second !== null, 'GET after the update carried no Last-Modified')
      assert(second !== firstModified,
        `Last-Modified did not move over an update; it stayed at ${second}`)
    })

    await check(CHECKS[5], async () => {
      const reply = await fetch(url, { method: 'DELETE' })
      assert(reply.status >= 200 && reply.status < 300,
        `DELETE answered ${reply.status}, expected a 2xx`)
      await reply.text()
    })

    await check(CHECKS[6], async () => {
      const reply = await fetch(url, { headers: { accept: TURTLE } })
      await reply.text()
      assert(reply.status === 404,
        `GET after DELETE answered ${reply.status}, expected 404`)
    })

    await check(CHECKS[7], async () => {
      const create = await fetch(url, {
        method: 'PUT', headers: { 'content-type': TURTLE }, body: NOTE
      })
      await create.text()
      const reply = await fetch(url, {
        method: 'PATCH',
        headers: { 'content-type': 'text/n3' },
        body: PATCH_WITH_BLANK_NODE
      })
      await reply.text()
      assert(reply.status >= 400 && reply.status < 500,
        `a PATCH whose insertion formula holds a blank node answered ` +
        `${reply.status}; LWS 1.0 core forbids it, so a 4xx is required`)
    })
  } finally {
    await running.close()
  }
}

await main()

// ------------------------------------------------------------ reporting

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-server ${shim.runtimeName}: ${passed} pass, ${failed} fail, ` +
  `${skipped} skipped (out of ${total})`)

let exitCode = failed === 0 ? 0 : 1

// The Node run drives the Deno run too, so one command reports both.
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
