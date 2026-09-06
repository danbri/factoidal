// Host tests for the Solid Protocol server host, replaying the HTTP
// examples of the specification text.
// https://github.com/danbri/factoidal/issues/659
//
//   node tests/solid/server/protocol.mjs
//   deno run --allow-read --allow-net --allow-env tests/solid/server/protocol.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH. Scores
// are printed as "N pass, M fail, S skipped (out of T)".
//
// WHAT THIS GATES
// The server host of `npm/factoidal/solid/server/index.mjs` end to end
// over a real socket, against the request and response examples in the
// Solid Protocol v0.11.0 text (<https://solidproject.org/TR/protocol>):
// storage discovery, containment after PUT and POST, the 409 on a
// containment edit, the 405 on deleting the storage root, the auxiliary
// lifecycle, N3 Patch, CORS and the LDN inbox.
//
// The engine's decisions in isolation are `#guard`s in
// `formal/lean4/L4Factoidal/Solid/Tests.lean`. What only this file can
// see is the round trip over a socket: the request arriving at
// `solidStep` as the ABI's JSON record, and the answer reaching the wire
// with its status, its repeated headers and its body intact.
//
// WHEN THE OPS ARE ABSENT
// The committed WebAssembly module is rebuilt by the coordinator. A
// module without the Solid ops answers "unknown op"; every check is then
// SKIPPED with that reason printed and the score line carries the skip
// count. A skip is never a pass (anti-pattern 3).

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

// --------------------------------------------------------- the check list
// Each name says which section of the Solid Protocol it replays, so a
// failure names the rule and not only the request.

const CHECKS = [
  'the server binds an ephemeral port',
  'storage discovery: the root advertises pim:Storage by Link rel=type (4.1)',
  'OPTIONS reports Allow, Accept-Post, Accept-Patch and Accept-Put (4.3)',
  'PUT creates a resource and the container gains its containment triple (5.3)',
  'POST to a container assigns a name and reports it in Location (5.4)',
  'PUT that edits a containment triple is refused with 409 (5.3)',
  'DELETE on the storage root is refused with 405 (5.5)',
  'a resource advertises its describedby auxiliary (4.2)',
  'deleting a resource deletes its auxiliary (4.2)',
  'PATCH applies an N3 Patch (5.6)',
  'a CORS preflight is answered with the allow headers (6)',
  'the LDN inbox is advertised and accepts a notification (7)'
]

// ------------------------------------------------------------- fixtures

const TURTLE = 'text/turtle'
const N3 = 'text/n3'
const LDP = 'http://www.w3.org/ns/ldp#'
const PIM_STORAGE = 'http://www.w3.org/ns/pim/space#Storage'

const NOTE = '<#it> <http://www.w3.org/2000/01/rdf-schema#label> "one" .'

// Solid Protocol 5.6: an N3 Patch is a text/n3 document with a
// solid:InsertDeletePatch. The engine parses and applies it.
const N3_PATCH = `@prefix solid: <http://www.w3.org/ns/solid/terms#> .
<> a solid:InsertDeletePatch ;
   solid:inserts { <#it> <http://www.w3.org/2000/01/rdf-schema#comment> "added" . } .`

const NOTIFICATION =
  '<> <https://www.w3.org/ns/activitystreams#actor> <https://example.org/alice> .'

/** Every `Link` header value of a reply, joined. A reply may carry the
 *  field more than once and `Headers.get` joins repeats with ", ". */
function links (reply) {
  const value = reply.headers.get('link')
  return value === null ? '' : value
}

function hasLinkRelation (reply, target, relation) {
  const text = links(reply)
  // RFC 8288 allows the parameters in either order and either quoting.
  const bare = text.replace(/\s+/g, '')
  return bare.indexOf(`<${target}>`) >= 0 &&
    (bare.indexOf(`rel="${relation}"`) >= 0 || bare.indexOf(`rel=${relation}`) >= 0)
}

function linkTargetFor (reply, relation) {
  const parts = links(reply).split(',')
  for (const part of parts) {
    const bare = part.replace(/\s+/g, '')
    if (bare.indexOf(`rel="${relation}"`) >= 0 || bare.indexOf(`rel=${relation}`) >= 0) {
      const match = /<([^>]*)>/.exec(part)
      if (match !== null) return match[1]
    }
  }
  return null
}

// ------------------------------------------------------------- the tests

async function main () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { listen, solidServerOpsAvailable } =
    await import('../../../npm/factoidal/solid/server/index.mjs')

  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }

  const probe = await solidServerOpsAvailable(engine)
  if (!probe.available) {
    for (const name of CHECKS) skip(name, probe.reason)
    return
  }

  // A fixed `now` keeps the engine's deterministic clock: every mutation
  // advances it by one second, so Last-Modified is decided by the engine
  // and not by how fast this machine runs.
  const running = await listen({
    engine, port: 0, now: 1000, owner: 'https://example.org/alice#me'
  })
  const at = (path) => `${running.origin}${path}`

  try {
    await check(CHECKS[0], () => {
      assert(typeof running.port === 'number' && running.port > 0,
        `no ephemeral port was bound: ${running.port}`)
    })

    await check(CHECKS[1], async () => {
      const reply = await fetch(at('/'), { headers: { accept: TURTLE } })
      await reply.text()
      assert(reply.status === 200, `GET / answered ${reply.status}, expected 200`)
      assert(hasLinkRelation(reply, PIM_STORAGE, 'type'),
        'GET / carried no Link: <http://www.w3.org/ns/pim/space#Storage>; ' +
        `rel="type"; its Link header was: ${links(reply) || '(absent)'}`)
    })

    await check(CHECKS[2], async () => {
      const reply = await fetch(at('/'), { method: 'OPTIONS' })
      await reply.text()
      assert(reply.status >= 200 && reply.status < 300,
        `OPTIONS answered ${reply.status}, expected a 2xx`)
      for (const name of ['allow', 'accept-post', 'accept-patch', 'accept-put']) {
        assert(reply.headers.get(name) !== null,
          `OPTIONS on the storage root carried no ${name} header`)
      }
    })

    await check(CHECKS[3], async () => {
      const put = await fetch(at('/notes/one'), {
        method: 'PUT', headers: { 'content-type': TURTLE }, body: NOTE
      })
      await put.text()
      assert(put.status >= 200 && put.status < 300,
        `PUT answered ${put.status}, expected a 2xx`)
      // 5.3: PUT creates intermediate containers, so /notes/ now exists
      // and holds one containment triple for the new resource.
      const container = await fetch(at('/notes/'), { headers: { accept: TURTLE } })
      const body = await container.text()
      assert(container.status === 200,
        `GET /notes/ answered ${container.status}, expected 200`)
      assert(body.indexOf(`${LDP}contains`) >= 0 || body.indexOf('contains') >= 0,
        `the container carried no ldp:contains triple: ${body.slice(0, 200)}`)
      assert(body.indexOf('one') >= 0,
        `the container did not contain the new resource: ${body.slice(0, 200)}`)
    })

    let posted = null
    await check(CHECKS[4], async () => {
      const reply = await fetch(at('/notes/'), {
        method: 'POST',
        headers: { 'content-type': TURTLE, slug: 'two' },
        body: NOTE
      })
      await reply.text()
      assert(reply.status === 201, `POST answered ${reply.status}, expected 201`)
      posted = reply.headers.get('location')
      assert(posted !== null, 'POST carried no Location header')
      const container = await fetch(at('/notes/'), { headers: { accept: TURTLE } })
      const body = await container.text()
      const name = posted.split('/').filter((part) => part.length > 0).pop()
      assert(body.indexOf(name) >= 0,
        `the container did not gain a containment triple for ${posted}: ` +
        body.slice(0, 200))
    })

    await check(CHECKS[5], async () => {
      // 5.3: "Servers MUST NOT allow HTTP PUT ... to update a
      // container's containment triples", answered with 409.
      const body = `<> <${LDP}contains> <${at('/notes/one')}> .`
      const reply = await fetch(at('/notes/'), {
        method: 'PUT', headers: { 'content-type': TURTLE }, body
      })
      await reply.text()
      assert(reply.status === 409,
        `PUT of a containment triple answered ${reply.status}, expected 409`)
    })

    await check(CHECKS[6], async () => {
      // 5.5: "Servers MUST NOT allow HTTP DELETE on the storage
      // container", answered with 405.
      const reply = await fetch(at('/'), { method: 'DELETE' })
      await reply.text()
      assert(reply.status === 405,
        `DELETE on the storage root answered ${reply.status}, expected 405`)
    })

    let auxiliary = null
    await check(CHECKS[7], async () => {
      const reply = await fetch(at('/notes/one'), { headers: { accept: TURTLE } })
      await reply.text()
      assert(reply.status === 200, `GET answered ${reply.status}, expected 200`)
      auxiliary = linkTargetFor(reply, 'describedby')
      assert(auxiliary !== null,
        'the resource advertised no describedby auxiliary; its Link header ' +
        `was: ${links(reply) || '(absent)'}`)
    })

    await check(CHECKS[8], async () => {
      assert(auxiliary !== null, 'the describedby target was not found by the check above')
      const target = auxiliary.startsWith('http') ? auxiliary : at(auxiliary)
      const before = await fetch(target, { headers: { accept: TURTLE } })
      await before.text()
      const removed = await fetch(at('/notes/one'), { method: 'DELETE' })
      await removed.text()
      assert(removed.status >= 200 && removed.status < 300,
        `DELETE answered ${removed.status}, expected a 2xx`)
      const after = await fetch(target, { headers: { accept: TURTLE } })
      await after.text()
      assert(after.status === 404,
        `the auxiliary survived its subject's deletion: it answered ${after.status}, ` +
        'expected 404')
    })

    await check(CHECKS[9], async () => {
      const create = await fetch(at('/notes/three'), {
        method: 'PUT', headers: { 'content-type': TURTLE }, body: NOTE
      })
      await create.text()
      const reply = await fetch(at('/notes/three'), {
        method: 'PATCH', headers: { 'content-type': N3 }, body: N3_PATCH
      })
      const patched = await reply.text()
      assert(reply.status >= 200 && reply.status < 300,
        `the N3 Patch answered ${reply.status}, expected a 2xx: ${patched.slice(0, 200)}`)
      const read = await fetch(at('/notes/three'), { headers: { accept: TURTLE } })
      const body = await read.text()
      assert(body.indexOf('added') >= 0,
        `the patched triple was not read back: ${body.slice(0, 200)}`)
    })

    await check(CHECKS[10], async () => {
      const reply = await fetch(at('/notes/three'), {
        method: 'OPTIONS',
        headers: {
          origin: 'https://app.example',
          'access-control-request-method': 'PUT',
          'access-control-request-headers': 'content-type'
        }
      })
      await reply.text()
      assert(reply.status >= 200 && reply.status < 400,
        `the preflight answered ${reply.status}, expected a 2xx or 3xx`)
      assert(reply.headers.get('access-control-allow-origin') !== null,
        'the preflight carried no Access-Control-Allow-Origin')
      assert(reply.headers.get('access-control-allow-methods') !== null,
        'the preflight carried no Access-Control-Allow-Methods')
    })

    await check(CHECKS[11], async () => {
      const reply = await fetch(at('/'), { headers: { accept: TURTLE } })
      await reply.text()
      const inbox = linkTargetFor(reply, `${LDP}inbox`)
      assert(inbox !== null,
        'the storage root advertised no ldp:inbox; its Link header was: ' +
        `${links(reply) || '(absent)'}`)
      const target = inbox.startsWith('http') ? inbox : at(inbox)
      const posted = await fetch(target, {
        method: 'POST', headers: { 'content-type': TURTLE }, body: NOTIFICATION
      })
      await posted.text()
      assert(posted.status === 201,
        `POST to the inbox answered ${posted.status}, expected 201`)
    })
  } finally {
    await running.close()
  }
}

await main()

// ------------------------------------------------------------ reporting

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`solid-server ${shim.runtimeName}: ${passed} pass, ${failed} fail, ` +
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
