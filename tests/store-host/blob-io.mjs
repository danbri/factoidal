// Conformance test for the RAW BYTE PATH OUT of the WebAssembly module:
// Wasm/Dispatch.lean's `callBlobIO`, Wasm/Exports.lean's
// `l4_call_blob_io` export, Wasm/l4_shim.c's `l4_call_blob_io_c`, and the
// `callBlobIO` binder in l4factoidal.js.
//
//   node tests/store-host/blob-io.mjs
//   deno run --allow-read --allow-run --allow-env tests/store-host/blob-io.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH, and says
// so plainly when it is not. Scores are printed as "N pass, M fail
// (out of T)".
//
// The operation under test is `blobEcho(lengthHint)`. It answers
// {"ok":true,"bytes":N} and an out region of N bytes where byte i is
// (i * 7 + 3) mod 256. The stride is odd and coprime with 256, so a
// dropped, duplicated or reordered byte changes the sequence. The
// 1,000,000-byte case is the one that shows truncation and gives a
// throughput figure; the 0-byte and 1-byte cases pin the boundaries.
//
// This file makes no format decision. It reads no manifest, decodes no
// block and computes no digest.

import { loadEngine } from '../../npm/factoidal/bin/engine.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined'
const runtime = isDeno ? 'deno' : 'node'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

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
      spawn: async (command, args) => {
        const output = await new globalThis.Deno.Command(command, {
          args, stdout: 'piped', stderr: 'piped'
        }).output()
        return {
          code: output.code,
          stdout: new TextDecoder().decode(output.stdout),
          stderr: new TextDecoder().decode(output.stderr)
        }
      },
      writeOut: (text) => globalThis.Deno.stdout.writeSync(new TextEncoder().encode(text)),
      writeErr: (text) => globalThis.Deno.stderr.writeSync(new TextEncoder().encode(text))
    }
  : await (async () => {
      const cp = await import('node:child_process')
      return {
        exit: (code) => process.exit(code),
        run: (command, args) => {
          const result = cp.spawnSync(command, args, { encoding: 'utf8' })
          return {
            code: result.status === null ? 1 : result.status,
            stdout: result.stdout ?? '',
            stderr: result.stderr ?? ''
          }
        },
        spawn: (command, args) => new Promise((resolve) => {
          const child = cp.spawn(command, args)
          let stdout = ''
          let stderr = ''
          child.stdout.on('data', (chunk) => { stdout += chunk })
          child.stderr.on('data', (chunk) => { stderr += chunk })
          child.on('close', (code) => resolve({ code: code ?? 1, stdout, stderr }))
        }),
        writeOut: (text) => process.stdout.write(text),
        writeErr: (text) => process.stderr.write(text)
      }
    })()

// --------------------------------------------------------------- harness

let passed = 0
let failed = 0
const failures = []

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

async function check (name, body) {
  try {
    await body()
    passed += 1
    console.log(`  ok   ${name}`)
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : error}`)
    console.log(`  FAIL ${name}`)
  }
}

/** The byte the Lean side must have produced at index `i`. */
const expectedByte = (i) => (i * 7 + 3) % 256

/** Index of the first byte that differs, or -1 when every byte agrees. */
function firstDifference (bytes) {
  for (let i = 0; i < bytes.length; i += 1) {
    if (bytes[i] !== expectedByte(i)) return i
  }
  return -1
}

// ------------------------------------------------------------- the checks

const engine = await loadEngine()

await check('the ops reflection names blobEcho under blobIoOps', () => {
  const reflection = engine.call('ops', [])
  assert(Array.isArray(reflection.blobIoOps),
    'the ops envelope carries no blobIoOps array')
  assert(reflection.blobIoOps.indexOf('blobEcho') >= 0,
    `blobIoOps is ${JSON.stringify(reflection.blobIoOps)}`)
})

for (const size of [0, 1, 1000000]) {
  await check(`blobEcho returns ${size} bytes, every one of them correct`, () => {
    const started = Date.now()
    const { envelope, bytes } = engine.callBlobIO('blobEcho', [String(size)])
    const elapsed = Date.now() - started
    assert(envelope.ok === true, `envelope is ${JSON.stringify(envelope)}`)
    assert(envelope.bytes === size, `envelope reports ${envelope.bytes} bytes`)
    assert(bytes instanceof Uint8Array, 'the region is not a Uint8Array')
    assert(bytes.length === size, `the region holds ${bytes.length} bytes`)
    const bad = firstDifference(bytes)
    assert(bad < 0,
      `byte ${bad} is ${bytes[bad]}, expected ${expectedByte(bad)}`)
    if (size >= 1000000) {
      const rate = elapsed > 0
        ? Math.round((size / 1048576) / (elapsed / 1000))
        : null
      console.log(`       ${size} bytes in ${elapsed} ms` +
        (rate === null ? '' : ` (${rate} MiB/s)`))
    }
  })
}

await check('a byte count that is not a number is refused', () => {
  let thrown = null
  try {
    engine.callBlobIO('blobEcho', ['not-a-number'])
  } catch (error) {
    thrown = error
  }
  assert(thrown !== null, 'a bad byte count was accepted')
})

await check('an op outside blobIoOps answers with an empty region', () => {
  const { envelope, bytes } = engine.callBlobIO('ops', [])
  assert(envelope.ok === true, `envelope is ${JSON.stringify(envelope)}`)
  assert(bytes.length === 0, `the region holds ${bytes.length} bytes`)
})

// ------------------------------------------------------------- reporting

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed
console.log(`${runtime}: ${passed} pass, ${failed} fail (out of ${total})`)

let exitCode = failed === 0 ? 0 : 1

if (!isDeno && argv.indexOf('--no-deno') < 0) {
  const testFile = new URL(import.meta.url).pathname
  const probe = shim.run('/bin/sh', ['-c', 'command -v deno'])
  const denoPath = probe.code === 0 && probe.stdout.trim().length > 0
    ? probe.stdout.trim()
    : null
  if (denoPath === null) {
    console.log('deno: not installed, so the Deno run is skipped (install deno to run it)')
  } else {
    console.log(`deno: ${denoPath}`)
    const result = await shim.spawn(denoPath,
      ['run', '--allow-read', '--allow-run', '--allow-env', testFile, '--no-deno'])
    shim.writeOut(result.stdout)
    if (result.stderr.length > 0) shim.writeErr(result.stderr)
    if (result.code !== 0) exitCode = 1
  }
}

shim.exit(exitCode)
