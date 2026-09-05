// Conformance test for npm/factoidal/store-host against the three Lean
// host externs of formal/lean4/Harness/PosixRangeIO.lean, realised in
// formal/lean4/ffi/block_pread.c.
//
//   node tests/store-host/conformance.mjs
//   deno run --allow-read --allow-write --allow-run --allow-env tests/store-host/conformance.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH, and says
// so plainly when it is not. Scores are printed as
// "N pass, M fail, S skipped (out of T)".
//
// The native binaries are read-only inputs. `l4block-shard-pack` builds a
// generation in a temporary directory; `l4block-shard-merkle-pread` is the
// oracle for the positioned read. That tool prints the SIZE of the range it
// verified, not the range's bytes, so the byte-level correspondence is made
// through the packer's own SHA-256 commitment in manifest.tsv: the host's
// bytes hash to the digest the packer recorded, and the native tool accepts
// the same offset and length on the same file.

import {
  StoreHostError, appendSyncAtSize, atomicReplace, listGeneration,
  openCollection, readRange, readWhole, runtime
} from '../../npm/factoidal/store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../../npm/factoidal/store-host/paths.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

// ------------------------------------------------------- runtime shims
// Only the test harness uses these. The module under test uses neither.

const shim = isDeno
  ? {
      env: (name) => globalThis.Deno.env.get(name),
      exit: (code) => globalThis.Deno.exit(code),
      mkdirTemp: (prefix) => globalThis.Deno.makeTempDirSync({ prefix }),
      mkdir: (path) => globalThis.Deno.mkdirSync(path, { recursive: true }),
      writeFile: (path, bytes) => globalThis.Deno.writeFileSync(path, bytes),
      removeTree: (path) => {
        try { globalThis.Deno.removeSync(path, { recursive: true }) } catch (_e) { /* already gone */ }
      },
      exists: (path) => {
        try { globalThis.Deno.statSync(path); return true } catch (_e) { return false }
      },
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
      selfCommand: () => globalThis.Deno.execPath(),
      selfArgs: (file, rest) =>
        ['run', '--allow-read', '--allow-write', '--allow-run', '--allow-env', file, ...rest]
    }
  : await (async () => {
      const fs = await import('node:fs')
      const os = await import('node:os')
      const cp = await import('node:child_process')
      return {
        env: (name) => process.env[name],
        exit: (code) => process.exit(code),
        mkdirTemp: (prefix) => fs.mkdtempSync(joinPath(os.tmpdir(), prefix)),
        mkdir: (path) => fs.mkdirSync(path, { recursive: true }),
        writeFile: (path, bytes) => fs.writeFileSync(path, bytes),
        removeTree: (path) => fs.rmSync(path, { recursive: true, force: true }),
        exists: (path) => fs.existsSync(path),
        run: (command, args) => {
          const result = cp.spawnSync(command, args, { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 })
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
        selfCommand: () => process.execPath,
        selfArgs: (file, rest) => [file, ...rest]
      }
    })()

// --------------------------------------------------------- tiny harness

let passed = 0
let failed = 0
let skipped = 0
const failures = []

async function check (name, body) {
  try {
    await body()
    passed += 1
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : String(error)}`)
  }
}

function skip (name, reason) {
  skipped += 1
  console.log(`  skip ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

function assertBytesEqual (actual, expected, message) {
  assert(actual instanceof Uint8Array, `${message}: not a Uint8Array`)
  assert(actual.length === expected.length,
    `${message}: length ${actual.length}, expected ${expected.length}`)
  for (let index = 0; index < expected.length; index += 1) {
    if (actual[index] !== expected[index]) {
      throw new Error(`${message}: byte ${index} is ${actual[index]}, expected ${expected[index]}`)
    }
  }
}

async function assertThrowsCode (body, code, message) {
  let error = null
  try {
    await body()
  } catch (caught) {
    error = caught
  }
  assert(error !== null, `${message}: nothing was thrown`)
  assert(error instanceof StoreHostError,
    `${message}: threw ${error && error.name} not StoreHostError`)
  assert(error.code === code, `${message}: code ${error.code}, expected ${code}`)
}

async function sha256Hex (bytes) {
  const digest = await globalThis.crypto.subtle.digest('SHA-256', bytes)
  return [...new Uint8Array(digest)]
    .map((byte) => byte.toString(16).padStart(2, '0')).join('')
}

function fill (length, byte) {
  const out = new Uint8Array(length)
  out.fill(byte)
  return out
}

// ------------------------------------------------- the concurrent reader
// Spawned as a child process by the atomic-replace check below. It reads
// the target file in a loop and reports any read that is neither of the
// two whole versions.

if (argv[0] === '--reader') {
  const target = argv[1]
  const lengthA = Number(argv[2])
  const lengthB = Number(argv[3])
  const deadline = Date.now() + Number(argv[4])
  let reads = 0
  let violations = 0
  let missing = 0
  const partials = []
  while (Date.now() < deadline) {
    let bytes
    try {
      bytes = readWhole(target)
    } catch (_error) {
      missing += 1
      continue
    }
    reads += 1
    const expectedByte = bytes.length === lengthA ? 0x41 : bytes.length === lengthB ? 0x42 : -1
    if (expectedByte < 0) {
      violations += 1
      if (partials.length < 4) partials.push(`length ${bytes.length}`)
      continue
    }
    for (let index = 0; index < bytes.length; index += 1) {
      if (bytes[index] !== expectedByte) {
        violations += 1
        if (partials.length < 4) partials.push(`byte ${index} = ${bytes[index]}`)
        break
      }
    }
  }
  console.log(JSON.stringify({ reads, violations, missing, partials }))
  shim.exit(0)
}

// ------------------------------------------------------------- fixtures

const testFile = fileUrlToPath(import.meta.url)
const repoRoot = fileUrlToPath(new URL('../..', import.meta.url).href).replace(/\/$/, '')

/** Where the committed native l4block-* binaries are. */
function nativeBinDirectory () {
  const override = shim.env('L4_BIN_DIR')
  if (typeof override === 'string' && override.length > 0) {
    // An override that names the wrong directory fails loudly. A silent
    // fall-through to "skipped" would report a green run that measured
    // nothing (anti-pattern 3).
    if (!shim.exists(joinPath(override, 'l4block-shard-pack'))) {
      throw new Error(`L4_BIN_DIR=${override} holds no l4block-shard-pack`)
    }
    return override
  }
  const local = joinPath(repoRoot, 'formal/lean4/.lake/build/bin')
  if (shim.exists(joinPath(local, 'l4block-shard-pack'))) return local
  // A git worktree has no .lake/build of its own; the main checkout does.
  try {
    const gitFile = new TextDecoder().decode(readWhole(joinPath(repoRoot, '.git')))
    const match = /gitdir:\s*(.*?)\/\.git\/worktrees\//.exec(gitFile)
    if (match !== null) {
      const main = joinPath(match[1], 'formal/lean4/.lake/build/bin')
      if (shim.exists(joinPath(main, 'l4block-shard-pack'))) return main
    }
  } catch (_error) { /* .git is a directory, not a worktree pointer */ }
  return null
}

const workDirectory = shim.mkdirTemp('factoidal-store-host-')

// ------------------------------------------------------------ the checks

console.log(`store-host conformance (${runtime})`)

// --- readWhole and readRange, the l4_block_pread counterpart -----------

const plainPath = joinPath(workDirectory, 'plain.bin')
const plainBytes = new Uint8Array(4096)
for (let index = 0; index < plainBytes.length; index += 1) plainBytes[index] = (index * 7) & 0xff
shim.writeFile(plainPath, plainBytes)

await check('readWhole returns the whole file', () => {
  assertBytesEqual(readWhole(plainPath), plainBytes, 'readWhole')
})

await check('readRange returns exactly the requested interior bytes', () => {
  assertBytesEqual(readRange(plainPath, 1000, 333), plainBytes.slice(1000, 1333), 'readRange')
})

await check('readRange of the whole extent equals readWhole', () => {
  assertBytesEqual(readRange(plainPath, 0, plainBytes.length), plainBytes, 'readRange full')
})

await check('readRange of zero bytes is empty', () => {
  assertBytesEqual(readRange(plainPath, 10, 0), new Uint8Array(0), 'readRange zero')
})

await check('readRange refuses a short read (the extern returns empty; readRange? gives none)', () =>
  assertThrowsCode(() => readRange(plainPath, 4000, 200), 'SHORT_READ', 'past the end'))

await check('readRange refuses an offset past the end', () =>
  assertThrowsCode(() => readRange(plainPath, 99999, 1), 'SHORT_READ', 'offset past the end'))

await check('readRange refuses a negative offset', () =>
  assertThrowsCode(() => readRange(plainPath, -1, 4), 'BAD_ARGUMENT', 'negative offset'))

await check('readRange refuses a non-integer length', () =>
  assertThrowsCode(() => readRange(plainPath, 0, 1.5), 'BAD_ARGUMENT', 'fractional length'))

await check('readRange refuses an offset at 2^53 (a UInt64 the host cannot represent)', () =>
  assertThrowsCode(() => readRange(plainPath, 2 ** 53, 1), 'BAD_ARGUMENT', 'huge offset'))

await check('readWhole of an absent file reports OPEN_FAILED', () =>
  assertThrowsCode(() => readWhole(joinPath(workDirectory, 'absent.bin')), 'OPEN_FAILED', 'absent file'))

await check('interleaved readRange calls share no file cursor', () => {
  const offsets = [0, 2048, 1, 4095, 512, 3000]
  for (let round = 0; round < 30; round += 1) {
    for (const offset of offsets) {
      const length = Math.min(64, plainBytes.length - offset)
      assertBytesEqual(readRange(plainPath, offset, length),
        plainBytes.slice(offset, offset + length), `round ${round} offset ${offset}`)
    }
  }
})

// --- appendSyncAtSize, the l4_delta_log_append_sync_at_size counterpart -

const appendPath = joinPath(workDirectory, 'append.bin')

await check('append at expected size 0 creates the file', () => {
  const first = fill(16, 0x31)
  assert(appendSyncAtSize(appendPath, first, 0) === true, 'append to an absent file returned false')
  assertBytesEqual(readWhole(appendPath), first, 'created file')
})

await check('append at the wrong expected size is refused and changes nothing', () => {
  const before = readWhole(appendPath)
  assert(appendSyncAtSize(appendPath, fill(8, 0x39), 0) === false, 'size 0 returned true')
  assert(appendSyncAtSize(appendPath, fill(8, 0x39), 15) === false, 'size - 1 returned true')
  assert(appendSyncAtSize(appendPath, fill(8, 0x39), 17) === false, 'size + 1 returned true')
  assertBytesEqual(readWhole(appendPath), before, 'file after three refusals')
})

await check('append at the right expected size appends exactly', () => {
  const before = readWhole(appendPath)
  const addition = fill(24, 0x32)
  assert(appendSyncAtSize(appendPath, addition, before.length) === true, 'correct size returned false')
  const after = readWhole(appendPath)
  assert(after.length === before.length + addition.length, `length ${after.length}`)
  assertBytesEqual(after.slice(0, before.length), before, 'prefix')
  assertBytesEqual(after.slice(before.length), addition, 'appended bytes')
})

await check('a sequence of appends builds the concatenation', () => {
  const path = joinPath(workDirectory, 'sequence.bin')
  let expected = new Uint8Array(0)
  for (let round = 0; round < 20; round += 1) {
    const chunk = fill(1 + round, 0x40 + round)
    assert(appendSyncAtSize(path, chunk, expected.length) === true, `round ${round} refused`)
    const next = new Uint8Array(expected.length + chunk.length)
    next.set(expected, 0)
    next.set(chunk, expected.length)
    expected = next
  }
  assertBytesEqual(readWhole(path), expected, 'concatenation')
})

await check('append refuses a payload that is not bytes', () =>
  assertThrowsCode(() => appendSyncAtSize(appendPath, 'text', 0), 'BAD_ARGUMENT', 'string payload'))

// --- atomicReplace, the l4_atomic_replace_file_sync counterpart ---------

const replacePath = joinPath(workDirectory, 'CURRENT')

await check('atomicReplace creates an absent file', () => {
  const bytes = new TextEncoder().encode('gen-1')
  assert(atomicReplace(replacePath, bytes) === true, 'returned false')
  assertBytesEqual(readWhole(replacePath), bytes, 'created')
})

await check('atomicReplace with shorter bytes leaves no tail of the old version', () => {
  const long = fill(500, 0x61)
  const short = fill(3, 0x62)
  assert(atomicReplace(replacePath, long) === true, 'long returned false')
  assert(atomicReplace(replacePath, short) === true, 'short returned false')
  assertBytesEqual(readWhole(replacePath), short, 'after the shrink')
})

await check('atomicReplace leaves no temporary file behind', () => {
  for (let round = 0; round < 20; round += 1) atomicReplace(replacePath, fill(round + 1, 0x63))
  const leftovers = listGeneration(workDirectory).filter((file) => file.name.indexOf('.tmp.') >= 0)
  assert(leftovers.length === 0, `left ${leftovers.map((file) => file.name).join(', ')}`)
})

await check('a concurrent reader never sees a partial replacement', async () => {
  // A same-thread reader cannot observe a partial write at all: the replace
  // path is synchronous in both runtimes, so nothing else in this process
  // runs during it. The observable question is whether ANOTHER process can
  // see the target between the temporary file's write and the rename. This
  // check answers that one, with a real second process.
  const target = joinPath(workDirectory, 'racy.bin')
  const lengthA = 65536
  const lengthB = 37
  const payloadA = fill(lengthA, 0x41)
  const payloadB = fill(lengthB, 0x42)
  atomicReplace(target, payloadA)
  const reader = shim.spawn(
    shim.selfCommand(),
    shim.selfArgs(testFile, ['--reader', target, String(lengthA), String(lengthB), '1500'])
  )
  const stop = Date.now() + 1200
  let replacements = 0
  while (Date.now() < stop) {
    atomicReplace(target, replacements % 2 === 0 ? payloadB : payloadA)
    replacements += 1
  }
  const result = await reader.wait()
  assert(result.code === 0, `the reader exited ${result.code}: ${result.stderr}`)
  const report = JSON.parse(result.stdout.trim().split('\n').pop())
  assert(replacements > 10, `only ${replacements} replacements ran`)
  assert(report.reads > 10, `the reader made only ${report.reads} reads`)
  assert(report.violations === 0,
    `${report.violations} partial reads out of ${report.reads} (${report.partials.join('; ')})`)
  assert(report.missing === 0, `the target was absent on ${report.missing} reads`)
})

// --- openCollection and listGeneration ---------------------------------

await check('openCollection reports NO_CURRENT when the root has no pointer', () => {
  const root = joinPath(workDirectory, 'empty-root')
  shim.mkdir(root)
  return assertThrowsCode(() => openCollection(root), 'NO_CURRENT', 'no CURRENT')
})

await check('openCollection refuses a CURRENT that would leave the root', () => {
  const root = joinPath(workDirectory, 'escaping-root')
  shim.mkdir(root)
  shim.writeFile(joinPath(root, 'CURRENT'), new TextEncoder().encode('../elsewhere'))
  return assertThrowsCode(() => openCollection(root), 'BAD_CHILD_NAME', 'escaping pointer')
})

await check('openCollection reports NO_MANIFEST when the generation has none', () => {
  const root = joinPath(workDirectory, 'bare-root')
  shim.mkdir(joinPath(root, 'gen-1'))
  shim.writeFile(joinPath(root, 'CURRENT'), new TextEncoder().encode('gen-1'))
  return assertThrowsCode(() => openCollection(root), 'NO_MANIFEST', 'no manifest')
})

await check('listGeneration lists regular files with their sizes and skips directories', () => {
  const directory = joinPath(workDirectory, 'listing')
  shim.mkdir(joinPath(directory, 'child'))
  shim.writeFile(joinPath(directory, 'b.bin'), fill(7, 1))
  shim.writeFile(joinPath(directory, 'a.bin'), fill(3, 1))
  const listed = listGeneration(directory)
  assert(listed.length === 2, `listed ${listed.length} entries`)
  assert(listed[0].name === 'a.bin' && listed[0].size === 3, 'first entry')
  assert(listed[1].name === 'b.bin' && listed[1].size === 7, 'second entry')
})

// --- correspondence with the native binaries ---------------------------

const NATIVE_CHECK_COUNT = 5
const binDirectory = nativeBinDirectory()
const fixture = joinPath(repoRoot, 'formal/lean4/Harness/TestData/heterogeneous-fixture.ttl')

if (binDirectory === null || !shim.exists(fixture)) {
  skip(`native correspondence (${NATIVE_CHECK_COUNT} checks)`, binDirectory === null
    ? 'no l4block-shard-pack found; set L4_BIN_DIR to the directory holding it'
    : `fixture absent: ${fixture}`)
  skipped += NATIVE_CHECK_COUNT - 1
} else {
  const collection = joinPath(workDirectory, 'collection')
  const generation = joinPath(collection, 'gen-1')
  const packed = shim.run(joinPath(binDirectory, 'l4block-shard-pack'), [fixture, generation, 'ibk3'])
  const activated = packed.code === 0
    ? shim.run(joinPath(binDirectory, 'l4block-shard-activate'), [collection, 'gen-1'])
    : { code: 1, stdout: '', stderr: 'the pack step failed' }

  await check('the native packer and activator produced a generation', () => {
    assert(packed.code === 0, `l4block-shard-pack exited ${packed.code}: ${packed.stderr}`)
    assert(activated.code === 0, `l4block-shard-activate exited ${activated.code}: ${activated.stderr}`)
  })

  // manifest.tsv is the packer's own artifact table. The test reads it to
  // learn which file holds which predicate and what the packer committed as
  // its digest. The module under test reads none of this.
  const tsv = new TextDecoder().decode(readWhole(joinPath(generation, 'manifest.tsv')))
  const rows = tsv.split('\n')
    .filter((line) => line.length > 0 && !line.startsWith('#'))
    .map((line) => {
      const cells = line.split('\t')
      return { predicate: cells[1], file: cells[2], bytes: Number(cells[4]), sha256: cells[5] }
    })

  await check('every artifact the packer recorded hashes to the digest it recorded', async () => {
    assert(rows.length > 0, 'manifest.tsv held no rows')
    for (const row of rows) {
      const bytes = readWhole(joinPath(generation, row.file))
      assert(bytes.length === row.bytes, `${row.file}: ${bytes.length} bytes, recorded ${row.bytes}`)
      const digest = await sha256Hex(bytes)
      assert(digest === row.sha256, `${row.file}: sha256 ${digest}, recorded ${row.sha256}`)
    }
  })

  await check('readRange agrees with the native verified read at the same offset and length', () => {
    let ranges = 0
    for (const row of rows) {
      const artifact = joinPath(generation, row.file)
      const whole = readWhole(artifact)
      const half = Math.floor(row.bytes / 2)
      const candidates = [
        [0, row.bytes],
        [0, Math.min(16, row.bytes)],
        [half, row.bytes - half],
        [Math.max(0, row.bytes - 8), Math.min(8, row.bytes)]
      ]
      for (const [offset, length] of candidates) {
        if (length <= 0) continue
        const native = shim.run(joinPath(binDirectory, 'l4block-shard-merkle-pread'),
          [generation, row.predicate, String(offset), String(length)])
        assert(native.code === 0,
          `native pread ${row.file} ${offset} ${length} exited ${native.code}: ${native.stderr}`)
        assert(native.stdout.indexOf(`verified-bytes=${length}`) >= 0,
          `native pread reported ${native.stdout.trim()}`)
        assert(native.stdout.indexOf(`offset=${offset}`) >= 0,
          `native pread reported ${native.stdout.trim()}`)
        assertBytesEqual(readRange(artifact, offset, length), whole.slice(offset, offset + length),
          `${row.file} at ${offset}+${length}`)
        ranges += 1
      }
    }
    assert(ranges >= 4, `only ${ranges} ranges were compared`)
  })

  await check('a range past the artifact end is refused by the native tool and by readRange', () => {
    const row = rows[rows.length - 1]
    const native = shim.run(joinPath(binDirectory, 'l4block-shard-merkle-pread'),
      [generation, row.predicate, String(row.bytes - 4), '64'])
    assert(native.code !== 0, `native pread accepted a range past the end: ${native.stdout.trim()}`)
    return assertThrowsCode(
      () => readRange(joinPath(generation, row.file), row.bytes - 4, 64),
      'SHORT_READ', 'past the artifact end')
  })

  await check('openCollection and listGeneration match what the packer wrote', () => {
    const opened = openCollection(collection)
    assert(opened.generation === 'gen-1', `CURRENT holds "${opened.generation}"`)
    assert(opened.manifestName === 'manifest.sbm2', `manifest name ${opened.manifestName}`)
    assertBytesEqual(opened.manifest, readWhole(joinPath(generation, opened.manifestName)),
      'manifest bytes')
    const listed = listGeneration(opened.generationDir)
    const sizes = new Map(listed.map((file) => [file.name, file.size]))
    for (const row of rows) {
      assert(sizes.get(row.file) === row.bytes,
        `${row.file}: listed ${sizes.get(row.file)}, recorded ${row.bytes}`)
    }
    assert(listed.length >= rows.length + 1, `listed only ${listed.length} files`)
  })
}

// --- wire version 10, through the store host --------------------------
//
// An SBM10 generation of IBK5 blocks
// (docs/designissues/2026-09-05-wire-version-10-scale.md). What is gated
// here is the HOST side of it: `plan.blobKeys` names the `blob-<hex>.lit`
// files a query touches, and `bin/store.mjs` must fetch them beside the
// blocks for both the stateless path and the handle path. A block above
// the 65,536-byte inline ceiling holds only a byte extent and a SHA-256,
// so a host that fetches the blocks alone gets a refusal, not a short
// literal.
//
// The engine checks need a wasm module built from a Store.lean that reads
// IBK5. The committed module refuses the layout, so the group is skipped
// with the reason printed until the coordinator rebuilds it. The probe is
// a positive capability check: an engine that reads wire version 10
// reports the manifest blob table.

const V10_FILE_CHECKS = 1
const V10_ENGINE_CHECKS = 4
const rdf12Source = joinPath(repoRoot, 'tests/local/data/rdf12_sample.trig')

if (binDirectory === null || !shim.exists(rdf12Source)) {
  skip(`wire version 10 (${V10_FILE_CHECKS + V10_ENGINE_CHECKS} checks)`,
    binDirectory === null
      ? 'no l4block-shard-pack found; set L4_BIN_DIR to the directory holding it'
      : `fixture absent: ${rdf12Source}`)
  skipped += V10_FILE_CHECKS + V10_ENGINE_CHECKS - 1
} else {
  const v10Root = joinPath(workDirectory, 'collection-v10')
  const v10Generation = joinPath(v10Root, 'gen-1')
  const v10Packed = shim.run(joinPath(binDirectory, 'l4block-shard-pack'),
    [rdf12Source, v10Generation, 'ibk5'])
  const v10Activated = v10Packed.code === 0
    ? shim.run(joinPath(binDirectory, 'l4block-shard-activate'), [v10Root, 'gen-1'])
    : { code: 1, stdout: '', stderr: 'the pack step failed' }

  await check('every out-of-line literal is a file named by its own SHA-256', async () => {
    assert(v10Packed.code === 0,
      `l4block-shard-pack exited ${v10Packed.code}: ${v10Packed.stderr}`)
    assert(v10Activated.code === 0,
      `l4block-shard-activate exited ${v10Activated.code}: ${v10Activated.stderr}`)
    const blobs = listGeneration(v10Generation)
      .filter((file) => file.name.startsWith('blob-') && file.name.endsWith('.lit'))
    assert(blobs.length === 2, `the generation holds ${blobs.length} blob files, expected 2`)
    for (const blob of blobs) {
      const bytes = readWhole(joinPath(v10Generation, blob.name))
      assert(bytes.length === blob.size,
        `${blob.name}: read ${bytes.length} bytes, listed ${blob.size}`)
      const digest = await sha256Hex(bytes)
      assert(blob.name === `blob-${digest}.lit`,
        `${blob.name} does not name its own digest ${digest}`)
    }
    const sizes = blobs.map((blob) => blob.size).sort((a, b) => a - b)
    assert(sizes[0] === 68226 && sizes[1] === 70000,
      `the out-of-line literals are ${sizes.join(', ')} bytes`)
  })

  // The engine half. `store.mjs` is the module under test here, not the
  // command: it is what turns `plan.blobKeys` into files on the region.
  const storeModule = await import('../../npm/factoidal/bin/store.mjs')
  const engineModule = await import('../../npm/factoidal/bin/engine.mjs')
  let v10Engine = null
  let v10Store = null
  let readsIbk5 = false
  try {
    v10Engine = await engineModule.loadEngine()
    v10Store = storeModule.openStore(v10Root)
    const envelope = storeModule.inspectManifest(v10Engine, v10Store)
    readsIbk5 = envelope.ok === true && Array.isArray(envelope.blobs)
  } catch (_error) {
    readsIbk5 = false
  }

  if (!readsIbk5) {
    skip(`wire version 10 through the engine (${V10_ENGINE_CHECKS} checks)`,
      'this engine reports no manifest blob table, so the committed wasm module ' +
      'does not read IBK5 yet; rebuild it (Wasm/build-wasm.sh) to run these')
    skipped += V10_ENGINE_CHECKS - 1
  } else {
    await check('the plan names the blob files a query touches', () => {
      const plan = storeModule.planQuery(v10Engine, v10Store,
        'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } ' +
        'BIND(STRLEN(?o) AS ?n) }')
      assert(plan.ok === true, 'the plan was refused')
      assert(Array.isArray(plan.blobKeys) && plan.blobKeys.length === 1,
        `the plan named ${JSON.stringify(plan.blobKeys)}`)
      assert(plan.blobKeys[0].startsWith('blob-') && plan.blobKeys[0].endsWith('.lit'),
        `the plan named ${plan.blobKeys[0]}`)
      assert(typeof plan.zoneExcluded === 'number',
        'the plan reports no zone-map exclusion count')
    })

    await check('the stateless path resolves the 70,000-byte literal', () => {
      const answer = storeModule.queryStore(v10Engine, v10Store,
        'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } ' +
        'BIND(STRLEN(?o) AS ?n) }')
      const bindings = answer.result.srj.results.bindings
      assert(bindings.length === 1, `STRLEN answered ${bindings.length} rows`)
      assert(bindings[0].n.value === '70000', `STRLEN answered ${bindings[0].n.value}`)
      assert(answer.artifacts.some((artifact) => artifact.key.startsWith('blob-')),
        'the host carried no blob artifact')
    })

    await check('a handle resolves the blobs once and answers the candidate paths', () => {
      const handle = storeModule.openStoreHandle(v10Engine, v10Store)
      try {
        assert(handle.blobs === 2, `the handle resolved ${handle.blobs} blobs, expected 2`)
        const needle = handle.query(
          'SELECT ?s WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } ' +
          'FILTER(CONTAINS(?o, "needle")) }')
        assert(needle.srj.results.bindings.length === 1,
          `the CONTAINS query answered ${needle.srj.results.bindings.length} rows`)
        const geo = handle.query(
          'SELECT ?s WHERE { GRAPH ?g { ?s ' +
          '<http://www.opengis.net/ont/geosparql#asWKT> ?o } FILTER(' +
          '<http://www.opengis.net/def/function/geosparql/sfIntersects>(?o, ' +
          '"POINT(5 5)"^^<http://www.opengis.net/ont/geosparql#wktLiteral>)) }')
        assert(geo.srj.results.bindings.length === 1,
          `the geometry query answered ${geo.srj.results.bindings.length} rows`)
      } finally {
        handle.close()
      }
    })

    await check('a handle opened without the blobs is refused, by name', () => {
      const envelope = storeModule.inspectManifest(v10Engine, v10Store)
      const keys = []
      for (const entry of envelope.entries) {
        keys.push(entry.key)
        for (const key of Object.values(entry.sidecars ?? {})) keys.push(key)
      }
      let refusal = null
      let opened = null
      try {
        opened = storeModule.openStoreHandle(v10Engine, v10Store, { keys })
      } catch (error) {
        refusal = error
      }
      if (opened !== null) opened.close()
      assert(refusal !== null, 'an open without the blob files was admitted')
      assert(refusal.message.indexOf('.lit') >= 0,
        `the refusal did not name the blob: ${refusal.message}`)
    })
  }
}

// ------------------------------------------------------------- reporting

shim.removeTree(workDirectory)

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`${runtime}: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)

let exitCode = failed === 0 ? 0 : 1

// The Node run drives the Deno run too, so one command reports both.
if (!isDeno && argv.indexOf('--no-deno') < 0) {
  const probe = shim.run('/bin/sh', ['-c', 'command -v deno'])
  const denoPath = probe.code === 0 && probe.stdout.trim().length > 0 ? probe.stdout.trim() : null
  if (denoPath === null) {
    console.log('deno: not installed, so the Deno run is skipped (install deno to run it)')
  } else {
    console.log(`deno: ${denoPath}`)
    const child = shim.spawn(denoPath,
      ['run', '--allow-read', '--allow-write', '--allow-run', '--allow-env', testFile, '--no-deno'])
    const result = await child.wait()
    shim.writeOut(result.stdout)
    if (result.stderr.length > 0) shim.writeErr(result.stderr)
    if (result.code !== 0) exitCode = 1
  }
}

shim.exit(exitCode)
