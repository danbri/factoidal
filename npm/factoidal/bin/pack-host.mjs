// Giving `factoidal pack` a call stack big enough to finish, without
// asking the reader for a runtime flag.
// https://github.com/danbri/factoidal/issues/649
//
// THE DEFECT THIS FILE EXISTS FOR
// The pack fold in the engine recurses one frame per term in one block's
// local term index, and that is far deeper than a query recurses per row.
// On the DEFAULT stack of Node 22 and of Deno 2 the pack of anything
// above roughly 0.25 MB of Turtle ends with `Maximum call stack size
// exceeded` -- measured 2026-09-04 against the committed module, where
// `sequence_variant.ttl` (241,149 B) passes and `chromosome.ttl`
// (316,116 B) does not. Every one of those inputs packs correctly once
// the stack is raised, and the generation is byte-identical to
// `l4block-shard-pack` output. So the defect is the frame budget alone.
// The depth, what sets it, and why a browser cannot be given more are in
// `docs/designissues/2026-09-03-npm-pack-in-wasm.md`.
//
// WHAT THIS FILE IS ALLOWED TO DO
// Start the same pack on a thread or in a child process that has a
// bigger stack, carry the progress reports back, and re-raise the same
// error. It reads no RDF, decides no artifact name, and moves no
// artifact bytes: the worker writes the generation itself, through the
// same `store-host` primitives, exactly where the artifacts arrive.
// A reader must not be able to tell that a worker is involved, except
// that the pack finishes (iron rule 7 of CLAUDE.md).
//
// THE TWO ROUTES
//   Node -- `worker_threads`, with `resourceLimits.stackSizeMb`. The
//           engine loads INSIDE the worker: a loaded WebAssembly
//           instance does not cross a thread boundary.
//   Deno -- `worker_threads` is not the route, and a Deno `Worker` takes
//           no stack size. The command re-executes itself once with
//           `--v8-flags=--stack-size=...`, guarded by an environment
//           variable so it can never loop. Confirmed honoured by
//           deno 2.9.4 / V8 15.0.245.2 on 2026-09-04:
//           `deno run -A --v8-flags=--stack-size=8000` packs
//           `anatomical_structure.ttl` (3,811,378 B) in 13.7 s, where
//           the same command without the flag overflows.
//
// WHAT IT DOES NOT FIX
// A browser tab has a fixed frame budget and no host flag, so neither
// route rescues an in-page packer. See the closing section of
// `docs/designissues/2026-09-03-npm-pack-in-wasm.md`.

import { StoreHostError, listGeneration, readWhole } from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'
import { loadEngine } from './engine.mjs'
import { PackError, packFile, packSupported, verifyGeneration } from './pack.mjs'
import { StoreOperationError, openStore } from './store.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined'

/**
 * The worker's stack, in mebibytes.
 *
 * MEASURED, 2026-09-04, macOS 15 arm64, Node 22.22.2, against
 * `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` -- 17,363,312
 * bytes, 888,949 triples, the largest input the milestone carries:
 *
 *   stackSizeMb  verdict
 *   4 (default)  Maximum call stack size exceeded
 *   6            Maximum call stack size exceeded
 *   7            Maximum call stack size exceeded
 *   8            pass, 42 s
 *   10           pass
 *   64           pass, 68 s
 *
 * 8 MiB is therefore the measured minimum, and 64 is eight times it.
 * The headroom is deliberate and it is cheap: a thread stack is reserved
 * address space, and only the pages actually touched become resident, so
 * an unused 56 MiB costs nothing. The depth is set by the number of
 * terms in ONE block's dictionary, not by the file size, so a file
 * smaller than gene.ttl but with a wider dictionary needs more, and a
 * value only just above the measured minimum would move the same defect
 * to another input.
 */
export const WORKER_STACK_MB = 64

/** The V8 stack limit the Deno re-exec asks for, in kibibytes -- the
 *  unit `--stack-size` takes. Same budget as WORKER_STACK_MB. */
export const REEXEC_STACK_KB = WORKER_STACK_MB * 1024

/** Set in the re-executed Deno child, so the guard can never loop. */
export const REEXEC_GUARD = 'FACTOIDAL_PACK_STACK_REEXEC'

/** Read one environment variable, or null where reading it is refused. */
function environment (name) {
  try {
    if (isDeno && globalThis.Deno.env) {
      const value = globalThis.Deno.env.get(name)
      return typeof value === 'string' && value.length > 0 ? value : null
    }
  } catch (_error) {
    // Deno without --allow-env. An absent override is the normal case.
    return null
  }
  const value = globalThis.process && globalThis.process.env
    ? globalThis.process.env[name]
    : undefined
  return typeof value === 'string' && value.length > 0 ? value : null
}

/** The stack the worker asks for: `WORKER_STACK_MB`, or the override in
 *  FACTOIDAL_PACK_STACK_MB, which exists so the measurement above can be
 *  repeated without editing this file. */
export function workerStackMb () {
  const override = environment('FACTOIDAL_PACK_STACK_MB')
  if (override === null) return WORKER_STACK_MB
  const value = Number(override)
  return Number.isSafeInteger(value) && value > 0 ? value : WORKER_STACK_MB
}

/** Whether the caller asked for the in-process path. `--no-worker` on the
 *  command line, or FACTOIDAL_NO_WORKER in the environment. The old
 *  behaviour stays testable, and a platform where the worker fails has a
 *  way out. */
export function workerRefused (options) {
  if (options && options.worker === false) return true
  return environment('FACTOIDAL_NO_WORKER') !== null
}

// ------------------------------------------------- carrying an error back
//
// `commandPack` distinguishes a PackError and a StoreHostError from
// everything else, and prints the engine's own words in each case. A
// worker boundary must not change any of that, so the failure crosses as
// a plain description and is rebuilt on the other side.

/** Describe a thrown value so it survives `postMessage`. */
export function describeError (error) {
  if (error instanceof PackError) {
    return {
      type: 'PackError',
      message: error.message,
      handle: error.handle,
      notWired: error.notWired
    }
  }
  if (error instanceof StoreHostError) {
    return {
      type: 'StoreHostError',
      message: error.message,
      code: error.code,
      path: error.path === undefined ? null : error.path
    }
  }
  if (error instanceof StoreOperationError) {
    return {
      type: 'StoreOperationError',
      message: error.message,
      capValue: error.capValue,
      capLimit: error.capLimit,
      digestKey: error.digestKey,
      stackLimit: error.stackLimit
    }
  }
  return {
    type: 'Error',
    message: error && error.message ? String(error.message) : String(error)
  }
}

/** Rebuild what `describeError` described. */
export function reviveError (description) {
  if (description.type === 'PackError') {
    return new PackError(description.message,
      { handle: description.handle, notWired: description.notWired })
  }
  if (description.type === 'StoreHostError') {
    const detail = description.path === null ? {} : { path: description.path }
    return new StoreHostError(description.code, description.message, detail)
  }
  if (description.type === 'StoreOperationError') {
    return new StoreOperationError(description.message, {
      capValue: description.capValue === null ? undefined : description.capValue,
      capLimit: description.capLimit === null ? undefined : description.capLimit,
      digestKey: description.digestKey === null ? undefined : description.digestKey,
      stackLimit: description.stackLimit
    })
  }
  return new Error(description.message)
}

/** Whether a failure is the runtime running out of call stack. */
export function isStackOverflow (error) {
  if (error instanceof RangeError) return true
  const message = error && error.message ? String(error.message) : String(error)
  return message.indexOf('call stack size exceeded') >= 0
}

// ------------------------------------------------------ the pack itself

/**
 * Load the engine and run one deep task, on whatever stack the caller has.
 *
 * This is the body both routes run: the worker calls it on its own big
 * stack, and `--no-worker` calls it in the process it was started in.
 *
 * `task.kind` selects the work. Both kinds recurse once per distinct term
 * in a block's local term index, so both need the raised stack -- the
 * verification `activate` runs decodes the same blocks the pack encoded.
 * `activate` overflowed on a 112,742-row generation that `pack` had just
 * written successfully, which is how the two came to share this path
 * (measured 2026-09-04, https://github.com/danbri/factoidal/issues/649).
 *
 * @returns {{notWired: true}|{report: object}}
 */
export async function packHere (task, onProgress) {
  const engine = await loadEngine()
  if (!packSupported(engine)) return { notWired: true }
  if (task.kind === 'activate') {
    return { report: activateHere(engine, task) }
  }
  const report = packFile(engine, task.input, task.output, {
    syntax: task.syntax,
    layout: task.layout,
    base: task.base,
    onProgress
  })
  return { report }
}

/**
 * Verify one generation and answer the engine's verdict.
 *
 * The host reads the manifest and every artifact and hands them over; the
 * engine checks each against the digest the manifest commits. Replacing
 * CURRENT is NOT done here -- it is the caller's step, and it happens on
 * the main thread only after this returns ok, so a worker that dies
 * mid-verification can never leave a half-moved pointer.
 */
function activateHere (engine, task) {
  const store = openStore(task.root, task.generation)
  const files = listGeneration(store.generationDir)
  const artifacts = files
    .filter((file) => file.name !== store.manifestName)
    .map((file) => ({
      key: file.name,
      bytes: readWhole(joinPath(store.generationDir, file.name))
    }))
  return verifyGeneration(engine, store.manifestHex, artifacts)
}

/**
 * Pack on a `worker_threads` thread with a raised stack. Node only.
 *
 * The worker writes every artifact itself, so no artifact byte crosses
 * the thread boundary; what crosses is the task, the progress reports
 * and the finish envelope.
 *
 * @returns {{notWired: true}|{report: object}}
 * @throws whatever the pack threw, rebuilt
 */
async function packInWorker (task, onProgress) {
  const { Worker } = await import('node:worker_threads')
  const entry = new URL('./pack-worker.mjs', import.meta.url)
  const stackSizeMb = workerStackMb()
  return await new Promise((resolve, reject) => {
    const worker = new Worker(entry, {
      workerData: { ...task, progress: typeof onProgress === 'function' },
      resourceLimits: { stackSizeMb },
      stdout: false,
      stderr: false
    })
    let settled = false
    const finish = (act) => {
      if (settled) return
      settled = true
      worker.terminate().then(act, act)
    }
    worker.on('message', (message) => {
      if (message.kind === 'progress') {
        if (typeof onProgress === 'function') onProgress(message.progress)
        return
      }
      if (message.kind === 'error') {
        const failure = reviveError(message.error)
        finish(() => reject(failure))
        return
      }
      finish(() => resolve(message.kind === 'notWired'
        ? { notWired: true }
        : { report: message.report }))
    })
    worker.on('error', (error) => { finish(() => reject(error)) })
    worker.on('exit', (code) => {
      if (settled) return
      settled = true
      reject(new PackError(`the pack worker exited with code ${code}`))
    })
  })
}

/**
 * Run one deep task, on the biggest stack this runtime will give it.
 *
 * On Node the worker route is the default. On Deno the caller has
 * already re-executed (see `denoReexec`), so this runs in process.
 *
 * @param {object} task {kind, ...}: a pack takes
 *   {input, output, syntax, layout, base}, an activate takes
 *   {root, generation}
 * @param {(progress: object) => void} [onProgress]
 * @param {object} [options] {worker: false} forces the in-process path
 */
export async function runPack (task, onProgress, options) {
  if (isDeno || workerRefused(options)) return await packHere(task, onProgress)
  return await packInWorker(task, onProgress)
}

// -------------------------------------------------------- the Deno route

/**
 * Re-execute this command once under Deno with a raised V8 stack.
 *
 * Returns null when the re-exec is not available or not wanted, and the
 * caller then packs in process. Returns the child's exit code when the
 * child ran, and the caller exits with it. Permissions are NOT
 * escalated: the child is given exactly the ones this process was
 * granted, queried rather than requested so no prompt appears.
 */
export async function denoReexec (options) {
  if (!isDeno) return null
  if (workerRefused(options)) return null
  if (environment(REEXEC_GUARD) !== null) return null
  const Deno = globalThis.Deno
  let granted
  try {
    granted = ['read', 'write', 'env', 'run', 'net', 'ffi', 'sys']
      .filter((name) => Deno.permissions.querySync({ name }).state === 'granted')
  } catch (_error) {
    return null
  }
  if (granted.indexOf('run') < 0 || granted.indexOf('read') < 0) return null
  const main = Deno.mainModule.startsWith('file://')
    ? fileUrlToPath(Deno.mainModule)
    : Deno.mainModule
  const args = [
    'run',
    ...granted.map((name) => `--allow-${name}`),
    `--v8-flags=--stack-size=${REEXEC_STACK_KB}`,
    main,
    ...Deno.args
  ]
  try {
    const child = new Deno.Command(Deno.execPath(), {
      args,
      env: { [REEXEC_GUARD]: '1' },
      stdin: 'inherit',
      stdout: 'inherit',
      stderr: 'inherit'
    }).outputSync()
    return child.code
  } catch (_error) {
    // No --allow-run at this exact path, or no executable. Pack here and
    // let the overflow advice speak if the stack runs out.
    return null
  }
}
