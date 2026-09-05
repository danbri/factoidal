// Differential test for the `factoidal` command against the native
// l4block-* tools. https://github.com/danbri/factoidal/issues/641
//
//   node tests/store-host/cli.mjs
//   deno run --allow-read --allow-write --allow-run --allow-env tests/store-host/cli.mjs
//
// The Node run also drives the Deno run when `deno` is on PATH, and says
// so plainly when it is not. Scores are printed as
// "N pass, M fail, S skipped (out of T)".
//
// WHAT IT GATES THAT NOTHING ELSE DOES
// `tools/wasm-store-query-smoke.sh` drives the three store operations
// through a purpose-written host and compares ROW COUNTS. This drives the
// shipped command, end to end, and compares the ROWS THEMSELVES: every
// binding of every row, against what `l4block-id-v3-query` and
// `l4block-quad-query` answer for the same query and the same generation.
// A routing fault that changes which rows come back, not how many, is
// only visible here (anti-pattern 34).
//
// The native binaries are read-only inputs; `l4block-shard-pack` writes
// its generations under a temporary directory.
//
// HOW ROWS ARE COMPARED
// The native tools print at most ten rows in `preview=`, as a Lean
// `repr`. Each row-content check therefore uses ORDER BY with a LIMIT of
// eight, so the preview holds every row the query answers and the order
// is defined by the query rather than by either engine's evaluation
// order. Row counts are compared without a limit as well.

import { fileUrlToPath, joinPath } from '../../npm/factoidal/store-host/paths.mjs'
import { listGeneration, readWhole } from '../../npm/factoidal/store-host/index.mjs'

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

// ------------------------------------------------------- runtime shims

const shim = isDeno
  ? {
      env: (name) => globalThis.Deno.env.get(name),
      exit: (code) => globalThis.Deno.exit(code),
      mkdirTemp: (prefix) => globalThis.Deno.makeTempDirSync({ prefix }),
      mkdir: (path) => globalThis.Deno.mkdirSync(path, { recursive: true }),
      removeTree: (path) => {
        try { globalThis.Deno.removeSync(path, { recursive: true }) } catch (_e) { /* already gone */ }
      },
      copyTree: function copyTree (from, to) {
        globalThis.Deno.mkdirSync(to, { recursive: true })
        for (const entry of globalThis.Deno.readDirSync(from)) {
          const source = joinPath(from, entry.name)
          const target = joinPath(to, entry.name)
          if (entry.isDirectory) copyTree(source, target)
          else globalThis.Deno.copyFileSync(source, target)
        }
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
      // How this runtime runs one of the repository's own .mjs files.
      selfCommand: () => globalThis.Deno.execPath(),
      selfArgs: (file, rest) =>
        ['run', '--allow-read', '--allow-write', '--allow-run', '--allow-env', file, ...rest],
      // The command needs only --allow-read for inspect and query. A
      // query that runs out of frames re-executes itself with a raised
      // V8 stack and needs --allow-run and --allow-env as well
      // (https://github.com/danbri/factoidal/issues/653); Deno's default
      // stack clears every query in this suite, so the read-only claim
      // still holds here and this is what keeps proving it.
      cliArgs: (file, rest) => ['run', '--allow-read', file, ...rest],
      // pack and activate WRITE: a generation directory, and CURRENT.
      // pack also RE-EXECUTES itself once with a raised V8 stack, which
      // is how Deno gets a call stack deep enough for an input above
      // about half a megabyte (https://github.com/danbri/factoidal/issues/649).
      // That needs --allow-run, and --allow-env for the guard variable
      // that stops the re-exec looping. Without them the command packs in
      // process and a large input overflows, which is the behaviour the
      // --no-worker check below gates on purpose.
      cliWriteArgs: (file, rest) =>
        ['run', '--allow-read', '--allow-write', '--allow-run', '--allow-env',
          file, ...rest],
      runtimeName: 'deno'
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
        removeTree: (path) => fs.rmSync(path, { recursive: true, force: true }),
        copyTree: (from, to) => fs.cpSync(from, to, { recursive: true }),
        exists: (path) => fs.existsSync(path),
        run: (command, args) => {
          const result = cp.spawnSync(command, args, { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 })
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
        selfArgs: (file, rest) => [file, ...rest],
        cliArgs: (file, rest) => [file, ...rest],
        cliWriteArgs: (file, rest) => [file, ...rest],
        runtimeName: 'node'
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
    console.log(`  ok   ${name}`)
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : String(error)}`)
    console.log(`  FAIL ${name}`)
  }
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

// ------------------------------------------------- canonical row shapes
// One rendering both sides are put into, so a comparison is a string
// comparison and a difference names the row and the binding.

const XSD_STRING = 'http://www.w3.org/2001/XMLSchema#string'

function literalText (lexical, datatype, language) {
  if (typeof language === 'string' && language.length > 0) {
    return `"${lexical}"@${language}`
  }
  if (typeof datatype !== 'string' || datatype.length === 0 || datatype === XSD_STRING) {
    return `"${lexical}"`
  }
  return `"${lexical}"^^<${datatype}>`
}

/** One SPARQL Query Results JSON term. */
function termOfSrj (term) {
  if (term.type === 'uri') return `<${term.value}>`
  if (term.type === 'bnode') return `_:${term.value}`
  if (term.type === 'literal') {
    return literalText(term.value, term.datatype, term['xml:lang'])
  }
  return JSON.stringify(term)
}

function rowText (pairs) {
  return pairs
    .slice()
    .sort((left, right) => (left[0] < right[0] ? -1 : left[0] > right[0] ? 1 : 0))
    .map(([name, text]) => `${name}=${text}`)
    .join(' | ')
}

function rowsOfSrj (srj) {
  return srj.results.bindings.map((binding) =>
    rowText(Object.keys(binding).map((name) => [name, termOfSrj(binding[name])])))
}

// -------------------------------------------- the native preview parser
// The native tools print `preview=` as a Lean `repr` of
// `List (List (String x Term))`. This reads that back; it interprets no
// storage format, only the tool's own printed output.

function parsePreview (text) {
  let index = 0
  const skipSpace = () => { while (index < text.length && /\s/.test(text[index])) index += 1 }
  const expect = (character) => {
    skipSpace()
    if (text[index] !== character) {
      throw new Error(`preview: expected "${character}" at ${index}: ${text.slice(index, index + 60)}`)
    }
    index += 1
  }
  const peek = () => { skipSpace(); return text[index] }
  const parseString = () => {
    skipSpace()
    if (text[index] !== '"') throw new Error(`preview: expected a string at ${index}`)
    index += 1
    let value = ''
    while (index < text.length && text[index] !== '"') {
      if (text[index] === '\\') {
        index += 1
        const escaped = text[index]
        value += escaped === 'n' ? '\n' : escaped === 't' ? '\t' : escaped === 'r' ? '\r' : escaped
        index += 1
      } else {
        value += text[index]
        index += 1
      }
    }
    index += 1
    return value
  }
  const parseName = () => {
    skipSpace()
    const start = index
    while (index < text.length && /[A-Za-z0-9_.]/.test(text[index])) index += 1
    return text.slice(start, index)
  }
  const parseTerm = () => {
    const constructor = parseName()
    if (constructor.endsWith('Term.iri')) return `<${parseString()}>`
    if (constructor.endsWith('Term.bnode')) return `_:${parseString()}`
    if (constructor.endsWith('Term.literal')) {
      expect('(')
      const lexical = parseString()
      expect(',')
      const datatype = parseString()
      expect(',')
      const tag = parseName()
      let language = null
      if (tag === 'some') language = parseString()
      else if (tag !== 'none') throw new Error(`preview: unknown language tag "${tag}"`)
      expect(')')
      return literalText(lexical, datatype, language)
    }
    throw new Error(`preview: unknown term constructor "${constructor}"`)
  }
  const parseRow = () => {
    expect('[')
    const pairs = []
    if (peek() === ']') { index += 1; return pairs }
    for (;;) {
      expect('(')
      const name = parseString()
      expect(',')
      pairs.push([name, parseTerm()])
      expect(')')
      if (peek() === ',') { index += 1; continue }
      expect(']')
      return pairs
    }
  }
  expect('[')
  const rows = []
  if (peek() === ']') return rows
  for (;;) {
    rows.push(rowText(parseRow()))
    if (peek() === ',') { index += 1; continue }
    expect(']')
    return rows
  }
}

// ------------------------------------------------------- the two engines

const testFile = fileUrlToPath(import.meta.url)
const repoRoot = fileUrlToPath(new URL('../..', import.meta.url).href).replace(/\/$/, '')
const cliFile = joinPath(repoRoot, 'npm/factoidal/bin/factoidal.mjs')

/** Where the committed native l4block-* binaries are. */
function nativeBinDirectory () {
  const override = shim.env('L4_BIN_DIR')
  if (typeof override === 'string' && override.length > 0) {
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

/** Run the shipped command with this runtime. */
function runCli (args) {
  const result = shim.run(shim.selfCommand(), shim.cliArgs(cliFile, args))
  return result
}

/** `factoidal pack` and `factoidal activate` write files, so the Deno
 *  child needs --allow-write as well. Every other command is read-only,
 *  and `runCli` keeps proving that. */
function runCliWrite (args) {
  return shim.run(shim.selfCommand(), shim.cliWriteArgs(cliFile, args))
}

/** `factoidal query --format json --quiet`, as canonical rows. */
function cliRows (root, query) {
  const result = runCli([
    'query', root, '--query', query, '--format', 'json', '--quiet'])
  assert(result.code === 0,
    `factoidal query exited ${result.code}: ${result.stderr.trim()}`)
  const srj = JSON.parse(result.stdout)
  return rowsOfSrj(srj)
}

/** The native tool's row count and its preview rows. */
function nativeRows (binDirectory, tool, root, query) {
  const result = shim.run(joinPath(binDirectory, tool), [root, '--query', query])
  assert(result.code === 0,
    `${tool} exited ${result.code}: ${result.stderr.trim()}`)
  const marker = result.stdout.lastIndexOf('preview=')
  assert(marker >= 0, `${tool} printed no preview: ${result.stdout.trim()}`)
  const countMatch = /rows=(\d+) preview=/.exec(result.stdout.slice(0, marker + 'preview='.length))
  assert(countMatch !== null, `${tool} printed no row count: ${result.stdout.trim()}`)
  return {
    count: Number(countMatch[1]),
    rows: parsePreview(result.stdout.slice(marker + 'preview='.length).trim())
  }
}

// ------------------------------------------------------------ fixtures

console.log(`factoidal command differential (${shim.runtimeName})`)

const binDirectory = nativeBinDirectory()
const workDirectory = shim.mkdirTemp('factoidal-cli-')

// The store the package carries. These checks need no native binary,
// because the point of the bundled store is that a fresh install with
// nothing else on the machine answers a query.

await check('sample-store prints a path that holds CURRENT', () => {
  const printed = runCli(['sample-store'])
  assert(printed.code === 0, `sample-store exited ${printed.code}: ${printed.stderr.trim()}`)
  const root = printed.stdout.trim()
  assert(root.length > 0, 'sample-store printed nothing')
  assert(shim.exists(joinPath(root, 'CURRENT')),
    `there is no CURRENT under ${root}`)
})

await check('sample-store --json names the licence of what it carries', () => {
  const printed = runCli(['sample-store', '--json'])
  assert(printed.code === 0, `sample-store --json exited ${printed.code}`)
  const facts = JSON.parse(printed.stdout)
  assert(facts.triples === 4434, `the facts claim ${facts.triples} triples, expected 4434`)
  assert(facts.blocks === 13, `the facts claim ${facts.blocks} blocks, expected 13`)
  assert(facts.licence === 'CC BY 4.0', `the facts claim the licence "${facts.licence}"`)
})

await check('inspect reads the bundled store and agrees with its own facts', () => {
  const root = runCli(['sample-store']).stdout.trim()
  const facts = JSON.parse(runCli(['sample-store', '--json']).stdout)
  const inspected = runCli(['inspect', root, '--json'])
  assert(inspected.code === 0, `inspect exited ${inspected.code}: ${inspected.stderr.trim()}`)
  const envelope = JSON.parse(inspected.stdout)
  assert(envelope.entries.length === facts.blocks,
    `the manifest holds ${envelope.entries.length} entries, the facts claim ${facts.blocks}`)
  assert(envelope.totalRows === facts.triples,
    `the manifest commits ${envelope.totalRows} rows, the facts claim ${facts.triples}`)
  assert(envelope.layout === facts.layout,
    `the manifest layout is ${envelope.layout}, the facts claim ${facts.layout}`)
})

await check('the bundled store answers a COUNT with no native binary', () => {
  const root = runCli(['sample-store']).stdout.trim()
  const result = runCli(['query', root, '--query',
    'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }', '--format', 'json', '--quiet'])
  assert(result.code === 0, `query exited ${result.code}: ${result.stderr.trim()}`)
  const srj = JSON.parse(result.stdout)
  assert(srj.results.bindings.length === 1, 'COUNT answered no row')
  assert(srj.results.bindings[0].n.value === '4434',
    `COUNT answered ${srj.results.bindings[0].n.value}, expected 4434`)
})

// A generation the command packed must also be one the command can
// ACTIVATE. Verification decodes the same blocks the pack encoded, so it
// recurses as deep; before 2026-09-04 the worker stack was given to pack
// alone and a 112,742-row generation packed and then failed to activate,
// leaving a store that could be built and not opened
// (https://github.com/danbri/factoidal/issues/649).
await check('a generation the command packed is one the command can activate', () => {
  const source = joinPath(repoRoot,
    'examples/wikidata/subsets/lifesci-kgx/data/anatomical_structure.ttl')
  if (!shim.exists(source)) {
    skipped += 1
    console.log('  skip pack-then-activate - the fixture is absent')
    return
  }
  const root = joinPath(workDirectory, 'packed-then-activated')
  shim.mkdir(joinPath(root, 'gen-1'))
  const packed = runCliWrite(['pack', source, joinPath(root, 'gen-1'), '--layout', 'ibk3', '--quiet'])
  assert(packed.code === 0, `pack exited ${packed.code}: ${packed.stderr.trim()}`)
  const activated = runCliWrite(['activate', root, 'gen-1'])
  assert(activated.code === 0,
    `activate exited ${activated.code}: ${activated.stderr.trim()}`)
  assert(activated.stdout.indexOf('artifacts verified') >= 0,
    `activate printed:\n${activated.stdout}`)
  assert(shim.exists(joinPath(root, 'CURRENT')),
    'activate did not write CURRENT')
  const inspected = runCli(['inspect', root, '--json'])
  assert(inspected.code === 0, `inspect exited ${inspected.code}`)
  const envelope = JSON.parse(inspected.stdout)
  assert(envelope.totalRows === 112742,
    `the activated generation commits ${envelope.totalRows} rows, expected 112742`)
})

await check('the bundled store answers the join the README prints', () => {
  const root = runCli(['sample-store']).stdout.trim()
  const result = runCli(['query', root, '--query',
    'SELECT ?c ?l WHERE { ' +
    '?c <http://www.w3.org/2004/02/skos/core#inScheme> ' +
    '   <http://cv.iptc.org/newscodes/videocodec/> ; ' +
    '   <http://www.w3.org/2004/02/skos/core#prefLabel> ?l . ' +
    'FILTER(langMatches(lang(?l), "en")) } ORDER BY ?c ?l LIMIT 4',
    '--format', 'json', '--quiet'])
  assert(result.code === 0, `query exited ${result.code}: ${result.stderr.trim()}`)
  const rows = JSON.parse(result.stdout).results.bindings
  assert(rows.length === 4, `the join answered ${rows.length} rows, expected 4`)
  assert(rows[0].c.value === 'http://cv.iptc.org/newscodes/videocodec/c001',
    `the first concept is ${rows[0].c.value}`)
  assert(rows[0].l.value === 'Analogue Black and White',
    `the first label is "${rows[0].l.value}"`)
})

if (binDirectory === null) {
  skipped += 1
  console.log('  skip every check - no l4block-shard-pack found; build formal/lean4 or set L4_BIN_DIR')
} else {
  const pack = (source, name, layout) => {
    const generation = joinPath(workDirectory, `${name}-gen`)
    const packed = shim.run(joinPath(binDirectory, 'l4block-shard-pack'),
      [joinPath(repoRoot, source), generation, layout])
    assert(packed.code === 0, `l4block-shard-pack ${source}: ${packed.stderr.trim()}`)
    const root = joinPath(workDirectory, name)
    shim.mkdir(root)
    shim.copyTree(generation, joinPath(root, 'gen-1'))
    const activated = shim.run(joinPath(binDirectory, 'l4block-shard-activate'), [root, 'gen-1'])
    assert(activated.code === 0, `l4block-shard-activate ${name}: ${activated.stderr.trim()}`)
    return root
  }

  const triples = pack('examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl',
    'store-ibk3', 'ibk3')
  const quads = pack('tests/local/data/quad_sample.trig', 'store-ibk4', 'ibk4')

  // The first two predicates of the IBK3 manifest, read from the packer's
  // own manifest.tsv, so the bound-predicate queries name predicates the
  // data really has.
  const manifestTsv = new TextDecoder().decode(
    readWhole(joinPath(triples, 'gen-1/manifest.tsv'))).split('\n')
  const predicateOf = (ordinal) => {
    for (const line of manifestTsv.slice(1)) {
      const fields = line.split('\t')
      if (fields[0] === String(ordinal)) return fields[1]
    }
    throw new Error(`manifest.tsv has no entry ${ordinal}`)
  }
  const predicate = predicateOf(0)
  const other = predicateOf(1)
  console.log(`  IBK3 predicates 0 and 1: ${predicate} | ${other}`)

  /**
   * One query, answered by the command and by the native tool.
   * The row COUNT must agree, and when the native tool printed every row
   * (its preview holds at most ten) the rows themselves must agree, in
   * order.
   */
  const compare = (label, tool, root, query) =>
    check(label, () => {
      const native = nativeRows(binDirectory, tool, root, query)
      const command = cliRows(root, query)
      assert(command.length === native.count,
        `the command answered ${command.length} rows, ${tool} answered ${native.count}`)
      if (native.count <= 10) {
        assert(native.rows.length === native.count,
          `${tool} previewed ${native.rows.length} of ${native.count} rows`)
        for (let index = 0; index < native.rows.length; index += 1) {
          assert(command[index] === native.rows[index],
            `row ${index} differs\n    command: ${command[index]}\n    ${tool}: ${native.rows[index]}`)
        }
      }
    })

  await compare('IBK3 COUNT over the whole generation', 'l4block-id-v3-query', triples,
    'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }')

  await compare('IBK3 bound predicate', 'l4block-id-v3-query', triples,
    `SELECT ?s ?o WHERE { ?s <${predicate}> ?o } ORDER BY ?s ?o LIMIT 8`)

  // No constant predicate, so the plan opens every entry of the manifest.
  // The subject is bound, which keeps the answer inside the ten rows the
  // native preview prints. The unlimited count of the same shape is the
  // COUNT check above.
  await compare('IBK3 unbound predicate opens the whole manifest', 'l4block-id-v3-query', triples,
    'SELECT ?p ?o WHERE { <http://www.wikidata.org/entity/Q423990> ?p ?o } ORDER BY ?p ?o')

  await compare('IBK3 unbound predicate, every row counted', 'l4block-id-v3-query', triples,
    'SELECT * WHERE { ?s ?p ?o }')

  // A recursion-depth characteristic of the wasm build, not of the store:
  // some evaluator paths recurse once per row, and 6455 rows through an
  // explicit projection exceed Node's default WebAssembly frame budget
  // while Deno's clears it (measured 2026-09-03). Since
  // https://github.com/danbri/factoidal/issues/653 the command must ANSWER
  // it with NO runtime flag: it retries on a worker thread with a raised
  // stack under Node, and re-executes itself with a raised V8 stack under
  // Deno. Exiting 1 with advice is what it did before, and is now a
  // regression, so this check no longer accepts it.
  await check('a projection too deep for the default stack is answered with no flag', () => {
    const result = runCli(['query', triples, '--query',
      'SELECT ?s ?p ?o WHERE { ?s ?p ?o }', '--format', 'json', '--quiet'])
    assert(result.code === 0,
      `the command exited ${result.code}: ${result.stderr.trim()}`)
    const srj = JSON.parse(result.stdout)
    assert(srj.results.bindings.length === 6455,
      `the runtime answered ${srj.results.bindings.length} rows, expected 6455`)
  })

  // The same query with --no-worker must answer THE SAME ROWS, not the
  // same count (anti-pattern 34). Either it overflows and explains
  // itself, which is the old behaviour the escape hatch keeps reachable,
  // or it answers, and then every row must match the worker's.
  await check('the worker and --no-worker answer the same rows', () => {
    const query = `SELECT ?s ?o WHERE { ?s <${predicate}> ?o } ORDER BY ?s ?o`
    const onWorker = runCli(['query', triples, '--query', query,
      '--format', 'json', '--quiet'])
    assert(onWorker.code === 0,
      `the command exited ${onWorker.code}: ${onWorker.stderr.trim()}`)
    const inProcess = runCli(['query', triples, '--query', query,
      '--format', 'json', '--quiet', '--no-worker'])
    if (inProcess.code !== 0) {
      assert(inProcess.stderr.indexOf('call stack') >= 0,
        `--no-worker failed for another reason:\n${inProcess.stderr}`)
      console.log('  note: --no-worker ran out of frames on this query, as designed')
      return
    }
    const left = rowsOfSrj(JSON.parse(onWorker.stdout))
    const right = rowsOfSrj(JSON.parse(inProcess.stdout))
    assert(left.length === right.length,
      `the worker answered ${left.length} rows, --no-worker answered ${right.length}`)
    assert(left.length > 0, 'the query answered no row, so nothing was compared')
    for (let index = 0; index < left.length; index += 1) {
      assert(left[index] === right[index],
        `row ${index} differs\n    worker:     ${left[index]}\n    no-worker:  ${right[index]}`)
    }
  })

  // Only the reference semantics decide this one, and it must be decided
  // against the same generation the backend answers from (anti-pattern 34).
  await compare('IBK3 FILTER NOT EXISTS over two predicates', 'l4block-id-v3-query', triples,
    `SELECT ?s WHERE { ?s <${predicate}> ?o FILTER NOT EXISTS { ?s <${other}> ?x } } ORDER BY ?s LIMIT 8`)

  await compare('IBK3 OPTIONAL', 'l4block-id-v3-query', triples,
    `SELECT ?s ?o ?x WHERE { ?s <${predicate}> ?o OPTIONAL { ?s <${other}> ?x } } ORDER BY ?s ?o ?x LIMIT 8`)

  await compare('IBK4 two graphs through GRAPH ?g', 'l4block-quad-query', quads,
    'SELECT ?g ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } } ORDER BY ?g ?s ?o')

  await compare('IBK4 default graph', 'l4block-quad-query', quads,
    'SELECT ?s ?p ?o WHERE { ?s ?p ?o } ORDER BY ?s ?p ?o')

  // The command's own surface: the plan it prints must be the plan the
  // native tool opened with, and a damaged artifact must be refused.
  await check('--explain names the same open mode the native tool prints', () => {
    const explained = runCli(['query', triples, '--query',
      `SELECT ?s WHERE { ?s <${predicate}> ?o }`, '--explain'])
    assert(explained.code === 0, `--explain exited ${explained.code}: ${explained.stderr.trim()}`)
    assert(explained.stdout.indexOf('mode ibk3-paged-merkle(1)') >= 0,
      `--explain printed:\n${explained.stdout}`)
    const native = shim.run(joinPath(binDirectory, 'l4block-id-v3-query'),
      [triples, '--query', `SELECT ?s WHERE { ?s <${predicate}> ?o }`])
    assert(native.stdout.indexOf('open-mode=ibk3-paged-merkle(1)') >= 0,
      `the native tool printed:\n${native.stdout}`)
  })

  await check('inspect decodes the manifest the packer wrote', () => {
    const inspected = runCli(['inspect', triples, '--json'])
    assert(inspected.code === 0, `inspect exited ${inspected.code}: ${inspected.stderr.trim()}`)
    const envelope = JSON.parse(inspected.stdout)
    assert(envelope.ok === true, 'inspect did not print an ok envelope')
    assert(envelope.rangeCommitted === true, 'the manifest reports no Merkle commitment')
    const predicates = envelope.entries.map((entry) => entry.predicate)
    assert(predicates.indexOf(predicate) >= 0,
      `inspect listed ${predicates.length} predicates without ${predicate}`)
    let rows = 0
    for (const entry of envelope.entries) rows += entry.rows
    assert(rows === envelope.totalRows,
      `the entries hold ${rows} rows, the envelope reports ${envelope.totalRows}`)
  })

  await check('a damaged artifact is refused and the key is named', async () => {
    const damaged = joinPath(workDirectory, 'store-damaged')
    shim.copyTree(triples, damaged)
    const artifact = joinPath(damaged, 'gen-1/predicate-0.ibk3')
    const bytes = readWhole(artifact)
    bytes[Math.floor(bytes.length / 2)] ^= 0xff
    if (isDeno) globalThis.Deno.writeFileSync(artifact, bytes)
    else (await import('node:fs')).writeFileSync(artifact, bytes)
    const result = runCli(['query', damaged, '--query',
      `SELECT ?s WHERE { ?s <${predicate}> ?o }`])
    assert(result.code === 1, `the command exited ${result.code}, expected 1`)
    assert(result.stderr.indexOf('predicate-0.ibk3') >= 0,
      `the refusal did not name the artifact:\n${result.stderr}`)
    assert(result.stderr.indexOf('SHA-256') >= 0,
      `the refusal did not name the digest:\n${result.stderr}`)
  })

  await check('a query over the row cap is refused before any artifact is read', () => {
    const big = pack('examples/wikidata/subsets/lifesci-kgx/data/anatomical_structure.ttl',
      'store-over-cap', 'ibk3')
    const result = runCli(['query', big, '--query', 'SELECT * WHERE { ?s ?p ?o }'])
    assert(result.code === 1, `the command exited ${result.code}, expected 1`)
    assert(/the cap is \d+/.test(result.stderr),
      `the refusal did not name a cap:\n${result.stderr}`)
    assert(result.stderr.indexOf('Narrow the query') >= 0,
      `the refusal suggested no next step:\n${result.stderr}`)
  })

  // ------------------------------------------------------- the pack path
  //
  // `factoidal pack` builds a generation inside the WebAssembly module and
  // writes what the module hands back. The gate is byte identity with
  // `l4block-shard-pack` over the same input: the two run the same pure
  // packer (L4Factoidal/Storage/PackStream.lean) and differ only in which
  // SHA-256 implementation hashes the leaves, which must not change a
  // committed byte. An engine built before the pack operations skips this
  // section by name rather than reporting a pass it did not measure.

  const packFixture = joinPath(repoRoot,
    'formal/lean4/Harness/TestData/heterogeneous-fixture.ttl')
  const packedByCommand = joinPath(workDirectory, 'pack-command-gen')
  const packProbe = runCliWrite(['pack', packFixture, packedByCommand,
    '--layout', 'ibk3', '--quiet'])
  // ONLY the "not yet wired" refusal is a skip. Any other failure is a
  // failure: a skip on every non-zero exit would report a broken pack as
  // an absent one.
  const packUnwired = packProbe.code !== 0 &&
    packProbe.stderr.indexOf('built before the streaming pack') >= 0

  if (packUnwired) {
    skipped += 3
    console.log('  skip the pack path - this engine carries no pack operations')
  } else {
    // The two generations must agree byte for byte. Named here once
    // because four checks need it.
    const assertSameBytes = (fromWasm, fromNative) => {
      const namesOf = (directory) =>
        listGeneration(directory).map((file) => file.name).sort()
      const wasmNames = namesOf(fromWasm)
      const nativeNames = namesOf(fromNative)
      assert(wasmNames.join(',') === nativeNames.join(','),
        `the two packers wrote different file sets:\n  command: ${wasmNames.join(', ')}\n  native:  ${nativeNames.join(', ')}`)
      assert(wasmNames.length > 0, 'the packers wrote nothing')
      for (const name of wasmNames) {
        const a = readWhole(joinPath(fromWasm, name))
        const b = readWhole(joinPath(fromNative, name))
        assert(a.length === b.length,
          `${name} is ${a.length} bytes from the command and ${b.length} from the native packer`)
        for (let index = 0; index < a.length; index += 1) {
          assert(a[index] === b[index], `${name} differs at byte ${index}`)
        }
      }
    }

    await check('pack exits 0', () => {
      assert(packProbe.code === 0,
        `factoidal pack exited ${packProbe.code}: ${packProbe.stderr.trim()}`)
    })
    await check('pack writes what the native packer writes, byte for byte', () => {
      const packedNatively = joinPath(workDirectory, 'pack-native-gen')
      const native = shim.run(joinPath(binDirectory, 'l4block-shard-pack'),
        [packFixture, packedNatively, 'ibk3'])
      assert(native.code === 0, `l4block-shard-pack: ${native.stderr.trim()}`)
      assertSameBytes(packedByCommand, packedNatively)
    })

    // ------------------------------- above the default frame budget
    //
    // https://github.com/danbri/factoidal/issues/649. On the DEFAULT
    // stack of Node and of Deno the pack of anything above roughly
    // 0.5 MB of Turtle ended with "Maximum call stack size exceeded".
    // `anatomical_structure.ttl` is 3,811,378 bytes, which failed on
    // both runtimes before the worker route landed, and is small
    // enough to pack in seconds. These three checks are what stops
    // that defect coming back.

    const bigSource = joinPath(repoRoot,
      'examples/wikidata/subsets/lifesci-kgx/data/anatomical_structure.ttl')

    const packBig = (layout, name) => {
      const byCommand = joinPath(workDirectory, `${name}-command-gen`)
      const byNative = joinPath(workDirectory, `${name}-native-gen`)
      const command = runCliWrite(['pack', bigSource, byCommand,
        '--layout', layout, '--quiet'])
      assert(command.code === 0,
        `factoidal pack --layout ${layout} exited ${command.code}: ${command.stderr.trim()}`)
      const native = shim.run(joinPath(binDirectory, 'l4block-shard-pack'),
        [bigSource, byNative, layout])
      assert(native.code === 0, `l4block-shard-pack ${layout}: ${native.stderr.trim()}`)
      assertSameBytes(byCommand, byNative)
    }

    await check('pack builds an IBK3 generation from 3.8 MB, byte for byte',
      () => { packBig('ibk3', 'big-ibk3') })

    await check('pack builds an IBK4 generation from 3.8 MB, byte for byte',
      () => { packBig('ibk4', 'big-ibk4') })

    // The escape hatch keeps the old behaviour reachable, and the old
    // behaviour must still explain itself rather than crash.
    await check('--no-worker still reports the frame budget instead of crashing', () => {
      const refused = runCliWrite(['pack', bigSource,
        joinPath(workDirectory, 'big-no-worker-gen'), '--layout', 'ibk3',
        '--quiet', '--no-worker'])
      if (refused.code === 0) {
        console.log('  note: this runtime packs 3.8 MB in process, so no advice was needed')
        return
      }
      assert(refused.code === 1, `the command exited ${refused.code}, expected 0 or 1`)
      assert(refused.stderr.indexOf('call stack') >= 0,
        `the failure was not the runtime's frame budget:\n${refused.stderr}`)
      assert(refused.stderr.indexOf('--stack-size') >= 0,
        `the failure suggested no next step:\n${refused.stderr}`)
    })

    await check('a packed generation activates and answers its own row count', () => {
      const root = joinPath(workDirectory, 'pack-store')
      shim.mkdir(root)
      shim.copyTree(packedByCommand, joinPath(root, 'gen-1'))
      const activated = runCliWrite(['activate', root, 'gen-1'])
      assert(activated.code === 0,
        `factoidal activate exited ${activated.code}: ${activated.stderr.trim()}`)
      const result = runCli(['query', root, '--query',
        'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }', '--format', 'json', '--quiet'])
      assert(result.code === 0, `query exited ${result.code}: ${result.stderr.trim()}`)
      const rows = JSON.parse(result.stdout).results.bindings
      assert(rows.length === 1, 'COUNT answered no row')
      assert(rows[0].n.value === '44',
        `COUNT answered ${rows[0].n.value}, the fixture holds 44 triples`)
    })
  }
}

// ------------------------------------------------------------ reporting

shim.removeTree(workDirectory)

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`${shim.runtimeName}: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)

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
