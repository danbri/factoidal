#!/usr/bin/env node
// The `factoidal` command: pack, activate, query, update and compact a
// persisted Shardborough store from Node or Deno, with no native binary.
// https://github.com/danbri/factoidal/issues/641
//
// STATE TODAY. The argument surface below is complete and settled, so that
// wiring the remaining subcommands changes no user-visible syntax.
// `version`, `inspect` and `query` run: the first needs only host file
// I/O, and the other two drive the three WebAssembly store operations of
// `formal/lean4/Wasm/Ops/Store.lean`. `pack`, `activate`, `update` and
// `compact` parse their arguments, report what they would do, and exit 3;
// they need operations that do not exist yet.
//
// This file reads files by name, moves bytes and renders what the engine
// answered. It parses no manifest, verifies no digest, decodes no block
// and chooses no artifact -- every one of those is a format decision and
// it lives in the Lean source (iron rule 7). The table renderer is a
// human display of the engine's own SPARQL Query Results JSON, not a
// second serializer: `--format json`, `--format nquads` and
// `--format turtle` all print documents the engine produced.

import {
  StoreHostError, atomicReplace, listGeneration, makeDirectory, readWhole,
  runtime
} from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'
import { loadEngine } from './engine.mjs'
import { sampleStoreFacts, sampleStorePath } from '../sample-store.mjs'
import { PackError, packSupported, verifyGeneration } from './pack.mjs'
import { denoReexec, isStackOverflow, runPack } from './pack-host.mjs'
import {
  STACK_REMEDY, StoreOperationError, inspectManifest, openStore, planQuery,
  queryStore, stackLimitAdvice, turtleOfNQuads
} from './store.mjs'

const EXIT_OK = 0
const EXIT_FAILURE = 1
const EXIT_USAGE = 2
const EXIT_NOT_WIRED = 3

// Progress is reported about every 16 MiB; the packer feeds 65,536 bytes
// a time, so this is the window that catches one feed per report.
const FEED_PROGRESS = 65536

const PACK_LAYOUTS = ['ibk3', 'ibk4']
const PACK_SYNTAXES = ['turtle', 'trig', 'nquads', 'ntriples']
const PACK_SUFFIXES = [
  ['.ttl', 'turtle'], ['.turtle', 'turtle'],
  ['.trig', 'trig'],
  ['.nq', 'nquads'], ['.nquads', 'nquads'],
  ['.nt', 'ntriples'], ['.ntriples', 'ntriples']
]

// Suffixes the engine parses elsewhere but the packer's streaming fold does
// not read. Naming them is better than "cannot tell the syntax from its
// name", which sends the reader looking for a --syntax value that does not
// exist.
const PACK_UNSUPPORTED_SUFFIXES = [
  ['.rdf', 'RDF/XML'], ['.owl', 'RDF/XML'], ['.xml', 'RDF/XML'],
  ['.jsonld', 'JSON-LD'], ['.json', 'JSON-LD'], ['.n3', 'Notation3'],
  ['.csv', 'CSV'], ['.tsv', 'TSV'], ['.hdt', 'HDT']
]

/** The parent of a path, and its last component. The `activate` hint
 *  printed after a pack needs both; neither is a format decision. */
function dirOf (path) {
  const cut = path.replace(/[/\\]+$/, '').lastIndexOf('/')
  return cut <= 0 ? '.' : path.slice(0, cut)
}
function nameOf (path) {
  const trimmed = path.replace(/[/\\]+$/, '')
  const cut = trimmed.lastIndexOf('/')
  return cut < 0 ? trimmed : trimmed.slice(cut + 1)
}

const ISSUE = 'https://github.com/danbri/factoidal/issues/641'

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

// Node writes to a PIPE asynchronously, and `process.exit()` drops
// whatever is still buffered. A SELECT that prints a few megabytes of
// SPARQL Query Results JSON into `| jq` therefore arrived truncated at
// the 64 KiB pipe boundary (measured 2026-09-03, 6455 rows). Setting the
// exit code and letting the process end on its own flushes it.
function exit (code) {
  if (isDeno) globalThis.Deno.exit(code)
  else process.exitCode = code
}

function out (line) { console.log(line) }
function err (line) { console.error(line) }

// ---------------------------------------------------------------- usage

const USAGE = `factoidal - the Factoidal persisted store, from Node or Deno

usage: factoidal <command> [options]

commands:
  version                     print the package and engine versions
  sample-store                print the path of the bundled sample store
  inspect  STORE              report what the activated manifest commits
  query    STORE [QUERY]      evaluate a SPARQL query against a store
  pack     INPUT OUTPUT       build one immutable generation from an RDF file
  activate STORE GENERATION   make one generation the activated generation
  update   STORE [UPDATE]     apply a SPARQL Update through the delta log
  compact  STORE GENERATION   fold the delta log into a new generation

global options:
  -h, --help                  print this text, or a command's own help
      --json                  machine-readable output where a command has it
      --quiet                 print results only, no progress lines

exit codes:
  0 success   1 failure   2 usage error   3 not yet wired (${ISSUE})

STORE is a collection root: the directory that holds CURRENT. This package
carries one, so the first query needs no other download:

  factoidal query "$(factoidal sample-store)" 'SELECT * WHERE { ?s ?p ?o } LIMIT 5'`

const COMMAND_USAGE = {
  version: `factoidal version - print the package and engine versions

usage: factoidal version [--json]

Prints the npm package version, the Lean engine's WebAssembly digest as
recorded by its build, and which host-I/O implementation is loaded.`,

  'sample-store': `factoidal sample-store - print the bundled store's path

usage: factoidal sample-store [--json]

Prints the collection root of the Shardborough store this package
carries, so a fresh install can query something at once:

  factoidal inspect "$(factoidal sample-store)"
  factoidal query "$(factoidal sample-store)" \\
    'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'

The store holds five IPTC NewsCodes vocabularies (CC BY 4.0; see NOTICE)
packed into IBK3 predicate blocks. --json adds what was recorded when it
was packed.`,

  inspect: `factoidal inspect - report what a store's manifest commits

usage: factoidal inspect STORE [--json] [--generation NAME]

Reads CURRENT, hands the manifest bytes to the engine's
storeManifestInspect operation, and prints what it decoded: the wire
version, the layout, the blank-node publication profile, the term-registry
version, whether the manifest carries a fixed-chunk Merkle commitment, and
one row per entry with its predicate, row count, byte length, block kind
and graph set.

options:
  --generation NAME  inspect this generation instead of the activated one
  --json             print the operation's envelope unchanged`,

  query: `factoidal query - evaluate a SPARQL query against a store

usage: factoidal query STORE [QUERY] [options]

QUERY is the query text. Give it as the second argument, or with --query,
or in a file with --file.

The command reads CURRENT and the manifest, asks the engine which
artifacts the query needs, reads exactly those, and hands their bytes to
the engine's storeQuery operation. The engine verifies every artifact
against the SHA-256 the manifest commits before it answers.

options:
  --query TEXT       the query text
  --file PATH        read the query text from a file
  --format FORMAT    table (default), json, nquads, turtle
  --limit N          print at most N table rows; the total is always named
  --explain          print the artifact plan instead of the results
  --generation NAME  query this generation instead of the activated one
  --json             shorthand for --format json
  --quiet            print the result only, no plan line on stderr

formats:
  table    a human display of the engine's SPARQL Query Results JSON;
           ASK prints true or false, CONSTRUCT prints its N-Triples
  json     SELECT prints the engine's SPARQL 1.1 Query Results JSON
           document; ASK and CONSTRUCT print the operation's envelope,
           because the operation answers those two with a boolean and a
           serialized graph rather than with a results document
  nquads   CONSTRUCT only: the graph the engine serialized
  turtle   CONSTRUCT only: that graph through the engine's own Turtle
           writer, which flattens named graphs into the default graph

not available, and why:
  --base IRI         the store query operation takes no base argument;
                     put a BASE clause in the query text instead
  xml, csv, tsv      the engine has no operation that writes the SPARQL
                     Results XML, CSV or TSV documents, and writing one
                     here would be a second serializer (iron rule 7)
  DESCRIBE           the engine answers "DESCRIBE is not supported by the
                     npm entry yet"

A store carrying a non-empty delta log is not served by this path: the
operation reads the manifest's committed artifacts only. Use the native
l4block-* tools for a store with uncompacted updates.`,

  pack: `factoidal pack - build one immutable generation from an RDF file

usage: factoidal pack INPUT OUTPUT [options]

INPUT is an RDF file. OUTPUT is the generation directory to create; it is
normally STORE/gen-N. Packing does not activate: run activate next.

options:
  --layout LAYOUT    ibk3 (triples, default) or ibk4 (quads)
  --syntax SYNTAX    turtle, trig or nquads; default from the file extension
  --chunk-bytes N    Merkle chunk size; default is the engine's
  --json             emit one JSON object
  --no-worker        pack in this process instead of on a worker thread

The pack fold recurses deeper than either runtime's default call stack
allows, so it runs on a worker thread with a raised stack under Node, and
under Deno the command re-executes itself once with a raised V8 stack
(https://github.com/danbri/factoidal/issues/649). --no-worker turns both
off; a pack above about half a megabyte of input then overflows.`,

  activate: `factoidal activate - make one generation the activated generation

usage: factoidal activate STORE GENERATION [--json]

Verifies every artifact of GENERATION and every cross-artifact relation,
then atomically replaces STORE/CURRENT. A generation that fails
verification never becomes current.`,

  update: `factoidal update - apply a SPARQL Update through the delta log

usage: factoidal update STORE [UPDATE] [options]

UPDATE is the update text. Give it as the second argument, or with
--update, or in a file with --file. The batch is appended to the
activated generation's delta log and is visible to the next query.

options:
  --update TEXT      the update text
  --file PATH        read the update text from a file
  --json             emit one JSON object`,

  compact: `factoidal compact - fold the delta log into a new generation

usage: factoidal compact STORE GENERATION [options]

Reads the activated generation and its committed delta batches, writes
GENERATION as a new immutable generation under STORE, and records its
compacted epoch. It does not activate unless --activate is given.

options:
  --activate         activate the new generation when it verifies
  --json             emit one JSON object`
}

// ------------------------------------------------------------- arguments

/**
 * Split argv into positional arguments and options. `--name value` and
 * `--name=value` both work; a flag with no value is `true`.
 */
function parseArguments (args, valueOptions) {
  const positional = []
  const options = Object.create(null)
  for (let index = 0; index < args.length; index += 1) {
    const argument = args[index]
    if (argument === '--') {
      positional.push(...args.slice(index + 1))
      break
    }
    if (argument === '-h') {
      options.help = true
      continue
    }
    if (!argument.startsWith('--')) {
      positional.push(argument)
      continue
    }
    const equals = argument.indexOf('=')
    const name = equals < 0 ? argument.slice(2) : argument.slice(2, equals)
    if (equals >= 0) {
      options[name] = argument.slice(equals + 1)
      continue
    }
    if (valueOptions.has(name)) {
      index += 1
      if (index >= args.length) {
        throw new UsageError(`option --${name} needs a value`)
      }
      options[name] = args[index]
      continue
    }
    options[name] = true
  }
  return { positional, options }
}

class UsageError extends Error {}

const VALUE_OPTIONS = {
  version: new Set([]),
  'sample-store': new Set([]),
  inspect: new Set(['generation']),
  query: new Set(['query', 'file', 'format', 'limit', 'base', 'generation']),
  pack: new Set(['layout', 'syntax', 'chunk-bytes', 'base']),
  activate: new Set([]),
  update: new Set(['update', 'file']),
  compact: new Set([])
}

// ------------------------------------------------------------- commands

function packageDirectory () {
  return fileUrlToPath(new URL('..', import.meta.url).href)
}

function readJsonFile (path) {
  const bytes = readWhole(path)
  return JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes))
}

function commandVersion (options) {
  const root = packageDirectory()
  const own = readJsonFile(joinPath(root, 'package.json'))
  let engine = null
  try {
    engine = readJsonFile(joinPath(root, 'l4-assets/version.json'))
  } catch (_error) {
    engine = null
  }
  const report = {
    package: own.name,
    version: own.version,
    host: runtime,
    engine: engine === null
      ? null
      : {
          engine: engine.engine,
          version: engine.version,
          gitSha: engine.gitSha,
          leanToolchain: engine.leanToolchain,
          wasmSha256: engine.wasmSha256,
          wasmBytes: engine.wasmBytes
        }
  }
  if (options.json) {
    out(JSON.stringify(report, null, 2))
    return EXIT_OK
  }
  out(`${report.package} ${report.version}`)
  out(`host-io ${report.host}`)
  if (report.engine !== null) {
    out(`engine ${report.engine.engine} ${report.engine.version} (${report.engine.leanToolchain})`)
    out(`wasm sha256 ${report.engine.wasmSha256} (${report.engine.wasmBytes} bytes)`)
  } else {
    out('engine (no l4-assets/version.json in this install)')
  }
  return EXIT_OK
}

function commandSampleStore (options) {
  const path = sampleStorePath()
  if (options.json === true) {
    out(JSON.stringify({ path, ...sampleStoreFacts }, null, 2))
    return EXIT_OK
  }
  out(path)
  return EXIT_OK
}

// ------------------------------------------------------------ rendering

/**
 * One graph name as the manifest reports it. `{"kind":"default"}` is the
 * default graph; the operation marks it that way so a host never has to
 * recognise a reserved IRI.
 */
function graphLabel (graph) {
  if (graph.kind === 'default') return 'default'
  if (graph.kind === 'iri') return `<${graph.value}>`
  if (graph.kind === 'bnode') return `_:${graph.value}`
  return JSON.stringify(graph)
}

/**
 * One SPARQL Query Results JSON term as a table cell. This is a display,
 * not a serialization: `--format json` prints the engine's own document
 * and `--format nquads` prints the engine's own N-Triples.
 */
function cellOfTerm (term) {
  if (term === undefined || term === null) return ''
  if (term.type === 'uri') return `<${term.value}>`
  if (term.type === 'bnode') return `_:${term.value}`
  if (term.type === 'literal') {
    const lang = term['xml:lang']
    if (typeof lang === 'string' && lang.length > 0) return `"${term.value}"@${lang}`
    if (typeof term.datatype === 'string') return `"${term.value}"^^<${term.datatype}>`
    return `"${term.value}"`
  }
  return JSON.stringify(term)
}

function plural (count, noun) {
  return `${count} ${noun}${count === 1 ? '' : 's'}`
}

/** Print rows as columns padded to their widest cell. */
function printTable (headers, rows) {
  const widths = headers.map((header) => header.length)
  for (const row of rows) {
    for (let index = 0; index < row.length; index += 1) {
      if (row[index].length > widths[index]) widths[index] = row[index].length
    }
  }
  const line = (cells) => cells
    .map((cell, index) => index === cells.length - 1 ? cell : cell.padEnd(widths[index]))
    .join('  ')
  out(line(headers))
  for (const row of rows) out(line(row))
}

// ------------------------------------------------------------- inspect

async function commandInspect (positional, options) {
  if (positional.length !== 1) throw new UsageError('inspect needs exactly one STORE')
  const root = positional[0]
  const named = typeof options.generation === 'string' ? options.generation : null
  const store = openStore(root, named)
  const engine = await loadEngine()
  const envelope = inspectManifest(engine, store)

  if (options.json) {
    // The operation's envelope, unchanged.
    out(JSON.stringify(envelope, null, 2))
    return EXIT_OK
  }

  const files = listGeneration(store.generationDir)
  let directoryBytes = 0
  for (const file of files) directoryBytes += file.size

  out(`store ${root}`)
  out(`generation ${store.generation}${store.activated ? ' (activated through CURRENT)' : ' (named on the command line)'}`)
  out(`manifest ${store.manifestName}, ${store.manifest.length} bytes, wire version ${envelope.wireVersion}`)
  out(`layout ${envelope.layout}`)
  out(`blank-node profile ${envelope.blankNodeProfile === '' ? '(none recorded)' : envelope.blankNodeProfile}`)
  out(`term registry ${envelope.termRegistryVersion === '' ? '(none recorded)' : envelope.termRegistryVersion}`)
  out(`fixed-chunk Merkle commitment ${envelope.rangeCommitted ? 'yes' : 'no'}`)
  out(`${envelope.entries.length} ${envelope.entries.length === 1 ? 'entry' : 'entries'}, ${envelope.totalBytes} bytes, ${plural(envelope.totalRows, 'row')}`)
  out(`generation directory holds ${files.length} files, ${directoryBytes} bytes`)
  out('')
  printTable(
    ['#', 'rows', 'bytes', 'kind', 'graphs', 'predicate'],
    envelope.entries.map((entry) => [
      String(entry.ordinal),
      String(entry.rows),
      String(entry.bytes),
      entry.blockKind,
      entry.graphs.length === 0 ? '-' : entry.graphs.map(graphLabel).join(' '),
      entry.predicate
    ]))
  return EXIT_OK
}

function notWired (command, detail) {
  err(`factoidal ${command}: not yet wired. ${detail}`)
  err(`This needs a WebAssembly operation from the Lean engine; see ${ISSUE}.`)
  return EXIT_NOT_WIRED
}

const QUERY_FORMATS = ['table', 'json', 'nquads', 'turtle']
const UNAVAILABLE_FORMATS = {
  xml: 'the SPARQL Results XML document',
  csv: 'the SPARQL Results CSV document',
  tsv: 'the SPARQL Results TSV document'
}

function queryText (positional, options) {
  if (typeof options.file === 'string') {
    return new TextDecoder('utf-8', { fatal: true }).decode(readWhole(options.file))
  }
  if (positional.length > 1) return positional.slice(1).join(' ')
  if (typeof options.query === 'string') return options.query
  throw new UsageError('query needs QUERY, --query TEXT or --file PATH')
}

function queryFormat (options) {
  if (options.json === true && typeof options.format !== 'string') return 'json'
  if (typeof options.format !== 'string') return 'table'
  const format = options.format.toLowerCase()
  if (QUERY_FORMATS.indexOf(format) >= 0) return format
  if (Object.prototype.hasOwnProperty.call(UNAVAILABLE_FORMATS, format)) {
    throw new UsageError(
      `--format ${format} needs an engine operation that writes ` +
      `${UNAVAILABLE_FORMATS[format]}; there is none, and writing one here ` +
      'would be a second serializer. Use --format json.')
  }
  throw new UsageError(`--format ${options.format} is not one of ${QUERY_FORMATS.join(', ')}`)
}

function queryLimit (options, format) {
  if (typeof options.limit !== 'string') return null
  const limit = Number(options.limit)
  if (!Number.isSafeInteger(limit) || limit < 0) {
    throw new UsageError('--limit needs a non-negative whole number')
  }
  if (format !== 'table') {
    throw new UsageError(
      '--limit truncates the printed table only; it is not carried into the ' +
      "engine's own documents. Put a LIMIT clause in the query instead.")
  }
  return limit
}

/** Report a refusal the store operations made, and what to do about it. */
function reportStoreFailure (error) {
  err(`factoidal query: ${error.message}`)
  if (error.capLimit !== null) {
    err(`This query needs more of the store than one WebAssembly call may read: ${error.capValue} against a cap of ${error.capLimit}.`)
    err('Narrow the query - bind a predicate, or restrict the graph - or use the native l4block-* tools.')
  } else if (error.stackLimit) {
    for (const line of stackLimitAdvice(STACK_REMEDY.query)) err(line)
  } else if (error.digestKey !== null) {
    err(`The bytes of '${error.digestKey}' in the generation directory are not the bytes the manifest commits.`)
    err('The generation is damaged or was edited after it was packed; repack or restore it.')
  }
  return EXIT_FAILURE
}

async function commandQuery (positional, options) {
  if (positional.length < 1) throw new UsageError('query needs a STORE')
  if (typeof options.base === 'string') {
    throw new UsageError(
      'the store query operation takes no base argument; put a BASE clause ' +
      'in the query text instead')
  }
  const root = positional[0]
  const sparql = queryText(positional, options)
  const format = queryFormat(options)
  const limit = queryLimit(options, format)
  const quiet = options.quiet === true

  const named = typeof options.generation === 'string' ? options.generation : null
  const store = openStore(root, named)
  const engine = await loadEngine()

  if (options.explain === true) {
    let plan
    try {
      plan = planQuery(engine, store, sparql)
    } catch (error) {
      if (error instanceof StoreOperationError) return reportStoreFailure(error)
      throw error
    }
    if (format === 'json' || options.json === true) {
      out(JSON.stringify(plan, null, 2))
      return EXIT_OK
    }
    out(`layout ${plan.layout} (wire version ${plan.wireVersion})`)
    out(`mode ${plan.mode}`)
    out(`${plural(plan.shards, 'artifact')}, ${plan.bytes} bytes, ${plural(plan.rows, 'row')}`)
    for (const key of plan.keys) out(`  ${key}`)
    return EXIT_OK
  }

  let answer
  try {
    answer = queryStore(engine, store, sparql)
  } catch (error) {
    if (error instanceof StoreOperationError) return reportStoreFailure(error)
    throw error
  }
  const { plan, result, blobBytes } = answer
  if (!quiet) {
    err(`mode ${result.mode}, ${plural(result.shards, 'artifact')}, ${blobBytes} bytes read, plan declares ${plural(plan.rows, 'block row')}`)
  }
  return renderQueryResult(engine, result, format, limit, quiet)
}

function renderQueryResult (engine, result, format, limit, quiet) {
  if (result.kind === 'select') {
    const vars = result.srj.head.vars
    const bindings = result.srj.results.bindings
    if (format === 'json') {
      out(JSON.stringify(result.srj, null, 2))
      return EXIT_OK
    }
    if (format !== 'table') {
      err(`factoidal query: --format ${format} needs a CONSTRUCT query; this one is a SELECT`)
      return EXIT_FAILURE
    }
    const shown = limit === null ? bindings : bindings.slice(0, limit)
    printTable(vars, shown.map((row) => vars.map((name) => cellOfTerm(row[name]))))
    if (shown.length < bindings.length) {
      err(`showing ${shown.length} of ${bindings.length} rows (--limit ${limit})`)
    } else if (!quiet) {
      err(plural(bindings.length, 'row'))
    }
    return EXIT_OK
  }
  if (result.kind === 'ask') {
    if (format === 'json') {
      // The operation answers ASK with a boolean, not with a results
      // document, so the envelope is what there is to print.
      out(JSON.stringify(result, null, 2))
      return EXIT_OK
    }
    if (format !== 'table') {
      err(`factoidal query: --format ${format} needs a CONSTRUCT query; this one is an ASK`)
      return EXIT_FAILURE
    }
    out(result.boolean ? 'true' : 'false')
    return EXIT_OK
  }
  if (result.kind === 'construct') {
    if (format === 'json') {
      out(JSON.stringify(result, null, 2))
      return EXIT_OK
    }
    if (format === 'turtle') {
      out(turtleOfNQuads(engine, result.nquads))
      return EXIT_OK
    }
    // table and nquads both print what the engine serialized.
    if (result.nquads.length > 0) out(result.nquads.replace(/\n$/, ''))
    return EXIT_OK
  }
  err(`factoidal query: the engine answered an unknown result kind "${result.kind}"`)
  return EXIT_FAILURE
}

/** The syntax tag for an input, from --syntax or from the file name. The
 *  engine is what actually decides how to read the bytes; this only picks
 *  which of its parsers to name. */
function packSyntax (input, options) {
  if (typeof options.syntax === 'string') {
    const syntax = options.syntax.toLowerCase()
    if (PACK_SYNTAXES.indexOf(syntax) >= 0) return syntax
    throw new UsageError(`--syntax ${options.syntax} is not one of ${PACK_SYNTAXES.join(', ')}`)
  }
  const lower = input.toLowerCase()
  for (const [suffix, syntax] of PACK_SUFFIXES) {
    if (lower.endsWith(suffix)) return syntax
  }
  for (const [suffix, name] of PACK_UNSUPPORTED_SUFFIXES) {
    if (lower.endsWith(suffix)) {
      throw new UsageError(
        `pack does not read ${name}. The packer's streaming fold reads ` +
        `${PACK_SYNTAXES.join(', ')} only. Convert the file first, for ` +
        "example with: factoidal parse FILE --out nquads")
    }
  }
  throw new UsageError(
    `cannot tell the syntax of ${input} from its name; give --syntax ` +
    `(${PACK_SYNTAXES.join(', ')})`)
}

/**
 * The base IRI relative IRIs in the source resolve against.
 *
 * The native packer uses `file://<input>`, so this matches it by default
 * and byte-identical output needs no flag. `--base` overrides it, and
 * `--base ''` asks for no base, which turns a relative IRI into a parse
 * error rather than a silently different term.
 */
function packBase (input, options) {
  if (typeof options.base === 'string') return options.base
  const absolute = input.startsWith('/') ? input : joinPath(currentDirectory(), input)
  return 'file://' + absolute
}

/** The process's working directory, on Node and on Deno. */
function currentDirectory () {
  if (isDeno) return globalThis.Deno.cwd()
  return process.cwd()
}

function packLayout (options) {
  if (typeof options.layout !== 'string') return 'ibk3'
  const layout = options.layout.toLowerCase()
  if (PACK_LAYOUTS.indexOf(layout) >= 0) return layout
  throw new UsageError(`--layout ${options.layout} is not one of ${PACK_LAYOUTS.join(', ')}`)
}

async function commandPack (positional, options) {
  if (positional.length !== 2) throw new UsageError('pack needs INPUT and OUTPUT')
  const [input, output] = positional
  const syntax = packSyntax(input, options)
  const layout = packLayout(options)
  // The pack fold needs a bigger call stack than either runtime gives by
  // default (https://github.com/danbri/factoidal/issues/649). Under Node
  // the work runs on a worker thread with a raised stack; under Deno the
  // command re-executes itself once with --v8-flags=--stack-size, and
  // this is where that happens, before any file is opened. --no-worker
  // keeps the in-process path testable.
  const host = { worker: options['no-worker'] !== true }
  const reexec = await denoReexec(host)
  if (reexec !== null) return reexec
  makeDirectory(output)
  const quiet = options.quiet === true
  let answer
  try {
    answer = await runPack(
      { kind: 'pack', input, output, syntax, layout, base: packBase(input, options) },
      quiet
        ? undefined
        : (progress) => {
            if (progress.bytesRead % (16 * 1024 * 1024) < FEED_PROGRESS) {
              err(`${progress.pass}: ${progress.bytesRead} bytes read, ${progress.artifacts} artifacts written`)
            }
          },
      host)
  } catch (error) {
    if (error instanceof PackError || error instanceof StoreHostError) {
      err(`factoidal pack: ${error.message}`)
      return EXIT_FAILURE
    }
    // Everything the engine refuses -- an unknown grammar tag, a parse
    // error, a cap -- arrives as a plain Error carrying the engine's own
    // words. A stack trace here would hide them.
    if (error instanceof Error && typeof error.message === 'string') {
      err(`factoidal pack: ${error.message.replace(/^l4factoidal:\s*/, '')}`)
      // The raised stack was refused, unavailable, or still not enough.
      if (isStackOverflow(error)) {
        for (const line of stackLimitAdvice(STACK_REMEDY.pack)) err(line)
      }
      return EXIT_FAILURE
    }
    throw error
  }
  if (answer.notWired === true) {
    return notWired('pack',
      'This install carries an engine built before the streaming pack ' +
      'operations. Update @factoidal/core, or set FACTOIDAL_L4_ASSETS to ' +
      'a newer build.')
  }
  const report = answer.report
  if (options.json === true) {
    out(JSON.stringify(report, null, 2))
    return EXIT_OK
  }
  out(`packed ${report.bytesRead} bytes of ${syntax} into ${output}`)
  out(`${report.written.length} artifacts, ${report.bytesWritten} bytes, layout ${layout}`)
  if (typeof report.rows === 'number') out(`${plural(report.rows, 'row')}`)
  out(`activate it with: factoidal activate ${dirOf(output)} ${nameOf(output)}`)
  return EXIT_OK
}

async function commandActivate (positional, options) {
  if (positional.length !== 2) throw new UsageError('activate needs STORE and GENERATION')
  const [root, generation] = positional
  // Verification decodes the same blocks the pack encoded, so it recurses
  // as deep and needs the same raised stack. Measured 2026-09-04: a
  // 112,742-row generation packed successfully and then failed to
  // activate with `Maximum call stack size exceeded`, leaving a store
  // that could be built and not opened
  // (https://github.com/danbri/factoidal/issues/649).
  const host = { worker: options['no-worker'] !== true }
  const reexec = await denoReexec(host)
  if (reexec !== null) return reexec
  let answer
  try {
    answer = await runPack({ kind: 'activate', root, generation }, undefined, host)
  } catch (error) {
    if (error instanceof PackError || error instanceof StoreHostError) {
      err(`factoidal activate: ${error.code ? error.code + ': ' : ''}${error.message}`)
      return EXIT_FAILURE
    }
    if (error instanceof Error && typeof error.message === 'string') {
      err(`factoidal activate: ${error.message.replace(/^l4factoidal:\s*/, '')}`)
      if (isStackOverflow(error)) {
        for (const line of stackLimitAdvice(STACK_REMEDY.pack)) err(line)
      }
      return EXIT_FAILURE
    }
    throw error
  }
  if (answer.notWired === true) {
    return notWired('activate',
      'This install carries an engine built before the activation ' +
      'verification operation. Update @factoidal/core.')
  }
  const verdict = answer.report
  if (verdict.ok !== true) {
    err(`factoidal activate: ${verdict.error}`)
    err('The generation is NOT activated; CURRENT is unchanged.')
    return EXIT_FAILURE
  }
  // Only now does the pointer move, and it moves atomically.
  const pointer = new TextEncoder().encode(generation)
  const synced = atomicReplace(joinPath(root, 'CURRENT'), pointer)
  if (options.json === true) {
    out(JSON.stringify({ ...verdict, generation, directorySynced: synced }, null, 2))
    return EXIT_OK
  }
  out(`activated ${generation}: ${verdict.artifacts} artifacts verified, ${verdict.bytes} bytes`)
  if (!synced) {
    err('CURRENT was replaced, but the directory entry was not synced; a ' +
        'crash now could lose the pointer update.')
  }
  return EXIT_OK
}

function commandUpdate (positional, options) {
  if (positional.length < 1) throw new UsageError('update needs a STORE')
  const text = positional.length > 1
    ? positional.slice(1).join(' ')
    : (typeof options.update === 'string' ? options.update : null)
  if (text === null && typeof options.file !== 'string') {
    throw new UsageError('update needs UPDATE, --update TEXT or --file PATH')
  }
  return notWired('update', 'The delta-log operations are stage 4 of the milestone.')
}

function commandCompact (positional, _options) {
  if (positional.length !== 2) throw new UsageError('compact needs STORE and GENERATION')
  return notWired('compact', 'Compaction is stage 4 of the milestone.')
}

const COMMANDS = {
  version: (positional, options) => commandVersion(options),
  'sample-store': (positional, options) => commandSampleStore(options),
  inspect: commandInspect,
  query: commandQuery,
  pack: commandPack,
  activate: commandActivate,
  update: commandUpdate,
  compact: commandCompact
}

// ----------------------------------------------------------------- main

async function main () {
  if (argv.length === 0) {
    out(USAGE)
    return EXIT_USAGE
  }
  const command = argv[0]
  if (command === '--help' || command === '-h' || command === 'help') {
    const topic = argv[1]
    if (typeof topic === 'string' && Object.prototype.hasOwnProperty.call(COMMAND_USAGE, topic)) {
      out(COMMAND_USAGE[topic])
    } else {
      out(USAGE)
    }
    return EXIT_OK
  }
  if (command === '--version') return commandVersion({})
  if (!Object.prototype.hasOwnProperty.call(COMMANDS, command)) {
    err(`factoidal: unknown command "${command}"`)
    err(USAGE)
    return EXIT_USAGE
  }
  let parsed
  try {
    parsed = parseArguments(argv.slice(1), VALUE_OPTIONS[command])
  } catch (error) {
    if (error instanceof UsageError) {
      err(`factoidal ${command}: ${error.message}`)
      return EXIT_USAGE
    }
    throw error
  }
  if (parsed.options.help) {
    out(COMMAND_USAGE[command])
    return EXIT_OK
  }
  try {
    return await COMMANDS[command](parsed.positional, parsed.options)
  } catch (error) {
    if (error instanceof UsageError) {
      err(`factoidal ${command}: ${error.message}`)
      err('')
      err(COMMAND_USAGE[command])
      return EXIT_USAGE
    }
    if (error instanceof StoreHostError) {
      err(`factoidal ${command}: ${error.code}: ${error.message}`)
      return EXIT_FAILURE
    }
    if (error instanceof StoreOperationError) {
      err(`factoidal ${command}: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
}

exit(await main())
