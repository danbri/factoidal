#!/usr/bin/env node
// The `factoidal` command: pack, activate, query, update and compact a
// persisted Shardborough store from Node or Deno, with no native binary.
// https://github.com/danbri/factoidal/issues/641
//
// STATE TODAY. The argument surface below is complete and settled, so that
// wiring the remaining subcommands changes no user-visible syntax. Only the
// subcommands that need nothing beyond host file I/O run: `version` and
// `inspect`. The other five parse their arguments, report what they would
// do, and exit 3. Every format decision they are waiting on -- parsing RDF,
// building blocks, verifying digests, evaluating SPARQL -- belongs to the
// Lean source and reaches this command through WebAssembly operations
// (iron rule 7).

import {
  StoreHostError, listGeneration, openCollection, readWhole, runtime
} from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'

const EXIT_OK = 0
const EXIT_FAILURE = 1
const EXIT_USAGE = 2
const EXIT_NOT_WIRED = 3

const ISSUE = 'https://github.com/danbri/factoidal/issues/641'

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

function exit (code) {
  if (isDeno) globalThis.Deno.exit(code)
  else process.exit(code)
}

function out (line) { console.log(line) }
function err (line) { console.error(line) }

// ---------------------------------------------------------------- usage

const USAGE = `factoidal - the Factoidal persisted store, from Node or Deno

usage: factoidal <command> [options]

commands:
  version                     print the package and engine versions
  inspect  STORE              report the activated generation and its files
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

STORE is a collection root: the directory that holds CURRENT.`

const COMMAND_USAGE = {
  version: `factoidal version - print the package and engine versions

usage: factoidal version [--json]

Prints the npm package version, the Lean engine's WebAssembly digest as
recorded by its build, and which host-I/O implementation is loaded.`,

  inspect: `factoidal inspect - report what is on disk in a store

usage: factoidal inspect STORE [--json] [--generation NAME]

Reads CURRENT, then lists the files of the activated generation with their
sizes. It reports the manifest's file name and byte length; it does not
decode the manifest, so it names no predicate, block count or digest.
Decoding is a WebAssembly operation (${ISSUE}).

options:
  --generation NAME  inspect this generation instead of the activated one
  --json             emit one JSON object`,

  query: `factoidal query - evaluate a SPARQL query against a store

usage: factoidal query STORE [QUERY] [options]

QUERY is the query text. Give it as the second argument, or with --query,
or in a file with --file. SELECT, ASK, CONSTRUCT and DESCRIBE are the
target; the engine decides the form.

options:
  --query TEXT       the query text
  --file PATH        read the query text from a file
  --format FORMAT    json (default), xml, csv, tsv, turtle, nquads, table
  --limit N          stop after N result rows
  --base IRI         base IRI for resolving relative IRIs in the query
  --explain          print the physical plan instead of the results
  --json             shorthand for --format json`,

  pack: `factoidal pack - build one immutable generation from an RDF file

usage: factoidal pack INPUT OUTPUT [options]

INPUT is an RDF file. OUTPUT is the generation directory to create; it is
normally STORE/gen-N. Packing does not activate: run activate next.

options:
  --layout LAYOUT    ibk3 (triples, default) or ibk4 (quads)
  --syntax SYNTAX    turtle, trig or nquads; default from the file extension
  --chunk-bytes N    Merkle chunk size; default is the engine's
  --json             emit one JSON object`,

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
  inspect: new Set(['generation']),
  query: new Set(['query', 'file', 'format', 'limit', 'base']),
  pack: new Set(['layout', 'syntax', 'chunk-bytes']),
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

function commandInspect (positional, options) {
  if (positional.length !== 1) throw new UsageError('inspect needs exactly one STORE')
  const root = positional[0]
  let generation
  let generationDir
  let manifestName = null
  let manifestBytes = null
  if (typeof options.generation === 'string') {
    generation = options.generation
    generationDir = joinPath(root, generation)
  } else {
    const opened = openCollection(root)
    generation = opened.generation
    generationDir = opened.generationDir
    manifestName = opened.manifestName
    manifestBytes = opened.manifest.length
  }
  const files = listGeneration(generationDir)
  let totalBytes = 0
  for (const file of files) totalBytes += file.size
  const report = {
    store: root,
    generation,
    generationDir,
    activated: typeof options.generation !== 'string',
    manifest: manifestName === null ? null : { name: manifestName, bytes: manifestBytes },
    fileCount: files.length,
    totalBytes,
    files
  }
  if (options.json) {
    out(JSON.stringify(report, null, 2))
    return EXIT_OK
  }
  out(`store ${report.store}`)
  out(`generation ${report.generation}${report.activated ? ' (activated through CURRENT)' : ' (named on the command line)'}`)
  if (report.manifest !== null) {
    out(`manifest ${report.manifest.name} ${report.manifest.bytes} bytes (not decoded here)`)
  }
  out(`files ${report.fileCount}, ${report.totalBytes} bytes total`)
  for (const file of files) {
    out(`  ${String(file.size).padStart(12)}  ${file.name}`)
  }
  return EXIT_OK
}

function notWired (command, detail) {
  err(`factoidal ${command}: not yet wired. ${detail}`)
  err(`This needs a WebAssembly operation from the Lean engine; see ${ISSUE}.`)
  return EXIT_NOT_WIRED
}

function commandQuery (positional, options) {
  if (positional.length < 1) throw new UsageError('query needs a STORE')
  const text = positional.length > 1
    ? positional.slice(1).join(' ')
    : (typeof options.query === 'string' ? options.query : null)
  if (text === null && typeof options.file !== 'string') {
    throw new UsageError('query needs QUERY, --query TEXT or --file PATH')
  }
  return notWired('query', 'The store query operation is stage 1 of the milestone.')
}

function commandPack (positional, _options) {
  if (positional.length !== 2) throw new UsageError('pack needs INPUT and OUTPUT')
  return notWired('pack', 'The streaming pack operations are stage 3 of the milestone.')
}

function commandActivate (positional, _options) {
  if (positional.length !== 2) throw new UsageError('activate needs STORE and GENERATION')
  return notWired('activate', 'Activation must verify every artifact before it replaces CURRENT.')
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
  inspect: commandInspect,
  query: commandQuery,
  pack: commandPack,
  activate: commandActivate,
  update: commandUpdate,
  compact: commandCompact
}

// ----------------------------------------------------------------- main

function main () {
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
    return COMMANDS[command](parsed.positional, parsed.options)
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
    throw error
  }
}

exit(main())
