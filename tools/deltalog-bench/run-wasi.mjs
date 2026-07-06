#!/usr/bin/env node
// tools/deltalog-bench/run-wasi.mjs
//
// Minimal WASI runner for the wasm32-wasi delta-log bench binary
// (tools/deltalog-bench/deltalog_bench.c cross-compiled by
// tools/bench-runtimes.sh via `clang --target=wasm32-wasi
// --sysroot=/usr`). Uses Node's built-in `node:wasi` module (stable
// since Node 20, marked experimental in stdout but functionally
// stable for preview1 command modules) -- no wasmtime/wasmer
// install needed.
//
// Usage: node run-wasi.mjs BINARY.wasm [argv...]
// Exits with the wasm program's own exit code; forwards argv[1:] as
// the program's own argv (argv[0] is a synthetic program name).

import { readFileSync } from 'node:fs';
import { WASI } from 'node:wasi';

const wasmPath = process.argv[2];
const args = process.argv.slice(3);

if (!wasmPath) {
  console.error('usage: run-wasi.mjs BINARY.wasm [argv...]');
  process.exit(2);
}

const wasi = new WASI({
  version: 'preview1',
  args: ['deltalog_bench', ...args],
  env: {},
  preopens: { '/': process.cwd() },
});

const wasmBuffer = readFileSync(wasmPath);
const { instance } = await WebAssembly.instantiate(wasmBuffer, wasi.getImportObject());
process.exitCode = wasi.start(instance);
