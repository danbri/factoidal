// factoidal — Node driver for the wasm_of_ocaml CLI bundle.
//
// Same runCli(args, files) contract as ./engine-js.js, but backed by
// factoidal.wasm.js + factoidal.wasm.assets/*.wasm. The technique is
// the one proven by browser-wasm.js / test/smoke-wasm.mjs:
//
//   - the wasm loader is an async IIFE whose Promise is discarded at
//     source level; a one-marker rewrite captures it so we can await
//     completion;
//   - we force the loader down its Node branch (versions.node truthy)
//     and hand it a fake require() whose 'node:fs' serves our
//     in-memory input documents (the wasm build has no MlFakeDevice /
//     jsoo_fs_tmp) and routes fds 1/2 into capture buffers;
//   - 'node:fs/promises'.readFile serves the .wasm asset bytes from
//     the real filesystem.
//
// Unlike engine-js.js this driver is async (wasm instantiation).

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const PKG_ROOT = path.resolve(__dirname, '..');

const IIFE_MARKER = ';($=>async ';
const IIFE_REWRITE = ';globalThis.__fwPromise=($=>async ';

function bundleCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_WASM_BUNDLE) c.push(process.env.FACTOIDAL_WASM_BUNDLE);
  c.push(path.join(PKG_ROOT, 'factoidal.wasm.js'));
  c.push(path.resolve(PKG_ROOT, '..', '..', 'docs', 'fstar-extracted', 'factoidal.wasm.js'));
  return c;
}

function resolveBundlePath() {
  for (const p of bundleCandidates()) {
    if (p && fs.existsSync(p)) return p;
  }
  throw new Error(
    'factoidal.wasm.js engine bundle not found. Run ' +
    "'formal/fstar/build-ocaml.sh wasm-factoidal' in the repo, or set " +
    'FACTOIDAL_WASM_BUNDLE.'
  );
}

/** True if the wasm bundle (loader + .wasm asset) is present. */
function wasmAvailable() {
  try {
    const loader = resolveBundlePath();
    const assets = path.join(path.dirname(loader), 'factoidal.wasm.assets');
    return fs.existsSync(assets) &&
      fs.readdirSync(assets).some((f) => f.endsWith('.wasm'));
  } catch (_) {
    return false;
  }
}

let _src = null;
let _srcPath = null;
let _assetsDir = null;

function loadSource() {
  const p = resolveBundlePath();
  if (_src !== null && _srcPath === p) return _src;
  const raw = fs.readFileSync(p, 'utf8');
  const ix = raw.indexOf(IIFE_MARKER);
  if (ix < 0) {
    throw new Error(
      'engine-wasm: could not locate the async IIFE marker in ' +
      'factoidal.wasm.js — the bundle shape may have changed.'
    );
  }
  _src = raw.slice(0, ix) + IIFE_REWRITE + raw.slice(ix + IIFE_MARKER.length);
  _srcPath = p;
  _assetsDir = path.join(path.dirname(p), 'factoidal.wasm.assets');
  return _src;
}

function makeStat(size, isFile, opts) {
  const bigint = !!(opts && opts.bigint);
  const toN = (v) => (bigint ? BigInt(v) : v);
  return {
    isFile:            () => isFile,
    isDirectory:       () => false,
    isCharacterDevice: () => !isFile,
    isBlockDevice:     () => false,
    isSymbolicLink:    () => false,
    isFIFO:            () => false,
    isSocket:          () => false,
    dev: toN(0), ino: toN(0), mode: toN(0o100644),
    nlink: toN(1), uid: toN(0), gid: toN(0), rdev: toN(0),
    size: toN(size),
    atimeMs: bigint ? 0n : 0,
    mtimeMs: bigint ? 0n : 0,
    ctimeMs: bigint ? 0n : 0,
  };
}

/**
 * Run one CLI invocation of the wasm engine bundle.
 * Same contract as engine-js.runCli, but async.
 *
 * @param {string[]} args
 * @param {Array<{name: string, content: string}>} files
 * @returns {Promise<{stdout: string, stderr: string, exitCode: number}>}
 */
async function runCli(args, files) {
  const src = loadSource();

  const TE = new TextEncoder();
  const TD = new TextDecoder('utf-8');
  const fileMap = new Map(
    (files || []).map((f) => [f.name, TE.encode(f.content)])
  );

  const stdoutBuf = [];
  const stderrBuf = [];

  let exitCode = 0;
  const EXIT_SENTINEL = new Error('__factoidal_exit__');
  EXIT_SENTINEL.__factoidalExit = true;

  const fakeOpenFds = Object.create(null);
  let nextFd = 100;

  function writeSync(fd, buf, offset, length /*, position */) {
    let s;
    if (typeof buf === 'string') {
      s = buf;
    } else {
      const u8 = buf instanceof Uint8Array
        ? buf
        : new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
      const start = offset || 0;
      const end = start + (length === undefined ? u8.length - start : length);
      s = TD.decode(u8.subarray(start, end));
    }
    (fd === 2 ? stderrBuf : stdoutBuf).push(s);
    return length === undefined ? s.length : length;
  }

  const fileForPath = (p) => fileMap.get(String(p)) || null;

  const fakeFs = {
    constants: {
      R_OK: 4, W_OK: 2, X_OK: 1, F_OK: 0,
      O_RDONLY: 0, O_WRONLY: 1, O_RDWR: 2, O_APPEND: 8, O_CREAT: 512,
      O_TRUNC: 1024, O_EXCL: 2048, O_NONBLOCK: 4096, O_NOCTTY: 8192,
      O_DSYNC: 4194304, O_SYNC: 128,
    },
    writeSync,
    openSync: (p /*, flags, mode */) => {
      const f = fileForPath(p);
      if (!f) {
        throw Object.assign(
          new Error(`ENOENT: no such file or directory, open '${p}'`),
          { code: 'ENOENT', errno: -2, syscall: 'open', path: p });
      }
      const fd = nextFd++;
      fakeOpenFds[fd] = { path: String(p), buf: f, offset: 0 };
      return fd;
    },
    closeSync: (fd) => { delete fakeOpenFds[fd]; },
    readSync: (fd, buf, offset, length, position) => {
      const f = fakeOpenFds[fd];
      if (!f) throw Object.assign(new Error('EBADF'), { code: 'EBADF', errno: -9 });
      const pos = (position === null || position === undefined)
        ? f.offset : Number(position);
      const remaining = Math.max(0, f.buf.length - pos);
      const n = Math.min(length, remaining);
      for (let i = 0; i < n; i++) buf[offset + i] = f.buf[pos + i];
      if (position === null || position === undefined) f.offset = pos + n;
      return n;
    },
    fsyncSync: () => {},
    existsSync: (p) => fileForPath(p) !== null,
    accessSync: (p) => {
      if (!fileForPath(p)) {
        throw Object.assign(new Error('ENOENT'), { code: 'ENOENT', errno: -2 });
      }
    },
    statSync: (p, o) => {
      const f = fileForPath(p);
      if (!f) {
        if (o && o.throwIfNoEntry === false) return undefined;
        throw Object.assign(new Error('ENOENT'), { code: 'ENOENT', errno: -2 });
      }
      return makeStat(f.length, true, o);
    },
    lstatSync: (p, o) => fakeFs.statSync(p, o),
    fstatSync: (fd, o) => {
      const f = fakeOpenFds[fd];
      return makeStat(f ? f.buf.length : 0, !!f, o);
    },
  };

  // Serve the .wasm asset from the real filesystem next to the loader.
  async function readWasmAsset(requestedPath) {
    const s = String(requestedPath);
    const marker = 'factoidal.wasm.assets/';
    const ix = s.lastIndexOf(marker);
    const sub = ix < 0 ? s : s.slice(ix + marker.length);
    const abs = path.join(_assetsDir, path.basename(sub));
    return fs.readFileSync(abs);
  }

  const fakeRequire = (name) => {
    if (name === 'node:fs')          return fakeFs;
    if (name === 'node:fs/promises') return { readFile: readWasmAsset };
    if (name === 'node:path')        return {
      join:    (...parts) => parts.filter(Boolean).join('/').replace(/\/+/g, '/'),
      dirname: (p)        => String(p).replace(/\/[^/]*$/, '') || '.',
    };
    if (name === 'node:os')            return { tmpdir: () => '/tmp' };
    if (name === 'node:tty')           return { isatty: () => false };
    if (name === 'node:child_process') return { spawnSync: () => ({ status: 0, signal: null }) };
    throw new Error(`engine-wasm shim: unexpected require('${name}')`);
  };
  fakeRequire.main = { filename: '/factoidal/main.js' };

  const fakeProc = {
    argv: ['node', 'factoidal', ...args],
    exit: (n) => { exitCode = n | 0; throw EXIT_SENTINEL; },
    stdout: { write: (s) => stdoutBuf.push(String(s)) },
    stderr: { write: (s) => stderrBuf.push(String(s)) },
    platform: 'linux',
    versions: { node: process.versions.node || '22.0.0' },
    env: {},
    cpuUsage: () => ({ user: 0, system: 0 }),
    on:       () => {},
    cwd:      () => '/static',
    chdir:    () => {},
  };

  const orig = {
    proc:      globalThis.process,
    jsooFs:    globalThis.jsoo_fs_tmp,
    require:   globalThis.require,
    fwPromise: globalThis.__fwPromise,
    consoleLog: console.log,
    consoleError: console.error,
  };

  globalThis.process = fakeProc;
  globalThis.require = fakeRequire;
  globalThis.jsoo_fs_tmp = undefined;
  delete globalThis.__fwPromise;
  // Belt and braces: some bundle variants route output through
  // console.log/.error (line-wise, newline re-appended on capture).
  console.log = (...a) => { stdoutBuf.push(a.map(String).join(' ') + '\n'); };
  console.error = (...a) => { stderrBuf.push(a.map(String).join(' ') + '\n'); };

  function restoreGlobals() {
    globalThis.process = orig.proc;
    globalThis.jsoo_fs_tmp = orig.jsooFs;
    if (orig.require === undefined) delete globalThis.require;
    else globalThis.require = orig.require;
    if (orig.fwPromise === undefined) delete globalThis.__fwPromise;
    else globalThis.__fwPromise = orig.fwPromise;
    console.log = orig.consoleLog;
    console.error = orig.consoleError;
  }

  try {
    (new Function(src))();
    const p = globalThis.__fwPromise;
    if (!p || typeof p.then !== 'function') {
      throw new Error(
        'engine-wasm: __fwPromise was not captured — the bundle shape ' +
        'may have changed.');
    }
    try {
      await p;
    } catch (e) {
      // process.exit throws the sentinel through the async IIFE; that
      // is the normal completion path.
      if (e !== EXIT_SENTINEL && !(e && e.__factoidalExit)) throw e;
    }
  } finally {
    restoreGlobals();
  }

  return {
    stdout: stdoutBuf.join(''),
    stderr: stderrBuf.join(''),
    exitCode,
  };
}

module.exports = { runCli, resolveBundlePath, wasmAvailable };
