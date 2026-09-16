// TypeScript declarations for 'factoidal/api' (issue #682) — the
// bundler-friendly, CSP-safe entry point. See api.js's header comment
// for the full picture (why this exists, what it does not cover).

/**
 * An already-loaded npm-entry ABI object (the `factoidalNpmEntry`
 * value `factoidal-npm-entry.js` / `factoidal-npm-entry.wasm.js`
 * registers), a Promise of one, or a zero-argument function returning
 * either.
 */
export type EntrySource =
  | object
  | Promise<object>
  | (() => object | Promise<object>);

export interface CreateApiOptions {
  /** Reported as the returned API's `engine` field. Default 'entry'. */
  engineName?: string;
  /** VC Data Integrity crypto init hook; see index.d.ts's driver doc. */
  initCrypto?: () => Promise<void>;
}

/**
 * Build a typed API (parse/query/serialize/... — the same surface
 * `factoidal` / `factoidal/wasm` export) around an already-loaded
 * npm-entry ABI object, without fetching or `eval`-ing anything.
 * Throws a TypeError (naming `factoidalNpmEntry`) if `entry` resolves
 * to something without a `queryDataset` function.
 */
export function createApi(
  entry: EntrySource,
  options?: CreateApiOptions
): import('./index').default;

/**
 * Lower-level constructor `createApi()` is built on: wires a typed
 * surface around a driver `{engineName, runCli, loadEntry,
 * initCrypto?}`. Exposed for callers assembling their own driver
 * (e.g. a custom transport for the npm-entry ABI).
 */
export function buildApi(driver: {
  engineName: string;
  runCli: (
    args: string[],
    files: Array<{ name: string; content: string }>
  ) => { stdout: string; stderr: string; exitCode: number } |
    Promise<{ stdout: string; stderr: string; exitCode: number }>;
  loadEntry: () => (object | null) | Promise<object | null>;
  initCrypto?: () => Promise<void>;
}): import('./index').default;

export const Dataset: typeof import('./index').Dataset;
export const dataFactory: import('./index').DataFactory;
/** Position-carrying parse failure (issue #344); see index.d.ts's ParseError doc comment. */
export const ParseError: typeof import('./index').ParseError;
/** Package version string, e.g. '0.7.1'. */
export const version: string;

declare const _default: {
  createApi: typeof createApi;
  buildApi: typeof buildApi;
  ParseError: typeof ParseError;
  Dataset: typeof Dataset;
  dataFactory: import('./index').DataFactory;
  version: string;
};
export default _default;
