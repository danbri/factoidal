// TypeScript declarations for 'factoidal/wasm' — same API as the main
// entry, backed by the wasm_of_ocaml engine bundle (Node >= 22).

import {
  DataFactory,
  DataInput,
  DataFormat,
  Dataset,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
} from './index';

export {
  Dataset,
  DataFactory,
  DataInput,
  DataFormat,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
};

export function parse(text: string, options?: ParseOptions): Promise<Dataset>;
export function query(
  data: DataInput,
  sparql: string,
  options?: QueryOptions
): Promise<Bindings[] | boolean | Dataset>;
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat }
): Promise<Dataset>;
export function serialize(
  data: DataInput,
  options?: SerializeOptions
): Promise<string>;
export function canonicalize(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<string>;

/**
 * The CERTIFIED core-RDFS closure (ρdf; see index.d.ts for the full
 * doc comment). Needs the npm-entry engine bundle.
 */
export function coreRdfsClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string }>;

/** Decidable core-RDFS fragment check — the regime theorems' fragment hypothesis. */
export function coreRdfsCheck(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; fragment: boolean }>;

/** Literature-name alias for coreRdfsClosure (ρdf). */
export function rhoDfClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string }>;

/** Literature-name alias for coreRdfsCheck (ρdf). */
export function rhoDfFragmentCheck(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; fragment: boolean }>;

/** RDFS-Plus closure (RDFS + practical OWL subset; see index.d.ts). */
export function rdfsPlusClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string; rounds: number }>;

/**
 * OWL DL consistency verdict via the verified clash-detecting tableau.
 * `consistent` is three-valued (`true`/`false`/`null` budget-out; see
 * index.d.ts). Needs the npm-entry engine bundle.
 */
export function owlIsConsistent(
  data: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ consistent: boolean | null; reason?: string }>;

/**
 * OWL entailment check: does `premise` entail `conclusion`? See
 * index.d.ts for the full doc comment. Needs the npm-entry engine
 * bundle.
 */
export function owlEntails(
  premise: DataInput,
  conclusion: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ entailed: boolean | null; via: 'closure' | 'refutation'; reason?: string }>;

export function capabilities(): Promise<{
  entry: boolean;
  construct: boolean;
  update: boolean;
  canonicalize: boolean;
}>;
export const dataFactory: DataFactory;
/** True if the wasm loader + .wasm asset are present. */
export function wasmAvailable(): boolean;
export const version: string;

declare const _default: {
  parse: typeof parse;
  query: typeof query;
  update: typeof update;
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  capabilities: typeof capabilities;
  Dataset: typeof Dataset;
  dataFactory: DataFactory;
  wasmAvailable: typeof wasmAvailable;
  version: string;
};
export default _default;
