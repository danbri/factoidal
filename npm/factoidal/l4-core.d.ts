// TypeScript declarations for 'factoidal/l4-core' — the typed core
// API served by the Lean 4 engine (L4Factoidal compiled to
// WebAssembly) instead of the F* extraction. Assets resolve through
// the 'factoidal/l4' ladder: @factoidal/lean, $FACTOIDAL_L4_ASSETS,
// then the repository checkout.

import {
  DataFactory,
  DataInput,
  DataFormat,
  Dataset,
  ParseOptions,
  QueryOptions,
  SerializeOptions,
  Bindings,
  ShaclValidateResult,
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
export function update(data: DataInput, sparql: string): Promise<Dataset>;
export function serialize(
  data: DataInput,
  options?: SerializeOptions
): Promise<string>;
export function canonicalize(data: DataInput): Promise<string>;
export function graphs(data: DataInput): Promise<string[]>;
export function canonicalHash(data: DataInput): Promise<string>;
export function owlClosure(
  data: DataInput,
  options?: { regime?: 'RDFS' | 'OWL-RL' }
): Promise<Dataset>;
export function coreRdfsClosure(data: DataInput): Promise<Dataset>;
export function coreRdfsCheck(data: DataInput): Promise<boolean>;
export function rhoDfClosure(data: DataInput): Promise<Dataset>;
export function rhoDfFragmentCheck(data: DataInput): Promise<boolean>;
export function rdfsPlusClosure(data: DataInput): Promise<Dataset>;

// Present on the surface, NOT implemented by the Lean engine: each
// rejects with an engine-capability error so an engine swap fails
// loudly rather than with `undefined is not a function`.
// capabilities() reports the truth per feature.
export function shaclValidate(
  data: DataInput,
  shapes: DataInput
): Promise<ShaclValidateResult>;
export function shexValidate(
  data: DataInput,
  schema: string,
  shapeMap: string
): Promise<unknown>;
export function owlIsConsistent(data: DataInput): Promise<boolean | null>;
export function owlEntails(
  data: DataInput,
  conclusion: DataInput
): Promise<boolean | null>;

export function capabilities(): Promise<Record<string, boolean | string>>;
export const dataFactory: DataFactory;
export const engine: 'lean4-wasm';
export function available(): boolean;
export const version: string;
