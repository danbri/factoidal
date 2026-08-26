// TypeScript declarations for factoidal/l4 — the Lean 4 (L4Factoidal)
// engine compiled to WebAssembly, bundled in this package's l4-assets/
// since issue #618. See l4.js for the asset-resolution ladder and
// docs/designissues/2026-08-22-npm-l4-module-packaging.md for why the
// wasm was split out originally and why that no longer applies.

/** A term in SPARQL Query Results JSON shape, plus `var` for patterns. */
export interface L4Term {
  type: 'uri' | 'literal' | 'bnode' | 'var';
  value: string;
  datatype?: string;
  'xml:lang'?: string;
}

export interface L4Triple {
  subject: L4Term;
  predicate: L4Term;
  object: L4Term;
}

/** SPARQL 1.1 Query Results JSON document. */
export interface L4ResultsDoc {
  head: { vars: string[] };
  results: { bindings: Array<Record<string, L4Term>> };
}

export interface L4Engine {
  version(): string;
  bgpQuery(triples: L4Triple[], bgp: L4Triple[]): Promise<L4ResultsDoc> | L4ResultsDoc;
}

export const engine: 'lean4-wasm';
export function available(): boolean;
export function loadL4(): Promise<L4Engine>;
export function version(): Promise<string>;
export function bgpQuery(triples: L4Triple[], bgp: L4Triple[]): Promise<L4ResultsDoc>;
