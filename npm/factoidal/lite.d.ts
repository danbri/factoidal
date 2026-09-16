// TypeScript declarations for '@factoidal/core/lite' (issue #684) --
// the 'lite' profile entry point. Same core typed surface as
// index.d.ts, restricted to what the lite npm-entry bundle
// implements: no SHACL, ShEx, OWL closure, JSON-LD, RDF/XML, CSVW,
// RML, RIF, XML, XPath, VC crypto, COTTAS, and no CLI bundle (no
// entailment regimes, no queryHdt).

import {
  DataFactory,
  DataInput,
  DataFormat,
  Dataset,
  DatasetHandle,
  ParseError,
  ParseOptions,
  QueryOptions,
  QueryInput,
  SerializeOptions,
  Bindings,
  ExtensionTerm,
} from './index';

export {
  Dataset,
  DataFactory,
  DataInput,
  DataFormat,
  DatasetHandle,
  ParseError,
  ParseOptions,
  QueryOptions,
  QueryInput,
  SerializeOptions,
  Bindings,
  ExtensionTerm,
};

/**
 * Parse one RDF document into a Dataset. Strict by default (issue
 * #344); see index.d.ts's `parse()` doc comment for the ParseError
 * shape and the `lenient` option.
 */
export function parse(text: string, options?: ParseOptions | DataFormat): Promise<Dataset>;

/**
 * Run a SPARQL 1.1 query. `data` may be a DatasetHandle from
 * openDataset(). See index.d.ts's `query()` doc comment.
 */
export function query(
  data: QueryInput,
  sparql: string,
  options?: QueryOptions | DataFormat
): Promise<Bindings[] | boolean | Dataset>;

/** Register a custom SPARQL extension function (SPARQL 1.1 §17.6, issue #463). */
export function registerExtensionFunction(
  iri: string,
  fn: (args: ExtensionTerm[]) =>
    ExtensionTerm | boolean | number | string | null | undefined |
    Promise<ExtensionTerm | boolean | number | string | null | undefined>
): Promise<void>;
/** Remove one registered extension function. */
export function unregisterExtensionFunction(iri: string): Promise<void>;
/** Remove every registered extension function. */
export function clearExtensionFunctions(): Promise<void>;

/** Bind a SPARQL SERVICE endpoint IRI to a local graph snapshot. */
export function registerServiceEndpoint(
  iri: string,
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: true; count: number }>;
/** Remove every registered SERVICE endpoint snapshot. */
export function clearServiceEndpoints(): Promise<void>;

/**
 * Apply a SPARQL 1.1 Update, returning the updated Dataset. `data`
 * must NOT be a DatasetHandle -- call `handle.update()` directly
 * instead.
 */
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat } | DataFormat
): Promise<Dataset>;

/** Open a dataset handle (issue #680); see index.d.ts's `openDataset()` doc comment. */
export function openDataset(
  data: DataInput,
  options?: { format?: DataFormat; baseIRI?: string } | DataFormat
): Promise<DatasetHandle>;

/** Serialize a dataset. `data` may be a DatasetHandle. */
export function serialize(
  data: QueryInput,
  options?: SerializeOptions | NonNullable<SerializeOptions['format']>
): Promise<string>;

/** RDFC-1.0 dataset canonicalization. `data` may be a DatasetHandle. */
export function canonicalize(
  data: QueryInput,
  options?: { format?: DataFormat } | DataFormat
): Promise<string>;

/** Enumerate the named graphs of an already-parsed Dataset. */
export function graphs(dataset: Dataset): Array<[iri: string, graph: Dataset]>;

/** RDFC-1.0 canonical hash of a single graph. */
export function canonicalHash(datasetOrGraph: Dataset): Promise<string>;

export function capabilities(): Promise<{
  entry: boolean;
  construct: boolean;
  update: boolean;
  canonicalize: boolean;
  graphs: boolean;
  canonicalHash: boolean;
  shacl: boolean;
  shex: boolean;
  owlClosure: boolean;
  tableau: boolean;
  rml: boolean;
  csvw: boolean;
  jsonld: boolean;
  jsonldFromRdf: boolean;
  didKey: boolean;
  xml: boolean;
  xpath: boolean;
  rif: boolean;
  xslt: boolean;
  mathml: boolean;
  xforms: boolean;
  jsonSchema: boolean;
  schematron: boolean;
  toan: boolean;
  matrix: boolean;
  sigmoid: boolean;
  vcCrypto: boolean;
  cottasBytesStore: boolean;
  /** Always 'lite' for this entry point (once an entry bundle has loaded). */
  profile: 'lite' | string;
  abiVersion: string | undefined;
  datasetHandles: boolean;
  parseDiagnostics: boolean;
  turtlePrefixes: boolean;
}>;

export const dataFactory: DataFactory;
/** Package version string, e.g. '0.7.1'. */
export const version: string;
/** Always 'js-lite' for this entry point. */
export const engine: string;

declare const _default: {
  parse: typeof parse;
  query: typeof query;
  registerExtensionFunction: typeof registerExtensionFunction;
  unregisterExtensionFunction: typeof unregisterExtensionFunction;
  clearExtensionFunctions: typeof clearExtensionFunctions;
  registerServiceEndpoint: typeof registerServiceEndpoint;
  clearServiceEndpoints: typeof clearServiceEndpoints;
  update: typeof update;
  openDataset: typeof openDataset;
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  graphs: typeof graphs;
  canonicalHash: typeof canonicalHash;
  capabilities: typeof capabilities;
  DatasetHandle: typeof DatasetHandle;
  ParseError: typeof ParseError;
  Dataset: typeof Dataset;
  dataFactory: DataFactory;
  version: string;
  engine: string;
};
export default _default;
