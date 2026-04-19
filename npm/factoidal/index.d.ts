// TypeScript declarations for factoidal.
//
// Kept minimal on purpose — the underlying engine's API surface is
// "take a data string + query string, return results", and we want the
// types to reflect that directly without inventing a class hierarchy.

/** RDF serialization format of the input data string. */
export type DataFormat =
  | 'turtle' | 'ttl'
  | 'ntriples' | 'nt'
  | 'nquads' | 'nq'
  | 'trig'
  | 'rdfxml' | 'rdf-xml' | 'rdf';

/** Entailment regime applied to the data before evaluation. */
export type EntailRegime = 'none' | 'RDFS' | 'OWL-RL';

/**
 * Output format. `'json'` returns a parsed SPARQL Results JSON object;
 * every other value returns the raw string the CLI would have printed.
 */
export type OutputFormat =
  | 'json' | 'csv' | 'tsv' | 'xml' | 'table' | 'ntriples';

export interface QueryOptions {
  /** Default: 'turtle'. */
  dataFormat?: DataFormat;
  /** Default: 'none'. */
  entail?: EntailRegime;
  /** Default: 'json'. */
  output?: OutputFormat;
}

/**
 * A single RDF term as it appears in a SPARQL Results JSON binding.
 * Follows https://www.w3.org/TR/sparql11-results-json/ .
 */
export interface RdfTerm {
  type: 'uri' | 'bnode' | 'literal' | 'typed-literal';
  value: string;
  /** Language tag, e.g. 'en' or 'de'. Present only for lang-tagged literals. */
  'xml:lang'?: string;
  /** Datatype IRI. Present for typed literals. */
  datatype?: string;
}

/**
 * SPARQL Results JSON shape for SELECT / ASK queries.
 * CONSTRUCT and DESCRIBE results are represented differently by the
 * engine; currently they come back as a plain object with whatever the
 * OCaml side emits (often empty pending CONSTRUCT wiring — see README).
 */
export interface SparqlResultsJson {
  head: { vars?: string[]; link?: string[] };
  /** Populated for SELECT queries. */
  results?: { bindings: Array<Record<string, RdfTerm>> };
  /** Populated for ASK queries. */
  boolean?: boolean;
}

/**
 * Run a SPARQL query against an RDF dataset in memory.
 *
 * @example
 *   const r = await query(
 *     '@prefix : <http://ex/> . :a :p :b .',
 *     'SELECT * WHERE { ?s ?p ?o }'
 *   );
 *   r.results.bindings.length  // 1
 *
 * When `options.output` is `'json'` (the default) the promise resolves
 * to a parsed SparqlResultsJson object. Otherwise it resolves to the
 * raw string the CLI would have emitted.
 *
 * The promise rejects if the engine returns a non-zero exit code
 * (e.g. unparseable query, malformed data).
 */
// The return type depends on `options.output`:
//   - `'json'` (default) → `SparqlResultsJson`
//   - everything else    → `string`
// A conditional return type gives callers accurate inference without
// forcing them into a two-argument overload dance.
type QueryResult<O extends OutputFormat | undefined> =
  O extends undefined ? SparqlResultsJson :
  O extends 'json'    ? SparqlResultsJson :
  string;

export function query<
  O extends OutputFormat | undefined = undefined
>(
  dataString: string,
  queryString: string,
  options?: Omit<QueryOptions, 'output'> & { output?: O }
): Promise<QueryResult<O>>;

/** Package version string, e.g. '0.1.0-alpha.0'. */
export const version: string;

declare const _default: {
  query: typeof query;
  version: typeof version;
};
export default _default;
