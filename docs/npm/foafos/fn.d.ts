// TypeScript declarations for factoidal/fn — the strictly functional
// dataset API. See fn.js for the implementation and
// docs/designissues/2026-07-05-functional-dataset-api.md for the
// design rationale (identity/cost model, dataflow pattern).

import type {
  Dataset,
  Quad,
  Bindings,
  DataFormat,
  EntailRegime,
  NamedNode,
  BlankNode,
  MathValue,
  XFormsBind,
  XFormsNodeValidity,
  SchematronFinding,
  ToanExpr,
  MatrixCell,
  MatrixResult,
} from './index';

export type {
  MathValue,
  XFormsBind,
  XFormsNodeValidity,
  SchematronFinding,
  ToanExpr,
  MatrixCell,
  MatrixResult,
} from './index';

/**
 * A frozen, deduplicated snapshot of a quad set. No method mutates —
 * every operation on an FnDataset is a free function that returns a
 * new FnDataset (or a plain value). Iterating yields frozen RDF/JS
 * Quad terms.
 *
 * Opaque and handle-based: FnDataset does not commit callers to an
 * in-memory-array representation. Today's only implementation holds
 * one internally, but the public surface (size, iteration, toArray(),
 * toNQuads(), match()) is the contract a future on-disk (COTTAS)
 * backend or a precomputed-hash-sidecar backend would satisfy without
 * this type's shape changing — see
 * docs/designissues/2026-07-05-functional-dataset-api.md's "future
 * backends" section.
 */
export class FnDataset implements Iterable<Quad> {
  private constructor(backend: unknown);
  readonly size: number;
  [Symbol.iterator](): Iterator<Quad>;
  toArray(): Quad[];
  /** Raw N-Quads text, arrival order (not canonicalized). */
  toNQuads(): string;
  match(
    subject?: Quad['subject'] | null,
    predicate?: Quad['predicate'] | null,
    object?: Quad['object'] | null,
    graph?: Quad['graph'] | null
  ): FnDataset;
}

/** The empty dataset — identity element for union() / difference(). */
export const EMPTY: FnDataset;

/** Snapshot a (possibly mutable) RDF/JS Dataset into an FnDataset. */
export function fromDataset(dataset: Dataset): FnDataset;

/** Materialize an FnDataset into a fresh, independently-mutable Dataset. */
export function toDataset(ds: FnDataset): Dataset;

/**
 * A mutable accumulator for incrementally-arriving quads — the
 * streaming-parser integration seam. addChunk() accepts one quad or
 * an iterable of quads; finish() de-duplicates once and returns a
 * frozen FnDataset. Calling either method after finish() throws.
 */
export interface Builder {
  addChunk(chunk: Quad | Iterable<Quad>): void;
  finish(): FnDataset;
}

/** Construct a streaming builder (see Builder). */
export function builder(): Builder;

/**
 * Sugar over builder(): consume a sync or async iterable of quad
 * batches into one finished FnDataset.
 */
export function fromChunks(
  chunks: Iterable<Quad | Iterable<Quad>> | AsyncIterable<Quad | Iterable<Quad>>
): Promise<FnDataset>;

/** Parse one RDF document into an FnDataset. */
export function parse(
  text: string,
  options?: { format?: DataFormat; baseIRI?: string }
): Promise<FnDataset>;

/** Set union, first-seen order. */
export function union(a: FnDataset, b: FnDataset): FnDataset;

/** Quads in a that are not in b. */
export function difference(a: FnDataset, b: FnDataset): FnDataset;

/** Keep quads matching quadPred(quad) => boolean. */
export function filter(
  ds: FnDataset,
  quadPred: (quad: Quad) => boolean
): FnDataset;

/** Transform every quad with f(quad) => quad; output is re-deduplicated. */
export function mapQuads(ds: FnDataset, f: (quad: Quad) => Quad): FnDataset;

/**
 * Run a SPARQL 1.1 query. SELECT -> Bindings[]; ASK -> boolean;
 * CONSTRUCT -> FnDataset (needs the npm-entry engine bundle — see
 * capabilities()).
 */
export function query(
  ds: FnDataset,
  sparql: string,
  options?: { entail?: EntailRegime }
): Promise<Bindings[] | boolean | FnDataset>;

/**
 * Materialize an entailment closure over ds's default graph as a new
 * FnDataset (a self-CONSTRUCT under the given regime — reuses
 * query()'s entailment support; named-graph triples are not
 * restated). Needs the npm-entry engine bundle.
 */
export function entail(ds: FnDataset, regime: EntailRegime): Promise<FnDataset>;

/** SHACL Core validation result (see validate()). */
export interface ValidateResult {
  conforms: boolean;
  /** SHACL_Validation.validation_report_to_graph's graph as an FnDataset. */
  report: FnDataset;
}

/**
 * SHACL Core validation. Needs the npm-entry engine bundle. Neither
 * argument is mutated or consumed.
 * @param ds the data graph
 * @param shapes the shapes graph
 */
export function validate(ds: FnDataset, shapes: FnDataset): Promise<ValidateResult>;

/**
 * ShEx (Shape Expressions) validation of one focus node against one
 * shape. Needs the npm-entry engine bundle. `null` means "deferred" --
 * outside this engine's decidable ShEx fragment, never a guessed
 * answer.
 * @param schema ShExJ (JSON Schema form), as text
 * @param focus an IRI, "_:label", or an RDF/JS NamedNode/BlankNode term
 * @param shape a shape label (same shapes as focus); omit/null for the
 *   schema's own `start`
 */
export function shex(
  ds: FnDataset,
  schema: string,
  focus: string | NamedNode | BlankNode,
  shape?: string | NamedNode | BlankNode | null
): Promise<boolean | null>;

/**
 * Evaluate an RML mapping graph against one logical source's raw data,
 * materializing the generated triples as a new FnDataset. Needs the
 * npm-entry engine bundle. Every triples map in `mapping` reads the
 * SAME `source` -- joins across two different logical sources are out
 * of scope for this entry point.
 * @param mapping the RML mapping graph
 * @param source raw JSON or CSV text (not RDF)
 */
export function fromMapping(
  mapping: FnDataset,
  source: string,
  kind: 'json' | 'csv'
): Promise<FnDataset>;

/**
 * CSVW csv2rdf conversion, materialized as a new FnDataset. Needs the
 * npm-entry engine bundle. Both arguments are raw text (CSVW's
 * metadata format is JSON, not RDF); '' or omitted metadata infers
 * the schema from the CSV's own header row. Every table in a
 * multi-table `tables` group reads the SAME `csv` text.
 * @param csv raw RFC 4180 tabular data (not RDF)
 * @param metadata CSVW metadata document (JSON text)
 */
export function fromCsvw(
  csv: string,
  metadata?: string,
  options?: {
    mode?: 'standard' | 'minimal';
    base?: string;
    url?: string;
  }
): Promise<FnDataset>;

/**
 * RIF Core forward-chaining saturation, materialized as a new
 * FnDataset (input triples + derived triples, default graph only).
 * Needs the npm-entry engine bundle.
 * @param ds the premise graph
 * @param rules a RIF Core XML rule document
 */
export function rif(ds: FnDataset, rules: string): Promise<FnDataset>;

/** RDFC-1.0 canonical N-Quads text. Needs the npm-entry engine bundle. */
export function canonicalize(ds: FnDataset): Promise<string>;

/**
 * sha256 hex digest of canonicalize(ds); memoized by FnDataset
 * identity. Needs the npm-entry engine bundle (canonicalize's cost).
 */
export function hash(ds: FnDataset): Promise<string>;

/**
 * Structural equality — exact quad-set match when that is conclusive
 * (always for blank-node-free data), RDFC-1.0 canonical-hash equality
 * otherwise. See fn.js for the full cost-model comment.
 */
export function equals(a: FnDataset, b: FnDataset): Promise<boolean>;

/** Enumerate named graphs (default graph excluded), first-seen order. */
export function graphs(ds: FnDataset): Array<[iri: string, graph: FnDataset]>;

/** A minimal mutable box holding one dataflow input value. */
export interface Cell<T> {
  get(): T;
  set(value: T): void;
}

export function cell<T>(initial: T): Cell<T>;

/** A read-only handle to a derived dataflow value. */
export interface Derived<T> {
  /** Recomputes only when an input's content-key has changed. */
  get(): Promise<T>;
}

/**
 * A derived dataflow node over one or more cells: recomputes
 * fn(...values) only when at least one input's content-key (FnDataset
 * content hash, or the value itself for non-dataset inputs) has
 * changed since the last get().
 */
export function derive<Args extends unknown[], R>(
  fn: (...args: Args) => R | Promise<R>,
  ...inputCells: { [K in keyof Args]: Cell<Args[K]> }
): Derived<R>;

/**
 * Left-to-right function composition for Observable-style dataflow:
 * `pipe(f, g, h)(x)` is `h(g(f(x)))`, awaiting any async step. With no
 * functions it is the identity.
 */
export function pipe(): (input: unknown) => Promise<unknown>;
export function pipe<A, B>(f: (a: A) => B | Promise<B>): (a: A) => Promise<B>;
export function pipe<A, B, C>(
  f: (a: A) => B | Promise<B>,
  g: (b: B) => C | Promise<C>
): (a: A) => Promise<C>;
export function pipe<A, B, C, D>(
  f: (a: A) => B | Promise<B>,
  g: (b: B) => C | Promise<C>,
  h: (c: C) => D | Promise<D>
): (a: A) => Promise<D>;
export function pipe(
  ...fns: Array<(x: unknown) => unknown>
): (input: unknown) => Promise<unknown>;

// ---------------------------------------------------------------------
// Typed engine functions (#74 FP surface). Re-exported from the JS
// engine api; full doc comments live in ./index.d.ts.
// ---------------------------------------------------------------------

export function xsltTransform(
  stylesheetXml: string,
  sourceXml: string
): Promise<string>;
export function mathmlEval(
  contentMathmlXml: string,
  bindings?: Record<string, string>
): Promise<MathValue>;
export function xformsRecalc(
  instanceXml: string,
  binds: XFormsBind[]
): Promise<{ instance: string; validity: XFormsNodeValidity[] }>;
export function jsonSchemaValidate(
  schemaJson: string,
  instanceJson: string
): Promise<{
  valid: boolean;
  result: 'pass' | 'fail' | 'unsupported';
  errors: string[];
}>;
export function schematronValidate(
  schematronXml: string,
  instanceXml: string
): Promise<{ findings: SchematronFinding[] }>;
export function toanSummation(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;
export function toanProduct(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;
export function toanSimplify(expr: ToanExpr): Promise<string>;
export function toanDiff(expr: ToanExpr, variable: string): Promise<string>;
export function toanSubst(
  expr: ToanExpr,
  variable: string,
  value: ToanExpr
): Promise<string>;
export function matrixDeterminant(
  matrix: MatrixCell[][]
): Promise<MatrixResult>;
export function matrixScalarProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;
export function matrixVectorProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;
export function matrixOuterProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/**
 * Run a SPARQL 1.1 query against a read-only HDT artifact's raw bytes
 * (factoidal_cli.ml's `--data-hdt` backend). No npm-entry engine
 * bundle needed -- CLI-only. Default graph only, SELECT/ASK only.
 */
export function queryHdt(
  hdtBytes: Uint8Array | ArrayBuffer | string,
  sparql: string
): Promise<Bindings[] | boolean>;

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
  rml: boolean;
  jsonld: boolean;
  rif: boolean;
}>;
