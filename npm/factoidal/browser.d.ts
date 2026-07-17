// TypeScript declarations for factoidal/browser (browser.js) — the
// browser ESM entry. This is a DIFFERENT surface from the Node entry
// (index.d.ts): the browser functions drive the js_of_ocaml CLI bundle
// over fetch() and the persistent npm-entry ABI directly, so most
// return the ABI's own parsed {ok, ...} envelope (or SPARQL-Results
// JSON) rather than the RDF/JS Dataset shapes the Node API returns.
//
// Shared value shapes (SPARQL-Results JSON, MathML/XForms/Schematron/
// TOAN/matrix codecs) are imported from ./index so the two declaration
// files can never disagree about them.

import type {
  SparqlResultsJson,
  MathValue,
  XFormsBind,
  XFormsNodeValidity,
  SchematronFinding,
  ToanExpr,
  MatrixCell,
  MatrixResult,
  XPathResult,
} from './index';

export type {
  SparqlResultsJson,
  MathValue,
  XFormsBind,
  XFormsNodeValidity,
  SchematronFinding,
  ToanExpr,
  MatrixCell,
  MatrixResult,
  XPathResult,
  ScaledValue,
  SigmoidParams,
} from './index';

/** Entailment regime accepted by the browser query paths. */
export type EntailRegime = 'none' | 'RDFS' | 'OWL-RL';
/** CLI output formats the browser query paths accept. */
export type OutputFormat = 'json' | 'csv' | 'tsv' | 'xml' | 'table' | 'ntriples';

/** One document for the fake filesystem (runFactoidalCli). */
export interface CliFile {
  /** Must start with '/static/'. */
  name: string;
  content: string;
}

/** The result of one in-browser CLI invocation. */
export interface CliResult {
  stdout: string;
  stderr: string;
  exitCode: number;
  engineMs: number;
}

/** One named-graph document for queryDataset(). */
export interface DatasetFile {
  content: string;
  /** Named-graph IRI; omitted means the default graph. */
  graph?: string;
  /** Default: 'turtle'. */
  dataFormat?: string;
}

// ---------------------------------------------------------------------
// Bundle-URL + CLI plumbing.
// ---------------------------------------------------------------------

/** Override where `factoidal.js` (the CLI bundle) is fetched from. */
export function setFactoidalUrl(url: string): void;
/** Current `factoidal.js` source URL. */
export function getFactoidalUrl(): string;
/**
 * Pack a JS string's UTF-8 bytes one-char-per-byte for the bundle's
 * fake filesystem / argv (a no-op for pure-ASCII input).
 */
export function encodeTextAsBundleBytes(s: string): string;
/** Run one in-browser CLI invocation of the js_of_ocaml bundle. */
export function runFactoidalCli(
  args: string[],
  files: CliFile[],
  options?: { transformSource?: (src: string) => string }
): Promise<CliResult>;

// ---------------------------------------------------------------------
// CLI-bundle operations (no npm-entry bundle needed).
// ---------------------------------------------------------------------

/**
 * Run a SPARQL query against one in-memory RDF document. Returns parsed
 * SPARQL-Results JSON when `output` is 'json' (default), the raw output
 * string otherwise.
 */
export function query(
  dataString: string,
  queryString: string,
  options?: { dataFormat?: string; entail?: EntailRegime; output?: OutputFormat }
): Promise<SparqlResultsJson | string>;

/** Parse a document and dump sorted N-Quads (default input format: 'jsonld'). */
export function toRdf(
  text: string,
  options?: { format?: string; baseIRI?: string }
): Promise<string>;

/** RDFC-1.0 canonicalization: canonical blank-node labels + sorted N-Quads. */
export function canonicalize(
  text: string,
  options?: { format?: string; baseIRI?: string }
): Promise<string>;

/**
 * Run a SPARQL query against a multi-file, multi-named-graph dataset,
 * on the js_of_ocaml (default) or wasm_of_ocaml engine.
 */
export function queryDataset(
  files: DatasetFile[],
  queryString: string,
  options?: {
    entail?: EntailRegime;
    output?: OutputFormat;
    engine?: 'js' | 'wasm';
    wasmUrl?: string;
    transformSource?: (src: string) => string;
  }
): Promise<SparqlResultsJson | string>;

/**
 * Run a SPARQL 1.1 query against a read-only HDT artifact's raw bytes
 * (CLI's `--data-hdt` backend). Default graph only, SELECT/ASK only.
 */
export function queryHdt(
  hdtBytes: Uint8Array | ArrayBuffer | string,
  sparql: string,
  options?: { output?: OutputFormat }
): Promise<SparqlResultsJson | string>;

// ---------------------------------------------------------------------
// npm-entry ABI loader + operations that need it. These return the
// ABI's own parsed {ok, ...} envelope.
// ---------------------------------------------------------------------

/** Override where `factoidal-npm-entry.js` is fetched from. */
export function setFactoidalNpmEntryUrl(url: string): void;
/** Fetch + evaluate the npm-entry bundle once, returning its ABI object. */
export function loadNpmEntry(): Promise<Record<string, (...args: string[]) => string>>;

/** RIF Core smoke saturation (a fixed capability probe, no user input). */
export function rifSmoke(): Promise<{
  inputNquads: string;
  saturatedNquads: string;
  inputCount: number;
  derivedCount: number;
  rounds: number;
  fuel: number;
  engineMs: number;
}>;

/** RIF Core forward-chaining saturation over a premise graph. */
export function rifEval(
  rifXml: string,
  dataNQuads: string
): Promise<{ ok: true; saturatedNquads: string; [k: string]: unknown }>;

/** SHACL Core validation (dataset-handle N-Quads in). */
export function shaclValidate(
  dataNQuads: string,
  shapesNQuads: string
): Promise<{ ok: true; conforms: boolean; reportNquads: string }>;

/**
 * ShEx validation of one focus node against one shape. `verdict` null
 * (deferred:true) means outside the decidable fragment — never guessed.
 */
export function shexValidate(
  dataNQuads: string,
  schemaJson: string,
  focus: string,
  shapeLabel?: string
): Promise<{ ok: true; verdict: boolean | null; deferred: boolean }>;

/** RDFS/OWL-RL entailment closure (default graph only). */
export function owlClosure(
  dataNQuads: string,
  mode: 'RDFS' | 'OWL-RL'
): Promise<{ ok: true; nquads: string }>;

/** OWL tableau class-expression materialisation (default graph only). */
export function tableauMaterialise(
  dataNQuads: string
): Promise<{ ok: true; nquads: string; addedCount: number }>;

/** OWL DL inconsistency verdict (RL -> tableau -> RL -> is_inconsistent);
 * `rlAlone` is the plain OWL-RL verdict on the same input. */
export function tableauDlInconsistent(
  dataNQuads: string
): Promise<{ ok: true; inconsistent: boolean; rlAlone: boolean }>;

/** OWL DL consistency verdict via the verified clash-detecting tableau
 * (Tableau.Refute over the OWL-RL closure); `consistent` is
 * true|false|null (null = budget-out, `reason` names the fuel cap). */
export function owlIsConsistent(
  dataNQuads: string,
  optsJson?: string
): Promise<{ ok: true; consistent: boolean | null; reason?: string }>;

/** OWL entailment check (OWL-RL closure path then negate-and-refute);
 * `entailed` is true|false|null, `via` is 'closure' | 'refutation'. */
export function owlEntails(
  premiseNQuads: string,
  conclusionNQuads: string,
  optsJson?: string
): Promise<{ ok: true; entailed: boolean | null; via: string; reason?: string }>;

/** RML mapping evaluation against one logical source. */
export function rmlMap(
  mappingNQuads: string,
  sourceData: string,
  sourceKind: 'json' | 'csv'
): Promise<{ ok: true; nquads: string }>;

/** CSVW csv2rdf conversion. */
export function csvwToRdf(
  csvText: string,
  metadataJson?: string,
  options?: { mode?: 'standard' | 'minimal'; base?: string; url?: string }
): Promise<{ ok: true; nquads: string }>;

/** JSON-LD parsing with JSON-LD-specific options. */
export function jsonldToRdf(
  jsonldText: string,
  options?: {
    base?: string;
    rdfDirection?: string;
    expandContext?: string;
    processingMode?: string;
  }
): Promise<{ ok: true; nquads: string }>;

/** Serialize N-Quads as expanded-form JSON-LD (JCS-canonical string). */
export function jsonldFromRdf(
  nquads: string,
  options?: { useNativeTypes?: boolean; useRdfType?: boolean }
): Promise<{ ok: true; jsonld: string }>;

/** did:key (Ed25519) resolution to a DID Document (N-Triples). */
export function didKeyResolve(
  didString: string
): Promise<{ ok: true; did: string; nquads: string }>;

/** XML 1.0 well-formedness (no DOCTYPE/DTD production). */
export function xmlWellformed(
  xmlText: string
): Promise<{ ok: true; wellformed: boolean }>;

/** XPath 1.0 evaluation over an XML document. */
export function xpathEval(
  xmlText: string,
  xpathExpr: string
): Promise<{ ok: true } & XPathResult>;

// ---------------------------------------------------------------------
// VC Data Integrity crypto (eddsa-rdfc-2022, HACL* wasm backend).
//
// INIT (browser): unlike the Node entry (which auto-awaits initHacl()),
// a page MUST initialise the HACL* wasm backend itself before the first
// VC call — the hacl-wasm URL is page-specific (serve `hacl-wasm/` and
// `await initHacl({ apiUrl })` from hacl-init.js). An uninitialised
// backend makes verify THROW (the {ok:false} error surfaces), never
// return a false-positive true (#286, the throw-on-uninit contract).
// ---------------------------------------------------------------------

export function vcSha256Hex(message: string): Promise<{ ok: true; sha256: string }>;
export function vcEd25519SecretToPublic(
  secretKeyHex: string
): Promise<{ ok: true; publicKeyHex: string }>;
export function vcEd25519Sign(
  secretKeyHex: string,
  messageHex: string
): Promise<{ ok: true; signatureHex: string }>;
export function vcEd25519Verify(
  publicKeyHex: string,
  messageHex: string,
  signatureHex: string
): Promise<{ ok: true; valid: boolean }>;
export function vcEddsaCreateFromCanonical(
  secretKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string
): Promise<{ ok: true; proofValue: string }>;
export function vcEddsaVerifyFromCanonical(
  publicKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string,
  proofValue: string
): Promise<{ ok: true; verified: boolean }>;

// ---------------------------------------------------------------------
// In-memory COTTAS/Parquet bytes store.
// ---------------------------------------------------------------------

/** Open a COTTAS artifact's bytes as a read-only store; returns a handle. */
export function openCottas(
  bytes: Uint8Array | ArrayBuffer | string
): Promise<string>;
/** SPARQL over a store opened by openCottas() (read-only, no entail). */
export function queryCottas(
  handle: string,
  sparql: string
): Promise<
  | { ok: true; kind: 'select'; srj: SparqlResultsJson }
  | { ok: true; kind: 'ask'; boolean: boolean }
  | { ok: true; kind: 'construct'; nquads: string }
>;
/** Release a store handle (does not evict the underlying byte cache). */
export function closeCottas(handle: string): Promise<void>;
/** Serialize dataset-handle N-Quads to COTTAS/Parquet bytes. */
export function toCottas(nQuads: string): Promise<Uint8Array>;

// ---------------------------------------------------------------------
// Typed engine functions (#74 FP surface, browser side). Same value
// shapes as the Node entry (index.d.ts).
// ---------------------------------------------------------------------

export function xsltTransform(stylesheetXml: string, sourceXml: string): Promise<string>;
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
): Promise<{ valid: boolean; result: 'pass' | 'fail' | 'unsupported'; errors: string[] }>;
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
export function matrixDeterminant(matrix: MatrixCell[][]): Promise<MatrixResult>;
export function matrixScalarProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function matrixVectorProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function matrixOuterProduct(a: MatrixCell[], b: MatrixCell[]): Promise<MatrixResult>;
export function sigmoidPoints(
  params: SigmoidParams
): Promise<Array<{ x: ScaledValue; y: ScaledValue }>>;
export function sigmoidFormulaMathml(): Promise<string>;

// ---------------------------------------------------------------------
// Durable browser persistence (IndexedDB-backed delta log). Browser-
// only: these use `indexedDB` and have no Node analogue — a Node caller
// drives the raw npm-entry ABI (deltaBatchToHex / deltaMergeApplyBrowser)
// or an injected storage layer directly (see tests/hub/post18_test.mjs's
// Map-backed stub, which mirrors this exact contract).
// ---------------------------------------------------------------------

/** A handle naming one IndexedDB-backed delta log. */
export interface DeltaLogHandle {
  dbName: string;
}

/** Open (creating if needed) a browser-persistent delta log. */
export function deltaLogOpen(dbName?: string): Promise<DeltaLogHandle>;
/**
 * Translate one SPARQL Update (INSERT/DELETE DATA, CLEAR, DROP, CREATE)
 * into a delta_batch and durably append it as one IndexedDB record.
 */
export function deltaLogAppend(
  handle: DeltaLogHandle,
  sparqlUpdate: string,
  options?: { epoch?: number }
): Promise<{ seq: number; opCount: number }>;
/** Read every committed batch back, seq order, as newline-joined hex blobs. */
export function deltaLogReadAllHex(handle: DeltaLogHandle): Promise<string>;
/** Read the durable log back and merge it onto a base dataset (N-Quads). */
export function deltaLogMerge(
  handle: DeltaLogHandle,
  baseNQuads: string
): Promise<string>;
/** Delete a browser-persistent delta log entirely (test/demo cleanup). */
export function deltaLogDestroy(handle: DeltaLogHandle): Promise<void>;

/** Package version string. */
export const version: string;

declare const _default: {
  query: typeof query;
  toRdf: typeof toRdf;
  canonicalize: typeof canonicalize;
  runFactoidalCli: typeof runFactoidalCli;
  setFactoidalUrl: typeof setFactoidalUrl;
  getFactoidalUrl: typeof getFactoidalUrl;
  encodeTextAsBundleBytes: typeof encodeTextAsBundleBytes;
  queryDataset: typeof queryDataset;
  version: string;
  loadNpmEntry: typeof loadNpmEntry;
  setFactoidalNpmEntryUrl: typeof setFactoidalNpmEntryUrl;
  rifSmoke: typeof rifSmoke;
  rifEval: typeof rifEval;
  shaclValidate: typeof shaclValidate;
  shexValidate: typeof shexValidate;
  didKeyResolve: typeof didKeyResolve;
  owlClosure: typeof owlClosure;
  tableauMaterialise: typeof tableauMaterialise;
  tableauDlInconsistent: typeof tableauDlInconsistent;
  owlIsConsistent: typeof owlIsConsistent;
  owlEntails: typeof owlEntails;
  rmlMap: typeof rmlMap;
  jsonldToRdf: typeof jsonldToRdf;
  jsonldFromRdf: typeof jsonldFromRdf;
  xmlWellformed: typeof xmlWellformed;
  xpathEval: typeof xpathEval;
  deltaLogOpen: typeof deltaLogOpen;
  deltaLogAppend: typeof deltaLogAppend;
  deltaLogReadAllHex: typeof deltaLogReadAllHex;
  deltaLogMerge: typeof deltaLogMerge;
  deltaLogDestroy: typeof deltaLogDestroy;
  openCottas: typeof openCottas;
  queryCottas: typeof queryCottas;
  closeCottas: typeof closeCottas;
  toCottas: typeof toCottas;
  xsltTransform: typeof xsltTransform;
  mathmlEval: typeof mathmlEval;
  xformsRecalc: typeof xformsRecalc;
  jsonSchemaValidate: typeof jsonSchemaValidate;
  schematronValidate: typeof schematronValidate;
  toanSummation: typeof toanSummation;
  toanProduct: typeof toanProduct;
  toanSimplify: typeof toanSimplify;
  toanDiff: typeof toanDiff;
  toanSubst: typeof toanSubst;
  matrixDeterminant: typeof matrixDeterminant;
  matrixScalarProduct: typeof matrixScalarProduct;
  matrixVectorProduct: typeof matrixVectorProduct;
  matrixOuterProduct: typeof matrixOuterProduct;
  sigmoidPoints: typeof sigmoidPoints;
  sigmoidFormulaMathml: typeof sigmoidFormulaMathml;
  vcSha256Hex: typeof vcSha256Hex;
  vcEd25519SecretToPublic: typeof vcEd25519SecretToPublic;
  vcEd25519Sign: typeof vcEd25519Sign;
  vcEd25519Verify: typeof vcEd25519Verify;
  vcEddsaCreateFromCanonical: typeof vcEddsaCreateFromCanonical;
  vcEddsaVerifyFromCanonical: typeof vcEddsaVerifyFromCanonical;
  queryHdt: typeof queryHdt;
};
export default _default;
