// TypeScript declarations for factoidal.
//
// Self-contained: the RDF/JS interfaces below are structurally
// compatible with @rdfjs/types (same names and shapes) but declared
// here so the package has zero dependencies.

// ---------------------------------------------------------------------
// RDF/JS data model (https://rdf.js.org/data-model-spec/)
// ---------------------------------------------------------------------

export interface NamedNode<Iri extends string = string> {
  termType: 'NamedNode';
  value: Iri;
  equals(other: Term | null | undefined): boolean;
}

export interface BlankNode {
  termType: 'BlankNode';
  value: string;
  equals(other: Term | null | undefined): boolean;
}

export interface Literal {
  termType: 'Literal';
  value: string;
  /** Language tag ('' when none). */
  language: string;
  /** Datatype IRI term (xsd:string for plain literals). */
  datatype: NamedNode;
  equals(other: Term | null | undefined): boolean;
}

export interface Variable {
  termType: 'Variable';
  value: string;
  equals(other: Term | null | undefined): boolean;
}

export interface DefaultGraph {
  termType: 'DefaultGraph';
  value: '';
  equals(other: Term | null | undefined): boolean;
}

export interface Quad {
  termType: 'Quad';
  value: '';
  subject: Quad_Subject;
  predicate: Quad_Predicate;
  object: Quad_Object;
  graph: Quad_Graph;
  equals(other: Quad | null | undefined): boolean;
}

export type Quad_Subject = NamedNode | BlankNode | Variable;
export type Quad_Predicate = NamedNode | Variable;
export type Quad_Object = NamedNode | BlankNode | Literal | Variable;
export type Quad_Graph = DefaultGraph | NamedNode | BlankNode | Variable;

export type Term =
  | NamedNode | BlankNode | Literal | Variable | DefaultGraph | Quad;

export interface DataFactory {
  namedNode<Iri extends string = string>(value: Iri): NamedNode<Iri>;
  blankNode(label?: string): BlankNode;
  literal(value: string, languageOrDatatype?: string | NamedNode): Literal;
  variable(name: string): Variable;
  defaultGraph(): DefaultGraph;
  quad(
    subject: Quad_Subject,
    predicate: Quad_Predicate,
    object: Quad_Object,
    graph?: Quad_Graph
  ): Quad;
  fromTerm(original: Term): Term;
  fromQuad(original: Quad): Quad;
}

/** The package's RDF/JS DataFactory. */
export const dataFactory: DataFactory;

/**
 * An in-memory RDF/JS DatasetCore
 * (https://rdf.js.org/dataset-spec/#datasetcore-interface) that also
 * round-trips to the engine's N-Quads interchange text.
 */
export class Dataset implements Iterable<Quad> {
  constructor(quads?: Iterable<Quad>);
  readonly size: number;
  add(quad: Quad): this;
  delete(quad: Quad): this;
  has(quad: Quad): boolean;
  match(
    subject?: Term | null,
    predicate?: Term | null,
    object?: Term | null,
    graph?: Term | null
  ): Dataset;
  [Symbol.iterator](): Iterator<Quad>;
  toArray(): Quad[];
  /** N-Quads serialization of the quads (the engine interchange form). */
  toNQuads(): string;
  toString(): string;
  static fromNQuads(
    text: string,
    options?: { blankNodePrefix?: string; factory?: DataFactory }
  ): Dataset;
}

// ---------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------

/** RDF serialization format tags accepted for input text. */
export type DataFormat =
  | 'turtle' | 'ttl'
  | 'ntriples' | 'nt'
  | 'nquads' | 'nq'
  | 'trig'
  | 'rdfxml' | 'rdf-xml' | 'rdf'
  | 'jsonld' | 'json-ld';

/** Entailment regime applied to the data before evaluation. */
/**
 * Entailment regime for query(): the W3C-named regimes plus two
 * experimental certified regimes (RDF.Entailment.RegimeDispatch.fst) —
 * 'x-rdfscore': BGP answers over the theorem-backed corerdfs (ρdf)
 * closure, sound and complete on fragment data;
 * 'x-rdfsplus': RDFS plus the practical OWL subset, every rule under
 * proved licensing + truth lemmas. See docs/theorem-registry.md.
 */
export type EntailRegime = 'none' | 'RDFS' | 'OWL-RL' | 'x-rdfscore' | 'x-rdfsplus';

/**
 * One SELECT solution: a Map from variable name (no leading '?') to
 * the bound RDF/JS term. Unbound variables are absent from the Map.
 */
export type Bindings = Map<string, Term>;

/** Input data: a Dataset, a document string, or several of either. */
export type DataInput =
  | Dataset
  | string
  | { text: string; format?: DataFormat }
  | Array<Dataset | string | { text: string; format?: DataFormat }>;

export interface ParseOptions {
  /** Default: 'turtle'. */
  format?: DataFormat;
  /** Base IRI for resolving relative IRIs (Turtle/TriG/RDF-XML). */
  baseIRI?: string;
}

export interface QueryOptions {
  /** Format tag for string data inputs. Default: 'turtle'. */
  format?: DataFormat;
  /** Default: 'none'. */
  entail?: EntailRegime;
}

/** Parse one RDF document into a Dataset. */
export function parse(text: string, options?: ParseOptions): Promise<Dataset>;

/**
 * Run a SPARQL 1.1 query.
 * SELECT resolves to Bindings[]; ASK resolves to a boolean;
 * CONSTRUCT resolves to a Dataset (needs the npm-entry engine bundle
 * — rejects with an Error mentioning "pending npm-entry build" when
 * only the CLI bundle is available).
 */
export function query(
  data: DataInput,
  sparql: string,
  options?: QueryOptions
): Promise<Bindings[] | boolean | Dataset>;

/**
 * Run a SPARQL 1.1 query against a read-only HDT (Header-Dictionary-
 * Triples) artifact's raw bytes (factoidal_cli.ml's `--data-hdt`
 * backend). No npm-entry engine bundle needed -- CLI-only. Default
 * graph only, SELECT/ASK only (no CONSTRUCT, no named graphs).
 * @param hdtBytes whole .hdt file contents
 */
export function queryHdt(
  hdtBytes: Uint8Array | ArrayBuffer | string,
  sparql: string
): Promise<Bindings[] | boolean>;

/**
 * An argument or return value of a custom extension function, in the
 * SRJ term shape: {type:'uri'|'literal'|'bnode', value, datatype?,
 * 'xml:lang'?}. An errored argument arrives as {type:'error'}.
 */
export interface ExtensionTerm {
  type: 'uri' | 'literal' | 'bnode' | 'error';
  value?: string;
  datatype?: string;
  'xml:lang'?: string;
}

/**
 * Register a custom SPARQL extension function (SPARQL 1.1 §17.6,
 * issue #463; Comunica-style). `fn` may be sync or async; it receives
 * the evaluated arguments as ExtensionTerm[] and returns an
 * ExtensionTerm, a JS primitive (boolean | number | string), a
 * Promise of either, or null/undefined (= the §17.6 error). A query
 * calling an IRI with no registered function gets the same error:
 * unbound in SELECT/BIND position, row dropped in FILTER position.
 */
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

/**
 * Bind a SPARQL SERVICE endpoint IRI to a local graph snapshot, so
 * SERVICE <iri> { ... } (and LATERAL { SERVICE ... }) queries resolve
 * against it in-process — the same registry the W3C federated-query
 * suite uses (qt:serviceData). The snapshot is the payload's default
 * graph.
 */
export function registerServiceEndpoint(
  iri: string,
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: true; count: number }>;

/** Remove every registered SERVICE endpoint snapshot. */
export function clearServiceEndpoints(): Promise<void>;

/**
 * Apply a SPARQL 1.1 Update, returning the updated Dataset.
 * Needs the npm-entry engine bundle.
 */
export function update(
  data: DataInput,
  updateText: string,
  options?: { format?: DataFormat }
): Promise<Dataset>;

export interface SerializeOptions {
  /**
   * Output format. Default: 'nquads'. 'turtle' (prefix-compacted,
   * subject-grouped) needs the npm-entry bundle and flattens every
   * named graph into the default graph — use 'nquads' when graph names
   * must survive.
   */
  format?: 'nquads' | 'ntriples' | 'turtle' | 'ttl';
  /** Format tag for string data inputs. Default: 'turtle'. */
  inputFormat?: DataFormat;
}

/** Serialize a dataset (engine-produced, sorted N-Quads order). */
export function serialize(
  data: DataInput,
  options?: SerializeOptions
): Promise<string>;

/**
 * RDFC-1.0 dataset canonicalization: canonical blank-node labels plus
 * sorted canonical N-Quads. Two isomorphic inputs canonicalize to the
 * same string.
 */
export function canonicalize(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<string>;

/**
 * Enumerate the named graphs of an already-parsed Dataset (default
 * graph excluded), in first-seen order. Pure enumeration over
 * `dataset`'s own quads -- no engine round-trip, always available.
 * `graph` is the same Dataset filtered to that one graph name (what
 * `dataset.match(null, null, null, graphTerm)` would return).
 */
export function graphs(dataset: Dataset): Array<[iri: string, graph: Dataset]>;

/**
 * RDFC-1.0 canonical hash of a single graph -- the graph-scoped
 * sibling of canonicalize(). Every quad's graph component is dropped
 * before canonicalizing, so isomorphic graphs (including under
 * blank-node relabeling) hash to the same string regardless of what
 * graph name they were extracted from. Typically called with one
 * entry of graphs()'s output.
 */
export function canonicalHash(datasetOrGraph: Dataset): Promise<string>;

/** A SHACL validation-report term (see shaclValidate). */
export interface ShaclValidateResult {
  conforms: boolean;
  /** SHACL_Validation.validation_report_to_graph's graph as a Dataset. */
  report: Dataset;
}

/**
 * SHACL Core validation. Needs the npm-entry engine bundle.
 * @param data the data graph
 * @param shapes the shapes graph
 */
export function shaclValidate(
  data: DataInput,
  shapes: DataInput,
  options?: { format?: DataFormat }
): Promise<ShaclValidateResult>;

/**
 * ShEx (Shape Expressions) validation of one focus node against one
 * shape. Needs the npm-entry engine bundle. `null` means "deferred" --
 * outside this engine's decidable ShEx fragment, never a guessed
 * answer.
 * @param schemaJson ShExJ (JSON Schema form), as text
 * @param focus an IRI, "_:label", or an RDF/JS NamedNode/BlankNode term
 * @param shape a shape label (same shapes as focus); omit/null for the
 *   schema's own `start`
 */
export function shexValidate(
  data: DataInput,
  schemaJson: string,
  focus: string | NamedNode | BlankNode,
  shape?: string | NamedNode | BlankNode | null,
  options?: { format?: DataFormat }
): Promise<boolean | null>;

/**
 * RDFS or OWL-RL entailment closure, materialized as a new Dataset
 * (input triples + derived triples). Needs the npm-entry engine
 * bundle. Default graph only.
 */
export function owlClosure(
  data: DataInput,
  mode: 'RDFS' | 'OWL-RL',
  options?: { format?: DataFormat }
): Promise<Dataset>;

/**
 * The CERTIFIED six-rule core-RDFS closure
 * (formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst's
 * `rho_df_closure`): rdfs2/3/5/7/9/11 only, with the machine-checked
 * decides-iff — on fragment inputs the result's simple query answers
 * are exactly the entailed consequences (see
 * docs/theorem-registry.md). Returns N-Triples text plus status.
 * "corerdfs" is this project's API name for the fragment the
 * literature calls ρdf (subPropertyOf/subClassOf/type/domain/range —
 * Muñoz, Pérez & Gutierrez, "Simple and Efficient Minimal RDFS",
 * J. Web Semantics 7(3), 2009).
 */
export function coreRdfsClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string }>;

/**
 * Decidable core-RDFS fragment check (`is_rho_df_frag`, with its F*
 * lemma tying it to the prop the regime theorems quantify over): does
 * the certified path's guarantee apply to this data?
 */
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

/**
 * RDFS-Plus closure (RDF.Entailment.RDFSPlus.fst's `rdfs_plus_closure`):
 * RDFS plus the practical OWL subset — owl:sameAs, owl:inverseOf,
 * Symmetric/Transitive/Functional/InverseFunctionalProperty,
 * equivalentClass/Property ("RDFS-Plus", Allemang & Hendler 2008;
 * "RDFS++", AllegroGraph). Every OWL row carries proved licensing +
 * truth lemmas; no chain-level completeness claim (theorem registry).
 */
export function rdfsPlusClosure(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ ok: boolean; ntriples: string; rounds: number }>;

/**
 * OWL tableau materialisation (formal/fstar/Tableau.fst's
 * `tableau_materialise`): add `i rdf:type <ClassExpression>` for every
 * individual the model-construction reasoner proves is a member of an
 * OWL class expression (someValuesFrom / hasValue / unionOf /
 * intersectionOf, and the named class an equivalentClass restriction
 * defines). Needs the npm-entry engine bundle. Default graph only.
 * `dataset` is input + tableau-derived triples; `addedCount` is how
 * many triples the tableau added.
 */
export function tableauMaterialise(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ dataset: Dataset; addedCount: number }>;

/**
 * OWL DL inconsistency verdict (bin/owl-runner's DL pipeline: OWL-RL
 * closure -> tableau materialise -> OWL-RL closure -> is_inconsistent).
 * `rlAlone` is the plain OWL-RL verdict on the same input, so a caller
 * can see the cases the tableau adds. Needs the npm-entry engine
 * bundle. Default graph only.
 */
export function tableauDlInconsistent(
  data: DataInput,
  options?: { format?: DataFormat }
): Promise<{ inconsistent: boolean; rlAlone: boolean }>;

/**
 * OWL DL consistency verdict via the verified clash-detecting tableau
 * (Tableau.Refute.tableau_consistent over the OWL-RL closure -- the
 * pure verified chain bin/owl-runner runs under `--regime dl`, minus
 * its native-only z3 oracle). Needs the npm-entry engine bundle.
 * Default graph only. `consistent` is three-valued: `false` (a clash on
 * every branch), `true` (a model built), or `null` -- a budget-out, with
 * `reason` naming the fuel cap (never a silent false).
 */
export function owlIsConsistent(
  data: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ consistent: boolean | null; reason?: string }>;

/**
 * OWL entailment check: does `premise` entail `conclusion`? Verified
 * two-path dispatch: `via: "closure"` (the conclusion is in the OWL-RL
 * closure of the premise) or `via: "refutation"` (the negated
 * conclusion is refuted on every goal). Needs the npm-entry engine
 * bundle. Default graph only. `entailed` is `true`, `false`, or `null`
 * (a refutation budget-out, with `reason` naming the cap).
 */
export function owlEntails(
  premise: DataInput,
  conclusion: DataInput,
  options?: { format?: DataFormat; fuel?: number | string }
): Promise<{ entailed: boolean | null; via: 'closure' | 'refutation'; reason?: string }>;

/**
 * Evaluate an RML mapping graph against one logical source's raw data,
 * returning the generated triples as a Dataset. Needs the npm-entry
 * engine bundle. Every triples map in `mapping` reads the SAME
 * `sourceData` -- joins across two different logical sources are out
 * of scope for this entry point.
 * @param mapping the RML mapping graph (Turtle by default)
 * @param sourceData raw JSON or CSV text (not RDF)
 */
export function rmlMap(
  mapping: DataInput,
  sourceData: string,
  sourceKind: 'json' | 'csv',
  options?: { format?: DataFormat }
): Promise<Dataset>;

export interface CsvwOptions {
  /** 'standard' (default): full csvw:TableGroup/Table/Row wrapper;
   *  'minimal': bare cell triples only. */
  mode?: 'standard' | 'minimal';
  /** Base IRI for resolving the metadata's `url` and templates
   *  (default 'file:///'). */
  base?: string;
  /** The tabular file's own URL, used when the metadata carries none
   *  (default 'table.csv'); cell predicates default to
   *  `<tableUrl>#<colName>`. */
  url?: string;
}

/**
 * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert raw tabular
 * data plus an optional CSVW metadata document (JSON text -- '' or
 * omitted infers the schema from the CSV's own header row) into a
 * Dataset. Needs the npm-entry engine bundle. Every table in a
 * multi-table `tables` group reads the SAME `csvText`.
 */
export function csvwToRdf(
  csvText: string,
  metadataJson?: string,
  options?: CsvwOptions
): Promise<Dataset>;

export interface JsonLdOptions {
  base?: string;
  rdfDirection?: string;
  expandContext?: string;
  processingMode?: string;
}

/**
 * Parse a JSON-LD document into a Dataset, with JSON-LD-specific
 * options `parse()` has no room for. Needs the npm-entry engine
 * bundle (plain `parse(text, {format:'jsonld'})` also works for the
 * common case).
 */
export function jsonldToRdf(
  jsonldText: string,
  options?: JsonLdOptions
): Promise<Dataset>;

export interface JsonLdFromRdfOptions {
  useNativeTypes?: boolean;
  useRdfType?: boolean;
  format?: DataFormat;
}

/**
 * Serialize an RDF dataset as an expanded-form JSON-LD document -- the
 * reverse of jsonldToRdf (the verified JSONLD.FromRdf.from_rdf).
 * Returns the parsed JSON-LD value (an array of node objects). Needs
 * the npm-entry engine bundle.
 */
export function jsonldFromRdf(
  data: DataInput,
  options?: JsonLdFromRdfOptions
): Promise<any>;

/**
 * did:key resolution: resolve a `did:key:z6Mk...` (Ed25519) to its DID
 * Document, returned as a Dataset (the verified DID_Key.did_key_document).
 * Needs the npm-entry engine bundle.
 */
export function didKeyResolve(didString: string): Promise<Dataset>;

/**
 * Test whether an XML document is well-formed (Parser_XML). The
 * byte-oriented parser has no DOCTYPE/DTD production, so a document
 * containing a DOCTYPE reports false. Needs the npm-entry engine bundle.
 */
export function xmlWellformed(xmlText: string): Promise<boolean>;

/** The value shape returned by {@link xpathEval}. */
export interface XPathResult {
  resultType: 'nodeset' | 'string' | 'number' | 'boolean';
  count?: number;
  stringValue?: string;
  nodes?: Array<{ kind: string; name: string; value: string }>;
  value?: string | number | boolean;
}

/**
 * Evaluate an XPath 1.0 expression over an XML document
 * (XPath_Eval.eval_xpath_from_root). Needs the npm-entry engine bundle.
 */
export function xpathEval(
  xmlText: string,
  xpathExpr: string
): Promise<XPathResult>;

/**
 * RIF Core forward-chaining saturation, materialized as a new Dataset
 * (input triples + derived triples, default graph only). Needs the
 * npm-entry engine bundle.
 * @param data the premise graph
 * @param rifRulesXml a RIF Core XML rule document
 */
export function rifEval(
  data: DataInput,
  rifRulesXml: string,
  options?: { format?: DataFormat }
): Promise<Dataset>;

// ---------------------------------------------------------------------
// In-memory COTTAS bytes store (docs/designissues/2026-07-06-inmemory-
// bytes-store.md). openCottas()'s handle is NOT a Dataset: rows decode
// lazily as queryCottas() touches them, never materializing the whole
// corpus onto the heap. Needs the npm-entry engine bundle.
// ---------------------------------------------------------------------

/** Open a COTTAS/Parquet artifact's raw bytes as a queryable, read-only store. */
export function openCottas(bytes: Uint8Array | ArrayBuffer | string): Promise<string>;

/**
 * Run a SPARQL 1.1 query against a store opened by openCottas(). No
 * `entail` option and no write overlay (read-only) -- see
 * npm/factoidal/lib/api.js's queryCottas doc comment for the full
 * divergence list from query().
 * @param handle from openCottas()
 */
export function queryCottas(
  handle: string,
  sparql: string
): Promise<Bindings[] | boolean | Dataset>;

/** Release a store opened by openCottas(). */
export function closeCottas(handle: string): Promise<void>;

/**
 * Serialize a dataset to COTTAS/Parquet bytes via the native writer
 * (RDF.CottasStore.BaseWriter.serialize_cottas_v2). Round-trips into
 * openCottas().
 */
export function toCottas(data: DataInput): Promise<Uint8Array>;

// ---------------------------------------------------------------------
// Typed engine functions (#74 npm FP surface). Each is a pure,
// value-in / value-out wrapper over one F*-extracted engine; all need
// the npm-entry bundle.
// ---------------------------------------------------------------------

/**
 * XSLT 1.0 transform (XSLT.Transform.transform): apply `stylesheetXml`
 * to `sourceXml`, returning the serialized result tree.
 */
export function xsltTransform(
  stylesheetXml: string,
  sourceXml: string
): Promise<string>;

/** The exact value a Content MathML expression evaluates to. */
export type MathValue =
  | { kind: 'rat'; num: number; den: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'undef'; reason: string };

/**
 * Evaluate a Content MathML document (MathML.Content.eval_doc_env).
 * `bindings` maps ci-variable names to value strings; pass {} (or
 * omit) for a closed expression.
 */
export function mathmlEval(
  contentMathmlXml: string,
  bindings?: Record<string, string>
): Promise<MathValue>;

/** One XForms model bind (a subset of the §7 MIPs). */
export interface XFormsBind {
  id?: string;
  target: string;
  calculate?: string;
  constraint?: string;
  relevant?: string;
  required?: string;
  readonly?: string;
  type?:
    | 'string' | 'boolean' | 'integer'
    | 'decimal' | 'float' | 'double';
}

/** Per-node validity from an XForms recalculate. */
export interface XFormsNodeValidity {
  target: string;
  value: string;
  typeValid: boolean;
  constraint: boolean;
  relevant: boolean;
  required: boolean;
  readonly: boolean;
  valid: boolean;
}

/**
 * XForms recalculate (XForms.Bind.recalculate): apply the model binds
 * to `instanceXml`, returning the recomputed instance and a validity
 * report per bound node.
 */
export function xformsRecalc(
  instanceXml: string,
  binds: XFormsBind[]
): Promise<{ instance: string; validity: XFormsNodeValidity[] }>;

/**
 * JSON Schema (draft-07) validation (JSONSchema.Validate.validate).
 * The verified validator gives a definite pass/fail/unsupported verdict
 * rather than a per-keyword error list; `errors` carries a single
 * reason string when the result is not a definite pass.
 */
export function jsonSchemaValidate(
  schemaJson: string,
  instanceJson: string
): Promise<{
  valid: boolean;
  result: 'pass' | 'fail' | 'unsupported';
  errors: string[];
}>;

/** One Schematron finding. */
export interface SchematronFinding {
  type: 'assert-fail' | 'report-hit' | 'indeterminate';
  context: string;
  test: string;
  message: string;
  path: string;
  reason?: string;
}

/**
 * Schematron validation (Schematron.Validate.validate): every finding
 * (failed assert, fired report, indeterminate) in pattern-then-document
 * order.
 */
export function schematronValidate(
  schematronXml: string,
  instanceXml: string
): Promise<{ findings: SchematronFinding[] }>;

/**
 * An exact-arithmetic expression in the TOAN JSON codec, mirroring
 * Math.Expr.expr (E_Int/E_Rat/E_Bool/E_Sym/E_App).
 */
export type ToanExpr =
  | { int: number }
  | { rat: [number, number] }
  | { bool: boolean }
  | { sym: string }
  | { app: string; args: ToanExpr[] };

/** Finite summation of `bodyExpr[idx:=lo..hi]`, as Content MathML. */
export function toanSummation(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;

/** Finite product of `bodyExpr[idx:=lo..hi]`, as Content MathML. */
export function toanProduct(
  bodyExpr: ToanExpr,
  idx: string,
  lo: number,
  hi: number
): Promise<string>;

/** Canonical simplification of `expr`, as Content MathML. */
export function toanSimplify(expr: ToanExpr): Promise<string>;

/** Derivative of `expr` w.r.t. `variable`, as Content MathML. */
export function toanDiff(expr: ToanExpr, variable: string): Promise<string>;

/** `expr[variable := value]` simplified, as Content MathML. */
export function toanSubst(
  expr: ToanExpr,
  variable: string,
  value: ToanExpr
): Promise<string>;

/** A matrix/vector cell: an integer or an exact [num, den] rational. */
export type MatrixCell = number | [number, number];

/** The rendered result of a matrix/vector operation. */
export interface MatrixResult {
  /** Math.Matrix.mres_to_string of the result ("undef" on failure). */
  result: string;
  /** The diagnostic reason when the result is undefined, else "". */
  reason: string;
}

/** Exact determinant of a square matrix (Math.Matrix.dyn_determinant). */
export function matrixDeterminant(
  matrix: MatrixCell[][]
): Promise<MatrixResult>;

/** Dot product of two vectors (Math.Matrix.dyn_scalarproduct). */
export function matrixScalarProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/** Cross product of two 3-vectors (Math.Matrix.dyn_vectorproduct). */
export function matrixVectorProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/** Outer product of two vectors (Math.Matrix.dyn_outerproduct). */
export function matrixOuterProduct(
  a: MatrixCell[],
  b: MatrixCell[]
): Promise<MatrixResult>;

/**
 * A fixed-precision decimal (Math.Sigmoid.scaled: mantissa / 10^scale),
 * the same (mantissa, scale) convention SPARQL11.Algebra.parse_to_scaled
 * uses for xsd:decimal literals. `decimal` is the same pair formatted
 * back to a string by SPARQL11_Algebra.format_scaled_value.
 */
export interface ScaledValue {
  mantissa: string;
  scale: string;
  decimal: string;
}

/** Parameters for {@link sigmoidPoints}: decimal-literal strings/numbers. */
export interface SigmoidParams {
  k: number | string;
  x0: number | string;
  l: number | string;
  xmin: number | string;
  xmax: number | string;
  n: number | string;
}

/**
 * n+1 evenly spaced samples of the logistic sigmoid
 * L / (1 + exp(-k*(x - x0))) over [xmin, xmax] (Math.Sigmoid.
 * sigmoid_points). All arithmetic -- argument reduction, the
 * truncated Taylor series, repeated squaring, and the x samples
 * themselves -- runs as exact rational arithmetic inside
 * Math.Sigmoid.fst; see that module's header for the documented error
 * bound on the returned (rounded) values.
 */
export function sigmoidPoints(
  params: SigmoidParams
): Promise<Array<{ x: ScaledValue; y: ScaledValue }>>;

/**
 * Presentation MathML for the sigmoid formula L / (1 + exp(-k*(x - x0))),
 * engine-serialized (MathML.Present.to_presentation_mathml applied to a
 * fixed Math.Expr.expr) -- never hand-written MathML.
 */
export function sigmoidFormulaMathml(): Promise<string>;

// ---------------------------------------------------------------------
// VC Data Integrity crypto (eddsa-rdfc-2022) — the F*-extracted
// VC_DataIntegrity pipeline, its four crypto assume vals realised by
// HACL*'s OWN official WebAssembly build (hacl-wasm). All need the
// npm-entry bundle AND the HACL* wasm backend.
//
// Init story: on the Node entries (index.js/index.mjs and the /wasm
// entry) these typed wrappers AUTO-AWAIT initHacl() on the first VC
// call — a caller never has to remember the init step. In the browser
// (browser.js) the page must initialise HACL* itself first (the
// hacl-wasm URL is page-specific); see browser.js's VC section. Either
// way, an uninitialised backend makes verify THROW, never silently
// return true (#286, the throw-on-uninit contract).
// ---------------------------------------------------------------------

/**
 * SHA-256 of a message string's bytes, as a lowercase hex digest
 * (VC_DataIntegrity.hash_sha256_hex, HACL* SHA-2).
 */
export function vcSha256Hex(message: string): Promise<string>;

/** Derive the Ed25519 public key (hex) from a 32-byte secret key (hex). */
export function vcEd25519SecretToPublic(secretKeyHex: string): Promise<string>;

/** Ed25519 signature (hex) over a hex-encoded message. */
export function vcEd25519Sign(
  secretKeyHex: string,
  messageHex: string
): Promise<string>;

/**
 * Ed25519 verification. Wrong key, tampered signature, altered
 * message, or a malformed-length input all resolve to false — never an
 * exception-hidden true.
 */
export function vcEd25519Verify(
  publicKeyHex: string,
  messageHex: string,
  signatureHex: string
): Promise<boolean>;

/**
 * Create an eddsa-rdfc-2022 Data Integrity proofValue (multibase-z,
 * base58btc) over already-canonicalized inputs — RDFC-1.0 canonical
 * N-Quads of the document and of the proof config (see canonicalize()).
 */
export function vcEddsaCreateFromCanonical(
  secretKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string
): Promise<string>;

/**
 * Verify an eddsa-rdfc-2022 proofValue against canonical inputs. Wrong
 * key, tampered document/config, or tampered proofValue all resolve to
 * false.
 */
export function vcEddsaVerifyFromCanonical(
  publicKeyHex: string,
  canonicalDocument: string,
  canonicalConfig: string,
  proofValue: string
): Promise<boolean>;

/**
 * VC Data Model 2.0 structural conformance check (VC.Credential.fst's
 * vc_check_from_string, F*-verified — 117 pass, 0 fail on the offline
 * vc_stage1 fixture suite). Pure structural validation, no crypto.
 * `v2ctxJson` is the vendored VCDM v2 base context document's raw JSON
 * text (third_party/contexts/credentials-v2.jsonld); `credentialJson`
 * is the raw JSON text of the VC/VP document under test.
 */
export function vcCheckCredential(
  v2ctxJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * credentialSubject presence/shape check, VERSION-AGNOSTIC (Track A1,
 * docs/designissues/2026-07-11-vc-canivc-eecc-plan.md) —
 * VC.Credential.fst's vc_check_credential_subject_from_string. Unlike
 * vcCheckCredential, does not require the VCDM 2.0 base @context to be
 * present/first.
 */
export function vcCheckCredentialSubject(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * DATA_LOSS_DETECTION_ERROR check (Track A1, same plan doc) —
 * VC.Credential.fst's vc_check_no_data_loss_from_string. `credentialJson`
 * must already have any remote @context IRI inlined to the real context
 * object.
 */
export function vcCheckNoDataLoss(
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/**
 * relatedResource digest verification (VCDM 2.0 §5.3) —
 * VC.Credential.fst's vc_check_related_resource_digests_from_string.
 * `registryJson` is a JSON array of {"id", "digestsHex"} entries computed
 * from vendored copies of each known resource's content bytes.
 */
export function vcCheckRelatedResourceDigests(
  registryJson: string,
  credentialJson: string
): Promise<{ valid: boolean; reason?: string }>;

/** Feature probe for the currently available engine bundles. */
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
  /** The sigmoid (Math.Sigmoid) ABI exports are present. */
  sigmoid: boolean;
  /**
   * The VC Data Integrity crypto ABI exports are present. Note: the
   * HACL* wasm backend is still initialised at call time — this flag
   * reports export availability, not that init has run.
   */
  vcCrypto: boolean;
  /** The in-memory COTTAS bytes store exports are present. */
  cottasBytesStore: boolean;
}>;

// ---------------------------------------------------------------------
// Legacy raw surface (single-shot CLI shapes)
// ---------------------------------------------------------------------

/** SPARQL Results JSON term (https://www.w3.org/TR/sparql11-results-json/). */
export interface SrjTerm {
  type: 'uri' | 'bnode' | 'literal' | 'typed-literal';
  value: string;
  'xml:lang'?: string;
  datatype?: string;
}

export interface SparqlResultsJson {
  head: { vars?: string[]; link?: string[] };
  results?: { bindings: Array<Record<string, SrjTerm>> };
  boolean?: boolean;
}

export type OutputFormat =
  | 'json' | 'csv' | 'tsv' | 'xml' | 'table' | 'ntriples';

/**
 * Legacy single-shot API: returns parsed SPARQL Results JSON when
 * output is 'json' (default), the raw output string otherwise.
 */
export function queryRaw(
  dataString: string,
  queryString: string,
  options?: {
    dataFormat?: DataFormat;
    entail?: EntailRegime;
    output?: OutputFormat;
  }
): Promise<SparqlResultsJson | string>;

/** Package version string, e.g. '0.1.0-alpha.0'. */
export const version: string;

declare const _default: {
  parse: typeof parse;
  query: typeof query;
  queryHdt: typeof queryHdt;
  update: typeof update;
  serialize: typeof serialize;
  canonicalize: typeof canonicalize;
  graphs: typeof graphs;
  canonicalHash: typeof canonicalHash;
  shaclValidate: typeof shaclValidate;
  shexValidate: typeof shexValidate;
  owlClosure: typeof owlClosure;
  tableauMaterialise: typeof tableauMaterialise;
  tableauDlInconsistent: typeof tableauDlInconsistent;
  owlIsConsistent: typeof owlIsConsistent;
  owlEntails: typeof owlEntails;
  rmlMap: typeof rmlMap;
  csvwToRdf: typeof csvwToRdf;
  jsonldToRdf: typeof jsonldToRdf;
  jsonldFromRdf: typeof jsonldFromRdf;
  didKeyResolve: typeof didKeyResolve;
  xmlWellformed: typeof xmlWellformed;
  xpathEval: typeof xpathEval;
  rifEval: typeof rifEval;
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
  vcCheckCredential: typeof vcCheckCredential;
  vcCheckCredentialSubject: typeof vcCheckCredentialSubject;
  vcCheckNoDataLoss: typeof vcCheckNoDataLoss;
  vcCheckRelatedResourceDigests: typeof vcCheckRelatedResourceDigests;
  capabilities: typeof capabilities;
  Dataset: typeof Dataset;
  dataFactory: DataFactory;
  queryRaw: typeof queryRaw;
  version: string;
};
export default _default;
