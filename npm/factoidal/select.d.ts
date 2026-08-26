// TypeScript declarations for factoidal/select — the backend selector
// (issue #618): one typed surface over both the F* engine (./index.js)
// and the Lean 4 engine (./l4-core.js), with an explicit, observable
// lean/fstar/lean1st/fstar1st/slowcompareboth switch. See select.js for
// the full design rationale and the sub-question decisions.

export type Backend = 'lean' | 'fstar' | 'lean1st' | 'fstar1st' | 'slowcompareboth';

export const BACKENDS: readonly Backend[];

/** Function names the selector can route (see select.js's ALWAYS_IF_ENTRY/CAP_FLAG). */
export const ROUTABLE: readonly string[];

export interface CallOptions {
  /** Per-call override of the selector instance's default backend. */
  backend?: Backend;
  /** lean1st/fstar1st only: function names routed to the OTHER engine
   * regardless of what the primary engine implements. */
  overrideFns?: string[];
}

export interface SingleEngineResult<T> {
  engine: 'lean' | 'fstar';
  backend: Backend;
  value: T;
}

export interface CompareBothResult<T> {
  engine: 'both';
  backend: 'slowcompareboth';
  /** false is a reportable finding, not a thrown error. */
  agree: boolean;
  comparison: { method: string };
  lean: T;
  fstar: T;
}

export type SelectResult<T> = SingleEngineResult<T> | CompareBothResult<T>;

/** { lean: boolean, fstar: boolean } per routable function name, derived live. */
export type CapabilityTable = Record<string, { lean: boolean; fstar: boolean }>;

export function capabilityTable(): Promise<CapabilityTable>;
export function engineSupports(engineApi: unknown, fnName: string): Promise<boolean>;
export function compareValues(
  fnName: string, leanValue: unknown, fstarValue: unknown
): Promise<{ equal: boolean; method: string }>;

export interface SelectorOptions {
  backend?: Backend;
  overrideFns?: string[];
}

export interface Selector {
  readonly backend: Backend;
  readonly overrideFns: string[];
  call(fnName: string, args: unknown[], callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  capabilityTable(): Promise<CapabilityTable>;
  parse(text: string, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  query(data: unknown, sparql: string, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  update(data: unknown, updateText: string, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  serialize(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<string>>;
  canonicalize(data: unknown, callOptions?: CallOptions): Promise<SelectResult<string>>;
  canonicalHash(data: unknown, callOptions?: CallOptions): Promise<SelectResult<string>>;
  graphs(data: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  owlClosure(data: unknown, mode: string, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  owlIsConsistent(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  owlEntails(premise: unknown, conclusion: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  coreRdfsClosure(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  coreRdfsCheck(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  rhoDfClosure(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  rhoDfFragmentCheck(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  rdfsPlusClosure(data: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  shaclValidate(data: unknown, shapes: unknown, options?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  shexValidate(data: unknown, schema: string, focus: unknown, shape?: unknown, callOptions?: CallOptions): Promise<SelectResult<unknown>>;
  /** Lean-only: `backend:'fstar'` throws (formal/fstar has no CL/IKL parser). */
  clParse(clifText: string, callOptions?: CallOptions): Promise<SelectResult<{
    ok: boolean;
    sentences: number;
    pureCL: boolean;
    normalized: string;
  }>>;
}

export function createSelector(options?: SelectorOptions): Selector;
