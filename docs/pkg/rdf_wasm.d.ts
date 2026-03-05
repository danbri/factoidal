/* tslint:disable */
/* eslint-disable */

export class JsRdfGraph {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Add a triple from string components.
     *
     * `subject`   — an IRI string or "_:bnodeId"
     * `predicate` — an IRI string
     * `object`    — an IRI string, "_:bnodeId", or a literal via `literal(...)` helper
     */
    addTriple(subject: string, predicate: string, object: string): void;
    /**
     * Add a triple whose object is a language-tagged literal.
     */
    addTripleLang(subject: string, predicate: string, lexical: string, lang: string): void;
    /**
     * Add a triple whose object is a typed literal.
     */
    addTripleTyped(subject: string, predicate: string, lexical: string, datatype: string): void;
    /**
     * Return all blank-node IDs as a JSON array.
     */
    bnodes(): string;
    /**
     * Remove all triples from the graph.
     */
    clear(): void;
    /**
     * Find triples by predicate IRI; returns JSON array.
     */
    findByPredicate(predicate_iri: string): string;
    /**
     * Find triples by subject IRI; returns JSON array of {s, p, o} objects.
     */
    findBySubject(subject_iri: string): string;
    /**
     * Create an empty RDF graph.
     */
    constructor();
    /**
     * Parse N-Triples data and add all triples to this graph.
     */
    parseNTriples(input: string): number;
    /**
     * Remove a triple by its index (0-based).
     */
    removeByIndex(index: number): void;
    /**
     * Execute a SPARQL SELECT query. Returns JSON with `variables` and `rows`.
     */
    sparqlQuery(query: string): string;
    /**
     * Serialize the full graph as JSON.
     */
    toJSON(): string;
    /**
     * Serialize the graph to N-Triples.
     */
    toNTriples(): string;
    /**
     * Return all triples as a JSON array with s/p/o structure.
     */
    triplesJSON(): string;
    /**
     * Number of triples in the graph.
     */
    readonly size: number;
}

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_jsrdfgraph_free: (a: number, b: number) => void;
    readonly jsrdfgraph_addTriple: (a: number, b: number, c: number, d: number, e: number, f: number, g: number) => [number, number];
    readonly jsrdfgraph_addTripleLang: (a: number, b: number, c: number, d: number, e: number, f: number, g: number, h: number, i: number) => [number, number];
    readonly jsrdfgraph_addTripleTyped: (a: number, b: number, c: number, d: number, e: number, f: number, g: number, h: number, i: number) => [number, number];
    readonly jsrdfgraph_bnodes: (a: number) => [number, number];
    readonly jsrdfgraph_clear: (a: number) => void;
    readonly jsrdfgraph_findByPredicate: (a: number, b: number, c: number) => [number, number];
    readonly jsrdfgraph_findBySubject: (a: number, b: number, c: number) => [number, number];
    readonly jsrdfgraph_new: () => number;
    readonly jsrdfgraph_parseNTriples: (a: number, b: number, c: number) => [number, number, number];
    readonly jsrdfgraph_removeByIndex: (a: number, b: number) => [number, number];
    readonly jsrdfgraph_size: (a: number) => number;
    readonly jsrdfgraph_sparqlQuery: (a: number, b: number, c: number) => [number, number, number, number];
    readonly jsrdfgraph_toJSON: (a: number) => [number, number];
    readonly jsrdfgraph_toNTriples: (a: number) => [number, number];
    readonly jsrdfgraph_triplesJSON: (a: number) => [number, number];
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __externref_table_dealloc: (a: number) => void;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
