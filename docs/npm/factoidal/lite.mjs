// ESM entry point for the 'lite' profile (issue #684). Re-exports the
// CJS implementation so we have one source of truth for the Node-side
// driver -- see lite.js's header for the full picture.
//
// import { parse, query } from '@factoidal/core/lite';
// const ds = await parse('@prefix : <http://ex/> . :a :p :b .');
// const rows = await query(ds, 'SELECT * WHERE { ?s ?p ?o }');

import cjs from './lite.js';

export const parse         = cjs.parse;
export const query         = cjs.query;
export const registerExtensionFunction   = cjs.registerExtensionFunction;
export const unregisterExtensionFunction = cjs.unregisterExtensionFunction;
export const clearExtensionFunctions     = cjs.clearExtensionFunctions;
export const registerServiceEndpoint     = cjs.registerServiceEndpoint;
export const clearServiceEndpoints       = cjs.clearServiceEndpoints;
export const update        = cjs.update;
export const openDataset   = cjs.openDataset;
export const serialize     = cjs.serialize;
export const canonicalize  = cjs.canonicalize;
export const graphs        = cjs.graphs;
export const canonicalHash = cjs.canonicalHash;
export const capabilities  = cjs.capabilities;
export const DatasetHandle = cjs.DatasetHandle;
export const ParseError    = cjs.ParseError;
export const Dataset       = cjs.Dataset;
export const dataFactory   = cjs.dataFactory;
export const version       = cjs.version;
export const engine        = cjs.engine;

export default cjs;
