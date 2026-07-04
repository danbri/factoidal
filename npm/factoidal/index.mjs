// ESM entry point. Re-exports the CJS implementation so we have one
// source of truth for the Node-side driver. Browsers should import
// `./browser.js` via the `"browser"` export condition instead.
//
// import { parse, query, canonicalize, dataFactory } from 'factoidal';
// const ds = await parse('@prefix : <http://ex/> . :a :p :b .');
// const rows = await query(ds, 'SELECT * WHERE { ?s ?p ?o }');

import cjs from './index.js';

export const parse        = cjs.parse;
export const query        = cjs.query;
export const update       = cjs.update;
export const serialize    = cjs.serialize;
export const canonicalize = cjs.canonicalize;
export const capabilities = cjs.capabilities;
export const Dataset      = cjs.Dataset;
export const dataFactory  = cjs.dataFactory;
export const queryRaw     = cjs.queryRaw;
export const version      = cjs.version;

export default cjs;
