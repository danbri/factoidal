// ESM entry point. Re-exports the CJS implementation so we have one
// source of truth for the Node-side driver. Browsers should import
// `./browser.js` via the `"browser"` export condition instead.
//
// import { query, version } from 'factoidal';
// const r = await query('...', 'SELECT * WHERE { ?s ?p ?o }');

import cjs from './index.js';

export const query   = cjs.query;
export const version = cjs.version;

export default cjs;
