// ESM re-export of api.js (issue #682) — see that file for the full
// picture. This is the bundler-friendly, CSP-safe import path: a
// static `import`, never a fetch + `new Function(src)` eval.
//
//   import { createApi } from '@factoidal/core/api';
//   import entryMod from '@factoidal/core/factoidal-npm-entry.js';
//   const factoidal = createApi(entryMod.factoidalNpmEntry);
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });

import cjs from './api.js';

export const createApi   = cjs.createApi;
export const buildApi    = cjs.buildApi;
export const ParseError  = cjs.ParseError;
export const Dataset     = cjs.Dataset;
export const dataFactory = cjs.dataFactory;
export const version     = cjs.version;

export default cjs;
