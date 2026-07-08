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
export const graphs       = cjs.graphs;
export const canonicalHash = cjs.canonicalHash;
export const capabilities = cjs.capabilities;
export const Dataset      = cjs.Dataset;
export const dataFactory  = cjs.dataFactory;
export const queryRaw     = cjs.queryRaw;
export const version      = cjs.version;

// Typed engine functions (#74 npm FP surface).
export const xsltTransform       = cjs.xsltTransform;
export const mathmlEval          = cjs.mathmlEval;
export const xformsRecalc        = cjs.xformsRecalc;
export const jsonSchemaValidate  = cjs.jsonSchemaValidate;
export const schematronValidate  = cjs.schematronValidate;
export const toanSummation       = cjs.toanSummation;
export const toanProduct         = cjs.toanProduct;
export const toanSimplify        = cjs.toanSimplify;
export const toanDiff            = cjs.toanDiff;
export const toanSubst           = cjs.toanSubst;
export const matrixDeterminant   = cjs.matrixDeterminant;
export const matrixScalarProduct = cjs.matrixScalarProduct;
export const matrixVectorProduct = cjs.matrixVectorProduct;
export const matrixOuterProduct  = cjs.matrixOuterProduct;

export default cjs;
