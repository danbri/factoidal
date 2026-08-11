// ESM entry point. Re-exports the CJS implementation so we have one
// source of truth for the Node-side driver. Browsers should import
// `./browser.js` via the `"browser"` export condition instead.
//
// import { parse, query, canonicalize, dataFactory } from 'factoidal';
// const ds = await parse('@prefix : <http://ex/> . :a :p :b .');
// const rows = await query(ds, 'SELECT * WHERE { ?s ?p ?o }');

import cjs from './index.js';

export const parse         = cjs.parse;
export const query         = cjs.query;
export const queryHdt      = cjs.queryHdt;
export const update        = cjs.update;
export const serialize     = cjs.serialize;
export const canonicalize  = cjs.canonicalize;
export const graphs        = cjs.graphs;
export const canonicalHash = cjs.canonicalHash;
export const capabilities  = cjs.capabilities;
export const Dataset       = cjs.Dataset;
export const dataFactory   = cjs.dataFactory;
export const queryRaw      = cjs.queryRaw;
export const version       = cjs.version;

// Validation / inference / mapping engines (need the npm-entry bundle).
export const shaclValidate      = cjs.shaclValidate;
export const shexValidate       = cjs.shexValidate;
export const owlClosure         = cjs.owlClosure;
export const coreRdfsClosure    = cjs.coreRdfsClosure;
export const rdfsPlusClosure    = cjs.rdfsPlusClosure;
export const coreRdfsCheck      = cjs.coreRdfsCheck;
export const rhoDfClosure       = cjs.rhoDfClosure;
export const rhoDfFragmentCheck = cjs.rhoDfFragmentCheck;
export const tableauMaterialise = cjs.tableauMaterialise;
export const tableauDlInconsistent = cjs.tableauDlInconsistent;
export const owlIsConsistent    = cjs.owlIsConsistent;
export const owlEntails         = cjs.owlEntails;
export const rmlMap             = cjs.rmlMap;
export const csvwToRdf          = cjs.csvwToRdf;
export const jsonldToRdf        = cjs.jsonldToRdf;
export const jsonldFromRdf      = cjs.jsonldFromRdf;
export const didKeyResolve      = cjs.didKeyResolve;
export const xmlWellformed      = cjs.xmlWellformed;
export const xpathEval          = cjs.xpathEval;
export const rifEval            = cjs.rifEval;

// In-memory COTTAS/Parquet bytes store (need the npm-entry bundle).
export const openCottas        = cjs.openCottas;
export const queryCottas       = cjs.queryCottas;
export const closeCottas       = cjs.closeCottas;
export const toCottas          = cjs.toCottas;

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
export const sigmoidPoints        = cjs.sigmoidPoints;
export const sigmoidFormulaMathml = cjs.sigmoidFormulaMathml;

// VC Data Integrity crypto (eddsa-rdfc-2022, HACL* wasm backend). The
// typed wrappers auto-await initHacl() on first call (see index.js).
export const vcSha256Hex                = cjs.vcSha256Hex;
export const vcEd25519SecretToPublic    = cjs.vcEd25519SecretToPublic;
export const vcEd25519Sign              = cjs.vcEd25519Sign;
export const vcEd25519Verify            = cjs.vcEd25519Verify;
export const vcEddsaCreateFromCanonical = cjs.vcEddsaCreateFromCanonical;
export const vcEddsaVerifyFromCanonical = cjs.vcEddsaVerifyFromCanonical;

export default cjs;
