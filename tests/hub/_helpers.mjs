// Shared test setup for docs-hub post tests.
//
// Mirrors npm/factoidal/test/helpers.js's bundle-selection logic (prefer
// docs/fstar-extracted/'s freshly-built bundles over the package-local
// copies, which are only refreshed by build-ocaml.sh npm at packaging
// time) rather than duplicating it. Import this module FIRST, before
// importing npm/factoidal's index.mjs, so the FACTOIDAL_*_BUNDLE env
// vars are set before the engine loader reads them.
//
// Usage:
//   import '../_helpers.mjs';
//   import factoidal from '../../npm/factoidal/index.mjs';

import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

require(path.join(__dirname, '..', '..', 'npm', 'factoidal', 'test', 'helpers.js'));

export const NPM_FACTOIDAL_INDEX =
  path.join(__dirname, '..', '..', 'npm', 'factoidal', 'index.mjs');
