import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells } from './_helpers.mjs';

test('post48: playground ships one browser-local conversion cell', () => {
  const [cell] = extractObservableCells('48-json-ld-playground.md');
  assert.ok(cell.includes('Factoidal.jsonldToRdf'));
  assert.ok(cell.includes('fn.canonicalize'));
  assert.ok(cell.includes('textarea'));
});
