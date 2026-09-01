import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const cells = extractObservableCells('46-browser-block-artifacts.md');

test('post46: distinguishes its IBK1 inspector from the newer block worker', async () => {
  const post = runReactivePost(cells, {});
  const format = await post.value('blockFormat');
  assert.deepEqual(format, {
    magic: 'IBK1',
    version: 1,
    headerBytes: 5,
    integrityNow: 'CRC32C framing plus SHA-256 checked against a trusted digest',
    browserBoundary: 'this page inspects IBK1; the Lean-WASM ABI now scans complete IBK2 and IBK3 artifacts',
  });
});
