import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const cells = extractObservableCells('46-browser-block-artifacts.md');

test('post46: states the actual IBK1 artifact boundary without claiming a browser query engine', async () => {
  const post = runReactivePost(cells, {});
  const format = await post.value('blockFormat');
  assert.deepEqual(format, {
    magic: 'IBK1',
    version: 1,
    headerBytes: 5,
    integrityNow: 'CRC32C framing plus SHA-256 checked against a trusted digest',
    browserBoundary: 'inspect, hash and optionally cache bytes; no block query ABI yet',
  });
});
