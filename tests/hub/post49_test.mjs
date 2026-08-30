import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells } from './_helpers.mjs';

test('post49: keeps one local-AI session for repeated proposals', () => {
  const [cell] = extractObservableCells('49-ai-for-local-kg.md');
  assert.match(cell, /let session = null, creating = null/);
  assert.match(cell, /if \(session\) return session/);
  assert.match(cell, /if \(creating\) return creating/);
  assert.match(cell, /String\(a\)\.startsWith\("unavailable"\)/);
  assert.match(cell, /Release local AI/);
  assert.match(cell, /session\?\.destroy\?\.\(\)/);
  assert.doesNotMatch(cell, /setTimeout\(\(\) => controller\.abort\(\), 60000\)/);
  assert.doesNotMatch(cell, /session\.destroy\?\.\(\);\n    } catch/);
});

test('post49: presents a reviewable proposal and runs it only on explicit action', () => {
  const [cell] = extractObservableCells('49-ai-for-local-kg.md');
  assert.match(cell, /Proposal below — it has not run a query\./);
  assert.match(cell, /out\.textContent = String\(proposal\)/);
  assert.match(cell, /named graphs only/);
  assert.match(cell, /LIMIT 20 as the final clause/);
  assert.match(cell, /Review and run this proposal locally/);
  assert.match(cell, /run\.addEventListener\("click"/);
  assert.match(cell, /Factoidal\.queryDataset\(data, query/);
  assert.match(cell, /Only a reviewed read-only SELECT, ASK, CONSTRUCT, or DESCRIBE/);
  assert.match(cell, /INSERT\|DELETE\|LOAD\|CLEAR\|CREATE\|DROP\|COPY\|MOVE\|ADD\|WITH\|USING\|SERVICE/);
  assert.match(cell, /SPARQL requires WHERE before LIMIT/);
  assert.match(cell, /does not declare PREFIX wdt/);
});
