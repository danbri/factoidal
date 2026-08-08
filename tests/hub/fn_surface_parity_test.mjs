// BROWSER-SURFACE PARITY, all posts: every `fn.<name>(` a published hub
// page calls must exist as an `async <name>(` wrapper in
// docs/_includes/hub.njk's fn object, and any wrapper that delegates to
// a same-named `Factoidal.<name>` must be exported by
// npm/factoidal/browser.js.
//
// Why: the reactive node harness binds `fn` to the NODE package, so a
// page can be fully green under `node --test` while its cells reject
// (or silently compute over nothing) in a real browser, where `fn` is
// the hand-curated hub.njk wrapper over the browser adapter. Three
// live breakages of this class shipped before this pin existed:
// fn.rhoDfFragmentCheck and fn.owlClosure (post 32, owner-reported
// 2026-08-07/08) and fn.sigmoidFormulaMathml + fn.sigmoidPoints
// (post 28, found by the 2026-08-08 hub_browser_all.sh sweep).
//
// This is a text-level pin: it proves the names EXIST on the browser
// surface, not that they compute the right values there. Value-level
// browser checks live in tests/web-demos/ (hub_browser_all.sh for
// rejected cells on every post; hub_post32_value_check.sh for post
// 32's cell values).

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';

const HUB_DIR = new URL('../../docs/web/hub/', import.meta.url);
const hub = readFileSync(new URL('../../docs/_includes/hub.njk', import.meta.url), 'utf8');
const adapter = readFileSync(new URL('../../npm/factoidal/browser.js', import.meta.url), 'utf8');

const postFiles = readdirSync(HUB_DIR).filter((f) => /^\d{2}-.*\.md$/.test(f)).sort();

test('fn-surface parity: every fn.* name called by any published hub post has a hub.njk wrapper (and a browser.js export where it delegates by the same name)', () => {
  assert.ok(postFiles.length >= 30, `expected 30+ hub posts, found ${postFiles.length}`);
  const missingWrapper = [];
  const missingExport = [];
  for (const f of postFiles) {
    const page = readFileSync(new URL(f, HUB_DIR), 'utf8');
    const names = [...new Set([...page.matchAll(/\bfn\.([A-Za-z_][A-Za-z0-9_]*)\s*\(/g)].map((m) => m[1]))];
    for (const name of names) {
      if (!new RegExp(`async\\s+${name}\\s*\\(`).test(hub)) {
        missingWrapper.push(`${f}: fn.${name}`);
        continue;
      }
      if (new RegExp(`Factoidal\\.${name}\\s*\\(`).test(hub)
          && !new RegExp(`export\\s+(async\\s+)?function\\s+${name}\\b`).test(adapter)) {
        missingExport.push(`${f}: fn.${name}`);
      }
    }
  }
  assert.deepEqual(missingWrapper, [],
    'fn.* names with no async wrapper in docs/_includes/hub.njk (cells REJECT live)');
  assert.deepEqual(missingExport, [],
    'hub wrappers delegating to a Factoidal.* function npm/factoidal/browser.js does not export');
});
