// Pins every code sample in
// docs/web/hub/32-this-answer-is-a-theorem.md.
//
// The page's cells call the certified rho-df API landed for G3:
// fn.rhoDfFragmentCheck (the decidable fragment hypothesis of the
// regime theorems) and fn.rhoDfClosure (the six-rule operator with
// the decides-iff). Here `fn === factoidal` (the node npm API); the
// browser cells reach the same extracted functions.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '32-this-answer-is-a-theorem.md';

const ORG_TTL = `
  PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
  PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
  PREFIX : <http://example.org/org#>

  :Engineer      rdfs:subClassOf :Employee .
  :Employee      rdfs:subClassOf :Agent .
  :manages       rdfs:domain     :Manager .
  :manages       rdfs:subPropertyOf :worksWith .
  :Manager       rdfs:subClassOf :Employee .

  :ada    rdf:type :Engineer .
  :grace  :manages :ada .
`;

test('post32: the org graph is IN the proved fragment', async () => {
  const r = await factoidal.rhoDfFragmentCheck(ORG_TTL);
  assert.equal(r.ok, true);
  assert.equal(r.fragment, true);
});

test('post32: certified closure derives the two-step subclass fact (rdfs9 twice) and the domain fact (rdfs2)', async () => {
  const closed = await factoidal.rhoDfClosure(ORG_TTL);
  assert.equal(closed.ok, true);
  const nt = closed.ntriples;
  assert.match(nt, /org#ada>\s+<http:\/\/www\.w3\.org\/1999\/02\/22-rdf-syntax-ns#type>\s+<http:\/\/example\.org\/org#Agent>/);
  assert.match(nt, /org#grace>\s+<http:\/\/www\.w3\.org\/1999\/02\/22-rdf-syntax-ns#type>\s+<http:\/\/example\.org\/org#Manager>/);
  // rdfs7: manages ⊑ worksWith lifts the fact
  assert.match(nt, /org#grace>\s+<http:\/\/example\.org\/org#worksWith>\s+<http:\/\/example\.org\/org#ada>/);
});

test('post32: the certified closure is idempotent (saturation is real, not one-round luck)', async () => {
  const once = await factoidal.rhoDfClosure(ORG_TTL);
  const twice = await factoidal.rhoDfClosure(once.ntriples);
  const setOf = (nt) => new Set(nt.split('\n').map(l => l.trim()).filter(Boolean));
  assert.deepEqual(setOf(twice.ntriples), setOf(once.ntriples));
});

test('post32: the ASK over the closure answers true — the theorem-backed answer of the page', async () => {
  const closed = await factoidal.rhoDfClosure(ORG_TTL);
  const dataset = await factoidal.parse(closed.ntriples, { format: 'ntriples' });
  const ask = await factoidal.query(dataset, `
    PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
    PREFIX : <http://example.org/org#>
    ASK { :ada rdf:type :Agent }
  `);
  assert.equal(typeof ask === 'object' ? ask.boolean ?? ask : ask, true);
});

test('post32: the fragment-escape counterexample behaves exactly as finding F-1 states', async () => {
  const escape = `
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    PREFIX : <http://example.org/x#>
    :P rdfs:subPropertyOf rdfs:subPropertyOf .
    :a :P _:b1 .
  `;
  const before = await factoidal.rhoDfFragmentCheck(escape);
  assert.equal(before.fragment, true);
  const closed = await factoidal.rhoDfClosure(escape);
  const after = await factoidal.rhoDfFragmentCheck(closed.ntriples);
  assert.equal(after.fragment, false);
});

test('post32: a literal-object subClassOf graph is OUT of the fragment — the checker is load-bearing', async () => {
  const bad = `
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    PREFIX : <http://example.org/x#>
    :A rdfs:subClassOf "not-a-class" .
  `;
  const r = await factoidal.rhoDfFragmentCheck(bad);
  assert.equal(r.fragment, false);
});

test('post32: the perf cell runs — both closures complete on the 60-class chain and the certified one derives the chain facts', async () => {
  let chain = 'PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nPREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\nPREFIX : <http://example.org/c#>\n';
  for (let i = 0; i < 60; i++) chain += `:C${i} rdfs:subClassOf :C${i + 1} .\n`;
  chain += ':x rdf:type :C0 .\n';
  const six = await factoidal.rhoDfClosure(chain);
  assert.equal(six.ok, true);
  assert.match(six.ntriples, /c#x>\s+<http:\/\/www\.w3\.org\/1999\/02\/22-rdf-syntax-ns#type>\s+<http:\/\/example\.org\/c#C60>/);
  const full = await factoidal.owlClosure(chain, 'RDFS');
  assert.ok(full);
});

test('post32: BROWSER-SURFACE PARITY — every fn.* name the page calls exists in the browser adapter AND the hub fn wrapper', async () => {
  // The reactive harness binds fn to the NODE package, which masked
  // two live-page breakages (fn.rhoDfFragmentCheck, fn.owlClosure had
  // no browser/hub wrappers — found by the owner on the deployed
  // page, 2026-08-07). This text-level pin closes that class: every
  // fn.<name>( reference in the page must appear as an export in
  // npm/factoidal/browser.js and as a method in the hub.njk fn object.
  const { readFileSync } = await import('node:fs');
  const page = readFileSync(new URL('../../docs/web/hub/' + POST_FILE, import.meta.url), 'utf8');
  const adapter = readFileSync(new URL('../../npm/factoidal/browser.js', import.meta.url), 'utf8');
  const hub = readFileSync(new URL('../../docs/_includes/hub.njk', import.meta.url), 'utf8');
  const names = [...new Set([...page.matchAll(/\bfn\.([A-Za-z_][A-Za-z0-9_]*)\s*\(/g)].map(m => m[1]))];
  assert.ok(names.length >= 4, `expected the page to call several fn.* functions, found ${names}`);
  for (const name of names) {
    // The hub fn object must define a wrapper method (async name( ... ).
    const inHub = new RegExp(`async\\s+${name}\\s*\\(`).test(hub);
    assert.ok(inHub, `fn.${name} used by the page has no wrapper in docs/_includes/hub.njk's fn object`);
    // If that wrapper delegates to a same-named Factoidal.* function,
    // the browser adapter must export it (fn.parse delegates to
    // toRdf etc., so same-name delegation is the only case checked).
    if (new RegExp(`Factoidal\\.${name}\\s*\\(`).test(hub)) {
      const inAdapter = new RegExp(`export\\s+(async\\s+)?function\\s+${name}\\b`).test(adapter);
      assert.ok(inAdapter, `hub fn.${name} delegates to Factoidal.${name}, which npm/factoidal/browser.js does not export`);
    }
  }
});

test('post32: every observable-js cell in the page parses and runs under the reactive harness', async () => {
  const cells = extractObservableCells(POST_FILE);
  assert.ok(cells.length >= 5, `expected at least 5 live cells, found ${cells.length}`);
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  for (const name of post.names) {
    const v = await post.value(name);
    assert.notEqual(v, undefined, `cell '${name}' evaluated to undefined`);
  }
});
