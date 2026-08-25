#!/usr/bin/env node
// docs/web/hub/assets/data/gen-cottas-corpus.mjs
//
// Generates docs/web/hub/assets/data/cottas-corpus.trig -- the fixture
// post 42 (docs/web/hub/42-*.md) fetches and pins. Run once, by hand,
// to (re)produce the committed file:
//
//   node docs/web/hub/assets/data/gen-cottas-corpus.mjs > \
//     docs/web/hub/assets/data/cottas-corpus.trig
//
// The fixture itself is committed (iron rule #9's spirit: a hub page
// works from a clone with no generation step) -- this script exists
// for reproducibility, not as something a page or test runs.
//
// Every value is a pure function of an integer index (Math only, no
// Math.random, no external entropy) so the corpus is byte-identical
// across regenerations and so tests/hub/post42_test.mjs can import
// these SAME functions to compute expected query answers instead of
// hardcoding numbers that could silently drift from the fixture.
//
// Shape: four named graphs under one TriG document --
//   ex:gPeople        -- N_PEOPLE person records (type, name, age,
//                         mbox, memberSince: 5 triples each)
//   ex:gOrgs          -- N_ORGS org records (type, name, location,
//                         founded: 4 triples each)
//   ex:gProjects      -- N_PROJECTS project records (type, name,
//                         budget: 3 triples each)
//   ex:gAffiliations  -- per person: worksFor (-> an org in
//                         ex:gOrgs) + contributesTo (-> a project in
//                         ex:gProjects): 2 triples each -- the
//                         cross-graph links post 42's GRAPH-join cell
//                         queries.
//
// SIZE (measured, dated 2026-08-25, this commit): the task target was
// ~100,000 triples, but at that size the SAME js_of_ocaml engine
// bundle this page loads in the browser (in-process, no OS subprocess
// -- npm/factoidal/lib/engine-js.js's header) took over two minutes to
// PARSE the corpus and did not finish `toCottas()` within a further
// two-minute cap; 10,000 triples already cost 7.5s parse + 14.3s
// `toCottas()`. That is the js_of_ocaml call path's real, measured
// cost, not a network or file-size artifact -- the committed fixture
// stays far under the 6 MB budget at every size tried. N_PEOPLE=500,
// N_ORGS=50, N_PROJECTS=100 below (4,000 triples total) keeps
// fetch+parse+toCottas+every query cell on post 42 comfortably inside
// tests/web-demos/hub_browser_all.sh's 25 s per-post cell-settle
// budget (measured combined total ~13-17s in Node against the same
// bundle; see the post's own prose for the citation). Override via
// CORPUS_N_PEOPLE/CORPUS_N_ORGS/CORPUS_N_PROJECTS env vars to
// regenerate at a different size (e.g. to re-check whether a later
// engine speedup raises this ceiling).

export const EX = 'http://example.org/factoidal/';
export const FOAF = 'http://xmlns.com/foaf/0.1/';
export const ORG = 'http://www.w3.org/ns/org#';
export const XSD = 'http://www.w3.org/2001/XMLSchema#';

export const N_PEOPLE = Number(process.env.CORPUS_N_PEOPLE || 500);
export const N_ORGS = Number(process.env.CORPUS_N_ORGS || 50);
export const N_PROJECTS = Number(process.env.CORPUS_N_PROJECTS || 100);
export const TOTAL_TRIPLES =
  5 * N_PEOPLE + 4 * N_ORGS + 3 * N_PROJECTS + 2 * N_PEOPLE;

// Turtle/SPARQL PN_LOCAL forbids a bare '/' in a prefixed name's local
// part (it would need a backslash escape) -- every local name below is
// slash-free so both the TriG fixture and the SPARQL cells that query
// it can use plain prefixed names (ex:person6789, not ex:person/6789).
export const GRAPH_PEOPLE = EX + 'gPeople';
export const GRAPH_ORGS = EX + 'gOrgs';
export const GRAPH_PROJECTS = EX + 'gProjects';
export const GRAPH_AFFILIATIONS = EX + 'gAffiliations';

// --- Deterministic field formulas (i, j, k are 1-based ids) ---------

export function personName(i) { return `Person ${i}`; }
export function personAge(i) { return 20 + (i % 50); } // 20..69
export function personMbox(i) { return `person${i}@example.org`; }
export function personMemberSince(i) { return 2000 + (i % 26); } // 2000..2025
export function orgIdForPerson(i) { return 1 + (i % N_ORGS); }
export function projectIdForPerson(i) { return 1 + (i % N_PROJECTS); }

export function orgName(j) { return `Org ${j}`; }
export function orgLocation(j) { return `City ${j % 100}`; }
export function orgFounded(j) {
  const year = 1950 + (j % 75);
  const month = 1 + (j % 12);
  const day = 1 + (j % 28);
  const pad = (n) => String(n).padStart(2, '0');
  return `${year}-${pad(month)}-${pad(day)}`;
}

export function projectName(k) { return `Project ${k}`; }
export function projectBudget(k) { return 50000 + ((k * 733) % 950000); }

// --- TriG rendering ---------------------------------------------------

export function personIri(i) { return `ex:person${i}`; }
export function orgIri(j) { return `ex:org${j}`; }
export function projectIri(k) { return `ex:project${k}`; }

function personBlock(i) {
  return (
    `${personIri(i)} a foaf:Person ;\n` +
    `  foaf:name "${personName(i)}" ;\n` +
    `  foaf:age "${personAge(i)}"^^xsd:integer ;\n` +
    `  foaf:mbox <mailto:${personMbox(i)}> ;\n` +
    `  ex:memberSince "${personMemberSince(i)}"^^xsd:gYear .\n`
  );
}

function orgBlock(j) {
  return (
    `${orgIri(j)} a org:Organization ;\n` +
    `  foaf:name "${orgName(j)}" ;\n` +
    `  org:location "${orgLocation(j)}" ;\n` +
    `  ex:founded "${orgFounded(j)}"^^xsd:date .\n`
  );
}

function projectBlock(k) {
  return (
    `${projectIri(k)} a ex:Project ;\n` +
    `  foaf:name "${projectName(k)}" ;\n` +
    `  ex:budget "${projectBudget(k)}"^^xsd:integer .\n`
  );
}

function affiliationBlock(i) {
  return (
    `${personIri(i)} org:worksFor ${orgIri(orgIdForPerson(i))} ;\n` +
    `  ex:contributesTo ${projectIri(projectIdForPerson(i))} .\n`
  );
}

export function generateTrig() {
  const parts = [];
  parts.push(
    `@prefix ex: <${EX}> .\n` +
    `@prefix foaf: <${FOAF}> .\n` +
    `@prefix org: <${ORG}> .\n` +
    `@prefix xsd: <${XSD}> .\n\n`
  );

  parts.push('ex:gPeople {\n');
  for (let i = 1; i <= N_PEOPLE; i++) parts.push(personBlock(i));
  parts.push('}\n\n');

  parts.push('ex:gOrgs {\n');
  for (let j = 1; j <= N_ORGS; j++) parts.push(orgBlock(j));
  parts.push('}\n\n');

  parts.push('ex:gProjects {\n');
  for (let k = 1; k <= N_PROJECTS; k++) parts.push(projectBlock(k));
  parts.push('}\n\n');

  parts.push('ex:gAffiliations {\n');
  for (let i = 1; i <= N_PEOPLE; i++) parts.push(affiliationBlock(i));
  parts.push('}\n');

  return parts.join('');
}

// Run directly (not imported): print the corpus to stdout.
if (import.meta.url === `file://${process.argv[1]}`) {
  process.stdout.write(generateTrig());
}
