// rif-demo-client.mjs
// ---------------------------------------------------------------------
// Engine-call logic for demo-rif.html, factored out of the page so it
// is importable and testable under Node without a DOM -- same
// rationale as jsonld-playground-client.mjs (see that file's header
// comment for the fuller explanation of the pattern).
//
// buildRifDemo(driver) follows the same dependency-injection shape as
// buildJsonLdPlayground(driver): the caller supplies the RIF Core
// calls (rifSmoke / rifEval / toNQuads) and this module supplies the
// demo-specific sample content and N-Quads-to-table-row plumbing.
// Two drivers exist:
//   - browser: npm/factoidal/browser.js's rifSmoke() / rifEval() /
//     loadNpmEntry() (fetch-based, used by demo-rif.html against the
//     Pages-mirrored npm package at ../npm/foafos/browser.js);
//   - Node: tests/web-demos/rif_demo_smoke.sh's inline require()-based
//     loader (mirrors npm/factoidal/index.js's loadEntry(), since
//     Node's global fetch does not support file: URLs the way a
//     browser's fetch supports same-origin relative paths).
// Both ultimately call the SAME factoidalNpmEntry.{rifSmoke,rifEval}
// exports (bin/npm-entry/entry_jsoo.ml), which in turn call the SAME
// verified F* functions (RIF_Core_Eval.fixpoint / RIF_Core_Eval.
// one_round / Parser_RIFXML.parse_rif_program) -- so a pass under Node
// is real evidence the browser page computes the same saturated graph,
// not just that some JS glue runs.
//
// !! NO RIF/RDF SEMANTIC LOGIC HERE !! Saturation lives in
// formal/fstar/RIF.Core.{Syntax,Translation,Eval}.fst and RIF-XML
// parsing lives in formal/fstar/Parser.RIFXML.fst. This file only
// shapes sample content and reformats the N-Quads text the F*-verified
// engine already produced -- the same "client-side reformatting only"
// contract documented in jsonld-playground-client.mjs.
// ---------------------------------------------------------------------

'use strict';

// The two-rule RIF Core program encoded in RIF.Core.Eval.fst's
// smoke_program: subClassOf transitivity + rdf:type propagation up the
// class hierarchy, written out as RIF Core XML per the grammar
// Parser.RIFXML.fst actually parses (Document/payload/Group/sentence/
// Forall/Implies/if,then/And/Subclass/Member/Var -- see that file's
// header comment for the full element vocabulary). This is not the
// only legal RIF-XML shape for these rules -- it is the specific
// subset of the grammar the parser accepts today.
export const SAMPLE_RIF_XML = `<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>x</Var></declare>
          <declare><Var>y</Var></declare>
          <declare><Var>z</Var></declare>
          <formula>
            <Implies>
              <if>
                <And>
                  <formula>
                    <Subclass><sub><Var>x</Var></sub><super><Var>y</Var></super></Subclass>
                  </formula>
                  <formula>
                    <Subclass><sub><Var>y</Var></sub><super><Var>z</Var></super></Subclass>
                  </formula>
                </And>
              </if>
              <then>
                <Subclass><sub><Var>x</Var></sub><super><Var>z</Var></super></Subclass>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
      <sentence>
        <Forall>
          <declare><Var>o</Var></declare>
          <declare><Var>c</Var></declare>
          <declare><Var>d</Var></declare>
          <formula>
            <Implies>
              <if>
                <And>
                  <formula>
                    <Member><instance><Var>o</Var></instance><class><Var>c</Var></class></Member>
                  </formula>
                  <formula>
                    <Subclass><sub><Var>c</Var></sub><super><Var>d</Var></super></Subclass>
                  </formula>
                </And>
              </if>
              <then>
                <Member><instance><Var>o</Var></instance><class><Var>d</Var></class></Member>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>
`;

// Same premise graph as RIF.Core.Eval.fst's smoke_input_graph, written
// in Turtle so the page's data textarea is human-editable (rifEval's
// ABI signature wants N-Quads; the page/Node driver converts via the
// engine's own Turtle parser -- see toNQuads() in demo-rif.html /
// rif_demo_smoke.sh, not re-implemented here).
export const SAMPLE_DATA_TTL = `@prefix ex:   <ex:> .
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

ex:alice   rdf:type        ex:Student .
ex:Student rdfs:subClassOf ex:Person  .
ex:Person  rdfs:subClassOf ex:Agent   .
`;

/**
 * @param {{
 *   rifSmoke: () => Promise<object>,
 *   rifEval: (rifXml: string, dataNQuads: string) => Promise<object>,
 *   toNQuads: (turtleText: string) => Promise<string>,
 * }} driver
 */
export function buildRifDemo(driver) {
  function nowMs() {
    if (typeof performance !== 'undefined' && performance.now) return performance.now();
    return Date.now();
  }

  /**
   * Live re-run of RIF.Core.Eval.fst's own smoke program. No user
   * input -- a fixed capability probe.
   * @returns {Promise<object>} the rifSmoke() envelope plus wallMs.
   */
  async function runSmoke() {
    const t0 = nowMs();
    const result = await driver.rifSmoke();
    return { ...result, wallMs: nowMs() - t0 };
  }

  /**
   * Live saturation of caller-supplied RIF-XML rules + Turtle data.
   * @param {string} rifXmlText
   * @param {string} dataTtlText
   * @returns {Promise<object>} the rifEval() envelope plus wallMs.
   */
  async function runCustom(rifXmlText, dataTtlText) {
    const t0 = nowMs();
    const nquads = await driver.toNQuads(dataTtlText);
    const result = await driver.rifEval(rifXmlText, nquads);
    return { ...result, wallMs: nowMs() - t0 };
  }

  return { runSmoke, runCustom };
}

// ---------------------------------------------------------------------
// N-Quads (default graph only -- RIF Core has no named-graph notion)
// -> {subject, predicate, object} rows, for the saturated-graph table.
// Tokenizer adapted from jsonld-playground-client.mjs's
// splitNQuadTerms; RIF's output never carries a fourth (graph) term so
// the row shape here drops it.
// ---------------------------------------------------------------------

/**
 * @param {string} nquads
 * @returns {Array<{subject:string, predicate:string, object:string}>}
 */
export function parseNQuadsToRows(nquads) {
  const rows = [];
  const lines = (nquads || '').split('\n');
  for (const raw of lines) {
    const line = raw.trim();
    if (!line) continue;
    const terms = splitNQuadTerms(line);
    if (terms.length < 3) continue;
    rows.push({ subject: terms[0], predicate: terms[1], object: terms[2] });
  }
  return rows;
}

function splitNQuadTerms(line) {
  const body = line.endsWith('.') ? line.slice(0, -1).trim() : line;
  const terms = [];
  const n = body.length;
  let i = 0;
  while (i < n) {
    while (i < n && /\s/.test(body[i])) i++;
    if (i >= n) break;
    if (body[i] === '<') {
      const end = body.indexOf('>', i);
      if (end < 0) break;
      terms.push(body.slice(i, end + 1));
      i = end + 1;
    } else if (body[i] === '"') {
      let j = i + 1;
      let esc = false;
      while (j < n) {
        if (esc) { esc = false; j++; continue; }
        if (body[j] === '\\') { esc = true; j++; continue; }
        if (body[j] === '"') { j++; break; }
        j++;
      }
      let end = j;
      if (body[end] === '@') {
        end++;
        while (end < n && /[A-Za-z0-9-]/.test(body[end])) end++;
      } else if (body[end] === '^' && body[end + 1] === '^') {
        end += 2;
        if (body[end] === '<') {
          const dtEnd = body.indexOf('>', end);
          end = dtEnd < 0 ? n : dtEnd + 1;
        }
      }
      terms.push(body.slice(i, end));
      i = end;
    } else if (body.startsWith('_:', i)) {
      let j = i + 2;
      while (j < n && !/\s/.test(body[j])) j++;
      terms.push(body.slice(i, j));
      i = j;
    } else {
      let j = i;
      while (j < n && !/\s/.test(body[j])) j++;
      terms.push(body.slice(i, j));
      i = j;
    }
  }
  return terms;
}

/**
 * Diff two N-Quads texts (input vs saturated) into a combined, ordered
 * row list with a `derived` flag: input rows first (in their original
 * order), then any saturated row whose (subject,predicate,object)
 * triple is not present in the input, in saturated-output order.
 * Comparison is done at the parsed-triple level rather than raw line
 * text so N-Quads formatting differences would not cause a false
 * "derived" flag.
 *
 * @param {string} inputNquads
 * @param {string} saturatedNquads
 * @returns {Array<{subject:string, predicate:string, object:string, derived:boolean}>}
 */
export function diffSaturatedRows(inputNquads, saturatedNquads) {
  const inputRows = parseNQuadsToRows(inputNquads);
  const saturatedRows = parseNQuadsToRows(saturatedNquads);
  const key = (r) => `${r.subject} ${r.predicate} ${r.object}`;
  const inputKeys = new Set(inputRows.map(key));
  const out = inputRows.map((r) => ({ ...r, derived: false }));
  for (const r of saturatedRows) {
    if (!inputKeys.has(key(r))) out.push({ ...r, derived: true });
  }
  return out;
}
