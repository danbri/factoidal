/**
 * RDF-WASM Demo — shows how to use the JsRdfGraph API from JavaScript.
 *
 * Usage (after building with wasm-pack):
 *   node demo.js          (Node.js with ESM)
 *   — or open index.html in a browser
 */

import init, { JsRdfGraph } from "../pkg/rdf_wasm.js";

async function main() {
  // Initialise the WASM module (no-op in Node if already loaded)
  await init();

  // ---- Create a graph ----
  const g = new JsRdfGraph();

  // Namespace shortcuts
  const EX   = "http://example.org/";
  const FOAF = "http://xmlns.com/foaf/0.1/";
  const RDF  = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";

  // ---- Populate with FOAF-style data ----
  g.addTriple(`${EX}alice`, `${RDF}type`,    `${FOAF}Person`);
  g.addTriple(`${EX}alice`, `${FOAF}knows`,  `${EX}bob`);
  g.addTriple(`${EX}bob`,   `${RDF}type`,    `${FOAF}Person`);

  // Plain string literal
  g.addTriple(`${EX}alice`, `${FOAF}name`, "Alice");

  // Language-tagged literal
  g.addTripleLang(`${EX}bob`, `${FOAF}name`, "Bob", "en");
  g.addTripleLang(`${EX}bob`, `${FOAF}name`, "Roberto", "it");

  // Typed literal (age as xsd:integer)
  g.addTripleTyped(
    `${EX}alice`,
    `${EX}age`,
    "30",
    "http://www.w3.org/2001/XMLSchema#integer",
  );

  // Blank node
  g.addTriple(`${EX}alice`, `${FOAF}knows`, "_:anon1");
  g.addTriple("_:anon1", `${FOAF}name`, "Charlie");

  // ---- Query & display ----
  console.log("=== Graph stats ===");
  console.log(`Triple count : ${g.size}`);
  console.log(`Blank nodes  : ${g.bnodes()}`);
  console.log();

  console.log("=== N-Triples ===");
  console.log(g.toNTriples());
  console.log();

  console.log("=== Triples about Alice ===");
  console.log(g.findBySubject(`${EX}alice`));
  console.log();

  console.log("=== All foaf:name triples ===");
  console.log(g.findByPredicate(`${FOAF}name`));
  console.log();

  console.log("=== Full graph JSON ===");
  console.log(g.toJSON());
}

main().catch(console.error);
