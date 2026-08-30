#!/usr/bin/env node
// Exercise the generated Lean/WASM artifact's narrow physical IBK2 worker op.
// Usage: node tools/wasm-ibk2-smoke.mjs BLOCK.ibk2 PREDICATE_IRI EXPECTED_ROWS
import fs from "node:fs";
import { loadL4 } from "../docs/web/hub/assets/l4/l4factoidal.js";

const [blockPath, predicate, expectedText] = process.argv.slice(2);
if (!blockPath || !predicate || !expectedText) {
  console.error("usage: wasm-ibk2-smoke.mjs BLOCK.ibk2 PREDICATE_IRI EXPECTED_ROWS");
  process.exit(2);
}
const expected = Number(expectedText);
if (!Number.isSafeInteger(expected) || expected < 0) {
  console.error("EXPECTED_ROWS must be a non-negative integer");
  process.exit(2);
}

const l4 = await loadL4();
const ops = l4.call("ops", []).ops;
if (!ops.includes("scanIBK2Predicate")) {
  throw new Error("generated Lean/WASM dispatch lacks scanIBK2Predicate");
}
const hex = fs.readFileSync(blockPath).toString("hex");
const result = l4.call("scanIBK2Predicate", [hex, predicate]);
if (result.rows !== expected) {
  throw new Error(`scanIBK2Predicate rows=${result.rows}, expected=${expected}`);
}
console.log(JSON.stringify({ version: l4.version(), op: "scanIBK2Predicate", rows: result.rows }));
