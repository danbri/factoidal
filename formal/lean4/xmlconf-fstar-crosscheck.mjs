// Cross-check harness: run the F*-extracted XML parser (via the npm
// bundle's xmlWellformed) over the same file list the Lean
// `xmlconf-probe` reads, so the two ports can be compared file by file
// rather than only by totals.
//
// Usage:  ls <dir>/*.xml | node xmlconf-fstar-crosscheck.mjs
// Output: one `WF <path>` / `NWF <path>` line per file, matching the
// Lean probe's verdict column.
import { readFileSync } from "node:fs";
import { xmlWellformed } from "../../npm/factoidal/index.mjs";

const paths = readFileSync(0, "utf8")
  .split("\n")
  .map((p) => p.trim())
  .filter((p) => p.length > 0);

let wf = 0;
for (const p of paths) {
  let ok = false;
  try {
    // Read as UTF-8, exactly as the Lean probe does, so an encoding
    // difference cannot masquerade as a parser difference.
    ok = await xmlWellformed(readFileSync(p, "utf8"));
  } catch {
    ok = false;
  }
  if (ok) wf++;
  console.log(`${ok ? "WF " : "NWF"} ${p}`);
}
console.error(
  `summary: ${wf} accepted as well-formed, ${paths.length - wf} rejected as malformed (out of ${paths.length} files)`,
);
