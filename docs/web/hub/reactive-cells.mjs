// Shared, DOM-free, runtime-free cell compiler for the documentation
// hub's reactive Observable-style cells.
//
// Imported by BOTH sides so they can never disagree about which
// identifiers a cell references:
//   - docs/_includes/hub.njk (browser): turns each ```observable-js
//     block into a vendored @observablehq/runtime Module variable and
//     lets the runtime topologically order + re-run cells by data
//     dependency.
//   - tests/hub/_helpers.mjs (Node): builds a headless runtime module
//     from a post's cell sequence so cross-cell references can be pinned.
//
// This is a project-owned module (not vendored third-party code); it is
// passthrough-copied to /vendor/hub/reactive-cells.mjs by
// docs/.eleventy.js so the browser can import it same-origin (no CDN).
//
// ---------------------------------------------------------------------
// What it does, and its limits.
//
// An Observable-style *named* cell looks like `name = <expr>` or
// `name = { ...statements...; return v; }`. Everything else (a cell that
// starts with `const`, `return`, `await`, a bare expression statement,
// ...) is an *anonymous* cell, exactly as the hub's cells work today.
//
// For each cell we compute:
//   - name : the declared variable name, or null (anonymous).
//   - refs : the free identifiers the cell body references.
//   - locals : identifiers the cell declares locally (const/let/var,
//              function/arrow params, catch bindings) -- coarse, see below.
//   - body : the async-function body to run (with a `return` supplied
//            for the expression form).
//
// The caller intersects `refs` with the set of KNOWN names (the fixed
// builtins plus every other cell's declared name) to get the cell's
// runtime `inputs`; globals like Math/JSON/console/document are NOT in
// that set, so they stay resolved through ordinary JS scope rather than
// being wired as reactive inputs.
//
// LIMITS (documented, pragmatic -- this is a tokenizer, not a full JS
// parser):
//   * Local-binding detection is regex-based and coarse. It reliably
//     handles `const/let/var x`, simple destructuring targets, function
//     and arrow parameter lists, and `catch (e)`. It does NOT model
//     block scope, so a name declared local anywhere in the cell is
//     treated as local everywhere in that cell. In practice this only
//     matters if a cell shadows a KNOWN name (a builtin or another
//     cell's name), which the hub's cells do not.
//   * Object-literal shorthand keys and computed member names are not
//     specially recognised beyond a `{ key:` / `, key:` skip heuristic.
//   * `return /regex/` immediately after a keyword can be misread as
//     division (regex-vs-divide is undecidable without a parser). Hub
//     cells that need a regex should assign it (`const re = /.../`),
//     where detection is reliable.
//   * Following Observable's own convention, `name = { ... }` is a BLOCK
//     body (write `return` inside it), not an object literal -- use
//     `name = ({ ... })` for an object.
// ---------------------------------------------------------------------

// Reserved words + literals/globals that must never be treated as a
// cell name or wired as a reactive input.
const RESERVED = new Set([
  "abstract", "arguments", "await", "boolean", "break", "byte", "case",
  "catch", "char", "class", "const", "continue", "debugger", "default",
  "delete", "do", "double", "else", "enum", "eval", "export", "extends",
  "false", "final", "finally", "float", "for", "function", "goto", "if",
  "implements", "import", "in", "instanceof", "int", "interface", "let",
  "long", "native", "new", "null", "of", "package", "private", "protected",
  "public", "return", "short", "static", "super", "switch", "synchronized",
  "this", "throw", "throws", "transient", "true", "try", "typeof", "var",
  "void", "volatile", "while", "with", "yield",
  "undefined", "NaN", "Infinity",
]);

function regexAllowed(prev) {
  return prev === "" || "([{,;=:!&|?+-*/%<>^~".includes(prev);
}

// Produce a same-length copy of `src` in which the characters inside
// string/template-text/comment/regex literals are replaced by spaces
// (newlines preserved), but code inside template interpolations
// (`${ ... }`) is kept intact. Identifier and structural scanning then
// runs against this masked text so a keyword inside a string can't be
// mistaken for a reference, and vice-versa.
export function maskSource(src) {
  let out = "";
  let i = 0;
  const n = src.length;
  const stack = []; // template contexts: { braceDepth } ; 0 = literal text
  let prevSig = "";

  while (i < n) {
    const c = src[i];
    const c2 = src[i + 1];
    const top = stack[stack.length - 1];

    // Inside a template literal's TEXT (not an interpolation).
    if (top && top.braceDepth === 0) {
      if (c === "\\") { out += "  "; i += 2; continue; }
      if (c === "`") { out += " "; stack.pop(); prevSig = "x"; i++; continue; }
      if (c === "$" && c2 === "{") { out += "  "; top.braceDepth = 1; i += 2; continue; }
      out += c === "\n" ? "\n" : " ";
      i++;
      continue;
    }

    // Code context (top level, or inside a template interpolation).
    if (c === "/" && c2 === "/") {
      out += "  "; i += 2;
      while (i < n && src[i] !== "\n") { out += " "; i++; }
      continue;
    }
    if (c === "/" && c2 === "*") {
      out += "  "; i += 2;
      while (i < n && !(src[i] === "*" && src[i + 1] === "/")) {
        out += src[i] === "\n" ? "\n" : " ";
        i++;
      }
      if (i < n) { out += "  "; i += 2; }
      continue;
    }
    if (c === '"' || c === "'") {
      const q = c;
      out += " "; i++;
      while (i < n && src[i] !== q) {
        if (src[i] === "\\") { out += "  "; i += 2; }
        else { out += src[i] === "\n" ? "\n" : " "; i++; }
      }
      if (i < n) { out += " "; i++; }
      prevSig = "x";
      continue;
    }
    if (c === "`") {
      out += " "; stack.push({ braceDepth: 0 }); i++;
      continue;
    }
    if (top && top.braceDepth > 0 && c === "{") {
      top.braceDepth++; out += c; prevSig = "{"; i++; continue;
    }
    if (top && top.braceDepth > 0 && c === "}") {
      top.braceDepth--;
      out += top.braceDepth === 0 ? " " : c; // 0 => back to template text
      prevSig = top.braceDepth === 0 ? "x" : "}";
      i++;
      continue;
    }
    if (c === "/" && regexAllowed(prevSig)) {
      out += " "; i++;
      let inClass = false;
      let bailed = false;
      while (i < n) {
        const rc = src[i];
        if (rc === "\n") { bailed = true; break; }
        if (rc === "\\") { out += "  "; i += 2; continue; }
        if (rc === "[") inClass = true;
        else if (rc === "]") inClass = false;
        else if (rc === "/" && !inClass) { out += " "; i++; break; }
        out += " "; i++;
      }
      if (!bailed) while (i < n && /[a-z]/i.test(src[i])) { out += " "; i++; }
      prevSig = "x";
      continue;
    }

    out += c;
    if (!/\s/.test(c)) prevSig = c;
    i++;
  }
  return out;
}

// Detect a leading `name = ...` declaration on the MASKED source.
// Returns { name, valueStart } or null. `valueStart` is the index into
// the ORIGINAL source just past the `=`.
function detectName(masked) {
  const m = /^\s*([A-Za-z_$][\w$]*)\s*=(?![=>])/.exec(masked);
  if (!m) return null;
  if (RESERVED.has(m[1])) return null;
  return { name: m[1], valueStart: m[0].length };
}

function collectRefs(maskedRegion) {
  const refs = [];
  const seen = new Set();
  const re = /[A-Za-z_$][\w$]*/g;
  let m;
  while ((m = re.exec(maskedRegion)) !== null) {
    const id = m[0];
    if (RESERVED.has(id)) continue;
    let p = m.index - 1;
    while (p >= 0 && /\s/.test(maskedRegion[p])) p--;
    const prevCh = p >= 0 ? maskedRegion[p] : "";
    if (prevCh === ".") continue; // member access a.b / a?.b
    let q = m.index + id.length;
    while (q < maskedRegion.length && /\s/.test(maskedRegion[q])) q++;
    const nextCh = maskedRegion[q] || "";
    if (nextCh === ":" && (prevCh === "{" || prevCh === ",")) continue; // obj key
    if (!seen.has(id)) { seen.add(id); refs.push(id); }
  }
  return refs;
}

function collectLocals(masked) {
  const locals = new Set();
  const add = (s) => {
    for (const id of s.match(/[A-Za-z_$][\w$]*/g) || []) locals.add(id);
  };
  let m;
  const declRe = /\b(?:const|let|var)\s+([^=;\n]+?)(?==|;|\bin\b|\bof\b|\n|$)/g;
  while ((m = declRe.exec(masked)) !== null) add(m[1]);
  const fnRe = /\bfunction\b\s*([A-Za-z_$][\w$]*)?\s*\(([^)]*)\)/g;
  while ((m = fnRe.exec(masked)) !== null) { if (m[1]) locals.add(m[1]); add(m[2]); }
  const arrowParenRe = /\(([^)]*)\)\s*=>/g;
  while ((m = arrowParenRe.exec(masked)) !== null) add(m[1]);
  const arrowBareRe = /(?:^|[^.\w$])([A-Za-z_$][\w$]*)\s*=>/g;
  while ((m = arrowBareRe.exec(masked)) !== null) locals.add(m[1]);
  const catchRe = /\bcatch\s*\(([^)]*)\)/g;
  while ((m = catchRe.exec(masked)) !== null) add(m[1]);
  return locals;
}

function buildBody(name, src, valueStart) {
  if (name === null) return src; // anonymous cell: run body verbatim
  const value = src.slice(valueStart);
  const trimmedLeft = value.replace(/^\s+/, "");
  if (trimmedLeft.startsWith("{")) {
    // Observable block-body convention: statements with their own `return`.
    return value;
  }
  // Expression body: strip a trailing `;` so `return ( expr ; );` can't form.
  const expr = value.replace(/;\s*$/, "");
  return "return (\n" + expr + "\n);";
}

/**
 * Analyze one cell's source.
 * @param {string} source
 * @returns {{name: string|null, refs: string[], locals: Set<string>, body: string}}
 */
export function analyzeCell(source) {
  const masked = maskSource(source);
  const nameInfo = detectName(masked);
  const name = nameInfo ? nameInfo.name : null;
  const valueStart = nameInfo ? nameInfo.valueStart : 0;
  const refRegion = name ? masked.slice(valueStart) : masked;
  return {
    name,
    refs: collectRefs(refRegion),
    locals: collectLocals(masked),
    body: buildBody(name, source, valueStart),
  };
}

/**
 * The reactive inputs to wire for a cell: its referenced identifiers
 * that are KNOWN (a builtin or another cell's name), excluding its own
 * name and its local bindings. Order is stable (first-reference order).
 * @param {{name: string|null, refs: string[], locals: Set<string>}} info
 * @param {Set<string>} knownNames
 * @returns {string[]}
 */
export function cellInputs(info, knownNames) {
  return info.refs.filter(
    (r) => knownNames.has(r) && r !== info.name && !info.locals.has(r)
  );
}

/**
 * Build the runtime variable definition: an async function whose
 * parameters are exactly `inputs` (positionally matching the order the
 * Observable runtime resolves and passes them), running `body`.
 * @param {string[]} inputs
 * @param {string} body
 * @returns {Function}
 */
export function makeDefinition(inputs, body) {
  // eslint-disable-next-line no-new-func
  return new Function(...inputs, "return (async () => {\n" + body + "\n})();");
}
