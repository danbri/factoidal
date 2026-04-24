module.exports = function(eleventyConfig) {
  // Pass-through copy: F*-extracted browser artifacts (js_of_ocaml + wasm_of_ocaml).
  // fstar-extracted/ holds w3c-runner.js (pure JS) and the wasm_of_ocaml loader
  // w3c-runner.wasm.js plus its companion assets directory. Keep directory layout
  // intact so the loader's fetch("./w3c-runner.wasm.assets/code-*.wasm") resolves.
  eleventyConfig.addPassthroughCopy("fstar-extracted");
  // Any wasm demo HTML that lives under fstar-extracted/ will come along for the
  // ride because of the directory pass-through above.

  // Pass-through the test-results directory so the machine-readable CSV/JSON
  // artifacts and the history/ subdirectory land on GitHub Pages alongside
  // index.html. Without this, /factoidal/test-results/latest.csv 404s even
  // though the file exists in the repo — Eleventy was processing index.html
  // but dropping sibling CSV/JSON.
  eleventyConfig.addPassthroughCopy("test-results");

  return {
    dir: {
      input: ".",
      output: "_site",
      includes: "_includes",
      data: "_data"
    },
    markdownTemplateEngine: "njk",
    htmlTemplateEngine: false,
    pathPrefix: "/factoidal/"
  };
};
