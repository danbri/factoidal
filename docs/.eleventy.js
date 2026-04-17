module.exports = function(eleventyConfig) {
  // Pass-through copy: F*-extracted browser artifacts (js_of_ocaml + wasm_of_ocaml).
  // fstar-extracted/ holds w3c-runner.js (pure JS) and the wasm_of_ocaml loader
  // w3c-runner.wasm.js plus its companion assets directory. Keep directory layout
  // intact so the loader's fetch("./w3c-runner.wasm.assets/code-*.wasm") resolves.
  eleventyConfig.addPassthroughCopy("fstar-extracted");
  // Any wasm demo HTML that lives under fstar-extracted/ will come along for the
  // ride because of the directory pass-through above.

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
