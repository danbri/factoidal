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

  // Rewrite cross-refs to .md files inside the rendered HTML so they point
  // at the .md-less URL Eleventy actually emits. Two shape fixes:
  //
  // (1) Strip `.md` extension, add trailing `/`.
  // (2) Prepend `../` — Eleventy's default pretty-URL output places each
  //     page at `dir/page.md` → `_site/dir/page/index.html`, so a sibling
  //     reference `sibling.md` from the new location resolves as a CHILD
  //     of `page/`, not a sibling of `page/` on disk. Prepending `../`
  //     restores sibling semantics.
  //
  // Link sources use bare .md links because they're also readable on
  // GitHub directly; Eleventy's default doesn't rewrite them. Caught
  // 40+ broken links via tests/local/check_pages_links.sh.
  eleventyConfig.addTransform("mdlink-to-slug", function(content, outputPath) {
    if (!outputPath || !outputPath.endsWith(".html")) return content;
    return content.replace(
      /(\bhref=")([^"#?]*)\.md(#[^"]*)?"/g,
      (_m, prefix, path, frag) => {
        if (/^(https?:|mailto:|ftp:|data:|\/)/.test(path)) return _m;
        // `./sibling.md` or `sibling.md` → `../sibling/`
        // `../other-dir/page.md` → `../../other-dir/page/`
        let clean = path.replace(/^\.\//, "");
        return `${prefix}../${clean}/${frag || ""}"`;
      }
    );
  });

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
