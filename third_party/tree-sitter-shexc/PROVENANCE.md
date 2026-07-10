# tree-sitter-shexc — vendored comparison probe

- Upstream: https://github.com/ericprud/tree-sitter-shexc
- Vendored commit: `27fcb96e8523b803e3fe955cf2bf4a3201543aa7`
  (2026-06-17, "fiddling with node / tree-sitter compatibility")
- License: MIT (see `LICENSE` in this directory; copyright Eric
  Prud'hommeaux)
- Vendored: 2026-07-10, full tree minus `.git/`.

## Role in this repository

This is a **comparison probe** in the sense of
`skills/test-suites/SKILL.md` § comparison probes — the same category
as the Apache Jena ARQ probes. It supplies an independent third-party
ShExC grammar (`src/grammar.json`, generated `src/parser.c`) that
`tests/shexc-treesitter/run.sh` runs differentially against our
F\*-extracted `Parser.ShExC` over the shexTest corpus (positive
`schemas/` fixtures and `negativeSyntax/` grammar-reject fixtures).

It is:

- never product code — nothing here is linked into the verified
  library, the CLI, the runners, or any shipped bundle;
- never inside the verified boundary (iron rule #11 does not apply to
  it because it realises nothing);
- advisory only — disagreements between it and `Parser.ShExC` are
  triaged (our bug / tree-sitter grammar bug / corpus defect), not
  scored on the dashboard.

The conformance number for ShExC grammar rejection comes from
`bin/shex-runner --negative-syntax` running `Parser.ShExC` itself.

## Updating

Re-clone upstream, replace this directory's contents (keep this file),
and update the commit hash + date above. There is no build step needed
for the audit doc (`docs/designissues/2026-07-10-shexc-treesitter-
grammar-audit.md` reads `src/grammar.json` as data); the Node harness
under `tests/shexc-treesitter/` compiles `src/parser.c` via node-gyp
on demand.
