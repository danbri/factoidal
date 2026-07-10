# tree-sitter-shexc

[![CI](https://github.com/ericprud/tree-sitter-shexc/actions/workflows/ci.yml/badge.svg)](https://github.com/ericprud/tree-sitter-shexc/actions/workflows/ci.yml)

[ShExC](https://shex.io/shex-semantics/#shexc) (Shape Expressions Compact
Syntax) grammar for [tree-sitter](https://tree-sitter.github.io/tree-sitter/).

ShExC is the Turtle-like compact syntax for [ShEx](https://shex.io/) shape
schemas, used to describe and validate the structure of RDF graphs. This
grammar covers the full ShExC syntax: directives (`BASE`/`PREFIX`/`IMPORT`),
shape expressions (`AND`/`OR`/`NOT`, `EXTENDS`, `EXTRA`, `CLOSED`), node
constraints and value sets, triple expressions with cardinalities, semantic
actions, and annotations.

## Development

Generate the parser from `grammar.js` and run the test corpus:

```sh
npm install --no-save tree-sitter-cli
npx tree-sitter generate
npx tree-sitter test
```

Or, for the Rust bindings:

```sh
cargo test
```

Test cases live in `test/corpus/*.txt`. To check a specific file:

```sh
npx tree-sitter parse path/to/file.shex
```

## Highlighting

`queries/highlights.scm` provides syntax-highlighting captures
(`@keyword`, `@string`, `@function`, `@variable`, `@type`, `@property`,
`@constant`, `@operator`, etc.) using the standard tree-sitter capture
names, suitable for Neovim, Helix, Zed, and similar editors.

## Editor integration

[`shexc-ts-mode`](https://github.com/ericprud/shexc-mode-for-emacs) is an
Emacs major mode built on this grammar, providing highlighting,
structure-aware indentation, imenu, and xref (jump to shape
definition/references).

## References

- [ShExC grammar in the ShEx specification](https://shex.io/shex-semantics/#shexc)
- [shex.js](https://github.com/shexjs/shex.js) -- the productions here are
  cross-checked against its Jison grammar
  (`packages/shex-parser/lib/ShExJison.jison`)

## License

[MIT](./LICENSE)
