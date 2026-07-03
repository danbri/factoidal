# Quarantine — do not use

Dead-end artifacts kept only where a design doc still cites them.
Nothing here is built, tested, or load-bearing.

The Rust-era artifacts that used to live here (the `rdf-wasm/` crate,
its `docs-wasm/` demo site, `docs-history/`, `CLAUDE.md.old`) were
deleted on 2026-07-03 — that whole implementation predated the
F\*-is-the-product pivot (Iron Rules #1–#2) and was a mistake before
the real work began. Recover from git history if ever needed
(`git log --diff-filter=D -- junk/do_not_use/`).

What remains and why:

- `c-output/` — the 2026-03 pre-Low\* KaRaMeL C-extraction pilot,
  preserved as a reference by
  `docs/designissues/2026-05-07-c-build-and-roaring-plan.md`.
- `hand_coded_parsers/` — hand-written OCaml parsers; the war-story
  evidence behind anti-pattern #1 (parsers belong in F\*).
- `rdfcore11.fstar.txt`, `sparql11.fstar.txt` — the earliest text-only
  F\* spec drafts, superseded by `formal/fstar/*.fst`.
- `docs-fstar-extracted/`, `ocaml-output-js/` — early js_of_ocaml
  output snapshots.
