module JSONLD.Loader

// ============================================================================
// JSON-LD remote-context / @import document loading — ASSUME-VAL I/O
// boundary (CLAUDE.md Iron Rule #11, "ASSUME-IO": pure I/O realisations
// of an `assume val` belong in the CONSUMER binary, not in
// ocaml-output/*.ml patches or experimental_ocaml_glue/*.sh, because
// this is a call-out a CLI/runner makes on the library's behalf, not a
// library-internal byte-layout concern).
//
// See docs/designissues/2026-07-04-jsonld-program-lessons.md's "remote
// contexts are suite-local files" decision: the W3C toRdf test suite's
// "remote" contexts are shipped alongside the manifest as ordinary
// files, addressed by manifest-declared / RFC-3986-resolved absolute
// IRIs (e.g. "https://w3c.github.io/json-ld-api/tests/toRdf/c001.jsonld").
// Conformance therefore needs a documentLoader ABSTRACTION — not live
// HTTP — so this assume val is the seam: given an absolute IRI, return
// the fetched document's raw bytes (expected to itself be a JSON
// document, usually `{"@context": {...}}` for a context reference), or
// None if the IRI cannot be resolved/fetched. Real network fetching for
// production use is a follow-up behind this SAME assume val (rule #11
// ASSUME-IO: OCaml curl/socket realisation for native, a JS loader hook
// for the npm wrapper) — it never blocks conformance against the local
// fixture suite.
//
// Realisation (per-consumer, never inside the verified library
// boundary):
//   - bin/jsonld-runner/jsonld_runner.ml (the toRdf manifest runner):
//     maps the W3C suite's fixed base-IRI prefix to
//     third_party/testing/json-ld/tests/ on disk and reads the file —
//     the same fixture-file convention the runner already uses for
//     `input` / `expect` paths (see that file's banner).
//   - Any other CLI entry point (bin/factoidal, a future npm loader
//     hook): realises this as `fun _ -> None` (an honest FAIL on a
//     document that needs a remote context) until a real HTTP/file
//     loader is wired up for that consumer specifically — never a
//     silent wrong answer.
//
// STATUS 2026-07-04 (JSON-LD Phase 5): this module declares the
// boundary only. JSONLD.Context's `context_process` (JString-context
// branch, currently `None // remote context loading: a later phase`)
// and an "@import" term-def member in JSONLD.Expand do NOT yet call
// this — wiring both, plus the jsonld_runner.ml realisation described
// above, is the next slice (tracked for an open GitHub issue per Iron
// Rule #3 once a realisation lands, per this phase's task brief).
// ============================================================================

assume val jsonld_load_document : string -> option string
