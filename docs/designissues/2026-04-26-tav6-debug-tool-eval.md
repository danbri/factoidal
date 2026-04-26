# Tav6 — Eval of `tools/factoidal-debug-query.sh` (2026-04-26)

Subagent Tav6 is evaluating the new `tools/factoidal-debug-query.sh` (8327 bytes,
2026-04-26 22:00). The tool wraps COTTAS corpus setup (`build-debug`,
`build-serializer`, `import-cottas`, `cottas-path`, `cottas-info`), planner
introspection (`explain` -> `factoidal --explain-only`), and an
`ocamldebug`-based reversible-step debugger (`debug` against `factoidal.byte`,
default breakpoint `Factoidal_cli:950`, with the user-visible hints
`step / backstep / reverse`). This is a landed implementation of the
"underused ocamldebug" path called out in
`docs/designissues/debugging-perf-ecosystem.md` Part IV. Eval covers:
existence, sanity (help / `cottas-info` / `explain` on the parliament corpus),
whether reverse-step actually works, overlap with `factoidal --explain`
(c8e317f), and Skill-vs-MCP packaging recommendation. Read-only; no
modifications, no push. Final report goes in chat to parent.
