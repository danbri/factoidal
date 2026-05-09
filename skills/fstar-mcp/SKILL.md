---
name: fstar-mcp
description: Use the F* MCP server (FStarLang/fstar-mcp) — a stdio bridge to F*'s --ide protocol — to query proof context, type-check expressions, and tune fuel/ifuel without re-running fstar.exe in batch mode. Use whenever you'd otherwise reach for `fstar.exe X.fst` or `make verify` to chase a single error message; whenever you need the typing context, the assumed hypotheses, or the goal that SMT couldn't discharge at a failure point; whenever you'd guess at fuel/ifuel before re-running. Also use when the user asks "is the F* MCP available", "use fstar-mcp for this", or "interactively check this".
---

# F\* MCP — interactive proof/typecheck instead of batch reruns

The Factoidal repo ships a project-scoped F\* MCP server (config in
`.mcp.json` at repo root — agent-vendor-neutral; Cursor / Continue /
Zed / Cline / Claude Code all read `.mcp.json`). On a fresh sandbox
the bootstrap script `tools/sandbox-bootstrap.sh` installs the binary
via `cargo install --locked --git https://github.com/FStarLang/fstar-mcp.git`
on first session; subsequent sessions reuse it. Under Claude Code the
bootstrap is triggered by `.claude/hooks/session-start.sh` (a one-line
wrapper around `tools/sandbox-bootstrap.sh`); other agent harnesses
can wire the same script into their own session-start hook.

The MCP exposes F\*'s `--ide` stdio protocol. That replaces the batch
loop of "edit `.fst` → `make verify` → wait 30 s+ → read error → guess
fix → repeat" with an interactive session: load a module once, query
the typing/proof context as you make changes, get errors back in
sub-second.

## Why this exists in the toolkit

The pain points it actually solves (verbatim from the case the user
flagged):

1. **Misreading terminal diagnostics.** F\* error lines often point
   at line N when the cause is line N-1 (CLAUDE.md reserved-word
   pitfall). Hardly fixed by MCP — still need to read carefully —
   but `fstar` MCP `lookup_at_position` lets you check what's actually
   bound at the offending position before guessing.

2. **Re-running too much instead of asking narrow questions.** Each
   `fstar.exe X.fst` is a 30 s+ fresh process plus dependency load.
   The MCP keeps the module loaded; ask `:type cp`, `:print-context`,
   `:check-with-options ifuel=N` and get answers in milliseconds.

3. **Lacking proof context at the failing point.** When SMT fails
   you see the goal but not the typing context, hypotheses, or fuel
   in scope. MCP exposes `current_proof_context` / similar so you can
   read the actual constraint set instead of re-deriving from source.

4. **Conflating parse / type / SMT / tactic / fuel / build-order
   errors.** "Could not prove" looks identical for fuel-too-low,
   SMT-too-weak, and broken hypothesis. MCP lets you bump fuel
   directly and re-check the same goal — if it discharges, you knew
   it was fuel.

5. **No memory of per-file F\* session state.** Every
   `fstar.exe` invocation is fresh; `.checked` artifacts cache
   verification but not interactive state. MCP keeps modules + their
   resolved deps in memory across queries.

6. **Treating F\* as a batch compiler.** F\* has had `--ide` for
   years (Emacs / VS Code modes). MCP is the same thing wrapped for
   tool use.

## How Claude should use it

When you would otherwise:

- Run `fstar.exe X.fst` to chase a single error → `create_session`,
  load X.fst, read the diagnostic from the live session.
- Run `make verify` after a small change → re-check just the changed
  module via the MCP. Do `make verify` only as a final pre-commit
  gate.
- Guess at fuel/ifuel and rebuild → `check-with-options
  fuel=N ifuel=M` interactively.
- Wonder what type F\* sees for an identifier → `type_at_position` /
  `lookup_at_position` instead of reading source + guessing.

## When NOT to use it

- The user wants a green build before merging — run `make verify` to
  confirm checked-files match the canonical CI flow. MCP confirms
  individual queries; CI confirms the batch.
- You're modifying OCaml glue / extracted `.ml` / build scripts — F\*
  MCP is irrelevant; use `build-and-test` skill.
- The session is on a contributor's local Mac/laptop without
  `cargo` — the install hook is no-op outside `CLAUDE_CODE_REMOTE`.

## Verification + version pinning gotcha

Anti-pattern #5 (z3 version mismatches). The Makefile passes
`--z3version 4.13.3`. Confirm `fstar-mcp` is sessions-creating with
the same constraint by passing `options: ["--z3version", "4.13.3"]`
to `create_session` for any module that depends on SMT. If MCP
silently uses a different z3, you can get green inside MCP and red
in `make verify` — the worst kind of drift.

## Manual install (non-sandbox)

If you're running locally (no `CLAUDE_CODE_REMOTE`) and want the MCP
anyway:

```bash
cargo install --git https://github.com/FStarLang/fstar-mcp.git
```

That installs to `~/.cargo/bin/fstar-mcp`. The wrapper at
`tools/fstar-mcp-launch.sh` finds it via `$HOME/.cargo/bin` then
`$PATH`. Then restart Claude Code in the repo; project-scoped MCPs
prompt for one-time approval on first session.

## Pairs with

- `fstar-env` — toolchain setup (opam switch, z3 version) that the
  MCP also depends on.
- `build-and-test` — when MCP says a module verifies, this skill is
  the right next step to confirm extraction + native + jsoo build
  paths.
