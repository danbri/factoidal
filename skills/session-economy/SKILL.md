---
name: session-economy
description: Work efficiently in a fresh Factoidal session — what the bootstrap hook already set up, token prudence (targeted reads and suite runs instead of shotguns), model and effort selection for subagents, context minimalism, and how to pick the next piece of work toward the project goal. Use at the start of an autonomous session, when planning subagent fan-outs, when a session is burning tokens re-deriving known state, or when deciding what to work on next.
---

# Session economy: spend tokens on the goal, not on rediscovery

The project goal (CLAUDE.md header): a performant, compliant engine
for RDF Core 1.1, RDF/S, OWL, SHACL, RDFC-1.0, and full SPARQL 1.1,
specified in F\* and proven by tests and measurements. Everything in
this skill is about maximising the fraction of a session's budget
that advances that goal.

## What a fresh session already has (don't re-derive it)

The SessionStart hook (`.claude/hooks/session-start.sh` →
`tools/sandbox-bootstrap.sh`, remote sandboxes only) has already:

- initialised the two load-bearing test submodules
  (`third_party/testing/{w3c,rdf-canon}`);
- smoke-checked the committed `bin/<platform>/` binaries and restored
  the `ocaml-output/` symlinks the `tests/local/` scripts expect;
- provisioned the pycottas venv (`_tmp.junk/pycottas-venv`) for the
  COTTAS regression scripts;
- installed/started the F\* MCP daemon on :3700 (when cargo exists);
- printed an orientation block with all of the above.

Trust the orientation block. Do not open a session with a dozen
exploratory `ls`/`cat`/`git log` calls to establish what it already
told you. What it does NOT set up: the opam/F\*/z3 toolchain (30–60
min build) — only needed for editing `.fst`; run the `fstar-env`
skill when a session actually needs it, and background the install
while doing binary-based work.

## Token prudence

- **Read skills on demand, not docs wholesale.** CLAUDE.md is the
  index; `skills/<name>/SKILL.md` is the unit of reading. The
  design-doc corpus (`docs/designissues/`, 200+ files) is archive —
  grep it for a topic, read the one file that matches.
- **Line-range reads for the big modules.** `SPARQL11.Algebra.fst`
  (251 KB), `SPARQL11.Parser.fst` (189 KB), `RDF.Graph.Executable.fst`
  (176 KB) do not fit in a context window and never need to. Grep for
  the symbol, read the surrounding 50–100 lines.
- **Targeted test runs.** `w3c_runner <suite>` for the suites your
  change touches; `--all` only before commit. Dashboard regeneration
  with `--cached` costs seconds; a full `./w3c-tests.sh` costs many
  minutes of OWL-catalog timeouts. Current scores are already in
  `docs/test-results/latest.json` — read them, don't re-run for them.
- **Never truncate evidence** (`tee`, not `tail -N` — anti-pattern
  #16), but do summarise it: report the score line, not the log.
- **Background anything slow** (anti-pattern #19/#20) and keep
  working; cap ad-hoc runs at 10 minutes (#17).

## Model and effort selection for subagents

Match the model tier to the task, not the project's prestige:

| Task shape | Tier |
|---|---|
| Mechanical fan-out: grep sweeps, inventory, file moves, doc-table updates, log triage | smallest/cheapest model, low effort |
| Ordinary implementation against a shipped sketch (anti-pattern #24), test-runner work, glue audits | mid tier |
| F\* proof work, spec design, adversarial verification of a claimed fix, root-cause analysis of soundness bugs | top tier, high effort |

Rules of thumb: if the subagent prompt contains the exact code sketch
and file:line targets (as #24 requires), a mid-tier model executes it
reliably — the intelligence was spent writing the prompt. Never send
a cheap model to modify `.fst` proof obligations. When unsure, omit
the override and inherit the session model.

## Context minimalism

- One subagent = one commit-sized deliverable (#23); the prompt ships
  code sketches + exact paths (#24) — see `subagent-prompting` for
  the copy-paste preamble blocks.
- Subagents return **raw results** (scores, diffs, file lists), not
  essays; the main loop keeps coordination state only.
- Checkpoint plan + state to `.claude-worklog.md` (#18) so context
  compaction costs nothing.
- Skills exist so sessions don't carry operational lore in-context.
  When you learn something durable the hard way, the deliverable
  includes the skill edit — that is this repo's definition of done
  for a lesson.

## Picking the next piece of work

In priority order, consult:

1. **Red on the dashboard** (`docs/test-results/latest.json`) — a
   failing suite outranks new work.
2. **Standing priorities** —
   `docs/claude-rules/current-state.md` § Standing priorities
   (kept current; update it when priorities shift).
3. **Open recovery plans** — #118 COTTAS runtime retirement, the
   stratification roadmap in `fstar-module-style`, the
   `--admit_smt_queries` shrink in `SPARQL11.Parser.fst`.
4. **Issue tracker** hygiene sweeps (`issue-hygiene` skill).

Never invent parallel infrastructure to avoid a hard F\* problem —
that reflex is how the OCaml boundary disaster started
(`ocaml-boundary` skill).

Whatever the task, keep one eye open for perf optimisation
opportunities (`perf-benchmarking` § Perf opportunism) — note them
with a measurement and a file:line, file them, finish your task.

Remember the deliverables are **tools**, not only test scores:
`factoidal query/serve/dump/canonicalize/validate` are the product
surface a user touches. Conformance suites gate them; they are not
the end in themselves.

## What this skill does NOT cover

- The bootstrap hook internals — read `tools/sandbox-bootstrap.sh`.
- Toolchain install — `fstar-env`.
- Long-run wall-clock discipline — `autonomous-time-discipline`.
- Subagent prompt templates — `subagent-prompting`.
