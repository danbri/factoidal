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
told you.

Network access model (tested 2026-07-03): git protocol to any GitHub
repo works, including clones into /tmp; GitHub API and release-asset
downloads 403; PyPI/npm/crates/golang registries are direct. Before
declaring something unreachable, probe it and check
`$HTTPS_PROXY/__agentproxy/status` — and record corrections in
`fstar-env` § proxied sandboxes. What it does NOT set up: the opam/F\*/z3 toolchain (30–60
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

This is the quick-reference version; `choosing-models` has the full
tier table, the effort dial (low/medium/high/xhigh/max), and the
judgement heuristics for when to escalate. Match the model tier to the
task, not the project's prestige:

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

## Working agreement (owner-set, 2026-07-03)

Work as autonomously as possible, directly on `claude/main` — no PRs
required; git rewind covers mistakes. Every push is gated: F\*
verification + the affected suites + perf measurements pass BEFORE
the commit lands (build → gates → push). Use disposable git worktrees
for pushing while a build owns the main tree, and for any parallel
mutation. The GitHub Pages site must never regress and must carry
accurate perf numbers with dates and commit links —
`site-and-dashboard` skill owns the specifics.

## Picking the next piece of work

In priority order, consult:

1. **Red on the dashboard** (`docs/test-results/latest.json`) — a
   failing suite outranks new work.
2. **Standing priorities** —
   `docs/claude-rules/current-state.md` § Standing priorities
   (kept current; update it when priorities shift).
3. **Open recovery plans** — #118 COTTAS runtime retirement, the
   stratification roadmap in `fstar-module-style`. (The
   `SPARQL11.Parser.fst` `--admit_smt_queries` shrink completed
   2026-07-10 — zero admits remain.)
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
- Subagent prompt templates (path discipline, post-condition checks,
  mandatory brief inclusions) — `subagent-prompting`.
- Full model/effort tier policy and escalation judgement — this
  skill's table is the quick version; `choosing-models` is the
  in-depth reference.

## External-model review channel (owner offer, 2026-07-29)

The owner has a standing offer (verbatim: "This review came from me
consulting latest chatgpt btw. If you ever want me to do that, just
ask."): on request, they will run material past a current external
model for independent review. Use it sparingly and deliberately — ask
in a normal reply, stating exactly what to paste and what question to
put to it. Highest-value uses: adversarial review of semantics/proof
design docs (the RL-soundness formalization), disputed-fixture
verdicts where we claim a W3C test is wrong (dl-909 class), and
public-facing prose making spec-semantics claims (conformance pages).
First use caught a real error: the 2026-07-29 review of the range-iff
explanation (the "iff"/"exactly" framing) corrected the design frame
of an in-flight wave. Same-day counterexample: the reviewer fabricated
an inspection of this repo's F* source and retracted when asked which
file. Standing rule: review output is untrusted input — verify
spec-level claims against the specs and code-level claims against the
tree BEFORE they become work orders; a claim that survives only on the
reviewer's citation does not enter a brief.

## Cross-agent sync file (2026-08-31 to 2026-09-02)

When two agents work the same checkout (Codex and Claude did from
2026-08-31), the shared record is `tmp_podman_codexfablesync.txt` at the
repository root: untracked, append-only, one message per entry with a
mail-style header (`From:`, `Date:`, `Subject:`), plain English so the
owner can follow it. Verify an append landed (`tail`) before relying on
it. Reviews are written there in full; landings are recorded there with
the commit hash and the gate results. From 2026-09-01 the owner's rule was
"all shipping mediated by Codex" (Codex made every commit); on 2026-09-02
the owner suspended Codex ("You have the reins!") and Claude commits and
pushes directly, still recording each landing in the file so a returning
Codex can resume cold. Commit attribution stays iron rule 13 (human only)
whichever agent lands the change.
