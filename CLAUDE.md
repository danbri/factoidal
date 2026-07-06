# Factoidal — Verified RDF/SPARQL from F\*

A formally verified RDF/SPARQL implementation. The **F\* specifications are
the product**. Executable code is obtained by **extraction**, not by
hand-writing Rust/JS/OCaml/anything that "mirrors" a spec.

**Goal:** a performant, compliant engine for RDF Core 1.1 (all concrete
syntaxes), RDF/S, OWL, SHACL, RDFC-1.0 canonicalization, and full
SPARQL 1.1 (query, update, protocol, results) — specified in F\*,
extracted to native/JS/wasm (and C via KaRaMeL), with correctness and
speed each proven by test suites and measurements, never by assertion.
Standing priorities: `docs/claude-rules/current-state.md` § Standing
priorities.

> **CLAUDE.md is short on purpose.** Operational detail lives in
> per-topic skill docs (`skills/<name>/SKILL.md` —
> [agentskills.io](https://agentskills.io) format, vendor-neutral) and
> design docs (`docs/designissues/`). The rules below are the ones
> every session must have in working memory. The rest is one click
> away — the `## Skills` section at the bottom of this file lists what
> exists, follow the link when a topic comes up.

## :warning: F\* Syntax Traps :warning:

Full examples + more traps: [`skills/fstar-module-style/SKILL.md`](skills/fstar-module-style/SKILL.md).
The two that corrupt files silently:

1. **F\* block comments `(* ... *)` NEST.** A stray `*)` inside a
   comment (e.g. quoting `construct(*)`) closes it early and F\*
   reports a syntax error **hundreds of lines later**. Never put `*)`
   or `(*` inside a block comment — reword ("COUNT-star") or use `//`
   line comments. Same trap in OCaml: write `(F-star)`, not `(F*)`.
2. **Reserved-ish identifiers with off-by-one errors.** `total`,
   `synth`, `in_mem`, and anything a parser can read as a dangling
   `in` are rejected with the error pointing at the line **after**
   (or below) the offender. Prefix with the domain noun
   (`triples_total`, `mem_dataset`). On any unexplained "Syntax
   error", check the line *above* the reported one first.

## Iron Rules

1. **F\* is the source of truth.** All RDF/SPARQL logic lives in `.fst` files.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml`
   or KaRaMeL for C/WASM. Never vibe-code an implementation that "mirrors"
   the spec.
3. **`assume val` = acknowledged gap.** Every `assume val` must have a
   stub patch in
   `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
   named `<issue>_<description>.sh` with a corresponding open GitHub
   issue. No silent holes.
4. **Parsers belong in F\*.** RDF format parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) are F\*-implemented and
   extracted. New parsers MUST be written in F\* first.
5. **Full SPARQL 1.1 is the target.** Query, Update, Protocol, SERVICE,
   all result formats. Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`,
   `.ttl` from disk. No synthetic queries "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of
   what F\* defines. Add functionality in F\* first, then extract.
8. **RDF semantics are not optional.** rdf-mt tests verify literal
   equivalence, datatype handling, language-tag normalization, RDFS
   closure rules. Core requirements, not "just inference."
9. **Commit compiled binaries.** `bin/<platform>/factoidal` and
   `bin/<platform>/w3c_runner` are committed so a fresh clone runs
   tests without an F\* toolchain. `ocaml-output/` symlinks point at
   the current platform's `bin/` dir. Do not gitignore binaries.
10. **No `--lax`.** All F\* must verify under z3 4.13.3 with no `--lax`,
    no `--admit_smt_queries`, no escape-hatch flags.
11. **Inside the verified library boundary, OCaml is `assume val`
    realisations only.** Hand-written `.ml` in
    `formal/fstar/ocaml-output/*.ml` and patches in
    `formal/fstar/experimental_ocaml_glue/*.sh` may only realise
    `assume val` declarations: pure I/O (file/clock/socket),
    host-engine call-outs (e.g. regex), or vendored crypto primitives.
    Byte-layout for a companion file is **not** acceptable here — the
    byte assembly belongs in F\* (`serialize : data -> Tot (list u8)`),
    and the OCaml side reduces to `write_bytes`. Consumer tools (CLI,
    runners, HTTP entry points) are not part of the verified library
    and belong in `bin/<consumer>/`.

    **Recovery plan + boundary audit + I/O verification pattern:**
    - [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](docs/designissues/2026-05-07-query-planning-fstar-recovery.md)
    - [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](docs/designissues/2026-05-07-io-verification-and-third-party.md)

    **Until** the boundary audit completes and recovery Phase 9 lands,
    the project carries the qualifier "**parser and algebra spec
    verified in F\*; on-disk backend has unverified OCaml-side
    optimization layers being migrated back to F\* (see fstar-purity-
    unwind.md)**" on READMEs, demo pages, talks, and PR descriptions.
12. **Activate the F\* opam switch before any F\* work.**
    `eval $(opam env --switch=fstar)` — every shell, every time, before
    `make verify` / `build-ocaml.sh` / `fstar.exe`. If `fstar.exe` is
    missing from PATH, stop and activate; do not burn time on partial
    builds. See the `fstar-env` skill for setup.
13. **No Claude attribution in git commits.** No `Co-Authored-By:
    Claude`, no "Generated with Claude Code", no session links, no
    prose crediting Claude in commit messages — this repo policy
    overrides the harness default. Full rule:
    [`skills/github-coauthor-policy/SKILL.md`](skills/github-coauthor-policy/SKILL.md).

## Known sound-but-narrow rewrites

`OWL.QueryRewrite.fst` — N=1 qualified `CE_MaxCardinality` rewrite
emits an anchor triple `?subj P ?_mxqc1_anchor_<k>` to make parent7
pass. The anchor is sound for the SPARQL 1.1 entailment regime suite
(70/70) but silently drops vacuous-truth individuals (zero `P`-edges
satisfy max-1) and OWL Full punned class-individuals. Tracked in
**#236**. Generalise from anchor → UNION as documented there before
relying on this rewrite for OWL DL outside the entailment regime
suite.

## Agent Work Strategy

Use subagents aggressively for parallelism — independent work
(verification + compile + test) runs concurrently. Top-level Claude
coordinates and never blocks the main loop. Use `run_in_background:
true` for long-running ops.

**Per anti-pattern #23/#24:** scope every subagent to a single
commit-sized goal; ship code sketches, not "figure it out". When
dispatching against the COTTAS backend or evaluator, the agent prompt
MUST forbid additions to `experimental_ocaml_glue/` other than the
rule-#11 acceptable forms.

## Anti-patterns (one-line summaries)

Full text + war stories: [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md).
Commit messages and inline comments reference these by number ("per
rule #17").

1. Writing OCaml parsers instead of F\* parsers.
2. Dismissing rdf-mt tests as "needing an inference engine."
3. Reporting misleading test scores (unlabelled numerators/denominators).
4. Building parallel OCaml toolkits instead of extending the F\* spec.
5. Symlinks/hacks for version mismatches (esp. z3) — fix the env.
6. Promoted-type blindness: handle `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool`
   alongside `ER_Term(T_Literal _)` everywhere.
7. Parser/evaluator AST mismatch: grep `SPARQL11_Parser.ml` first.
8. `parse_to_scaled` before `parse_double_to_scaled` — try double-aware
   first; E-notation gets mis-parsed otherwise.
9. Recursive string-function base cases kill metadata — handle the
   single-element case explicitly to preserve lang tags + datatypes.
10. OCaml `Str` regex operates on bytes, not codepoints; unmatched
    group back-refs raise `Not_found`.
11. `build-ocaml.sh compile` does NOT apply `ocaml-patches.sh`. Use
    `extract` after a fresh extraction.
12. `(*` inside F\* comments silently swallows the file. Use `//`.
13. Never edit extracted `.ml` files in `ocaml-output/` directly —
    fix the `.fst` or add a patch.
14. Never `|| true` to swallow shell failures — capture exit code
    explicitly (`CMD_RC=0; cmd || CMD_RC=$?`).
15. Never sneak semantic logic into `ocaml-patches.sh` or `w3c_runner.ml`.
16. Never truncate command output with `tail -N` / `head -N` — use `tee`.
17. Never let ad-hoc parse / SPARQL runs hang — cap at 10 min
    (`timeout 600`). Kill and shrink input on cap trips.
18. Dump in-flight plan to `.claude-worklog.md` at checkpoints.
19. Long-running processes log to `.claude-runs/` with hard wall-clock cap.
20. Never burn clock foregrounding long parses/full builds — background them.
21. Never stall on parallel work in flight; pick the next item.
22. Subagent stall is a checkpoint, not a loss — check `git status`/log.
23. One subagent = one commit = one deliverable.
24. Subagent prompts ship code sketches + file:line + signatures.
25. Never write cryptic score strings. "972/59" without labels is
    banned — write "972 pass, 59 fail (out of 1031)".
26. No sycophantic adjectives in user-facing prose. `honest`,
    `genuine`, `important`, `critical`, `big-picture`, `headline`,
    `key insight`, `key finding`, etc. perform candor instead of
    being clear. The sentence either carries weight or it doesn't.
    Full rule + rewrites in `skills/markdown-style/SKILL.md`.
27. Landing an old-branch agent commit onto a much newer tip silently
    drops `build-ocaml.sh` module-list entries (auto-merge) and
    consumer `.ml` changes — the build exits 0 but the feature isn't
    built. Verify the module list + force ancestor-safe consumer files;
    prefer a dedicated landing agent. Full text: hazard #11 in
    `skills/workflow-gotchas-debugging/SKILL.md`.
28. A hub post's live cells run against the js/npm bundle, not the
    native binary. A docs landing that adds cells calling a new F\*
    feature is NOT docs-only — rebuild the bundle (the js build
    incrementally SKIPS npm-entry; force it) and gate on `node --test
    tests/hub/postNN`. Full text: hazard #12 in the same skill.

## Skills (operational details, on-demand)

Skill files live at `skills/<name>/SKILL.md` in the
[agentskills.io](https://agentskills.io) format — a vendor-neutral
spec adopted by ~30 agent products (Claude Code, Cursor, Codex,
Gemini CLI, Goose, Copilot, OpenHands, Roo, …). `skills/` is the
single source of truth; `.claude/skills/` contains per-skill symlinks
so Claude Code discovers them natively (frontmatter preloaded at
session start). Other harnesses: point your skill discovery at
`skills/` or add your own symlink dir — do not fork the content.
Read the linked file the first time you touch that topic in a
session.

- [`session-economy`](skills/session-economy/SKILL.md) — fresh-session
  bootstrap contract, token prudence, subagent model/effort selection,
  and how to pick the next piece of work. **Read first in autonomous
  sessions.**
- [`session-cost-accounting`](skills/session-cost-accounting/SKILL.md)
  — measure a session's real cost incl. subagent children
  (`tools/session-cost.sh`, agentsview recipe + traps).
- [`skos-integrity`](skills/skos-integrity/SKILL.md) — check a SKOS
  vocabulary against the SKOS Reference integrity conditions using
  the SHACL validator, SPARQL property paths, and OWL-RL closure;
  ships shapes, queries, SKOS OWL axioms, and a valid/broken sample
  vocabulary pair.
- [`session-restore`](skills/session-restore/SKILL.md) — restore a
  fresh/recycled VM to working state in minutes: cache-branch
  inventory (toolchain-cache, checked-cache), what the hook restores
  automatically, skill-symlink regeneration, and the never-again
  rules from the 90-minutes-of-compiles incident.
- [`crypto-policy`](skills/crypto-policy/SKILL.md) — never roll our
  own crypto; HACL\* adoption order for the hash/signature
  `assume val`s (#63), and the wasm compatibility gate.
- [`fstar-env`](skills/fstar-env/SKILL.md) — F\* / opam / z3
  setup and repair.
- [`build-and-test`](skills/build-and-test/SKILL.md) — build,
  extract, compile, run W3C tests.
- [`fast-verify-extract`](skills/fast-verify-extract/SKILL.md) — make
  the verify→extract→compile→test loop fast: .checked cache
  semantics, targeted single-module rebuilds, safe parallelism
  (make -j, never concurrent ad-hoc fstar.exe), CI cache proposals.
  The loop speed is what keeps us validation-guided instead of
  flying dark.
- [`test-suites`](skills/test-suites/SKILL.md) — every suite (W3C,
  OWL, RDFC-1.0, parity, Jena probes, external-suite policy) and the
  score-reporting discipline. **Testing drives everything.**
- [`perf-benchmarking`](skills/perf-benchmarking/SKILL.md) — timing
  harnesses, baselines, observability, profiling policy. Speed is
  measured separately from correctness, always.
- [`site-and-dashboard`](skills/site-and-dashboard/SKILL.md) — the
  11ty site, test-results dashboard, demos, Fly.io endpoint, and the
  registry of progress tables + who updates each.
- [`disk-storage-format`](skills/disk-storage-format/SKILL.md) — how
  data lands on disk: the COTTAS/Parquet base + its 10 sidecars, the
  durable-UPDATE delta log (framing, crash-safety, epoch guard), the
  symlink-current compaction layout, and the exact import/query/
  compact/serve CLI invocations.
- [`fstar-module-style`](skills/fstar-module-style/SKILL.md) — module
  organization (semantic core vs pragmatics), stratification roadmap,
  .fsti policy, syntax traps in full, KaRaMeL-compatible style.
- [`ocaml-boundary`](skills/ocaml-boundary/SKILL.md) — rule #11 in
  depth: the glue taxonomy, patch lifecycle, companion-file byte
  rules, vendoring policy, extraction-target status.
- [`github-and-prs`](skills/github-and-prs/SKILL.md) — gh CLI
  with `--repo danbri/factoidal`, branch + PR conventions.
- [`github-coauthor-policy`](skills/github-coauthor-policy/SKILL.md)
  — no Claude attribution in commit messages (iron rule #13).
- [`repo-tour`](skills/repo-tour/SKILL.md) — directory layout,
  "where does X live?".
- [`fstar-mcp`](skills/fstar-mcp/SKILL.md) — F\* MCP server for
  interactive proof / typecheck queries (replaces batch `fstar.exe`
  reruns for diagnostic work).
- [`mcp-setup-readme`](skills/mcp-setup-readme/SKILL.md) — how the
  repo's MCP wiring is configured (`.mcp.json`, bootstrap script,
  daemon manager, port, transport). Read when adding/debugging the
  MCP plumbing rather than using F* MCP for proofs.
- [`markdown-style`](skills/markdown-style/SKILL.md) — clickable-link
  rules + the no-sycophantic-adjectives rewrite list.
- [`choosing-models`](skills/choosing-models/SKILL.md) — model/effort
  selection per subagent. Core rule: for all coding tasks, judge an
  appropriate lower-power model and run it in a subagent; Fable-class
  sessions orchestrate, gate, and design — they don't type the code.
- [`subagent-prompting`](skills/subagent-prompting/SKILL.md) —
  worktree path discipline + post-condition checks.
- [`workflow-gotchas-debugging`](skills/workflow-gotchas-debugging/SKILL.md)
  — diagnostic playbook for the dev-loop hazards we've actually hit.
- [`autonomous-time-discipline`](skills/autonomous-time-discipline/SKILL.md)
  — wall-clock + Monitor + lock-cleanup pattern for long autonomous
  sessions. Read when kicking long background builds, when "the
  job has been silent for a while," or before a multi-hour solo run.
- [`issue-hygiene`](skills/issue-hygiene/SKILL.md) — keep GitHub
  issues + checklists in sync as PRs land.
- [`jsoo-debug-bundle`](skills/jsoo-debug-bundle/SKILL.md) — build a
  source-mapped JS bundle so browser-only crashes show real OCaml
  stacks.

## Expanded docs (full reference)

- [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md)
  — full anti-pattern text with war stories.
- [`docs/claude-rules/performance.md`](docs/claude-rules/performance.md)
  — perf status + history (current measured throughput; the 2026-04
  slow-Turtle root causes).
- [`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md)
  — F\* inventory, `assume val` table, W3C scores.
- [`docs/code-name-glossary.md`](docs/code-name-glossary.md) — Yod6 /
  Tet3 / Lamed3 / etc. decoder. **No new short-codes** — use
  descriptive names per the recovery plan.
- [`docs/claude-rules/README.md`](docs/claude-rules/README.md) — index
  and the relationship between this file and the expanded docs.
- [`docs/fable-notes-xyz-20260706.md`](docs/fable-notes-xyz-20260706.md)
  — strategy + workflow handoff notes from the 2026-07-06 sessions
  (state of the project, impact ranking, landing discipline, gaps,
  sequencing). Read early in a fresh autonomous session.

## Recovery + planning docs

- [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](docs/designissues/2026-05-07-query-planning-fstar-recovery.md)
  — F\*-only recovery roadmap; replaces the OCaml shadow logic
  (Yod6/Tet3/Lamed3/Mem5/Pe5/Bet7/Tav5/Heth3) with proper F\*
  modules.
- [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](docs/designissues/2026-05-07-io-verification-and-third-party.md)
  — hash-based round-trip verification pattern; HACL\* / EverParse
  vendoring policy; corrected boundary-audit taxonomy.
- [`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`](docs/designissues/2026-05-07-c-build-and-roaring-plan.md)
  — KaRaMeL C-build pilot + Roaring continuation tracks.
