# Factoidal

A linked information system for graph data on the Web: storage, query,
linking, and service over Web protocols. F\* and Lean 4 ground its APIs,
interfaces and protocols in the W3C specifications and in mathematics.

## Writing to the owner

Report in ASD-STE100 Simplified Technical English. Owner:
"only report to me in ASD-STE100 Simplified Technical English."

1. Do not claim honesty. No "to be honest", "to be straight with you",
   "candidly", "the truth is". Owner, 2026-08-24: "Every time you
   highlight your alleged honesty or straightness in a particular
   context wastes tokens undermining everything else you say."
2. Do not report that you obeyed a rule or ignored a hook. Do the
   correct thing and report the result.
3. Use the terminology of the W3C specifications, the RDF/OWL/SPARQL
   literature and the Lean 4 and F\* manuals
   ([`docs/w3c-glossary.md`](docs/w3c-glossary.md)). Do not invent
   terms or code names. No metaphors.
4. Keep it short. The owner reads on a phone. Lead with the result or
   the decision needed. Label every score: "972 pass, 59 fail (out of
   1031)".
5. Refer to tracked work by full GitHub issue URL. Work tracking lives
   in issues; the index is https://github.com/danbri/factoidal/issues/404.
6. Record an owner decision in this file the first time it is given.
7. When you explain how a subsystem works in chat, write the
   explanation into `docs/designissues/` in the same landing and link
   it from the relevant skill. Owner, 2026-09-03: "this and similar
   ought to be recorded properly somewhere I can find it. Ephemeral
   coding logs aren't that place."

How to interpret and record owner instructions:
[`skills/reading-owner-steers/SKILL.md`](skills/reading-owner-steers/SKILL.md).
Prose register, banned words and the emoji palette:
[`skills/markdown-style/SKILL.md`](skills/markdown-style/SKILL.md).

## Goal

Owner, 2026-08-22, verbatim:

> "The key thing is to define APIs and interfaces and protocols
> grounded via F\* and Lean4 in W3C specs and maths. These should be
> implemented faithfully, efficiently, tunably, and formally, but
> don't confuse the spec and the code satisfying it. Even as we use
> F\* and/or Lean 4 to define and implement everything. The use of
> these formal languages gives us, and coding agents, collaborators
> etc., a safe platform for experimentation and variation without
> fear that small improvements will destroy standards compliance."
>
> "If we get this right we may get a good chance of creating SOTA
> technology and a highly optimised, flexible, performant rdf db and
> querying etc environment."

Consequences:

- A specification and its implementation are separate artifacts, even
  when both are written in F\* or Lean. The relation between them is a
  proof or a measurement.
- Performance work is in scope in both trees, provided the
  specification stays fixed and the refinement is proved or measured.
  "It is the spec tree" is not a reason to refuse an optimisation.
- Executable code comes from extraction of the formal source.

Target: RDF 1.1 (all concrete syntaxes), RDFS, OWL, SHACL, RDFC-1.0, and
SPARQL 1.1 (query, update, protocol, results), extracted to native, JS
and wasm (C through KaRaMeL). Standing priorities:
`docs/claude-rules/current-state.md` § Standing priorities.

## F\* syntax traps

Full list: [`skills/fstar-module-style/SKILL.md`](skills/fstar-module-style/SKILL.md).

1. F\* block comments `(* ... *)` nest. A `*)` or `(*` inside a comment
   gives a syntax error hundreds of lines later. Use `//` comments, or
   write "COUNT-star". In OCaml comments write `(F-star)`.
2. Identifiers such as `total`, `synth`, `in_mem` cause a syntax error
   reported on the line after the offender. Prefix them with a domain
   noun (`triples_total`). For an unexplained syntax error, check the
   line above first.

## Iron rules

Commit messages cite these numbers.

1. The formal source is the source of truth. RDF/SPARQL logic lives in
   `.fst` (`formal/fstar`) and `.lean` (`formal/lean4`, `L4Factoidal`)
   files.
2. Code is extracted (`fstar.exe --codegen OCaml`, KaRaMeL, Lean to C
   to wasm). Do not hand-write an implementation that mirrors a spec.
   Optimise inside the formal source, where the refinement can be
   proved.
3. Each `assume val` is either (a) a gap, with a stub patch in
   `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/<issue>_<description>.sh`
   and an open issue, or (b) an allowed realisation under rule 11, in
   `experimental_ocaml_glue/*.sh`. Count them; do not quote a number:
   `grep -rhE '^[[:space:]]*assume val ' formal/fstar --include='*.fst' --include='*.fsti' | wc -l`.
   Inventory: `docs/claude-rules/current-state.md` § assume val
   inventory. Audit: `docs/designissues/fstar-ocaml-boundary-audit.md`.
4. RDF parsers are written in F\* (or Lean) first and extracted.
5. Full SPARQL 1.1 is the target. Do not use 1.0 manifests where 1.1
   exists.
6. Run the real W3C test files from disk. No synthetic tests modelled
   on them.
7. No hand-written JS/Rust/OCaml reimplementation of what F\* defines.
8. RDF semantics (rdf-mt: literal equivalence, datatypes, language
   tags, RDFS closure) are core requirements.
9. Commit compiled binaries: `bin/<platform>/factoidal` and
   `bin/<platform>/w3c_runner`. `ocaml-output/` symlinks point at the
   current platform's `bin/`.
10. No `--lax`, no `--admit_smt_queries`, no other escape flags. All
    F\* verifies under z3 4.13.3. There are no exceptions.
11. Inside the verified library, hand-written OCaml only realises
    `assume val`s: pure I/O, host-engine call-outs (for example regex),
    or vendored crypto. Byte layout belongs in F\*
    (`serialize : data -> Tot (list u8)`); OCaml only writes the bytes.
    Consumer tools (CLI, runners, HTTP) go in `bin/<consumer>/`.
    Details: [`skills/ocaml-boundary/SKILL.md`](skills/ocaml-boundary/SKILL.md),
    [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](docs/designissues/2026-05-07-query-planning-fstar-recovery.md),
    [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](docs/designissues/2026-05-07-io-verification-and-third-party.md).
    Until recovery Phase 9 lands, READMEs, demos, talks and PR
    descriptions carry this qualifier: "parser and algebra spec
    verified in F\*; on-disk backend has unverified OCaml-side
    optimization layers being migrated back to F\* (see
    fstar-purity-unwind.md)".
12. Run `eval $(opam env --switch=fstar)` in each shell before F\*
    work. If `fstar.exe` is not on PATH, stop and activate it. Setup:
    [`skills/fstar-env/SKILL.md`](skills/fstar-env/SKILL.md).
13. Commits name the responsible human only. Owner, 2026-08-26: "all
    attributions are to responsible human only". No Claude trailers,
    no generated-with lines, no session links, no Claude author or
    committer identity. `.claude/settings.json` turns off Claude Code's
    attribution, and `tools/sandbox-bootstrap.sh` sets the repo-local
    identity. Details:
    [`skills/github-coauthor-policy/SKILL.md`](skills/github-coauthor-policy/SKILL.md).
14. When you repair an error in our working method, update CLAUDE.md
    or the relevant skill in the same landing. Name the error, its
    date and its cost. Model:
    [`skills/measuring-inference/SKILL.md`](skills/measuring-inference/SKILL.md).
15. Do not skip a gate because its tool is absent. Install the tool
    and run the gate. Deno and Lean install in under a minute; recipes
    in [`skills/session-restore/SKILL.md`](skills/session-restore/SKILL.md)
    § Gate tools.

Lean: run every `lake` command with `formal/lean4/` as its working
directory, in the same command (`cd formal/lean4 && lake build`). Never
run `lake` at the repository root. Details:
[`skills/factoidal-lean-basics/SKILL.md`](skills/factoidal-lean-basics/SKILL.md).

## Owner decisions

Quoted verbatim. Do not paraphrase.

**Port functionality, not files** (2026-08-24): "the key thing is to
port functionality not files. The port was partly motivated by fear F\*
version was accumulating cruft and this may help to clear it." Module
counts are a progress indicator. Where an F\* module is cruft, implement
the function correctly in Lean and mark the F\* file.

**Priority order** (2026-08-24): "Good to progress Cottas but I suggest
core of rdf/s, sparql, owl, rif, csvw, shacl, shex, xml, xpath, cslt,
schematron are more urgent. Cottas rdf store didn't really get mature
enough to use in f\*, we may ship Factoidal and make a separate
FactoidalDB repo to focus attention on the issues." ("cslt" means
XSLT.)

**Lean 4 is the full-scope target** (2026-08-29): "The Lean port is
only a week old, but improved quickly enough that I am inclined to make
the switch. It hasn't yet been applied to the full scope of Factoidal
but that is my intent." This does not claim Lean/F\* parity. Keep the F\*
path executable as a differential oracle until the Lean functionality
and gates land.

**Hex layer, issue 566** (2026-08-24; settled, do not ask again): "Yeah
DO NOT PORT THAT TERRIBLE HEX CRAP!!!" "Fix it upstream in F\* and do
not worry about legacy. You can defer that for now just mark the F\*
file as fucked and link to GitHub. Do it right in Lean." Lean
implements the byte format directly. The F\* file carries a header
linking https://github.com/danbri/factoidal/issues/566. The same ruling
applies to `Parquet.Footer`.

**RDF.NQuads.Streaming and SPARQL11.Parser.AskBgpRoundTrip**
(2026-08-24): "These are important. We need performant nquads and sparql
implementations across all surfaces!" "Rdf.nquads.streaming it is ok to
make the changes, ideally both f\* and lean4 behave same". Where Lean
changed, F\* follows.

**Prove over an abstraction** (2026-08-24): "Ideally we should prove it
over an abstraction of both, in lean4 and also optionally f\*". State a
shared property once (a typeclass or parameterised structure in Lean)
and instantiate it.

**No users** (2026-08-24, restated 2026-08-26): "We have no users so rip
it up where it is crap." "it has zero audience and users so far."
Backwards compatibility and migration cost are not arguments. When a
design is wrong, change it.

**A stated shortfall is a failing test plus an open issue**
(2026-09-07): "You must use failing tests, annotated to show the
expected failure, and an associated open github issue to track the
shortfall." Each "not implemented", "not yet" or "known gap" in code or
docs needs (1) an open issue, by full URL, and (2) a test marked as an
expected failure naming that issue, which turns the suite red if it
starts to pass. First case: https://github.com/danbri/factoidal/issues/676,
`npm/factoidal/test/xmpp.test.mjs`. Conventions:
[`skills/test-suites/SKILL.md`](skills/test-suites/SKILL.md) § Expected failures.

## Subagents and worktrees

- Run independent work in parallel subagents, in the background. One
  subagent, one commit-sized deliverable; give it file paths, line
  numbers, signatures and a code sketch. Prompting rules:
  [`skills/subagent-prompting/SKILL.md`](skills/subagent-prompting/SKILL.md).
  Model choice: [`skills/choosing-models/SKILL.md`](skills/choosing-models/SKILL.md).
- A brief for COTTAS or evaluator work forbids additions to
  `experimental_ocaml_glue/` other than rule 11 forms.
- Check `df -h /` before a worktree agent. At most three worktrees at a
  time; each holds 1.5 to 2.8 GB. Before you remove one, check
  `git -C <path> log --oneline origin/claude/main..HEAD`. Remove it in
  the same turn you land its commit. (Hazard 36 in
  `skills/workflow-gotchas-debugging`.)
- A worktree agent first runs `tools/ensure-test-env.sh`. Do not trust a
  score from a checkout where it exits 1.

## Anti-patterns

Full text: [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md)
(entries 26 to 34 are in its last section). Hazard numbers refer to
[`skills/workflow-gotchas-debugging/SKILL.md`](skills/workflow-gotchas-debugging/SKILL.md).

1. Writing OCaml parsers instead of F\* parsers.
2. Dismissing rdf-mt tests as "needing an inference engine".
3. Unlabelled test scores.
4. Parallel OCaml toolkits instead of extending the F\* spec.
5. Symlinks or hacks for version mismatches (z3). Fix the environment.
6. Handle `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool` with `ER_Term(T_Literal _)`.
7. Parser/evaluator AST mismatch: grep `SPARQL11_Parser.ml` first.
8. Try `parse_double_to_scaled` before `parse_to_scaled`.
9. In recursive string functions, handle the single-element case so
   language tags and datatypes survive.
10. OCaml `Str` works on bytes; unmatched group back-references raise
    `Not_found`.
11. `build-ocaml.sh compile` does not apply `ocaml-patches.sh`; use
    `extract` after extraction.
12. `(*` inside an F\* comment. Use `//`.
13. Do not edit extracted `.ml` in `ocaml-output/`.
14. No `|| true`. Capture the exit code: `RC=0; cmd || RC=$?`.
15. No semantic logic in `ocaml-patches.sh` or `w3c_runner.ml`.
16. Do not truncate command output with `tail`/`head`; use `tee`.
17. Cap ad-hoc parse and SPARQL runs at `timeout 600`.
18. Write the plan to `.claude-worklog.md` at checkpoints.
19. Long processes log to `.claude-runs/` with a wall-clock cap.
20. Run long parses and full builds in the background.
21. Do not wait on parallel work; take the next item.
22. A stalled subagent may have committed; check `git status` and log.
23. One subagent, one commit, one deliverable.
24. Subagent prompts carry code sketches, file:line and signatures.
25. Write "972 pass, 59 fail (out of 1031)", never "972/59".
26. Banned in prose and comments: candour and importance adjectives
    (`honest`, `genuine`, `important`, `critical`, `key insight`),
    aphorisms, "not X, but Y" pairs, "worth noting", and metaphor in a
    statement of a semantic rule. Rewrite table:
    [`skills/markdown-style/SKILL.md`](skills/markdown-style/SKILL.md).
27. Landing an old-branch commit onto a new tip can drop
    `build-ocaml.sh` module-list entries. Check the module list (hazard 11).
28. An audit that finds nothing says first what the audit can see.
    State its method with the result (hazard 28).
29. A theorem whose hypothesis contains its conclusion proves nothing.
    Delete it (hazard 29).
30. A measurement tool derives its inputs from the repository on each
    run, never from a cache (hazard 30).
31. Coverage is an explicit decision, never a name match. A count that
    moves without a cause is a bug (hazard 31,
    [`skills/counting-coverage/SKILL.md`](skills/counting-coverage/SKILL.md)).
32. A hub post's live cells run on the JS bundle. Rebuild it and run
    `node --test tests/hub/postNN` and
    `tests/web-demos/hub_browser_all.sh` (hazards 12, 22).
33. Commit `.ml` files only after a complete `extract`, staged by
    explicit path (hazard 34).
34. A routing change between the reference evaluator and a backend is
    gated by a query only the reference semantics decide (EXISTS,
    MINUS, OPTIONAL+FILTER, sub-SELECT) on the changed path (hazard 35).

## Skills

`skills/<name>/SKILL.md`, [agentskills.io](https://agentskills.io)
format. `.claude/skills/` holds symlinks. Other harnesses: point skill
discovery at `skills/`. Read a skill the first time its topic comes up.

Session and process:
- [`session-economy`](skills/session-economy/SKILL.md): fresh-session bootstrap, token use, choosing the next work. Read first in autonomous sessions.
- [`session-restore`](skills/session-restore/SKILL.md): restore a fresh container; caches; gate tool installs.
- [`session-cost-accounting`](skills/session-cost-accounting/SKILL.md): session cost including subagents.
- [`autonomous-time-discipline`](skills/autonomous-time-discipline/SKILL.md): long background jobs and stall detection.
- [`choosing-models`](skills/choosing-models/SKILL.md): model and effort per subagent.
- [`subagent-prompting`](skills/subagent-prompting/SKILL.md): subagent briefs, worktree paths, post-conditions.
- [`workflow-gotchas-debugging`](skills/workflow-gotchas-debugging/SKILL.md): numbered hazards and recovery steps.
- [`reading-owner-steers`](skills/reading-owner-steers/SKILL.md): interpret and record owner instructions.
- [`issue-management`](skills/issue-management/SKILL.md): status reports, issue references. Read before any report.
- [`issue-hygiene`](skills/issue-hygiene/SKILL.md): keep issues in sync with landings.
- [`obsolescence-sweep`](skills/obsolescence-sweep/SKILL.md): find text a landing made false.
- [`markdown-style`](skills/markdown-style/SKILL.md): prose register, links, banned words, emoji palette.
- [`github-and-prs`](skills/github-and-prs/SKILL.md): gh with `--repo danbri/factoidal`.
- [`github-coauthor-policy`](skills/github-coauthor-policy/SKILL.md): commit attribution (rule 13).
- [`repo-tour`](skills/repo-tour/SKILL.md): directory layout.

Build, test, measure:
- [`build-and-test`](skills/build-and-test/SKILL.md): build, extract, compile, run W3C tests.
- [`fast-verify-extract`](skills/fast-verify-extract/SKILL.md): `.checked` cache, targeted rebuilds.
- [`test-suites`](skills/test-suites/SKILL.md): all suites, score reporting, expected failures.
- [`perf-benchmarking`](skills/perf-benchmarking/SKILL.md): timing harnesses and baselines.
- [`measuring-inference`](skills/measuring-inference/SKILL.md): measure reasoning engines. Read before optimising closure.
- [`counting-coverage`](skills/counting-coverage/SKILL.md): count port coverage. Read before writing a coverage number.
- [`danbri-function-precrime-checkers`](skills/danbri-function-precrime-checkers/SKILL.md): measure stack, memory and time scaling in tests.
- [`site-and-dashboard`](skills/site-and-dashboard/SKILL.md): site, dashboard, demos, Fly.io endpoint.
- [`jsoo-debug-bundle`](skills/jsoo-debug-bundle/SKILL.md): source-mapped JS bundle for browser crashes.
- [`npm-release`](skills/npm-release/SKILL.md): release `@factoidal/core`.

F\*:
- [`fstar-env`](skills/fstar-env/SKILL.md): F\*, opam, z3 setup.
- [`fstar-module-style`](skills/fstar-module-style/SKILL.md): module layout, syntax traps, extraction traps.
- [`fstar-mcp`](skills/fstar-mcp/SKILL.md): interactive F\* queries.
- [`mcp-setup-readme`](skills/mcp-setup-readme/SKILL.md): MCP configuration.
- [`ocaml-boundary`](skills/ocaml-boundary/SKILL.md): rule 11 in detail.
- [`proof-factory`](skills/proof-factory/SKILL.md): rule-by-rule F\* proofs at scale.

Lean 4:
- [`factoidal-lean-basics`](skills/factoidal-lean-basics/SKILL.md): the Lean tree, builds, proof policy.
- [`lean4-proof-patterns`](skills/lean4-proof-patterns/SKILL.md): proofs over fuel-bounded definitions.
- [`lean4-performance`](skills/lean4-performance/SKILL.md): performance work with semantics kept.
- [`lean4-wasm-export`](skills/lean4-wasm-export/SKILL.md): Lean to one wasm module.
- [`lean-proof`](third_party/skills/leanprover-skills/lean-proof/SKILL.md), [`lean-mwe`](third_party/skills/leanprover-skills/lean-mwe/SKILL.md): vendored from leanprover/skills. Nothing with `sorry` is committed.
- [`lean-review`](third_party/skills/lean-agent-skills/lean-review/SKILL.md): vendored Lean diff review.

Storage and engines:
- [`blockengine`](skills/blockengine/SKILL.md): Lean RDF block engine and physical plans.
- [`shardborough-storage`](skills/shardborough-storage/SKILL.md): Lean persisted store and `l4block-*` CLI.
- [`disk-storage-format`](skills/disk-storage-format/SKILL.md): F\* COTTAS on-disk format.
- [`lws-solid`](skills/lws-solid/SKILL.md): Linked Web Storage and Solid.

Using and extending:
- [`using-factoidal`](skills/using-factoidal/SKILL.md): drive Factoidal from an external agent.
- [`skos-integrity`](skills/skos-integrity/SKILL.md): SKOS integrity checks.
- [`jsonld-context-cache`](skills/jsonld-context-cache/SKILL.md): offline JSON-LD contexts.
- [`crypto-policy`](skills/crypto-policy/SKILL.md): HACL\* only; no own crypto.
- [`node-crypto-haclstar-vc-wasm-build`](skills/node-crypto-haclstar-vc-wasm-build/SKILL.md): VC crypto in Node and browser.

## Reference docs

- [`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md): F\* inventory, `assume val` table, scores, the OWL max-cardinality rewrite limits (https://github.com/danbri/factoidal/issues/236).
- [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md): anti-patterns in full.
- [`docs/claude-rules/performance.md`](docs/claude-rules/performance.md): performance status and history.
- [`docs/theorem-registry.md`](docs/theorem-registry.md): W3C rule to proof status. Update with each proof landing.
- [`docs/w3c-glossary.md`](docs/w3c-glossary.md): specification vocabulary.
- [`docs/code-name-glossary.md`](docs/code-name-glossary.md): old code names. Add no new ones.
- [`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](docs/designissues/2026-09-03-rdf-parsing-strategy.md): parser layers and theorems.
- [`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`](docs/designissues/2026-09-05-shard-pack-profile-and-memory.md): shard packer time and memory.
- [`docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md`](docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md): npm usability and bundle profiles.
- [`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`](docs/designissues/2026-05-07-c-build-and-roaring-plan.md): KaRaMeL C build and Roaring.
- [`docs/fable-notes-xyz-20260706.md`](docs/fable-notes-xyz-20260706.md): 2026-07-06 strategy notes.
