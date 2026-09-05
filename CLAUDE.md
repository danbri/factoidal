## How to write to the owner (read this first)

Owner, 2026-08-24, verbatim:

> "I pay Anthropic for you to ALWAYS BE STRAIGHT WITH ME. Every time you
> highlight your alleged honesty or straightness in a particular context
> wastes tokens undermining everything else you say."

1. **Never advertise honesty.** No "to be straight with you", "to be
   honest", "I need to be clear with you", "the truth is", "candidly".
   Straightness is the baseline. Announcing it in one place implies its
   absence everywhere else.
2. **Plain technical English**, with domain terminology from established
   authorities — the W3C specifications, the RDF/OWL/SPARQL literature,
   the Lean 4 and F\* manuals. Do not invent vocabulary.
3. **No unsolicited metaphors.** State the mechanism.
4. **Report in ASD-STE100 Simplified Technical English.**
5. **Keep it short.** The owner reads on a phone, between other
   commitments. Lead with the result or the decision needed.
6. **A repeated steer means the last report failed.** Record decisions
   in this file the first time, not the third.
7. **An explanation of how a subsystem works, once given in chat, is
   written into `docs/designissues/` in the same landing** and linked
   from the worknote index and the relevant skill. Owner, 2026-09-03,
   verbatim: "this and similar ought to be recorded properly somewhere I
   can find it. Ephemeral coding logs aren't that place." The first such
   record: `docs/designissues/2026-09-03-rdf-parsing-strategy.md`.

> **only report to me in ASD-STE100 Simplified Technical English.**

# Factoidal — a linked information system with graph data and the Web at its heart

(Owner's framing, 2026-08-22.)

**The product is the system**: a highly optimised, flexible, performant
environment for graph data on the Web — storing it, querying it,
linking it, and serving it over Web protocols. F\* and Lean 4 are how
its APIs, interfaces and protocols are grounded in the W3C
specifications and in mathematics. They are not a separate deliverable, and a specification
is not a substitute for the code that satisfies it.

That grounding is what buys the freedom to go fast: implementations
may be varied, tuned and replaced aggressively, because the specs make
it impossible for an improvement to silently destroy standards
compliance. Executable code is still obtained by **extraction from the
formal source**, never by hand-writing Rust/JS/OCaml that "mirrors" a
spec — that is the mechanism, not the goal.

## Founding view (danbri, 2026-08-22) — verbatim

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

What follows from it, and settles recurring arguments:

- **Spec and implementation are DISTINCT artifacts even when both are
  written in F\* or Lean.** A fast implementation is not a betrayal of
  the spec; a spec-shaped definition is not a performance failure. The
  correct relation between them is a proof, not a resemblance.
- **Efficiency and tunability are in scope, not concessions.** Speed
  work is legitimate everywhere, in either tree, provided the spec it
  satisfies stays fixed and the satisfaction is proved or measured —
  never assumed.
- **The point of the formal layer is freedom to experiment.** Agents
  and collaborators should be able to vary implementations
  aggressively; the specs are what make that safe. Treat a refusal to
  optimise "because it is the spec tree" as a category error — move
  or prove the boundary instead.

**Goal:** a performant, compliant engine for RDF Core 1.1 (all concrete
syntaxes), RDF/S, OWL, SHACL, RDFC-1.0 canonicalization, and full
SPARQL 1.1 (query, update, protocol, results) — grounded in F\* and
Lean 4, extracted to native/JS/wasm (and C via KaRaMeL), with
correctness and speed each established by proof, test suites and
measurement, never by assertion.
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

1. **The formal source is the source of truth.** RDF/SPARQL logic
   lives in `.fst` files (`formal/fstar`, the shipping engine) and in
   `.lean` files (`formal/lean4`, `L4Factoidal`) — never in
   hand-written code downstream of them.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml`
   or KaRaMeL for C/WASM; the Lean tree compiles via Lean→C→wasm. Never
   vibe-code an implementation that "mirrors" the spec. Optimising an
   implementation IS allowed and wanted — inside the formal source,
   where the refinement can be proved.
3. **`assume val` = acknowledged gap OR allowed realisation — never a
   silent hole.** An `assume val` is one of two things, and each has a
   home:
   (a) an acknowledged **GAP** (logic that should be extracted-from-F\*
   but isn't yet) — MUST have a stub patch in
   `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
   named `<issue>_<description>.sh` with a corresponding open GitHub
   issue; or
   (b) an allowed **realisation** under rule #11 (pure I/O — file/clock/
   socket; a host-engine call-out; a vendored crypto primitive; or an
   Option-B perf realisation whose byte-format spec lives in F\* with a
   hash-witness CI test) — realised in `experimental_ocaml_glue/*.sh`.
   Most of the **82** `assume val`s today (18 modules, measured
   2026-09-03) are (b) (the COTTAS/HDT storage I/O layer). Count them,
   do not quote this line: `grep -rhE '^[[:space:]]*assume val '
   formal/fstar --include='*.fst' --include='*.fsti' | wc -l`. This rule
   said "~148" from an unmeasured estimate until 2026-09-03; per-module
   figures are in `docs/claude-rules/current-state.md` § assume val
   inventory, beside the same command.
   Neither kind may be a *silent* hole: a (a)-gap without an
   issue, or a (b)-realisation carrying semantic/planning/byte-layout
   logic that belongs in F\*, is a violation. (Audit: `docs/designissues/
   fstar-ocaml-boundary-audit.md`.)
**Lean Lake working directory.** `formal/lean4/` is the self-contained
Lake project. Every `lake build`, `lake exe`, or `lake env` command must run
with `formal/lean4/` as its explicit working directory. Repository Git
commands run at the repository root. Do not combine them in a command which
depends on a preceding `cd` remaining in effect. Never invoke `lake` from the
repository root: check the current tool call's working directory before every
Lean command. This was repeatedly missed on 2026-08-31 and produced invalid
root-level Lake failures.
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
    no `--admit_smt_queries`, no escape-hatch flags. The last legacy
    exception (`SPARQL11.Parser.fst`'s two `--admit_smt_queries true`
    pragma regions, 119 definitions) was eliminated 2026-07-10; the
    rule now holds with no carve-outs. Never add a new one.
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
13. **No Claude attribution anywhere in git history.** This covers
    two things, and the second was missed for a month:
    (a) **Message content** — no `Co-Authored-By: Claude`, no
    "Generated with Claude Code", no session links, no prose crediting
    Claude in commit messages.
    (b) **Author and committer identity** — every commit is attributed
    to the responsible HUMAN. Owner instruction, 2026-08-26, verbatim:
    "all attributions are to responsible human only".
    This repo policy overrides the harness default, and the harness
    actively pushes the other way: the hosted CCR image ships a
    SessionStart hook setting the GLOBAL identity to
    `Claude <noreply@anthropic.com>`, plus a Stop hook that instructed
    the agent to run `git config user.name Claude` whenever a commit
    failed GitHub's Verified check. An agent obeying that hook would
    have rewritten the human author out of the commit — the hook and
    this rule were in direct contradiction, and the hook was the one
    with teeth. `tools/sandbox-bootstrap.sh` now pins the
    REPOSITORY-LOCAL identity on every session start, which git prefers
    over the global one regardless of hook ordering, and reports it in
    the bootstrap block. Accepted cost, stated so nobody "fixes" it:
    the container's SSH signing key is registered to the bot address,
    so human-committed commits show as "Unverified" on GitHub. Correct
    attribution outranks the badge. Full rule:
    [`skills/github-coauthor-policy/SKILL.md`](skills/github-coauthor-policy/SKILL.md).
14. **A repaired methodology error is not done until the docs that
    prevent its repetition are updated.** After identifying and fixing
    an error in our own working method — a wrong causal claim, a
    silent-failure mechanism, a discipline that was skipped — revise
    CLAUDE.md and/or the relevant `skills/<name>/SKILL.md` in the SAME
    landing, so the next session inherits the correction instead of
    rediscovering the mistake. Name the error concretely, with its
    date and cost; a rule without its war story does not stick
    (`skills/measuring-inference/SKILL.md` is the model — every rule
    carries the wrong claim that paid for it). The repair commit and
    the doc update belong together; "fixed it, will document later"
    is how the same failure bills twice.

## Known sound-but-narrow rewrites

`OWL.QueryRewrite.fst` — N=1 qualified `CE_MaxCardinality` rewrite
emits an anchor triple `?subj P ?_mxqc1_anchor_<k>` to make parent7
pass. The anchor silently drops vacuous-truth individuals (zero
`P`-edges satisfy max-1) and OWL Full punned class-individuals — that
narrowness remains. The internal-variable LEAK the 2026-07-09 strict
runner exposed (`?_sv_`/`?_mc_`/`?_mxqc1_` vars appearing in `SELECT *`
result rows) is FIXED (task #100): `OWL.QueryEval.eval_select_query_owl`
strips rewrite-internal vars from the FINAL user projection only, via
`SPARQL11.Algebra.strip_rewrite_internal_vars`. It must stay at the
top level — inner `wrap_distinct_over_ggp` Select_All sub-selects
deliberately re-expose the anchor var so the enclosing pattern can JOIN
on it (simple5), so stripping inside them decorrelates the join. The
regime suite is at 70 pass, 0 fail (out of 70; re-measured 2026-07-10). Tracked in **#236**. Generalise from anchor
→ UNION as documented there before relying on this rewrite for OWL DL
outside the entailment regime suite (the anchor still MULTIPLIES rows
per P-edge and drops vacuous-truth individuals).

## Standing decisions (owner, 2026-08-24)

Recorded here because they were repeated several times before being
written down. Verbatim; paraphrase drifts.

### Port functionality, not files

> "the key thing is to port functionality not files. The port was partly
> motivated by fear F\* version was accumulating cruft and this may help
> to clear it."

Module-count coverage is a progress indicator, not the goal. Where an
F\* module is cruft, the Lean side implements the FUNCTION correctly and
the F\* file is marked, not transcribed.

### Priority order

> "Good to progress Cottas but I suggest core of rdf/s, sparql, owl, rif,
> csvw, shacl, shex, xml, xpath, cslt, schematron are more urgent. Cottas
> rdf store didn't really get mature enough to use in f\*, we may ship
> Factoidal and make a separate FactoidalDB repo to focus attention on
> the issues."

- **Urgent:** RDF/S, SPARQL, OWL, RIF, CSVW, SHACL, ShEx, XML, XPath,
  XSLT (read from "cslt"), Schematron.
- **Not urgent:** COTTAS. Possible future split into a FactoidalDB repo.

### Lean 4 is the intended full-scope target (owner, 2026-08-29)

> "The Lean port is only a week old, but improved quickly enough that I am
> inclined to make the switch. It hasn't yet been applied to the full scope of
> Factoidal but that is my intent."

This newer direction makes the Lean 4 tree the target for the full Factoidal
scope. It changes the 2026-08-24 COTTAS ordering for the block-engine
workstream. It does not claim current Lean/F* parity. Keep the existing F*
path executable as lineage and a differential oracle until the corresponding
Lean functionality and gates land. Port functionality, not files.

### Issue 566 — the hex layer. RULED, do not ask again.

> "Yeah DO NOT PORT THAT TERRIBLE HEX CRAP!!!"
> "We have no users so rip it up where it is crap."
> "Fix it upstream in F\* and do not worry about legacy. You can defer
> that for now just mark the F\* file as fucked and link to GitHub. Do it
> right in Lean. F\* Cottas is essentially unused. I am only human using
> anything."

- Do NOT port the hex layer to Lean. Lean implements the byte format
  directly.
- The F\* file carries a header marking it broken and linking
  <https://github.com/danbri/factoidal/issues/566>. Legacy compatibility
  is deferred; there are no users.
- `Parquet.Footer` was waiting on this call. The call is made and the
  same ruling applies. It is not blocked and needs no further asking.

### RDF.NQuads.Streaming and SPARQL11.Parser.AskBgpRoundTrip

> "These are important. We need performant nquads and sparql
> implementations across all surfaces!"
> "Rdf.nquads.streaming it is ok to make the changes, ideally both f\* and
> lean4 behave same"

Changes approved. The two trees should agree in behaviour; where the
Lean side changed (the streaming offset), the F\* side follows rather
than the two drifting.

### Prove over an abstraction

> "Ideally we should prove it over an abstraction of both, in lean4 and
> also optionally f\*"

Where a property holds of both trees, state it once over an abstraction
(a typeclass or parameterised structure in Lean) and instantiate it,
rather than proving it twice. Lean first; F\* optional.

### There are no users. Prefer the right structure to the compatible one

The issue-566 ruling above says "We have no users so rip it up where
it is crap." That is a GENERAL rule, not a hex-layer one. Owner
restatement, 2026-08-26, verbatim:

> "You speak like this is a huge codebase with many users. Thw honest
> truth is that I made it using my anthropic claude subscription
> overnight, and it has zero audience and users so far."

Blast radius, backwards compatibility and migration cost are not
arguments here. When a design is wrong, change the design; keep the
superseded artifact only as the record of why it changed. Cost of
getting this wrong: on 2026-08-26 the coordinator recommended the
conservative option for
[issue 609](https://github.com/danbri/factoidal/issues/609) item 3 —
adopt the divergence as a stated interpretation condition rather than
repair the dataset embedding — on blast-radius grounds that only apply
to a codebase with users. The owner overruled it: "The correct path is
(3.)".

## Reading owner steers: prioritization is not prohibition

The owner usually steers this project from a phone, between other
obligations, against a fast stream of agent output — with no good
tooling for bookmarking, tagging, or cross-referencing what scrolled
past. Instructions given under those conditions are prioritizations
made on a partial view, and the owner has said plainly that they are
sometimes inaccurate or flawed — most likely for protocol-shaped work,
which is harder to test casually than format-shaped work (a format
test is files-in/triples-out; a protocol test needs simulated or live
endpoints, so a quick scope judgment about it is easier to get wrong).

Rules that follow:

1. **"X deprioritized" is an ordering decision, never a scope
   prohibition.** Do not let a steer calcify into "out of scope by
   owner directive" through document inheritance. (It happened: a
   2026-07-11 "protocols deprioritized" was inherited three documents
   deep into "owner-excluded" labels on specific CSVW tests. The owner
   never made that call; see the 2026-07-15 correction in the CSVW
   triage ledger. The owner's own account of what that steer meant,
   given 2026-08-22, verbatim: "Protocols were not deprioritised but
   we needed basic sparql first - and early f\* was glacially slow at
   points where io bridged the non f\* universe." Note that BOTH the
   original label and the earlier gloss recorded here were wrong: it
   was a sequencing constraint plus a performance problem at the I/O
   boundary, not a judgement about protocol work.)
2. **Quote steers with date and original wording** when writing them
   into ledgers or design docs. Paraphrase drifts; drift compounds.
3. **Never invent a rationale and attribute it to the owner.** State
   who decided a thing, or label it a Claude-inferred default. In this
   repo `git blame` CANNOT settle provenance — every commit carries
   the owner's git identity by iron rule #13 — so provenance survives
   only if the prose carries it. (It happened: 2026-08-22, a
   Claude-authored skill bullet said the Lean tree's plain evaluator
   split was "absolute — never port performance machinery here",
   placed under an "owner priority" heading it was never given. It
   hardened into "must stay that way" in a design doc, then into a
   chat claim that the owner considered indexed joins destructive.
   Owner: "BS, I never said this." Cost: a real design question —
   should the Lean tree get indexed joins and a refinement proof? —
   was recorded as closed for a day. Corrected in
   `skills/factoidal-lean-basics` with a standing provenance note.)
4. **Load-bearing implications get surfaced, not inferred.** Before
   recording "owner excluded N tests" or dropping a suite from a
   goal, put the implication back to the owner as one short question.
   A sentence of friction now beats a fabricated decision that future
   sessions will read as settled.
5. **Write for phone-triage.** The owner's instruction quality is a
   function of our output quality: lead with the result or the
   decision needed, keep it short, no pseudo-private jargon (glossary
   rule), scores always labelled. A wall of codenames upstream
   becomes a flawed instruction downstream.
6. **Use a small, stable emoji palette as visual anchors** (owner
   request, 2026-07-15): colored emoji render as scannable texture on
   a phone, letting the owner navigate giant scrolling blocks at
   flick-speed. Fixed meanings, applied sparingly (one marker per
   line that matters, never decoration): ✅ landed/gates green ·
   ❌ regression/gate failure · 🔴 blocker needing action ·
   🟡 in flight · 📊 score line · 🧭 decision needed from owner ·
   ⚠️ risk/caveat · 🧹 cleanup/hygiene. Owner messages may use emoji
   as markers too — treat them as tagging, not tone. Full register
   rules: `skills/markdown-style/SKILL.md`.
7. **Work tracking lives in GitHub issues, not session state** (owner
   correction, 2026-08-11, verbatim: "This is unacceptably shit for
   ios app users - you spew thousands of lines of blabber at us with
   no tooling to organize it. Use github properly."). Session-local
   task lists are invisible on mobile and die with the container.
   Every workstream gets a real issue; the one-page index is
   **#404 Active work tracker** (update it at every harvest cycle —
   staleness there is a bug). Status reports LINK issues instead of
   restating their content.
8. **Old steers decay — re-verify before acting on one.** "Protocols
   deprioritized" predated SPARQL Protocol reaching 56 pass, 0 fail
   (34 protocol + 19 graph-store + 3 service-description, both trees);
   citing a steer against a tree that has since moved is acting on
   stale data.

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

**Check `df -h /` before dispatching a worktree agent, cap concurrency at
three, and remove each worktree in the same turn you land its commit.**
Each worktree holds a 1.5-2.8 GB copy of the Lean build cache; seven live
at once filled the disk on 2026-09-03 and every tool call failed, including
the one that would have diagnosed it. Before deleting a worktree, check it
for unlanded commits (`git -C <path> log --oneline origin/claude/main..HEAD`)
— that sweep rescued a 301-line design document written twelve days
earlier. Full recovery procedure: hazard #36 in
`skills/workflow-gotchas-debugging`.

**Worktree agents start with `tools/ensure-test-env.sh`** — worktrees
inherit zero test submodules, and absent fixtures produce lying 0/0
scores and phantom ENOENT failures (hazard #15,
`skills/workflow-gotchas-debugging`). Never trust a suite number from
a checkout where that script exits 1.

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
26. **Three language bans** in prose AND code comments (owner
    correction, 2026-08-23). Rewrite table:
    `skills/markdown-style/SKILL.md`.
    (a) **Sycophantic adjectives**: `honest`, `genuine`, `important`,
    `critical`, `big-picture`, `headline`, `key insight`, `key
    finding`.
    (b) **Aphorisms** — a short balanced sentence written to sound
    like a maxim. Banned examples from this repo: "A vacuous truth is
    not an entailment", "a cap that hides which test it costs is a
    silent cap", "Withholding is sound; manufacturing emptiness is
    not". Write the rule as a rule. Also banned: "not X, but Y"
    contrast pairs, and telling the reader which of your points
    matters ("worth noting", "the point is", "this matters
    because"). These are named patterns in the published catalogue of
    Claude writing tics.
    (c) **Metaphor in any statement of a SEMANTIC RULE.** "A spelling
    difference is not a value difference" was metaphor AND factually
    wrong — `"colour"` and `"color"` ARE different `xsd:string`
    values. The actual rule is about whether a datatype's LEXICAL
    MAPPING is injective. Use the specification's own term from
    [`docs/w3c-glossary.md`](docs/w3c-glossary.md); if the term is
    missing, add it there first.
27. Landing an old-branch agent commit onto a much newer tip silently
    drops `build-ocaml.sh` module-list entries (auto-merge) and
    consumer `.ml` changes — the build exits 0 but the feature isn't
    built. Verify the module list + force ancestor-safe consumer files;
    prefer a dedicated landing agent. Full text: hazard #11 in
    `skills/workflow-gotchas-debugging/SKILL.md`.
28. An audit that finds nothing is evidence about the AUDIT's reach
    before it is evidence about the code. State the method next to the
    result, and pick one that can see the failure you are looking for.
    (2026-08-23: a squashed-module-name audit of the Lean port gap
    reported "no other false negative"; four modules, 1,298 F* lines,
    were already covered — the method cannot see a consolidation or a
    substantive rename, and its silence about exactly those was read as
    coverage. The reported figure was 120 of 220; the real one was 125.
    Full text: hazard #28 in `skills/workflow-gotchas-debugging`.)
29. A theorem whose hypothesis restates its conclusion type-checks
    and proves nothing. Before claiming a theorem discharges an
    obligation, unfold the conclusion and check no premise contains it;
    a proof body of `exact h` is the tell. Delete such a theorem, never
    weaken it -- it makes commit messages and design docs claim the
    obligation is met. (2026-08-23, `Cottas.PresenceWriter`: a
    `buildPresence_correct` under the heading "the producer-side
    obligation, closed" took `BuiltCorrectly` with re-indexed bounds as
    a hypothesis. Full text: hazard #29 in
    `skills/workflow-gotchas-debugging`.)
30. A measurement tool must derive its inputs from the repository on
    every run. A cached file list reports the cache, not the tree, and
    says nothing about being old. (2026-08-23:
    `tools/lean-port-gap.py` read its Lean module list from the
    session scratchpad and reported a module as not covered minutes
    after its Lean file landed; the same cache would have made the
    tool crash on a fresh container. Fail loudly on an empty walk, and
    write generated reports to a temp path. Full text: hazard #30 in
    `skills/workflow-gotchas-debugging`.)
31. Coverage is an explicit decision, never a name resemblance. A
    matching last name component is a suggestion to audit, not a
    result; and a lookup table whose misses fall through to a
    heuristic cannot report its own breakage. (2026-08-23: adding
    `HDT/Store.lean` made `SPARQL11.Store` — 1,452 lines, unported —
    vanish from the Lean port gap's not-covered list, because both end
    in `Store`. The audit found seven such false positives and two
    aliases pointing at a Lean module that does not exist, hidden
    because the leaf rule matched something else. The reported count
    had been over by five. A count that moves without a cause is a bug
    report: chase it before writing the number down. Full text: hazard
    #31 in `skills/workflow-gotchas-debugging`.)
32. A hub post's live cells run against the js/npm bundle, not the
    native binary. A docs landing that adds cells calling a new F\*
    feature is NOT docs-only — rebuild the bundle (the js build
    incrementally SKIPS npm-entry; force it) and gate on `node --test
    tests/hub/postNN` AND the headless-browser sweep
    `tests/web-demos/hub_browser_all.sh` — the node harness binds
    `fn` to the node package, so it cannot see browser-surface gaps
    (missing hub.njk wrappers, Turtle-vs-N-Quads calling-convention
    mismatches: two owner-reported live breakages, 2026-08-07/08).
    Full text: hazards #12 and #22 in the same skill.
33. A `.ml` under `ocaml-output/` captured between `fstar.exe --codegen
    OCaml` and `./ocaml-patches.sh` compiles and is missing every glue
    realisation. Three Lean-titled commits swept such files into git on
    2026-08-24; the shipping linux binary was rebuilt from them and lost
    the COTTAS on-disk companion chain, the SPARQL extension-function
    registry, the Parquet footer glue and the SHACL `sh:sparql` marker
    for two days, with `git status` clean and every suite green. Commit
    `.ml` only after a COMPLETE `extract`, stage it by explicit path,
    and never let a commit carry files its subject does not name. Full
    text: hazard #34 in `skills/workflow-gotchas-debugging`.
34. A routing change that moves query shapes from the reference evaluator
    to a backend runner must be gated by a query only the reference
    semantics decide (EXISTS/NOT EXISTS, MINUS, OPTIONAL+FILTER,
    sub-SELECT) on the path that changed. (2026-09-02: the WASM/CLI query
    op was routed through the physical-plan runners without
    `env.dataset`; FILTER NOT EXISTS answered zero rows for a day while
    `lake build`, native-smoke, the hub suite and CI were all green, none
    of which ran an EXISTS query through that path. Found by
    `tools/w3c-persisted-census.sh`. Full text: hazard #35 in
    `skills/workflow-gotchas-debugging`.)

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
- [`factoidal-lean-basics`](skills/factoidal-lean-basics/SKILL.md)
  — the Lean 4 side (formal/lean4/, L4Factoidal,
  https://github.com/danbri/factoidal/issues/466): toolchain,
  build/demo/test, the no-sorry/no-axiom policy + audit, the purity
  doctrine replacing `assume val`, lean-lsp-mcp + lemma search, and
  the paid-for Lean pitfalls.
- [`blockengine`](skills/blockengine/SKILL.md) — design, implement, and
  review the Lean-generated RDF block engine: landed Cottas/SPARQL reuse,
  term and graph IDs, block denotation, physical plans, PushIR, bitmap
  indexes, PostgreSQL/TiKV adapters, and refinement gates.
- [`shardborough-storage`](skills/shardborough-storage/SKILL.md) — operate
  the Lean persisted store: pack → activate → query the collection root →
  update through the delta log → compact, the `l4block-*` CLI table, what a
  generation directory contains, the corpus ladder and census tools, and
  the rules for changing a format (encoder admission equals decoder
  admission; byte change means new wire version).
- [`lean-proof`](third_party/skills/leanprover-skills/lean-proof/SKILL.md)
  and [`lean-mwe`](third_party/skills/leanprover-skills/lean-mwe/SKILL.md)
  — vendored unmodified from leanprover/skills (Apache-2.0, provenance in
  `third_party/skills/leanprover-skills/PROVENANCE.md`): the upstream
  one-tactic-at-a-time proof method and the minimal-example recipe for
  upstream bug reports. Local policy on top: nothing with `sorry` is
  committed.
- [`lean-review`](third_party/skills/lean-agent-skills/lean-review/SKILL.md)
  — vendored unmodified from gotrevor/lean-agent-skills (Apache-2.0): the
  diff-scoped trust and hygiene check registry for Lean changes
  (`maxHeartbeats`, `native_decide`, `axiom`, `sorry`, `unsafe`/`partial`,
  silenced linters), `#print axioms` as the authoritative check.
- [`lean4-proof-patterns`](skills/lean4-proof-patterns/SKILL.md) — prove
  properties of fuel-bounded, match-heavy definitions without Mathlib:
  the theorem shape for fuel independence, nested-match splitting, the
  large-Nat-literal trap that hangs `split`/`generalize`, `rename_i`
  order, `omega` after `List.length_cons`, timed per-theorem compiles to
  bisect a hang. Read when a Lean proof stalls or before dispatching a
  proof subagent.
- [`lean4-performance`](skills/lean4-performance/SKILL.md) — improve
  performance-sensitive Lean 4 code while preserving total semantics,
  observable order, and the executable proof boundaries: parsers, block
  ingestion, data structures, recursion, hot paths. Measure first; not for
  unmeasured micro-optimisation.
- [`lean4-wasm-export`](skills/lean4-wasm-export/SKILL.md) — compile the
  Lean 4 port to ONE wasm module for browser + Node + Deno (#466): the
  toolchain route and the three rejected, rebuilding Lean's runtime and
  core library for wasm32 GMP-free, the C ABI + memory ownership, how to
  add an export, and the traps (silent `leanir`, the `-DNDEBUG` abort).
- [`npm-release`](skills/npm-release/SKILL.md) — release
  `@factoidal/core`: which artifacts `Wasm/build-wasm.sh` and
  `build-ocaml.sh npm` produce, the four byte-identical wasm mirrors,
  the three `version.json` files and their writers, trusted publishing
  through the OIDC workflow (the owner's npm account is
  security-key-only, so token and one-time-password publishing always
  fail), the gates with their current numbers, and the packaging traps.
- [`crypto-policy`](skills/crypto-policy/SKILL.md) — never roll our
  own crypto; HACL\* adoption order for the hash/signature
  `assume val`s (#63), and the wasm compatibility gate.
- [`node-crypto-haclstar-vc-wasm-build`](skills/node-crypto-haclstar-vc-wasm-build/SKILL.md)
  — the concrete build: VC Data-Integrity crypto running off-native
  (Node + browser) via HACL\*'s official wasm (#286). Three realisation
  paths, the throw-on-uninit safety contract, build-ocaml.sh wiring, npm
  ABI, provenance/licence, and the land-from-off-main recipe.
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
- [`proof-factory`](skills/proof-factory/SKILL.md) — run the
  rule-by-rule F\* proof program at scale: the closure-identity law,
  the guard-depth ≤3 rule, brief anatomy for first-attempt passes,
  spray-and-verify economics per model tier, the harvest pattern for
  stalled proof agents, and the findings discipline (six ledger
  drifts + one engine completeness gap caught by proofs). Read
  before dispatching any proof subagent or proving engine rules
  against the W3C tables.
- [`measuring-inference`](skills/measuring-inference/SKILL.md) — how to
  measure what a reasoning engine actually does: which phase the time is
  in, why synthetic shapes lie about real vocabularies, negative tests
  that pass by deriving nothing, theorems with unsatisfiable
  hypotheses, and silent caps. Read **before** optimising any closure
  or entailment path, or before a plausible mechanism becomes a work
  order. Every rule carries the wrong claim that paid for it.
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
- [`using-factoidal`](skills/using-factoidal/SKILL.md) — drive
  Factoidal from any external LLM/agent system: both engine flavours
  (F\* CLI + npm, Lean wasm + native), the capability matrix with
  measured scores, runnable examples per spec area, and the l4_call
  dispatch ABI. Self-contained for readers outside this repo.
- [`fstar-mcp`](skills/fstar-mcp/SKILL.md) — F\* MCP server for
  interactive proof / typecheck queries (replaces batch `fstar.exe`
  reruns for diagnostic work).
- [`mcp-setup-readme`](skills/mcp-setup-readme/SKILL.md) — how the
  repo's MCP wiring is configured (`.mcp.json`, bootstrap script,
  daemon manager, port, transport). Read when adding/debugging the
  MCP plumbing rather than using F* MCP for proofs.
- [`markdown-style`](skills/markdown-style/SKILL.md) — clickable-link
  rules, the no-sycophantic-adjectives rewrite list, and the
  aphorism/metaphor ban with its rewrite table (anti-pattern #26).
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
- [`counting-coverage`](skills/counting-coverage/SKILL.md) — how to
  count what a port or migration has covered without the number lying.
  **Read before writing any coverage number, before adding an alias-table
  entry, and whenever a count moves and you cannot name the commit that
  moved it.** Core rule: a name is a hint, coverage is a decision.
- [`issue-management`](skills/issue-management/SKILL.md) — **read
  before any status report, plan, or issue reference.** GitHub issues
  are the only durable work record; every issue reference is a full
  clickable URL (bare `#NNN` is dead text in rendered markdown);
  session-local labels and code names are forbidden in anything a
  reader sees later; technical Simple English with a banned-filler
  table ("load-bearing", "smoke test", ...).
- [`issue-hygiene`](skills/issue-hygiene/SKILL.md) — keep GitHub
  issues + checklists in sync as PRs land.
- [`jsoo-debug-bundle`](skills/jsoo-debug-bundle/SKILL.md) — build a
  source-mapped JS bundle so browser-only crashes show real OCaml
  stacks.
- [`jsonld-context-cache`](skills/jsonld-context-cache/SKILL.md) —
  resolve remote JSON-LD `@context` IRIs offline from
  `third_party/jsonld-context-cache/` (URL-keyed, content-addressed,
  versioned). Read when a JSON-LD/DID/VC document will not parse
  because its context is remote, when adding or refreshing a cached
  context, or when wiring a documentLoader (#275). Carries the
  per-URL licence rule and why an empty-context fallback is banned.

## Expanded docs (full reference)

- [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md)
  — full anti-pattern text with war stories.
- [`docs/claude-rules/performance.md`](docs/claude-rules/performance.md)
  — perf status + history (current measured throughput; the 2026-04
  slow-Turtle root causes).
- [`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md)
  — F\* inventory, `assume val` table, W3C scores.
- [`docs/theorem-registry.md`](docs/theorem-registry.md) — the G1
  reviewable-core registry: every W3C rule id → spec predicate →
  engine function → proof status, plus the trust-surface enumeration.
  UPDATE WITH EVERY PROOF LANDING (hand-curated until generated).
- [`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](docs/designissues/2026-09-03-rdf-parsing-strategy.md)
  — how each RDF syntax is parsed: the reference parser, the streaming
  execution for the shard packer, the theorems between them, costs paid
  and open. Update it when a parser layer changes.
- [`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`](docs/designissues/2026-09-05-shard-pack-profile-and-memory.md)
  — where the shard packer's time goes and how its peak memory grows: the
  `/usr/bin/sample` method with its blind spots, the two accidental costs it
  found and their repairs, the measured curve (time AND memory both linear;
  memory is 3.76 bytes of peak footprint per source byte, which puts YAGO at
  about 534 GB), what stays live to the end of a pack, and why a memory
  curve fitted without a point an order of magnitude above the others read
  as sublinear and was wrong.
- [`docs/w3c-glossary.md`](docs/w3c-glossary.md) — the cross-spec
  architectural vocabulary: lexical space / value space / lexical
  mapping, entailment and models, open-world and no-unique-name,
  OWL 2 class expressions, tableau terms, conformance-testing terms,
  and the local vocabulary that is NOT specification language. Use
  these terms; do not paraphrase them.
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
