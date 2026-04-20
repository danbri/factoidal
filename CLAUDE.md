# Factoidal — Verified RDF/SPARQL from F*

## :warning: F* Comment Syntax — DANGER :warning:

**F\* comments `(* ... *)` support NESTING.** Any `*)` inside a comment
prematurely closes it, and any `(*` opens a new nesting level. This means
constructs containing `*)` will **silently corrupt the rest of your file**
when placed inside comments.

**This WILL break:**
```fstar
(* ARQ algebra example
   construct(*)
*)
```
The `*)` inside `construct(*)` closes the comment. Everything after it becomes
code. F\* then reports a syntax error **hundreds of lines later**, making
debugging extremely difficult.

**Safe alternatives:**
- Reword to avoid parens-star: `(* COUNT-star special case *)`
- Use `//` line comments (F\* supports them): `// COUNT(*) special case`
- Escape or rephrase: `(* SELECT vars-or-star ... *)`

**Rule: Never put `*)` or `(*` inside an F\* block comment.** Grep your `.fst`
files for these sequences if you get mysterious syntax errors far from the
actual cause.

## What This Project Is

A formally verified RDF/SPARQL implementation. The **F\* specifications are the
product**. Executable code is obtained by **extraction**, not by hand-writing
Rust/JS/OCaml/anything that "mirrors" a spec.

## Iron Rules

1. **F\* is the source of truth.** All RDF/SPARQL logic lives in `.fst` files.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml` (or
   KaRaMeL for C/WASM). Never vibe-code an implementation and claim it "mirrors"
   the spec.
3. **assume val = acknowledged gap.** Every `assume val` must have a stub in
   `minimal_regrettable_glue_code_each_with_an_open_issue/` (individual patch
   files, each with a GitHub issue number in the filename). No silent holes.
4. **Parsers belong in F\*.** RDF serialization parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) are implemented in F\* and
   extracted. All hand-written OCaml parsers have been removed. New parsers
   MUST be written in F\* first.
5. **Full SPARQL 1.1 is the target.** This includes Query, Update, Protocol,
   SERVICE (federated query), and all result formats (XML/SRX, JSON, CSV, TSV).
   Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`, `.ttl` from
   disk. Do not construct synthetic queries that are "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of what F\*
   defines. If you need new functionality, add it in F\* first, then extract.
8. **RDF semantics are not optional.** The rdf-mt (model theory) tests verify
   fundamental RDF graph semantics — literal equivalence, datatype handling,
   language tag normalization, RDFS closure rules. These are core requirements,
   not "just inference." Dismissing them is wrong.
9. **Commit compiled binaries.** The compiled `w3c_runner` and `factoidal`
   binaries live in `bin/<platform>/` (e.g., `bin/darwin-arm64/`,
   `bin/linux-x86_64/`) and MUST be committed to git. This lets anyone
   check out the repo and immediately run tests without needing an F\*/opam
   toolchain. `ocaml-output/` contains symlinks to the current platform's
   binaries. `build-ocaml.sh compile` auto-detects the platform and outputs
   to the correct directory. Do not add binaries to `.gitignore`. Do not
   skip them when staging.
10. **Patches are for stubs and workarounds, NOT logic.** Post-extraction
    patches live in `minimal_regrettable_glue_code_each_with_an_open_issue/`
    as individual files named `<issue>_<description>.sh`. Each patch MUST
    have a corresponding open GitHub issue. Patches may wire `assume val`
    stubs, fix F\* type system limitations, and do forward-reference wiring.
    They must **never** contain RDF/SPARQL semantic logic. If you find yourself
    writing "if the entailment regime is RDFS then do X" in a patch, STOP —
    that logic belongs in F\*. Every line of logic in a patch is unverified,
    won't extract to C/WASM, and must be re-implemented for every target.
    **Known violations:** blank-node-as-existential rewriting (#53).
    When an issue is resolved (F\* replaces the patch), delete the patch
    file. Resolved: RDFS closure + reflexivity axioms (#60) — now lives in
    `RDF.Graph.Executable.fst` as `rdfs_closure_with_reflexivity`.

## Agent Work Strategy

When working on this project with Claude Code:

- **Use subagents aggressively for parallelism.** Launch multiple subagents for
  independent tasks (e.g., F\* verification + OCaml compilation + test running).
  Never get blocked waiting on one thing when other work can proceed.
- **Top-level Claude is the coordinator.** Don't get distracted doing deep work
  that a subagent could handle. Keep subagents productive and track their results.
- **Never block.** If one task is waiting, start another. Use background agents
  for long-running operations (F\* verification, test runs).

## Anti-Patterns — Do NOT Repeat These Mistakes

Previous Claude sessions made these errors. Read and internalize:

1. **Writing OCaml parsers instead of F\* parsers.** Do not write new `.ml`
   parser files. All hand-written OCaml parsers have been deleted. There are
   NO OCaml parser files to use as a pattern. New parsers go in `.fst` files.

2. **Dismissing rdf-mt tests as "needing an inference engine."** The rdf-mt
   test suite tests fundamental RDF semantics that RDF.Graph.Executable.fst
   must implement:
   - Language tag case-insensitive comparison (`@en-US` = `@en-us`)
   - Plain literal ↔ xsd:string equivalence
   - Datatype value equivalence (`"010"^^xsd:integer` = `"10"^^xsd:integer`)
   - RDFS closure rules (subClassOf, subPropertyOf, domain, range inference)
   These are bugs in the F\* spec, not out-of-scope features.

3. **Reporting misleading test scores.** "383/0 RDF" means nothing when it only
   tests hand-written OCaml parsers against syntax tests. The actual RDF
   implementation (RDF.Graph.Executable.fst) is not tested by parser tests.
   Always report what the numbers actually measure.

4. **Building parallel toolkits.** If the existing F\* code doesn't handle
   something, the fix is to extend the F\* spec — not to write OCaml code that
   does the same thing outside the verified boundary.

5. **Creating symlinks or hacks for version mismatches.** Do not create
   symlinks for z3 or other tool version issues. Fix the actual environment.

6. **Promoted type blindness.** When `eval_expr` evaluates a variable bound
   to a numeric literal, it returns `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool` —
   NOT `ER_Term(T_Literal l)`. Any function that only pattern-matches on
   `ER_Term(T_Literal l)` will silently fail on promoted values. This
   has caused bugs in: `fn_datatype`, `fn_isLiteral`, `fn_lang`,
   `er_string_info`, `eval_concat`. **Rule: every function that handles
   `ER_Term(T_Literal l)` must also handle `ER_Num`, `ER_Dec`, `ER_Dbl`,
   and `ER_Bool` where semantically appropriate.**

7. **Parser/evaluator AST mismatch.** The SPARQL parser may emit different
   AST nodes than the evaluator expects. Example: `COUNT(*)` is parsed as
   `E_Aggregate(Agg_Count, _, E_BoolLit true)` but the evaluator checked
   for `E_Var "*"`. **Rule: when adding evaluator logic for a new construct,
   check what the parser actually emits** (grep SPARQL11_Parser.ml).

8. **parse_to_scaled before parse_double_to_scaled.** `parse_to_scaled`
   treats E-notation characters as fractional digits: `"1.0E2"` parses as
   `(1000, 3)` = 1.0 instead of 100. **Rule: always try
   `parse_double_to_scaled` first** when the input might contain
   E-notation (doubles). `parse_double_to_scaled` falls through to
   `parse_to_scaled` for non-E strings, so it's safe as the default.

9. **Recursive base case kills metadata.** `eval_concat` used
   `er_string ""` (plain xsd:string, no lang tag) as its base case. When
   folding right-to-left, this stripped lang tags from the last element,
   which cascaded up. **Rule: for recursive string functions, handle the
   single-element case explicitly** to preserve language tags and datatypes.

10. **OCaml Str regex: bytes not codepoints.** OCaml's `Str` module
    operates on bytes, not Unicode codepoints. `[^a-z0-9]` matches
    individual bytes of UTF-8 multi-byte characters. Also: referencing
    an unmatched group (`\2` when group 2 didn't participate) raises
    `Not_found`. Both limit REPLACE() conformance. A Unicode-aware regex
    library (Pcre, Re) would fix this but adds a dependency.

11. **`build-ocaml.sh compile` does NOT apply `ocaml-patches.sh`.**
    Only `build-ocaml.sh extract` runs the patches. After a fresh
    extraction, you must either use `extract` or manually run
    `./ocaml-patches.sh ocaml-output`. Forgetting this silently
    regresses all `assume val` stubs to `failwith` and loses IRI
    resolution, RDF/XML validation, surrogate guards, and RDFS closure.

12. **Using `(*` in F\* comments when writing SPARQL-related code.** F\* comments
    `(* ... *)` nest. If a comment mentions SPARQL's `(*, /)` (multiplicative
    operators) or `COUNT(*)`, the `(*` opens a nested comment that silently
    swallows the rest of the file. F\* extraction will succeed but silently drop
    all definitions after the broken comment. **Use `//` line comments instead**
    when comment text contains `(*` or `*)`.

13. **Editing extracted `.ml` files directly.** Files in `ocaml-output/` that
    come from F\* extraction (`RDF_Graph_Executable.ml`, `SPARQL11_Algebra.ml`,
    `SPARQL11_Parser.ml`, `Parser_*.ml`) are **regenerated by
    `./build-ocaml.sh extract`**, destroying any manual edits. Even
    `w3c_runner.ml` (hand-written I/O glue) is patched by `ocaml-patches.sh`.
    **Rule: never edit extracted `.ml` files directly.** Instead:
    - Fix the F\* source (`.fst`) if possible (durable, verified)
    - If F\* verification blocks the fix, add a patch to `ocaml-patches.sh`
    - `ocaml-patches.sh` accepts a directory and patches all files in sequence
    A GitHub Action checks PRs for direct edits to extracted files.

14. **Never use `|| true` to swallow command failures in shell scripts.**
    `|| true` silently hides real errors. When a command might fail and you
    need the script to continue (e.g., under `set -e`), capture the exit code
    instead: `CMD_RC=0; OUTPUT=$(cmd ...) || CMD_RC=$?`. This lets the script
    continue while preserving the exit code for error reporting. The grep-based
    success checks still gate overall pass/fail.

15. **Sneaking logic into ocaml-patches.sh or w3c_runner.ml.** When a test
    fails, the temptation is to "quickly fix it" by adding OCaml code to the
    patches or test runner. This is cobbling by another name. Examples that
    happened and must be elevated to F\*:
    - RDFS reflexivity axioms computed in `w3c_runner.ml` (issue #60 —
      now resolved; lives in RDF.Graph.Executable.fst as
      `rdfs_closure_with_reflexivity`)
    - Blank-node-to-variable rewriting for entailment (issue #61)
    - Entailment regime detection and closure application
    **The test:** if the code makes a semantic decision about RDF or SPARQL,
    it belongs in `.fst` files. If it reads a file or compares strings, it's
    I/O glue and can stay. `ocaml-patches.sh` may only contain: `assume val`
    stubs, forward-reference wiring, F\* type system workarounds (with a
    comment explaining the F\* limitation), and I/O-layer fixes.

16. **Truncating command output with `tail -N` or `head -N`.** Piping test
    runners, build logs, or diagnostic output through `tail -20` (or similar)
    silently discards the vast majority of the output. When a 1000-line test
    run is piped through `tail -20`, 98% of the results vanish — including
    the specific FAIL lines needed for debugging. This happened in
    `build-ocaml.sh` where `w3c_runner --all 2>&1 | tail -20` hid all
    individual test results. **Rule: never truncate command output in
    scripts or CI.** Use `tee` to save full output to a file while still
    streaming to the terminal: `cmd 2>&1 | tee results.log`. If you only
    want a summary on screen, print the summary *after* the full run, don't
    pipe through `tail`. The same applies to `head -N` — it kills the
    process via SIGPIPE once N lines are emitted, so later output (including
    summary lines) is lost entirely.

17. **Letting ad-hoc tests hang indefinitely.** The Turtle parser is known to
    be slow on large inputs (a 35MB file ran past 6 minutes and never
    terminated in a previous session). When running an ad-hoc `factoidal
    --count`, `factoidal --dump`, or SPARQL eval on a file that isn't part
    of the W3C test suite, **always set a wall-clock cap of 10 minutes
    (600000ms) or less** via the Bash tool's `timeout` parameter or
    `timeout 600 <cmd>`. If the cap trips, **kill the process and shrink
    the input** — don't just rerun and hope. The W3C test files are
    individually tiny, so the suite itself doesn't hit this; the trap is
    benchmarks and real-world user data. If you genuinely need a longer
    run (e.g. deliberate scaling test), say so explicitly and use
    `run_in_background: true` so the main loop isn't blocked.

18. **Dump in-flight plan to disk at checkpoints.** The Claude Code harness
    persists the conversation transcript but NOT the agent's in-memory
    "what I plan to do next" state. If the session is interrupted (Esc,
    timeout, crash), that state evaporates. **Rule:** after every material
    change and before every long-running tool call, write the current plan
    + "next step I was about to take" to `.claude-worklog.md` at the repo
    root, as a timestamped bulleted entry. Overwrite the "CURRENT STATE"
    section at the top; append to the "HISTORY" section below. A new
    session should be able to read that file and resume without losing
    context.

    Minimum fields per checkpoint:
    - timestamp (UTC)
    - current goal (one line)
    - last completed step
    - next step planned
    - any in-flight processes (with PID + log path)
    - uncommitted local changes (git status summary)
    - known regressions or blockers

    Also use `TaskCreate` / `TaskUpdate` for the same information — the
    worklog is the durable on-disk mirror.

    `.claude-worklog.md` itself is gitignored (session-specific state, not
    source); a `.claude-worklog.template.md` is tracked so the format
    stays discoverable.

19. **Every long-running process goes to a timestamped log + wall-clock
    cap.** Turtle parsing, W3C test runs, F\* extraction, and anything
    that has ever been observed taking >2 minutes MUST be launched with:
    - `run_in_background: true` so the main loop isn't blocked
    - stdout+stderr redirected to a file under `.claude-runs/` named
      `<op>-<YYYYMMDD-HHMMSS>.log`
    - a hard wall-clock cap (`timeout 600` or equivalent) — if the cap
      trips, capture the log, record the stuck state in
      `.claude-worklog.md`, and do **not** just rerun and hope
    - a status line appended to `.claude-worklog.md` at launch and at
      completion: `started X at T, log=<path>, cap=<N>s`

    The 10-minute cap in rule #17 applies. This rule adds the logging +
    reporting requirements. Anything that hits the cap is a reportable
    event, not a silent rerun.

20. **Never burn clock time on the known-slow Turtle path.** The Turtle
    parser is O(n²) on file size (see "Known Performance Issues" below),
    so naive runs like `./build-ocaml.sh` (which triggers `w3c_runner
    --all`, ~3–10+ minutes) or `factoidal --count bigfile.ttl` can tie
    up the main loop for ages while eating tokens. **Before running any
    W3C-scale test, build-with-tests, or parse on non-trivial Turtle
    input:**
    - Launch it via an `Agent` subagent OR with `run_in_background: true`,
      never in the foreground of the main loop. Only the subagent /
      background stream pays the wait; the main loop keeps moving.
    - Always pass a hard `timeout` (≤ 10 minutes, often much less —
      default 300s for a single suite, 600s for `--all`). Hitting the
      cap is reportable per rule #19.
    - Prefer targeted commands over the shotgun: `./build-ocaml.sh
      extract` / `compile` / `js` / `wasm` separately; `w3c_runner
      bind functions` instead of `--all`; `factoidal --count` only on
      files that fit in rule #17's cap.
    - Don't iterate on small changes by re-running 1000s of W3C tests.
      Run one suite or one file; spot-check the diff; save the full
      suite for commit-time validation.
    - If a test is only slow because the parser is slow (not because
      the test itself is large), prefer N-Triples/N-Quads or an HDT
      ingest when possible — the pure tokenizer paths are fast.

    Rule of thumb: if the command *has ever* been observed over 60
    seconds, it goes to a subagent or background with a timeout. No
    "I'll just run it and see."

21. **Never stall on parallel work.** If a push, CI run, browser
    check, or background build is in flight, do NOT wait for it —
    pick the next independent item off the priority queue and start
    it. The notification system surfaces results when they land.
    "Let me wait and verify before moving on" is a failure mode, not
    caution — waiting idly costs the user clock time and tokens.
    Exceptions: when the next item genuinely depends on the in-flight
    result (e.g., debugging a just-failed test), or when the user
    has explicitly asked you to pause.

    Corollaries:
    - Don't batch work behind a single background task when the
      tasks are independent — run them in parallel (separate Agent
      subagents, separate `run_in_background` bashes).
    - "I should verify X first" is only true if a later step would
      be wasted if X is broken. Otherwise, start the later step;
      the verification result catches up.
    - Git push + CI redeploy is never a reason to pause. The result
      arrives hours later; the user doesn't want a progress-waiting
      loop in between.

22. **Subagent stall is a checkpoint, not a loss.** When a subagent
    reports "failed: stream watchdog" or similar, DO NOT discard its
    work. Check the tree:
    - `git status --short` — uncommitted changes may be the subagent's
      finished work, interrupted before it ran `git commit`.
    - `git log --oneline` — the subagent may have committed but not
      pushed, in which case you just push.
    - `stat -f "%m"` on the files it was supposed to touch — fresh
      mtime (minutes ago, not hours) means real work happened.

    Three of tonight's (2026-04-18/19) subagent stalls were actually
    completed work with stream disconnect; committing the tree + running
    one quick build was all that was needed. One stalled before useful
    output; `git status` being clean told us to discard and move on.

    Rule of thumb: **never re-launch a stalled subagent on the same
    task without first checking for salvageable tree state.** Mis-taken
    re-launches cost 10 minutes AND double the risk of tree contention.

23. **Scope every subagent to a single commit-sized goal.** Tonight's
    UPDATE stage (b) subagent was asked to do three operations
    (`U_InsertData` + `U_DeleteData` + `U_DeleteWhere`) plus the F\*
    mutable store model plus runner wiring plus test comparison.
    It stalled. Earlier subagents with tight single-goal scope
    (SHA pure hashes; SPARQL.Protocol.fst core; RDFS elevation; OWL
    Datalog subset; UPDATE parser stage a; Protocol HTTP server glue)
    all landed cleanly.

    Rule: one subagent = one commit = one conceptual deliverable.
    Split "store model + 3 ops + runner wiring" into 3+ separate
    subagent tasks, even if it means sequential.

24. **Subagent prompts ship code sketches, not "figure it out".**
    The 600s stream watchdog fires during long research phases
    (read many files → plan → write). Empirical rate tonight: ~40%
    of subagents stalled in research before writing any code.
    Mitigations: (a) put the concrete diff/pseudocode in the prompt,
    (b) cite the exact file + line number to edit, (c) name helper
    functions to reuse by signature, (d) cap scope at one function
    or one rule — not "implement X". And (e) pair subagent work with
    top-level inline work so progress continues when they stall.

## Known Performance Issues

### Turtle parser is too slow for real-world input

Measured on 2026-04-17 after the ballyhoo Parser.TurtleScanner integration:

| N triples | File size | Time |
|-----------|-----------|------|
| 1,000     | 56 KB     | 25 seconds |
| 10,000    | 576 KB    | > 8 minutes (killed) |
| ~700,000  | 35.8 MB   | > 6 minutes (never observed to finish) |

The scanner integration (span-based tokens, ASCII fast path, tail-recursive
list accumulation via `rev_prepend`) helped vs. the pre-ballyhoo parser, but
the per-triple constant is still on the order of 25 ms for short triples —
roughly 40 triples/s. Scaling to 10k triples appears super-linear, suggesting
an `O(n*k)` or worse path somewhere beneath F*'s extraction (likely in the
`FStar_String.sub` / `Z.t` arithmetic that gets threaded through every char
operation).

**Working around this:**
- For real data (tens of MB+), use the HDT or COTTAS binary backends
  (`Parser.BallyhooHDT`, `Parser.BallyhooCOTTAS`, already on main). These
  bypass Turtle parsing entirely. **Caveat:** neither is a verified F\*
  reader today — the F\* modules fix the API shape via `assume val`, and
  the HDT path shells out to the external `hdtSearch` CLI. See
  `docs/designissues/2026-04-19-hdt-fstar-status.md` for the full audit
  before relying on these for anything other than existing use cases.
- The architectural path in `docs/designissues/turtle-text-scanner.md`
  still has steps 4 (chunk-resumable scanning) and 5 (revisit doc-level
  parsing) as future work. Chunk-resumable won't fix the per-char
  constant, but may unlock streaming/incremental use.
- **The structural plan** lives in
  `docs/designissues/2026-04-19-turtle-parser-speed.md` — three named
  bottlenecks (`nat`→`Z.t` positions, eager `span_to_string`, O(n)
  list append in the grammar) and a phased A/B/C/D plan to close the
  ~250× gap. Read that before starting new Turtle perf work so we
  stop spending cycles on constant-factor tweaks to the scanner.
- Solving this may ultimately require either (a) replacing hot extracted
  string primitives with direct OCaml Bytes operations (via a narrow
  `assume val` boundary), or (b) a hand-written non-F* tokenizer that
  feeds the verified grammar layer. Both would require per-project-rule
  discussion since they weaken the verified surface. The speed plan
  argues Phase B (machine-int positions) is the verified-friendly
  alternative that should be tried first.

Ad-hoc parse tests MUST be capped at 10 minutes per rule #17 above.

## Current State (Honest Assessment)

### F\* Specifications

```
formal/fstar/
  RDF.Graph.Executable.fst     1052 lines, 0 admit, 0 assume val
  SPARQL11.Algebra.fst        3783 lines, 4 admit (proof lemmas), 12 assume val
  SPARQL11.Parser.fst         2942 lines, 3 assume val
                               ⚠ ~65% uses --admit_smt_queries true (see below)
  Parser.Combinators.fst       387 lines — parser combinator foundation
  Parser.NTriples.fst          679 lines
  Parser.Turtle.fst           1339 lines
  Parser.NQuads.fst            302 lines
  Parser.TriG.fst              505 lines
  Parser.XML.fst               602 lines
  Parser.RDFXML.fst            812 lines
  Parser.SRX.fst               273 lines
  Parser.CSVResults.fst        610 lines
  Parser.JSONResults.fst       408 lines
  Makefile                     verify + extract-c targets
  build-ocaml.sh               F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh             master script: applies all patches from
                               minimal_regrettable_glue_code_each_with_an_open_issue/
  minimal_regrettable_glue_code_each_with_an_open_issue/
                               individual patch files, each named
                               <issue>_<description>.sh with GitHub issue
```

### ⚠ Verification Gaps — Be Honest About These

**SPARQL11.Parser.fst** uses `--admit_smt_queries true` from approximately
line 802 to line 2722 (~1920 lines, ~65% of the file). This means Z3 does
NOT verify the proof obligations for the parser's mutually recursive
functions. The parser type-checks but the SMT proofs are not discharged.
This is a significant gap in the formal verification story and must be
disclosed when claiming "verified."

**ASK query comparison in w3c_runner.ml** does not check the expected
boolean value — ASK tests always pass regardless of the query result. This
inflates the pass count slightly.

**Blank node comparison** in the test runner uses a simplified matching
(any bnode matches any other bnode) rather than proper graph isomorphism.
Some tests may pass that shouldn't under strict comparison.

### Known Gaps in RDF.Graph.Executable.fst

The F\* RDF graph spec uses **syntactic equality only**. It lacks:

- **Language tag case-insensitivity**: `literal_eq` compares `lang_tag` with `=`
  (string equality). Per RDF 1.1, `@en-US` and `@en-us` denote the same value.
- **Plain literal ↔ xsd:string equivalence**: Per RDF 1.1, `"foo"` (plain) and
  `"foo"^^xsd:string` are the same value. The spec treats them as distinct.
- **Datatype value equivalence**: `"010"^^xsd:integer` and `"10"^^xsd:integer`
  denote the same value. The spec compares lexical forms as strings.
- **RDFS closure rules**: No subClassOf/subPropertyOf inference, no domain/range
  type inference, no container membership property axioms.

These are not exotic features — they are what the W3C rdf-mt test suite tests.

### OCaml Output (extracted + test glue)

```
formal/fstar/ocaml-output/
  RDF_Graph_Executable.ml    F*-extracted OCaml
  SPARQL11_Algebra.ml        F*-extracted OCaml (patched for assume vals)
  SPARQL11_Parser.ml         F*-extracted SPARQL parser
  Parser_Combinators.ml      F*-extracted parser combinators
  Parser_NTriples.ml         F*-extracted N-Triples parser
  Parser_Turtle.ml           F*-extracted Turtle parser
  Parser_NQuads.ml           F*-extracted N-Quads parser
  Parser_TriG.ml             F*-extracted TriG parser
  Parser_XML.ml              F*-extracted XML parser
  Parser_RDFXML.ml           F*-extracted RDF/XML parser
  Parser_SRX.ml              F*-extracted SRX (SPARQL Results XML) parser
  Parser_CSVResults.ml       F*-extracted CSV/TSV results parser
  w3c_runner.ml              W3C manifest reader + test runner CLI (I/O glue)
  fstar_int_stubs.js         js_of_ocaml int stubs
```

Hand-coded parsers have been deleted. Legacy copies remain in `junk/do_not_use/hand_coded_parsers/` as a warning.

### assume val inventory (SPARQL11.Algebra.fst)

| assume val | Purpose | Stub |
|-----------|---------|------|
| `regex_match` | SPARQL REGEX | OCaml `Str` in ocaml-patches.sh |
| `regex_replace` | SPARQL REPLACE | OCaml `Str` in ocaml-patches.sh (forward ref) |
| `hash_md5` | MD5 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha1` | SHA-1 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha256` | SHA-256 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha384` | SHA-384 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha512` | SHA-512 hash | OCaml `Digest` in ocaml-patches.sh |
| `eval_expr_ebv` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_expr_fwd` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_exists_fwd` | forward decl (EXISTS) | wired in ocaml-patches.sh |
| `eval_subselect_fwd` | forward decl (subqueries) | wired in ocaml-patches.sh |
| `eval_property_path_fwd` | forward decl (property paths) | wired in ocaml-patches.sh |

### Plain-English Status Summary (as of 2026-04-16)

Factoidal is a formally verified RDF/SPARQL implementation written in F\* and
tested against the official W3C conformance suites. The core SPARQL query
evaluator passes 375 of 418 applicable query/syntax tests (90%), with perfect
scores in BIND (10/10), EXISTS (6/6), grouping (6/6), project-expression (7/7),
property paths (33/33), CSV/TSV results (6/6), JSON results (4/4), and
near-perfect in functions (74/75), aggregates (45/46), negation (11/12),
syntax-query (93/94). The main SPARQL gaps are: UPDATE not yet implemented
(205 tests skipped — in scope, tracked by #59), Protocol not yet implemented
(34 tests skipped), SERVICE returns empty (needs HTTP client, tracked by #57),
OWL entailment (26 entailment failures are mostly OWL-specific, beyond RDFS),
and CONSTRUCT partially implemented (2/7, 4 need Turtle result serializer).

On the RDF parsing side, F\*-extracted parsers handle all six serialization
formats: N-Triples 41/70, Turtle 296/313, N-Quads 53/87, TriG 338/356,
RDF/XML 121/166, rdf-mt 39/39. Most remaining parser failures are
negative-syntax validation (the parser is too lenient — accepts input it
should reject) and prefixed name edge cases.

**Caveats on test numbers (be honest):** ASK query comparison in w3c_runner.ml
does not check the expected boolean value — ASK tests always pass. Blank node
matching is simplified (any bnode matches any other) rather than proper graph
isomorphism. These may inflate the pass count slightly.

### W3C Test Results (as of 2026-04-16)

**SPARQL 1.1 — 375 pass, 43 fail, 205 skip, 8 unsupported (631 total)**

Per-suite: aggregates 45/46, bind 10/10, bindings 10/10, cast 4/6,
construct 2/7, csv-tsv-res 6/6, delete-insert 8/8, entailment 44/70,
exists 6/6, functions 74/75, grouping 6/6, json-res 4/4, negation 11/12,
project-expression 7/7, property-path 33/33, service 0/7,
subquery 9/14, syntax-query 93/94, syntax-fed 3/3.
Not yet implemented: 205 UPDATE operations (add, basic-update, clear, copy,
delete, delete-data, delete-where, drop, move, http-rdf-update,
syntax-update-\*, update-silent). Protocol: 34 not yet implemented.
Service-description: 3 not yet implemented.

**RDF 1.1 — 888 pass, 143 fail (1031 total)**

Per-suite: N-Triples 41/70, Turtle 296/313, N-Quads 53/87, TriG 338/356,
RDF/XML 121/166, rdf-mt 39/39.

**RDF 1.1 Model Theory — 39 pass, 0 fail (39 total)**

All rdf-mt tests pass: literal equivalence, datatype handling, RDFS closure
rules, language tag normalization, value-space entailment with consistent
blank node mapping.

### What rdf-mt Actually Tests (39 tests)

| Category | Count | What It Tests | F\* Status |
|----------|-------|---------------|------------|
| Simple matching | 7 | Language tag distinction, URI matching, reification non-entailment | **PASS** |
| Literal/datatype semantics | 20 | Value equivalence, plain↔xsd:string, lang tag case, ill-formedness | **PASS** |
| RDF closure rules | 4 | Container membership (rdf:\_n), rdfs:member superProperty | **PASS** |
| RDFS closure rules | 14 | subClassOf, subPropertyOf, domain, range, intensional semantics | **PASS** (via ocaml-patches.sh closure) |
| Advanced model theory | 3 | Value space disjointness, completeness axioms | **PASS** (not tested — 9 skipped) |

## What Was Removed (junk/do_not_use/)

Everything in `junk/do_not_use/` is **vibe-coded or derived from vibe-coded
artifacts**. Do not use it. Do not revive it.

## The Plan

### Architecture

```
F* formal spec (the product)
    |
    v
fstar.exe --codegen OCaml (extraction, proof-erased)
    |
    v
OCaml test runner (minimal I/O glue only)
    |-- reads W3C manifest files from disk (I/O)
    |-- calls F*-extracted parsers for .rq/.ttl/.nt/.nq/.trig/.rdf/.srx
    |-- calls F*-extracted evaluator
    |-- compares actual vs expected (using F*-extracted comparison)
    |-- emits pass/fail per test
    v
W3C SPARQL 1.1 + RDF 1.1 conformance results
```

### Phase 1 — SPARQL test infrastructure (DONE)

W3C test runner works. 303/408 SPARQL eval/syntax tests pass (105 fail,
205 skip/update, 18 unsupported format).

### Phase 2 — Fix RDF semantics in F\* (MOSTLY DONE)

1. **Language tag case-insensitive comparison** — DONE (`lang_tag_eq` in F\*)
2. **Plain literal ↔ xsd:string equivalence** — DONE (`literal_value_eq`)
3. **Datatype value space equivalence** — DONE (`datatype_value_eq`, `normalize_integer_lexical`)
4. **RDFS closure rules** — DONE (`rdfs_closure` with subPropertyOf, domain, range, subClassOf, container membership)
5. **Simple entailment** (blank node as existential variable) — TODO

Remaining: re-extract, wire into test runner, run rdf-mt tests.

### Phase 3 — F\* parsers (IN PROGRESS)

Replace hand-written OCaml parsers with F\*-extracted implementations.

**Parser architecture**: `Parser.Combinators.fst` provides the combinator
foundation (pchar, pstring, psat, pbind, pmap, palt, pmany, etc.). All parsers
are built on this. `Parser.XML.fst` is a **non-validating XML parser** — it
reads well-formed XML into a tree but does NO DTD processing, NO external entity
resolution, NO schema validation. Only predefined entities (&amp; &lt; &gt;
&quot; &apos;) and character references (&#123; &#x1A;). Namespace prefixes are
preserved as part of element/attribute names (namespace URI resolution is the
RDF/XML layer's job, not the XML parser's).

1. N-Triples parser in F\*
2. Turtle parser in F\*
3. N-Quads parser in F\*
4. TriG parser in F\*
5. RDF/XML parser in F\* (uses Parser.XML.fst — non-validating XML parser)
6. CSV/TSV results format parser in F\*
7. SRX (SPARQL Results XML) parser in F\*
8. SPARQL query parser in F\* (SPARQL11.Parser.fst started)

### Phase 4 — Close SPARQL gaps

Working from test failures, extend the F\* SPARQL spec:

1. **Result formats** — JSON Results (`application/sparql-results+json`),
   CSV (`text/csv`), TSV (`text/tab-separated-values`) serializers in F\*.
   SRX parser already exists; JSON/CSV/TSV result parsers needed for test
   comparison. ~20 tests blocked.
2. **SPARQL UPDATE** — INSERT DATA, DELETE DATA, INSERT/DELETE (with WHERE),
   LOAD, CLEAR, DROP, ADD, MOVE, COPY, CREATE. Requires mutable graph store
   model in F\*. 205 tests. Tracked by #59.
3. **SPARQL Protocol** — HTTP interface for query and update operations.
   34 tests. Requires HTTP server, which can use `assume val` with OCaml
   stub (see I/O and networking below).
4. **SERVICE (federated query)** — Requires HTTP client to contact remote
   SPARQL endpoints. 7 tests. Tracked by #57.
5. **Service Description** — 3 tests.

### Phase 5 — I/O, Networking, and Async

F\* extracted code is pure/total by default. Networking (SERVICE, Protocol,
LOAD) requires I/O effects. Strategy:

- **`assume val` for I/O primitives.** Declare HTTP client/server operations
  as `assume val` in F\* with OCaml stubs. This keeps the verified boundary
  around query semantics while allowing real network operations.
- **Simple synchronous blocking API.** For `web_fetch : url -> result`, a
  blocking OCaml stub using `Unix.open_connection` or `Cohttp_lwt_unix` is
  the simplest approach. Good enough for test runner and CLI usage.
- **Async considerations for extracted applications.** When F\*-extracted code
  runs in a larger async context (e.g., a web server), the blocking stubs
  become a problem. Options:
  1. **Thread pool** — run blocking F\* calls in a thread pool, integrate
     with Lwt/Async via `Lwt_preemptive.detach` or similar.
  2. **Effect-polymorphic F\*** — F\* has `Effect` and `PURE`/`DIV`/`ST`
     effect system. In principle, I/O effects can be modeled, but extraction
     of effectful code to async OCaml is not well-supported by F\* today.
  3. **js_of_ocaml + promises** — for browser/Node targets, blocking I/O
     is impossible. The js_of_ocaml path would need promise-based stubs
     with continuation-passing, which is architecturally different.
  The current plan: start with blocking stubs (#57), document the limitation,
  and track async extraction as a separate research issue.

### Phase 6 — Verified extraction pipeline

- Low\* rewrite for standalone C extraction via KaRaMeL
- CI: verify F\* → extract → test → sign

## Setup

### First-time clone

```bash
git clone --recurse-submodules https://github.com/danbri/factoidal.git
cd factoidal

# If already cloned without --recurse-submodules:
git submodule update --init --recursive
```

The W3C test files live in `tests/w3c/` (submodule pointing to
`github.com/w3c/rdf-tests`). Without initialising the submodule, the test
runner will have no test data.

### System prerequisites

```bash
# Debian/Ubuntu
sudo apt-get install -y opam libgmp-dev pkg-config

# macOS (Homebrew)
brew install opam gmp pkg-config
```

### F\* toolchain (opam)

```bash
# Initialize opam (first time only)
opam init -y
# Create the F* switch:
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install fstar z3 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js

# Activate (run in every new shell)
eval $(opam env --switch=fstar)
```

### Install z3 (CRITICAL — verification cannot work without it)

**This project is about verified code. z3 is not optional.** Every session must
ensure z3 is available before doing any F\* work. Without z3, extraction and
verification will fail.

```bash
# Check if z3 is available:
z3 --version  # must show 4.13.3

# If z3 is missing, install the pre-built binary (opam build often fails):

# Linux x86-64:
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip" -o z3.zip
unzip -q z3.zip
cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
chmod +x /usr/local/bin/z3-4.13.3
ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# macOS arm64 (Apple Silicon):
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip" -o z3.zip
unzip -q z3.zip
cp z3-4.13.3-arm64-osx-13.7/bin/z3 /usr/local/bin/z3-4.13.3
chmod +x /usr/local/bin/z3-4.13.3
ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# macOS alternative (may not get exact version):
brew install z3

# Verify it works:
z3-4.13.3 --version  # must show "Z3 version 4.13.3"
```

**Do NOT use `--lax` at all.** All F\* modules must verify and extract without
`--lax`. The `--lax` flag is banned — it defeats the purpose of formal
verification. Install z3 first, then verify and extract.


### Quick verification

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

# Verify F* specs
make verify

# Extract + compile + test
./build-ocaml.sh

# Run W3C tests (w3c_runner is built by build-ocaml.sh)
cd ocaml-output
./w3c_runner                    # all SPARQL suites
./w3c_runner --rdf              # RDF parser suites
./w3c_runner --all              # both
./w3c_runner --list             # list suites
./w3c_runner bind functions     # specific suites
./w3c_runner -v aggregates      # verbose: full expected/actual dump on stderr
```

**Failure output**: FAIL lines always show UNMATCHED expected rows inline.
Use `-v` for the full expected/actual row dump (goes to stderr).

### Extraction notes

- **Never use `--lax`** — all modules must verify before extraction
- `--codegen OCaml` erases proofs, ghost code, spec-only material
- Extracted `.ml` files use `FStar_*` runtime from `fstar.lib` opam package
- `assume val` declarations extract as `failwith "Not yet implemented"` — must be patched
- `noeq` types block KaRaMeL C extraction (OCaml extraction works fine)

### W3C Test Suites

```
tests/w3c/                          git submodule: github.com/w3c/rdf-tests
  rdf/rdf11/rdf-n-triples/         N-Triples syntax tests (70)
  rdf/rdf11/rdf-turtle/            Turtle syntax+eval tests (313)
  rdf/rdf11/rdf-n-quads/           N-Quads syntax tests (87)
  rdf/rdf11/rdf-trig/              TriG syntax+eval tests (356)
  rdf/rdf11/rdf-xml/               RDF/XML eval tests (166)
  rdf/rdf11/rdf-mt/                Model theory / semantics (39)
  sparql/sparql11/                 SPARQL 1.1 test suites (34 suites, 631 tests)
```

## Key Dependencies

- `fstar` — F\* compiler (opam, 2025.12.15)
- `z3` — SMT solver (required by F\*)
- `fstar.lib` — F\* OCaml runtime library (opam)
- `str` — OCaml regex library (for regex_match stub)
- `zarith` — arbitrary-precision integers (F\* extracts `Prims.int` as `Z.t`)
- `js_of_ocaml` — OCaml to JavaScript compiler (optional)
- `zarith_stubs_js` — bigint stubs for js_of_ocaml (optional)
- `libgmp-dev` — system package required by zarith (apt-get)

## GitHub CLI (`gh`) in Claude Code

The git remote uses a local proxy (`127.0.0.1`), so `gh` commands that infer
the repo from the remote will fail with "none of the git remotes configured
for this repository point to a known GitHub host." **Fix: always pass
`--repo danbri/factoidal` explicitly.**

```bash
# These work:
gh pr create --repo danbri/factoidal --base claude/main --head my-branch ...
gh pr list --repo danbri/factoidal
gh pr view 42 --repo danbri/factoidal

# This does NOT work (no --repo):
gh pr create --base claude/main ...  # ERROR: unknown host
```

## Repository Structure

```
factoidal/
├── formal/fstar/              THE PRODUCT
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator
│   ├── SPARQL11.Parser.fst        SPARQL parser (in development)
│   ├── Parser.*.fst               RDF format parsers (combinators, Turtle, etc.)
│   ├── Makefile
│   ├── build-ocaml.sh
│   ├── ocaml-patches.sh               applies patches from glue directory
│   ├── minimal_regrettable_glue_code_each_with_an_open_issue/
│   │   ├── 53_blank_node_variable_rewriting.sh
│   │   ├── 62_forward_ref_wiring.sh
│   │   ├── 63_regex_hash_uuid_stubs.sh
│   │   ├── 64_sparql_parser_escape_stubs.sh
│   │   ├── 65_base_iri_resolution.sh
│   │   ├── 66_zero_length_property_path.sh
│   │   ├── 67_rdfxml_validation.sh
│   │   ├── 68_unicode_boundary_workarounds.sh
│   │   └── 69_runner_io_glue.sh
│   └── ocaml-output/          extracted .ml + symlinks to bin/<platform>/
├── bin/                       pre-built binaries per platform
│   ├── darwin-arm64/          macOS Apple Silicon
│   │   ├── factoidal
│   │   └── w3c_runner
│   └── linux-x86_64/         Linux x86-64 (statically linked)
│       ├── factoidal
│       └── w3c_runner
├── tests/w3c/                 git submodule (W3C test files)
├── kgx/                       SPARQL CONSTRUCT queries (future)
├── docs/
│   ├── designissues/          architecture docs
│   └── skills/                operational knowledge
├── junk/do_not_use/           vibe-coded artifacts (DO NOT USE)
└── CLAUDE.md                  this file
```
