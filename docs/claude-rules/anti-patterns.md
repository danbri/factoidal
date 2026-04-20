# Anti-Patterns — Do NOT Repeat These Mistakes

Previous Claude sessions made these errors. Read and internalize.

This is the expanded "why" file. The short-form rule titles live next to
this file in `CLAUDE.md`'s main body (when they do); the full context,
war-stories, and verbatim justifications live here, keyed by number.

The numbers below match the numbering in commit messages and in
cross-references like "per rule #17" throughout the codebase. They are
stable — do not renumber.

---

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

25. **Never write cryptic score strings.** "SPARQL 527/37/58/9, RDF
    972/59, entailment 51/19, rdf-mt 39/0" is unreadable. Always
    write the full form: "SPARQL 1.1 query suite: 527 pass, 37 fail,
    58 skip, 9 unsupported (out of 631)". "RDF 1.1 parser suites:
    972 pass, 59 fail (out of 1031)". Etc. Every number earns its
    label; fraction-like strings are banned from commits, commit
    messages, chat output, and docs. Readability over brevity.
