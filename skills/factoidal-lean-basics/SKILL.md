---
name: factoidal-lean-basics
description: Work with Factoidal's Lean 4 tree under formal/lean4/, including scope inspection, builds, tests, proof policy, executable and WASM paths, and recorded workflow failures. Use for Lean changes, port planning, capability questions, or environment setup.
---

# Factoidal Lean basics

## What exists (started 2026-08-22; re-measure before scope claims)

`formal/lean4/` is a self-contained lake project, library name
`L4Factoidal` (naming deliberately not finalised — owner: "don't rush
that"). Workstream + continuation ladder:
https://github.com/danbri/factoidal/issues/466

| Area | Files | Content |
|---|---|---|
| RDF core | `RDF/Core.lean`, `XmlCanon.lean`, `Graph.lean` | term model, XMLLiteral c14n, graphs/datasets, bnode renaming; eqb transitivity + membership/length lemma families |
| Isomorphism | `RDF/Isomorphism*.lean` | §3.6 spec + witness-returning bounded search, soundness proved |
| Canonicalisation | `RDF/Canonical*.lean`, `Harness/CanonProbe.lean` | RDFC-1.0 parameterised by `HashAlgorithm`; §3 sortedness + issuer injectivity proved; rdf-canon suite 86 pass, 0 fail (of 86) |
| SPARQL algebra | `SPARQL/Algebra.lean`, `PropertyPath.lean`, `Invariants.lean` | 15-constructor GraphPattern (GRAPH/LATERAL/BIND/VALUES/SERVICE/sub-SELECT/paths), dataset-aware `evalIn`; monotonicity/merge/empty laws proved |
| SPARQL physical paths | `SPARQL/IndexedEvalRefinement.lean`, `AlgebraRefinement.lean`, `StoreBackend.lean`, `StorePlan.lean`, `StoreFastPath.lean`, `StoreDataset.lean` | exact-list indexed BGP/hash-join refinement; partial declarative algebra refinement; backend capabilities, planning, fast paths, and dataset routing |
| Cottas | `Cottas/*.lean` (33 files at `73209342c232`) | total reader/writer, dictionaries, on-disk search, selective decode, planning, pruning, counts, presence and offset indexes |
| HDT | `HDT/*.lean` (5 files at `73209342c232`) | container, theorems, dictionary, triples, and static store |
| SPARQL expressions | `SPARQL/Expr*.lean` | §17 EBV, scaled numerics (order proved), §17.3 logic, builtins; EXISTS/NOW/extension fns/SERVICE via `EvalEnv` parameters |
| SPARQL query | `SPARQL/Query*.lean` | QueryPattern→GraphPattern lowering, forms, modifiers, aggregates; ORDER BY permutation + DISTINCT laws proved; LATERAL cases pinned |
| SPARQL results | `SPARQL/Results*.lean` | SRX/SRJ/CSV/TSV parse+serialise; SRJ N-row shape theorem proved |
| RDFS | `RDFS/Vocabulary.lean`, `RdfsCore.lean`, `Closure*.lean` | rdfs-core derivation relation + closure; extensive/sound/complete-at-saturation proved |
| RDF syntaxes | `Syntax/Lexing.lean`, `NTriples.lean`, `NQuads.lean`, `Turtle.lean`, `TriG.lean`, `IriResolve.lean`, `Harness/TurtleProbe.lean` | rdf11+rdf12 parse/serialise; RFC 3986 resolution (all §5.4 examples guarded); rdf-turtle eval 111 of 111, rdf-trig 107 of 108 |
| XML | `XML/*.lean`, `xmlconf-probe` | XML 1.0 parser with 20 WFCs, namespaces; xmlconf probe cross-checked file-by-file against F\* |
| JSON | `JSON/*.lean` | RFC 8259 parser/serialiser; escape + literal round-trips proved |
| Crypto | `Crypto/SHA2*.lean`, `Crypto/Ed25519.lean` | SHA-256/384/512 + `HashAlgorithm` agility; size theorems; FIPS vectors (million-byte ones parked opt-in). Ed25519 = the ONE `@[extern]` (HACL\* C through `lakefile.lean` `extern_lib`) |
| JSON-LD 1.1 | `JSONLD/{Context,Expand,ToRdf,Compact,Flatten,FromRdf,Html}.lean`, `Harness/{JsonLdProbe,JsonLdApiProbe}.lean` | context processing, expansion, toRdf, compaction (§6), flattening (§7), Serialize RDF as JSON-LD (§8.5-8.7), HTML script extraction; loader is a parameter, framing out of scope. `l4jsonld-probe` toRdf 467 pass, 0 fail, 0 skip (out of 467); `l4jsonld-api` expand+compact+flatten+fromRdf+html 791 pass, 0 fail, 2 local-override (out of 793) — matching the F\* runners manifest for manifest |
| VC / DID | `VC/*.lean`, `Harness/VcProbe.lean` | Data Integrity `eddsa-rdfc-2022` create/verify (canonical forms, datasets, JSON-LD documents; primitives are parameters), base58/multibase with the decode-of-encode theorem, did:key both ways; `l4vc-probe` 58 pass, 0 fail (RFC 8032 22, did:key 8, vc_runner roundtrip 8, W3C vc-di-eddsa spec vectors 20) |
| Wasm | `Wasm/`, `docs/web/hub/assets/l4/`, skill `lean4-wasm-export` | Lean→C→wasm via Emscripten (1.4 MB, ~40 ms load); hub post 36 runs Lean and F\* side by side |
| Tests/demo | `Tests.lean`, `Demo.lean` | build-time guards + `#print axioms` audit; runnable tour |
| Docs | `README.md` / `PORT_NOTES.md` | reviewer reading order / F\* correspondence, decisions, assumption report |

Measured 2026-08-22, late: the library has zero `sorry`, zero user `axiom`, zero `native_decide`, and exactly ONE `@[extern]`/`opaque` family (HACL* Ed25519, `Crypto/Ed25519.lean`). ⚠️ `partial def` is NOT zero and is GROWING FAST. **Re-measured 2026-08-29: 212 declarations across 35 library files, plus 14 across 9 harness files.** The library breakdown is XPath 44, ShEx 50, OWL 37, XSLT 27, RIF 15, Math 11, Geo 6, MathML 5, Testing 4, GRDDL 3, XForms/JSONSchema/CSVW 2 each, and XSD/Storage/Schematron/HTTP 1 each. `formal/lean4/Wasm/` contains none. RDF, RDFS, SPARQL, Cottas, HDT, SHACL, JSON-LD and `Unified/` have no live `partial def` declarations. OWL is not clean: its 37 include the tableau search and materialization functions. WHY IT COSTS: a `partial def` compiles to an opaque constant — no equation lemmas, no kernel reduction, invisible to `decide`. ⚠️ It is NOT invisible to `#guard`: `#guard` evaluates through the INTERPRETER, so a guard whose expression calls a `partial def` does run and does fail the build when the expression is false. Measured 2026-08-26 on a `partial def loopy`: `#guard loopy 3 == 99` errors with "did not evaluate to `true`", while `example : loopy 3 = 7 := by decide` fails with "its `Decidable` instance did not reduce to `isTrue` or `isFalse`". The line is interpreter vs kernel. So a `partial def` CAN be pinned by `#guard` and CANNOT be the direct subject of the same equation proof. That happened on 2026-08-26: design doc §4.7 puts `RIF.Engine.saturate` on the left of `unified_adequate_rifCore`, and `groundTm`/`matchFormula`/`qualifyTm` being `partial` forced the landed theorem onto `DatalogProgram.lfp`, with engine agreement demoted to a `#guard` pin (https://github.com/danbri/factoidal/issues/612). Whether these are accepted debt or must be made total is tracked with the full breakdown at https://github.com/danbri/factoidal/issues/617. Do not quote any `partial def` figure without re-measuring. Method that excludes prose mentions inside comments: `rg '^\s*(private\s+|protected\s+)?partial def\b' formal/lean4/L4Factoidal`.

## Toolchain

- Install: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y`.
- **PATH trap (2026-08-22, paid for):** every fresh harness shell
  needs `export PATH="$HOME/.elan/bin:$PATH"` or `lake` is absent —
  and a gate script that silently loses `lake` LOOKS like it passed.
  During the MINUS sabotage demo the first "the build caught nothing"
  result was actually "the build never ran" (`command not found`
  filtered away by a grep for 'error'). Always confirm the tool ran
  before trusting its silence.
- The lakefile is `lakefile.lean` (Lean DSL) since the VC stage — the
  TOML format has no `extern_lib`; keep new targets in the DSL.
- `formal/lean4/lean-toolchain` pins the version (4.33.1 at
  creation); elan auto-fetches it. Bump only deliberately, own
  commit, green `lake build`.
- **Zero dependencies** — no mathlib, no batteries, core Lean only.
  Keep it that way until a theorem genuinely needs mathlib (that
  costs a multi-GB fetch or `lake exe cache get` on every fresh
  machine). Corollary: lemma names found via loogle/leansearch are
  often mathlib-only — check for `Init.*`/`Std.*` (core) namespaces
  before using.

## Build, test, demo

- `cd formal/lean4 && lake build` — this IS the test run and the
  proof check: `#guard` expressions evaluate during elaboration, so a
  wrong answer is a build error; every theorem is kernel-rechecked.
- `formal/lean4/Wasm/build-wasm.sh` — rebuild the WebAssembly artifact.
  Needed whenever a Lean change must reach the browser, and whenever
  `lean-toolchain` is bumped (the wasm objects are generated from the
  toolchain's core sources, so a version bump without a rebuild leaves
  the artifact built against the old core library).
- `lake env lean --run Demo.lean` — the human-facing tour: BGP rows
  printed Turtle-ish, the §18.5 MINUS domain-disjointness contrast,
  live monotonicity, RDF 1.2 triple-term matching, the literal
  equality subtleties.
- **Sabotage testing** (do this when extending): deliberately break a
  semantic clause, confirm `lake build` FAILS at a named `#guard` or
  theorem, restore (`git checkout -- <file>`), confirm green.
  Verified example: deleting MINUS's `!domainsDisjoint` conjunct
  fails `Tests.lean:89` with the violated expression printed.
- ⚠️ **`Wasm/Ops/*.lean` was OUTSIDE that safety net until 2026-08-26.**
  The dispatch ops carried no `#guard` at all — they were gated only by
  `Wasm/native-smoke.sh` and `Wasm/cli-smoke.sh`, which need a built
  binary and an explicit run. Measured by sabotage while adding the
  CL/IKL ops of https://github.com/danbri/factoidal/issues/623:
  replacing `clFiniteSat`'s `noSeqQuantList` test with `false` — so the
  op ANSWERS where it is meant to REFUSE, outside the hypothesis of
  `satisfiesFin_eq` — left `lake build` reporting
  "Build completed successfully"; only the smoke script failed. A
  session that ran the build and not the scripts would have shipped it.
  `Wasm/Ops/CL.lean` now carries `#guard`s for its refusals and
  refutations (re-running the same sabotage fails the build at the two
  named guards), and the same should be done for the other ops modules,
  which are still smoke-script-only. When you add an op, pin the
  NEGATIVE cases: an op answering `true` unconditionally passes every
  affirmative guard.
- New `#guard`s go in `Tests.lean`; new theorems in `Invariants.lean`
  (or a sibling), each with a doc comment citing the spec section.

## Proof policy (stricter than the F\* tree's)

- **No `sorry`. No user `axiom`. No `native_decide`** (it adds trust in
  the compiled evaluator via `Lean.ofReduceBool`). Partial functions
  (`partial def`) also count as debt. New semantic, SPARQL, storage, and block-
  engine definitions must be total. Existing partial declarations outside
  those areas are measured above and tracked separately.
- Audit: `#print axioms <theorem>`. Acceptable base is exactly
  `propext`, `Classical.choice`, `Quot.sound` (Lean's standard
  foundations). `Tests.lean` keeps audit lines on the headline
  theorems so every build log shows it.
- Well-formedness witnesses for string constants are `rfl` (kernel
  evaluation) — the Lean counterpart of F\* `assert_norm`. For
  literals built by concatenation at call sites, use the autoparam
  pattern: `def iri! (s : String) (h : isIri s := by rfl) : WfIri`.

## Purity doctrine — the Lean answer to F\* `assume val`

Lean's equivalents are `axiom`, `sorry`, `@[extern]`/`opaque` (host
implementations), and `partial`. This project uses NONE of the first
two. `partial` was harness-only by design, but has since entered
non-core library modules (see the baseline note above — open decision); `@[extern]`/`opaque`
exists in exactly ONE place — `Crypto/Ed25519.lean`, HACL\* Ed25519 via
Lake's `extern_lib` (`lakefile.lean`, `ffi/hacl_ed25519.c`), the single
permitted extern family under the crypto-policy skill's Lean 4
amendment, with its trust statement in the module header and its
run-time measurement (RFC 8032 vectors) in `lake exe l4vc-probe`. The ten
`assume val`s in `SPARQL11.Algebra.fst` (none in the ported fragment)
each dissolve by parameterisation when their feature is ported:

| F\* `assume val` | Pure Lean form |
|---|---|
| SHA/MD5 hash builtins (§17.4.4) | implement in pure Lean; provable against a spec |
| Unicode case mapping | pure tables/functions |
| `NOW()` | timestamp passed as an argument; clock read once in `IO main` |
| `extension_function_call` (§17.6) | a typed function argument to eval, not a global registry |
| `service_endpoint_lookup` | an endpoint→graph map passed into evaluation |
| `eval_property_path_fwd` | F\* file-ordering artifact; doesn't arise |

Principle: what F\* asserted in a comment ("pure from F\*'s
perspective") Lean expresses in types — the semantics is a total
function of explicit inputs; real I/O lives typed in `IO` at the
executable edge only.

## Interactive tooling

- **lean-lsp-mcp** — registered in `.mcp.json` as `lean-lsp`, run via
  `uvx lean-lsp-mcp` (needs uv:
  `curl -LsSf https://astral.sh/uv/install.sh | sh`). The Lean
  analogue of the repo's `fstar` MCP: file diagnostics, the GOAL
  STATE at a position (the thing you need when a tactic fails), hover
  docs, lemma-search bridges. First call is slow (boots the Lean
  server on the lake project). Prefer it over re-running `lake build`
  to chase one error.
- **Lemma search**: https://loogle.lean-lang.org/ (by type shape,
  e.g. `?a ++ ?b = ?b ++ ?a`), https://leansearch.net/ (natural
  language); in-Lean `exact?`, `apply?`, and `simp?` (then PIN the
  lemmas it reports — don't leave bare `simp?`).
- For a human reviewer: the VS Code "lean4" extension's infoview.
- Deeper automation (aesop, omega is already core, mathlib tactics)
  only when a theorem demands it — see the zero-dependency rule.

## Pitfalls already paid for (don't rediscover)

1. **Derived `BEq` is lawless.** `deriving BEq` gives an instance
   with no `LawfulBEq`, so `x == x` is unprovable by `simp` and
   `beq_iff_eq` is unavailable. Derive `DecidableEq` INSTEAD and let
   `instBEqOfDecidableEq` provide a lawful `==`. (Cost: every proof
   downstream of a `TextDirection` BEq derivation failed until the
   derivation was dropped.)
2. **`List.filter_filter` conjunction order**: core states
   `filter p (filter q l) = filter (fun a => p a && q a) l` — outer
   predicate FIRST. State fusion theorems in that order.
3. **Subtype instances**: `{s : String // p s}` derives
   `DecidableEq` for free but needs manual `Hashable`/`Repr`/
   `ToString` instances (one-liners on `.val`).
4. **`abbrev` keeps dot-notation**: `abbrev Graph := List Triple`
   still resolves `g.mem` to `Graph.mem` — safe to define namespace
   functions on abbrevs.
5. **Sabotage-tests can void themselves** — see the PATH trap above.
6. **Parallel worktree agents eat disk**: each agent worktree is a
   full checkout (~1.2 GB with the committed binaries) plus its own
   `.lake` build; eight at once plus caches hit ENOSPC on a 228 GB
   laptop (2026-08-22) and a ninth spawn failed. Before a fan-out:
   `df -h /`, `git worktree prune`, remove stale worktrees under
   `.claude/worktrees/`, `npm cache clean --force`; budget ~1.5 GB
   per agent; never delete the owner's own caches
   (`~/.cache/huggingface` was 20 GB) without asking.
   THE FIX that actually worked (9.5 GB reclaimed in one pass): the
   bulk of a worktree is the committed platform binaries + bundles,
   byte-identical across worktrees. On APFS, replace each worktree's
   copy with a clone of the main checkout's file (`cmp -s` to verify
   identical, then `cp -c main/f wt/f.tmp && mv wt/f.tmp wt/f`) —
   blocks are shared, git sees no change, agents keep working.
7. **Well-founded recursion blocks `decide`/`rfl`.** A mutually
   recursive function group (the JSON parser's five functions)
   compiles via well-founded recursion, so the kernel cannot unfold it
   by evaluation and `decide`/`rfl` get stuck. Recipe: `unfold <fn>`
   (its equation lemma) then `decide`; or keep parsers structurally
   recursive on a fuel `Nat` where possible.
8. **`/-` inside prose opens a block comment** — a doc comment or
   string containing `/-` (e.g. "XML/-JSON") nests a new comment and
   silently swallows the file to EOF, exactly like F\*'s `(* *)` trap.
   Never write `/-` in comment prose; `local` is a reserved word in
   Lean 4 too (2026-08-22, results-formats port).
9. **Integrate agent branches with MERGES, then push; never
   `git pull --rebase` afterwards.** A rebase replays the branch's
   commits onto origin and re-hits the same additive conflicts
   (`L4Factoidal.lean` imports, `PORT_NOTES.md` appends) the merge
   already resolved (2026-08-22). Recipe: `git merge --no-edit
   origin/lean4/<topic>` → resolve additive conflicts by keeping BOTH
   sides (dedupe import lines) → `lake build` green → `git pull
   --no-rebase` if origin moved → `git push`.
10. **`decide`/`rfl` over a concrete parser or tokenizer result eats
    RAM by the gigabyte, and the swap it forces FILLS THE DISK.** One
    theorem `tokensOf (tokenize "<http://a/b>") = …` cost 72 s and
    10 GB; ten of them in one file killed `lean` with signal 9, and
    the macOS swapfiles it wrote took the laptop from 7 GB free to
    0 GB — the disk watchdog fired three times before the cause was
    known (2026-08-22, SPARQL parser port). Concrete-input facts are
    `#guard`s (compiler evaluation, free); keep at most one `decide`
    proof as a demonstration. Relatedly, `split at h` on a scrutinee
    holding `pX topFuel …` weak-head-normalises every fuel level —
    expose `parseSparqlWith (fuel : Nat)` and keep fuel symbolic in
    proofs (`cases h : e`). If free disk oscillates with no large
    files appearing, suspect swap from a proof, not a writer.
11. **Probe executables resolve test paths from the CWD.**
    `lake exe l4jsonld-probe` / `l4sparql-probe` look for
    `third_party/testing/...` relative to where they run; `lake exe`
    runs them from `formal/lean4`, so invoke the built binary from the
    repo root (`formal/lean4/.lake/build/bin/l4jsonld-probe`) or pass
    an absolute manifest path where the probe accepts one. A probe
    that prints "manifest not found" has measured nothing.

12. **A proof about a match arm splits on EVERY scrutinee of that
    arm's inner match.** `strLitNextStep`'s `\u` arm matched on
    `hexVal h0, hexVal h1, hexVal h2, hexVal h3` at once, so any proof
    that reached it produced 16 cases; the `\U` arm produced 256. With
    the surrounding nineteen arms also split, `simp_all` reached
    10.5-12 GB and took SIGKILL, measured three ways (2026-08-24,
    <https://github.com/danbri/factoidal/issues/574>). The fix is to
    factor the inner match into one `Option`-valued helper — `hex4`,
    `hex8` — so the arm splits two ways. Behaviour is unchanged and the
    existing `#guard` differential table against the legacy definition
    is what proves that.
13. **An arm does NOT carry the earlier arms' negations.** Lean's
    equation compiler turns overlapping patterns into a case tree, so a
    catch-all arm such as `| c :: rest` gives you `c` and `rest` and
    nothing else — not `c ≠ '"'`, not `c ≠ '\\'`. A proof that needs
    those must state them as its own lemma
    (`strLitNextStep_plain`, `strLitNextStep_badEscape` in
    `Syntax/LocalityLiteral.lean`), proved by `unfold` then `split`
    over the arms. `grind` closes the residual cases that `simp_all`
    leaves, because it instantiates hypotheses that carry binders —
    `simp_all` does not.
14. **`cases h : f x` rewrites the GOAL, not the other hypotheses.**
    After it, `rw [h] at k` is still needed for every hypothesis `k`
    that mentions `f x`, and `rw [h] at k ⊢` then FAILS, because the
    goal no longer contains the pattern. Two rounds of the same error
    cost a rebuild each (2026-08-24).

- **`lake build l4w3c` is not `lake build`.** The harness target skips
  every theorem-only module (`*Refinement.lean`, `*Theorems.lean` files
  nothing executable imports). A gate that builds only `l4w3c` can pass
  while an engine change broke the agreement proofs downstream — and a
  commit message then claims "full lake build clean" falsely.
  (2026-08-24: the SPARQL 1.2 EBV/literalPromote change broke
  `SPARQL.ExprRefinement` and `SHACL.SparqlTheorems`; two commits
  shipped before the full build caught it. When an engine definition
  changes, its spec-transcription twin — `ebvSpec`, `termToExpr?` —
  must move in the same commit.) Before any commit claiming build
  cleanliness: `lake build`, no target.

## Style contract (owner priority: W3C-expert readability)

- Every definition's doc comment cites the W3C document + section it
  implements; module headers state what is and is NOT ported and why.
- Spec/engine split: keep the plain evaluator as an executable semantic
  reference. The current tree also has hash joins, indexed BGP evaluation,
  backend planning, Cottas/HDT stores, and exact-list refinement proofs for
  the indexed SPARQL path. The owner chose on 2026-08-29 to make Lean the
  intended full-scope target. Add performance machinery in Lean and state its
  relation to the plain evaluator. The Block model, PushIR, PostgreSQL adapter,
  and TiKV adapter remain proposed; follow `skills/blockengine/SKILL.md`.

  PROVENANCE NOTE (2026-08-22, recorded after the owner rejected a
  fabricated rationale): the sentence above previously read "the split
  is absolute — never port them here", sat under the "owner priority"
  heading, and was Claude-authored in the skill-consolidation commit
  0d7219c75e4. No owner instruction said it. It then hardened into
  "must stay that way" in a design doc and into "the owner said
  porting hash-join machinery would destroy the tree's job" in chat.
  The owner's reply: "BS, I never said this." Every commit in this
  repo is authored as the owner's git identity (iron rule #13), so
  `git blame` CANNOT tell owner-written text from Claude-written text
  — provenance must be carried in the prose itself. Label
  Claude-inferred defaults as such, at the moment of writing.
- Naming: the certified six-rule RDFS fragment is **rdfs-core** /
  `RdfsCore` in identifiers and prose — never "ρdf" (owner,
  2026-08-22: the Greek letter reads as "pdf" on a phone). Cite the
  Muñoz–Pérez–Gutierrez 2007 name once, in a doc comment, for
  reviewers who know the literature.
- Theorem names state observational content
  (`Binding.lookup_merge`); `@[simp]` only on genuine
  simplification laws.
- `PORT_NOTES.md` is the F\*↔Lean ledger: update its correspondence
  table and assumption report with every ported module.
- Iron-rule-#6 discipline carries over: NO conformance claims for
  the Lean side until a Lean executable reads the same W3C manifests
  `bin/w3c-runner` does (the continuation ladder at
  https://github.com/danbri/factoidal/issues/466).
