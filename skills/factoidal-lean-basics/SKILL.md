---
name: factoidal-lean-basics
description: Everything a session needs for the Lean 4 side of Factoidal (formal/lean4/, library L4Factoidal, issue #466) — what exists and how complete it honestly is, toolchain setup (elan/lake, the PATH trap), how to build/run/demo/test, the no-sorry/no-axiom/no-native_decide proof policy and its audit, the purity doctrine replacing F* assume vals, interactive tooling (lean-lsp-mcp, loogle, leansearch), and the Lean pitfalls this project has already paid for. Use when touching anything under formal/lean4/, planning the next porting rung, answering "can we run it?", or bootstrapping Lean on a fresh machine.
---

# Factoidal Lean basics

## What exists (2026-08-22 baseline)

`formal/lean4/` is a self-contained lake project, library name
`L4Factoidal` (naming deliberately not finalised — owner: "don't rush
that"). Workstream + continuation ladder:
https://github.com/danbri/factoidal/issues/466

| File | Content |
|---|---|
| `L4Factoidal/RDF/Core.lean` | RDF 1.1/1.2 terms: wf-IRI subtypes, literals incl. RDF 1.2 base direction, triple terms; the THREE literal equalities (strict/engine/value) kept distinct; strict equality proved to be identity |
| `L4Factoidal/RDF/XmlCanon.lean` | rdf:XMLLiteral exclusive-c14n value equality (the WebOnt-miscellaneous-202 fix, ported whole) |
| `L4Factoidal/RDF/Graph.lean` | set-semantics graphs, datasets, blank-node renaming, membership theorems |
| `L4Factoidal/SPARQL/Algebra.lean` | solution mappings (§18.1.8), compatibility/merge (§18.3), triple patterns incl. SPARQL 1.2 triple-term patterns, BGP evaluation, §18.5 Join/LeftJoin/Union/Minus/Filter |
| `L4Factoidal/SPARQL/Invariants.lean` | PROVED: empty-pattern laws, merge/lookup characterisation, filter/minus safety, BGP monotonicity |
| `L4Factoidal/Tests.lean` | 19 `#guard` build-time tests + `#print axioms` audit lines |
| `Demo.lean` | runnable guided tour with a Turtle-ish printer |
| `Wasm/` | the WebAssembly export: JSON string-in/string-out ABI (`Abi.lean`), the `@[export]` C symbols (`Exports.lean`), a native driver over the same ABI (`Main.lean`), the C shim and `build-wasm.sh`. Produces `docs/web/hub/assets/l4/l4factoidal.wasm` (1.4 MB), which runs in browser, Node and Deno — hub post 36 runs it beside the F\* engine. Recipe + traps: `skills/lean4-wasm-export/SKILL.md` |
| `README.md` / `PORT_NOTES.md` | reviewer reading order / F\* correspondence + assumption report |

Honest completeness: ~1,200 lines, 69 defs, 31 theorems — roughly 2%
of Factoidal, but the load-bearing 2%: the full term model and the
algebra core, cleanly separated from engine machinery. There is NO
parser (queries are Lean AST values), no expression language (filters
are `Binding → Bool`), no projection/ORDER BY, no Turtle. Say so when
asked; never imply more.

## Toolchain

- Install: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y`.
- **PATH trap (2026-08-22, paid for):** every fresh harness shell
  needs `export PATH="$HOME/.elan/bin:$PATH"` or `lake` is absent —
  and a gate script that silently loses `lake` LOOKS like it passed.
  During the MINUS sabotage demo the first "the build caught nothing"
  result was actually "the build never ran" (`command not found`
  filtered away by a grep for 'error'). Always confirm the tool ran
  before trusting its silence.
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
- New `#guard`s go in `Tests.lean`; new theorems in `Invariants.lean`
  (or a sibling), each with a doc comment citing the spec section.

## Proof policy (stricter than the F\* tree's)

- **No `sorry`. No user `axiom`. No `native_decide`** (it smuggles in
  trust of the compiled evaluator via `Lean.ofReduceBool`). Partial
  functions (`partial def`) also count as debt — everything so far is
  total and should stay so.
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
implementations), and `partial`. This project uses NONE. The ten
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

## Style contract (owner priority: W3C-expert readability)

- Every definition's doc comment cites the W3C document + section it
  implements; module headers state what is and is NOT ported and why.
- Spec/engine split is absolute: `formal/lean4` holds the
  SPECIFICATION evaluator (list scans, nested-loop join). The F\*
  tree's planner / index seam / hash join / fuel bounds / `*_tr`
  rewrites are performance machinery — never port them here.
- Theorem names state observational content
  (`Binding.lookup_merge`); `@[simp]` only on genuine
  simplification laws.
- `PORT_NOTES.md` is the F\*↔Lean ledger: update its correspondence
  table and assumption report with every ported module.
- Iron-rule-#6 discipline carries over: NO conformance claims for
  the Lean side until a Lean executable reads the same W3C manifests
  `bin/w3c-runner` does (ladder rung 3 on #466).
