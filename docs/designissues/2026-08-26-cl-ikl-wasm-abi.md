# The CL/IKL wasm ABI surface

Design note for the rebuild session. Tracked at
<https://github.com/danbri/factoidal/issues/623>.

Written 2026-08-26. Read `skills/lean4-wasm-export` before touching
`build-wasm.sh` — it carries traps 5–8 from the first Linux build.

## Why this branch exists

Two agents are pushing to `claude/autoexec-scratchpad-assess-37oeok`
(an extraction-drift repair and a CL/IKL purge). A separate branch keeps
the rebuild session from contending with them. Rebase onto that branch
before rebuilding — see the ordering constraint below.

## Ordering constraint, and it is hard

**Do not rebuild until the CL/IKL purge has landed.** It deletes
`formal/lean4/L4Factoidal/CL/ToRdf.lean` and `CL/IklRegime.lean` and
removes two ops from the dispatch. A rebuild before that bakes in ops
that are being deleted, and the artifact would be wrong the moment the
purge merges.

Check `formal/lean4/L4Factoidal/CL/ToRdf.lean` is absent before starting.

## The op surface this work should produce

| Op | Action | Source |
|---|---|---|
| `clParse` | keep | `CL/Clif.lean` |
| `clToDataset` | gone — deleted by the purge | — |
| `queryWithIklService` | gone — deleted by the purge | — |
| `clSerialize` | **add** | `Sentence.toClif` |
| `clAlphaNorm` | **add** | `Sentence.alphaNorm` |
| `clFiniteSat` | **add** | `CL/FiniteSat.lean` |
| `clNormalize` | **add** | `CL/Normalize.lean` |

Each op is a `def` in `formal/lean4/Wasm/Ops/CL.lean` plus two lines in
`Wasm/Dispatch.lean` — one entry in the op-name list, one `arity` case.

### The three easy ones

`clSerialize` and `clAlphaNorm` are `String -> String` wrappers over
functions that already exist. `clNormalize` exposes Hayes's
satisfiability-preserving reduction of IKL to Common Logic
(<https://github.com/danbri/factoidal/issues/625>, landed in Lean
2026-08-26). It is the op with the clearest use: it lets a JS caller
hand IKL to a conventional first-order engine.

Its documentation must state two limits, because both are real:

- The reduction preserves **satisfiability, not equivalence**. It suits
  entailment and consistency testing. It is not a transformation to
  apply to data you intend to keep.
- The **intrusion case is outside what is proved**. `tails_satisfiable`
  and `normalize_preserves` carry `noIntrS [] [] E = true`.

`clSerialize`'s docs must note that `clif_roundTrip` is an OPEN lemma
(`CL/ClifAdequacy.lean`): the fragment boundary `marksLexable` is
measured, not proved.

### `clFiniteSat` is the one that needs design

`satFin_eq` (`CL/FiniteSatTheorems.lean:474`) reads:

```lean
theorem satFin_eq [BEq α] [LawfulBEq α] (fi : FiniteInterp α)
    (hdom : ∀ x : α, x ∈ fi.domain) (v : FinVal α) (s : Sentence)
    (hns : noSeqQuant s = true) :
    sat fi v s = true ↔ Sat fi.toInterp v.ind v.seq s
```

So the op has to carry a whole **interpretation** across a string ABI:
domain, name-to-element map, relation extensions, function graphs. That
JSON schema is a design decision, not a wiring job, and it is the bulk
of the work.

**Both preconditions must be surfaced in the result, never assumed.**
`hdom` (domain completeness) and `hns` (no sequence quantifiers) are
checkable; a checker that silently answers outside its own hypotheses is
worse than one that refuses. Return a refusal that names which condition
failed.

## Disk is the blocker

emsdk is roughly 1.7 GB. Free space was about 1.8 GB with agents
running, so this needs handling before anything else.

Measured 2026-08-26: `git gc --prune=now` and `git prune --expire=now`
both returned clean and freed nothing. The 11 GB of loose objects are
reachable history of the committed binaries (iron rule #9), not garbage.
A successful `git repack -a -d` is the clean way through and is worth
trying once the tree is quiet.

Smaller reclaimables: `/root/.cache` ~75 MB, `/root/.npm` ~15 MB, the
F\* `.checked` cache ~169 MB (a cache, but expensive to rebuild).

## Landing the artifact

Two committed copies must stay **byte-identical**:

- `docs/web/hub/assets/l4/l4factoidal.wasm`
- `npm/factoidal/l4-assets/l4factoidal.wasm`

Both were sha256 `6593d044…` before this work. Update
`npm/factoidal/l4-assets/version.json`'s `wasmSha256` — the
`npm-publish-lean.yml` tarball gate checks it against the shipped wasm
and fails on a mismatch.

The hub loads the engine from `docs/web/hub/assets/l4/l4factoidal.js`
(see `docs/_includes/hub.njk`), which is a repository path served from
GitHub Pages, not from npm. Hub post 44 exercises `clParse` through that
path.

## Gates

- `cd formal/lean4 && lake build` — full tree green.
- `#print axioms` clean on anything carrying a theorem: `propext`,
  `Classical.choice`, `Quot.sound` only.
- SPARQL 1.1 entailment sentinel **70 pass, 0 fail (out of 70)**. Run
  the runner **from the repository root** — the suite runners resolve
  manifest paths relative to the root and print `manifest not found`
  while still exiting 0 when run from `formal/lean4`, so a wrong working
  directory yields no score rather than a wrong one.
- `npm test` from `npm/factoidal`.
- `node --test tests/hub/*.mjs`.
- `tests/web-demos/hub_browser_all.sh` — **not optional**. The node
  harness binds `fn` to the node package and cannot see browser-surface
  gaps; two live breakages were found that way (anti-pattern #32).

Never truncate runner output with `tail -N` (anti-pattern #16): the
runners print the score line and then explanatory prose, so a `tail -3`
captures the prose and loses the number.

## Push discipline

Stage by explicit path. Never `git add -A`, `git add .`, or
`git commit -a`. On push rejection, `git pull --rebase` and push again.
An agent broke this rule on 2026-08-26 and swallowed another agent's
in-flight files into its commit.
