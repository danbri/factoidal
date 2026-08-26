# 2026-08-26 — The IKL-to-RDF projection is deleted, and the wasm artifact is ahead of its source

Issues: [#626](https://github.com/danbri/factoidal/issues/626) (the
purge), [#627](https://github.com/danbri/factoidal/issues/627) (the
wasm rebuild).

## 1. The instruction

Owner, 2026-08-26, verbatim:

> "Re shas56 prop ids, alphanorm 'Treat it as superseded rather than
> repaired.' Stronger: close its issues, PRs, branches if alive, purge
> it from code, wasm js c fstar lean markdown whatever, docs, and hub
> notebooks. Make it go away. This is a day old codebase on very
> complex and subtle topics, so strip out the cruft."

## 2. What went

The content-addressed proposition naming scheme
`urn:cl:that:sha256:<hex over alpha-normalized canonical CLIF>` and the
IKL-to-RDF projection ("direction B") built around it.

The scheme was Claude-invented. The owner never asked for it.
[#589](https://github.com/danbri/factoidal/issues/589) was a QUESTION
about whether the tree respects IKL's proposition-individuation rules;
the naming scheme predates that question.

Deleted files:

| file | lines | what it was |
| --- | --- | --- |
| `formal/lean4/L4Factoidal/CL/ToRdf.lean` | 536 | the whole projection: `propNormClif`, `propIri`, `recordTriple`, `projectionTriple`, `emitProposition`, `toRdfDataset`, and the `urn:cl:def:asserts` / `urn:cl:def:sentence` / `urn:cl:def:rdfProjection` vocabulary |
| `formal/lean4/L4Factoidal/CL/IklRegime.lean` | 250 | the `x-ikl-*` entailment-regime family, whose one handler was defined by the `urn:cl:that:` prefix test plus the assertion decoration |
| `docs/web/hub/39-propositions-as-first-class-citizens.md` | — | the public post about the scheme (already a withdrawal stub) |

Deleted surfaces: the `clToDataset` and `queryWithIklService` wasm ops
and their dispatch entries; the `l4factoidal cl to-rdf` and
`l4factoidal cl query` CLI verbs; the `x-ikl-*` branch of the W3C
harness's regime dispatch and of `Unified.regimeToSchema`.

`clParse` is unaffected. It reads CLIF and produces no RDF.

## 3. What was kept, and why

`Sentence.alphaNorm` (`formal/lean4/L4Factoidal/CL/Alpha.lean`) had two
jobs. Only one was the cruft.

* **Naming key.** `propNormClif` fed `alphaNorm.toClif` into the sha256
  that named a proposition graph. Deleted with `ToRdf.lean`.
* **IKL GUIDE Appendix B condition (1)**, stated as an interpretation
  condition: alpha-variant sentences name ONE proposition. That is
  IKL's own semantics and part of the
  [#598](https://github.com/danbri/factoidal/issues/598) model theory.
  KEPT, with every use: `Unified/DatasetEmbed.lean`'s
  `PropAlphaInvariant`, `Unified/ClBridge.lean`'s
  `typeBlind_alphaInvariant` and the
  [#609](https://github.com/danbri/factoidal/issues/609) item-3
  separation theorems, and `Unified/Witnesses.lean`'s alpha-keyed
  interpretation witness.

Also untouched: `CL/Normalize.lean`, `CL/NormalizeSemantics.lean`,
`CL/IklModels.lean` (the 2026-08-26 Hayes-normalization landing, which
contains no `alphaNorm` reference at all), `CL/Clif.lean`,
`CL/Semantics.lean`, `CL/FiniteSat*.lean`, and the reserved
`urn:cl:def:` operator vocabulary of `Unified/RdfEmbed.lean` and
`OWL/RLSemantics.lean` — `names`, `asserts`, `literalValueOf`,
`tripleTerm`, `listMember`, `typedAllMembers`. Those belong to the
unified layer, not to the projection.

## 4. Theorems restated, not lost

`Unified/ClBridge.lean` stated its §1 and §8 soundness results over
`CL.IklRegime.extendDataset`, whose selection predicate was a
conjunction: the graph name starts with `urn:cl:that:`, AND the default
graph decorates it with `urn:cl:def:asserts`. Reading the proofs, no
step used the first conjunct — `embed_entails_asserted_merge`'s proof
discards it at `hp.2`. The statements are therefore now over the
assertion decoration alone, which is strictly more general:

| deleted name | replacement | over |
| --- | --- | --- |
| `iklPremises_extend_entailed` | `asserted_merge_premises_entailed` | `mergeAsserted` |
| `ikl_extend_entailed` | `embed_entails_asserted_merge` | `mergeAsserted` |
| `regime_sound_ikl` | `asserted_merge_sound` | `mergeAsserted` |
| `ikl_extend_entailed_nonvacuous` | `embed_entails_asserted_merge_nonvacuous` | `mergeAsserted` |

`mergeAsserted ds = mergeWhere (fun ng => graphAsserted ds ng) ds`, and
`graphAsserted` is `Unified/DatasetEmbed.lean`'s own test — no CL
module is involved.

Two theorems were deleted outright, because their subject is gone:

* `extendDataset_eq_mergeWhere` — it said the handler IS `mergeWhere`
  at its own predicate. There is no handler.
* `graphAsserted_eq_assertsDecorated` — it pinned the unified layer's
  assertion test to the engine's second spelling of the same test.
  There is now one spelling.

The witness dataset `wDs` was a real `CL.toRdfDataset` output, pinned
by a `#guard` against the parser and translator. It is now built from
plain IRIs in `ClBridge.lean` §2: one named graph, one content triple,
an `urn:cl:def:asserts` decoration, and an `ist` link decoration for
the mention-only comparison. Nothing in §3-§8 turned on the graph name
being a digest.

## 5. 🔴 The wasm artifact is ahead of its source

Tracked in [#627](https://github.com/danbri/factoidal/issues/627).

The committed Lean wasm module was NOT rebuilt in this landing — the
build needs emsdk, absent from the container, with about 1.8 GB free.
Both committed copies are byte-identical:

```
6593d0449b5905e5b02c1e32cf643238ef26a67589cb910158948dbf3798f58d  docs/web/hub/assets/l4/l4factoidal.wasm
6593d0449b5905e5b02c1e32cf643238ef26a67589cb910158948dbf3798f58d  npm/factoidal/l4-assets/l4factoidal.wasm
```

built at `de455950e618f0a2928b4d94dd7cf4c064c95457`,
2026-08-25T15:44:03Z.

So the artifact still exports, dispatches, and reflects in its own
`ops` list two op names — `clToDataset` and `queryWithIklService` —
that `formal/lean4` no longer defines, and still carries the deleted
naming scheme and projection vocabulary inside its compiled code.

Recorded in the `sourceDrift` block of all three Lean `version.json`
files: `npm/factoidal/l4-assets/version.json`,
`npm/factoidal-lean/version.json`, `docs/npm/lean/version.json`.

Reachability: no JS surface in `npm/factoidal` dispatches to either op
(`l4-core.js` never wired them; `select.js` keeps them out of
`ROUTABLE`). The drift is reachable only through a direct `call()` on
the raw module.

To clear it: rebuild per
[`skills/lean4-wasm-export/SKILL.md`](../../skills/lean4-wasm-export/SKILL.md),
refresh `wasmSha256` / `wasmBytes` / `gitSha` / `builtAt` in the three
files, delete the `sourceDrift` blocks, and confirm the artifact's
`ops` reflection no longer lists the two names.

## 6. Consequence for [#620](https://github.com/danbri/factoidal/issues/620)

[#620](https://github.com/danbri/factoidal/issues/620) asked for a
reversibility theorem: RDF → IKL → RDF, constraining the projection's
naming and decoration choices. The projection is deleted, so the
theorem has no subject. The RDF → IKL direction survives and is
already proved — `Unified/RdfEmbed.lean`, `Unified/DatasetEmbed.lean`,
`Unified/RdfAdequacy.lean` — with no naming convention to justify.
