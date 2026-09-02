# Provenance: gotrevor/lean-agent-skills (vendored, unmodified)

- Source: https://github.com/gotrevor/lean-agent-skills
- Commit: b64932fad7d7f4a8ece6a1d254acf46b7f339802 (branch main, fetched 2026-09-02)
- Licence: Apache-2.0 (LICENSE alongside this file)
- Files: skills/lean-review/SKILL.md, copied byte for byte with
  `gh api ... -H 'Accept: application/vnd.github.raw'`.
- Why this one: `lean-review` is a diff-scoped check registry for the
  things a green `lake build` does not show — a raised `maxHeartbeats`,
  `native_decide`, a new `axiom`, `sorry`, `unsafe`/`partial`/`opaque`,
  silenced linters — with `#print axioms` named as the authoritative check.
  That is this repository's proof policy (`skills/factoidal-lean-basics`,
  "Proof policy") stated as a review procedure. Its three sibling skills
  (`mathlib-bump`, `lean-erdos-review`, `comparator-harness`) target Mathlib
  version bumps and the formal-conjectures house style and are not vendored.
- Local reading: where the registry says "flag", this repository says
  "refuse to commit" for `sorry`, a user `axiom`, `native_decide` and a new
  `partial`; a `maxHeartbeats` raise is allowed only `set_option ... in` on
  one declaration with a comment. Do not edit the vendored file; refresh by
  re-fetching and updating the commit here.
