# Lean 4 full-corpus gate

## 2026-08-31

### Finding

The full Lean package was not covered by a GitHub Actions workflow.  A
focused block-engine executable could therefore build while an unrelated
library theorem failed.  This occurred after the streaming Turtle refactor
(`f83dc599f`): `maxUnderscoreRun` became a compatibility wrapper over
`UnderscoreRun.feedChars`, but its proof retained the old direct-recursion
induction.

The failing declaration did not contain an authored `sorry`; Lean reported
`sorryAx` because it emits an internal placeholder when elaboration of an
otherwise-declared theorem fails.  That is still an invalid proof result and
must fail the repository gate.

### Repair

`L4Factoidal.Syntax.TurtleTheorems` now proves the invariant at the actual
streaming abstraction:

```text
state.longest <= (state.feedChars chars).longest
```

The legacy `maxUnderscoreRun_ge_best` theorem follows directly by unfolding
the wrapper.  This makes the property applicable to chunked input as well as
whole documents.

`.github/workflows/verify-lean4.yml` installs the pinned toolchain and runs
the explicit full-corpus gate:

```text
cd formal/lean4
lake build L4Factoidal
```

### Verification

On 2026-08-31, local `lake build L4Factoidal` completed successfully over
435 targets.  The repaired Turtle theorem's axiom audit reports only
`propext` and `Quot.sound`, not `sorryAx`.
