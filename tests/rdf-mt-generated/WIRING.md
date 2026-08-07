# Wiring note (not applied — per task brief, standalone only)

This suite is deliberately NOT wired into `w3c-tests.sh` or any other
existing test entry point. To add it to the orchestrator, add exactly
this one line wherever the other `tests/local/*.sh` scripts are invoked
in `w3c-tests.sh` (grep that file for `tests/local/` to find the
existing call site and match its pattern — pass/fail accumulation,
log redirection, etc.):

```sh
tests/rdf-mt-generated/run.sh
```

It needs no extra environment beyond what `tools/ensure-test-env.sh`
already guarantees (a committed `factoidal` binary reachable via
`formal/fstar/ocaml-output/factoidal` or `bin/linux-x86_64/factoidal`),
and it writes only inside its own `fixtures/` directory plus a
`mktemp -d` workdir it cleans up on exit — safe to add to any existing
test-running loop without extra sandboxing.

Do not fold its checks into `w3c_runner --rdf rdf-mt`: that suite reads
W3C manifest files (positive/negative entailment tests over `.rq`
ASK-style semantics run through the pure evaluator path) and is
governed by iron rule #6 ("run the real W3C test files"). This suite
runs the same closure logic through the extracted, compiled `factoidal
entail` CLI path instead — a deliberately different boundary than the
runner exercises, per the A2 adoption goal ("exercising the
extraction/implementation boundary the pure F* theorems do not
cover"). Keep them as two separate suites, both included in the
orchestrator, rather than merging one into the other.
