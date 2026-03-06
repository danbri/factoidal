# Periodic Review Hooks

## What to Review and When

### Every Session (before starting work)
- [ ] Run `cargo test` — verify baseline
- [ ] Check `git status` — no uncommitted changes from previous session
- [ ] Review CLAUDE.md claims against actual test results

### After Every SPARQL Change
- [ ] Run full scorecard: `cargo test w3c_sparql_combined_scorecard -- --nocapture`
- [ ] Compare total against previous commit's scorecard
- [ ] Update CLAUDE.md scorecard if total changed by ≥5
- [ ] Commit with scorecard delta in message

### Weekly
- [ ] Verify W3C N-Triples: still 72/72
- [ ] Verify W3C Turtle: still 223/223
- [ ] Check WASM build: `cd rdf-wasm && ./build.sh`
- [ ] Review F* spec line count vs CLAUDE.md claim
- [ ] Check Rust LOC per module vs CLAUDE.md claims
- [ ] Look for stale TODOs in code

### Monthly
- [ ] Update W3C test submodule: `cd tests/w3c && git pull`
- [ ] Re-run full suite against updated tests
- [ ] Review `docs/designissues/` for outdated claims
- [ ] Check QLever endpoint availability for kgx pipeline
- [ ] Review Hax project status for Rust→F* extraction readiness

## Accuracy Audit Checklist

### CLAUDE.md Claims to Verify

| Claim | How to verify | Command |
|-------|-------------|---------|
| F* spec ~241 lines | `wc -l formal/fstar/rdfcore11.fstar.txt` | Direct |
| 172 total tests | `cargo test 2>&1 | grep "test result:" | awk '{s+=$4} END{print s}'` | Sum |
| N-Triples 72/72 | `cargo test w3c_ntriples 2>&1 | grep "test result:"` | Direct |
| Turtle 223/223 | `cargo test w3c_turtle -- --nocapture 2>&1 | grep "individual"` | Scorecard |
| SPARQL X/436 | `cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"` | Scorecard |
| Rust LOC per module | `wc -l rdf-wasm/src/*.rs` | Direct |
| Test execution time | `time cargo test 2>&1 | tail -1` | Direct |

### Common Inaccuracies to Watch For

1. **F* line count** — changes when spec is extended (was claimed as ~160, actually 241)
2. **SPARQL pass count** — changes with every engine improvement
3. **Total test count** — changes when new test files are added
4. **Execution time** — varies by machine and build profile
5. **"In Progress" items** — may be completed but not updated
6. **Rust LOC** — grows with features, check periodically

## Automated Review Script

```bash
#!/bin/bash
# save as scripts/review.sh

echo "=== Factoidal Health Check ==="
echo ""

echo "## F* Spec"
echo "Lines: $(wc -l < formal/fstar/rdfcore11.fstar.txt)"
echo ""

echo "## Rust Code"
wc -l rdf-wasm/src/*.rs
echo ""

echo "## Test Results"
cd rdf-wasm
cargo test 2>&1 | grep "test result:" | while read line; do
    echo "  $line"
done
echo ""

echo "## SPARQL Scorecard"
cargo test w3c_sparql_combined_scorecard -- --nocapture 2>&1 | grep "TOTAL"
echo ""

echo "## Git Status"
cd ..
git status --short
echo ""

echo "=== Done ==="
```

## Update Triggers

Update CLAUDE.md when:
- SPARQL scorecard changes by ≥5 tests
- F* spec is extended (new sections or proofs)
- New test files are added
- New design documents are created
- Architecture tree changes (new directories)
- New dependencies added

Update docs/skills/ when:
- New testing patterns are discovered
- New optimization techniques are applied
- New measurement tools are integrated
- Workflow improvements are identified

## Cross-Reference Check

Ensure consistency between:
- CLAUDE.md architecture tree ↔ actual directory structure
- CLAUDE.md test counts ↔ actual `cargo test` output
- CLAUDE.md F* coverage table ↔ actual F* spec sections
- CLAUDE.md SPARQL scorecard ↔ actual scorecard output
- docs/designissues/ links in CLAUDE.md ↔ actual files
- docs/skills/ references ↔ actual files
