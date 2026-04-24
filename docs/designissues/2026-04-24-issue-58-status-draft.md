# Issue #58 status comment — draft (2026-04-24)

**Agent Xi — docs-only.** Drafts the status comment for GitHub issue #58
("OWL DL entailment: 28 tests need OWL reasoner") and a RIF-out-of-scope
declaration. Does NOT close the issue (that's the user's call).

## Source data

- Latest scoreboard: `docs/test-results/latest.csv` →
  `2026-04-24 21:45 UTC ... sparql,entailment,62,4,4,0` (62 pass, 4 fail).
- Earliest 2026-04-23 baseline: `docs/test-results/history/2026-04-23T18-36-31Z.csv`
  → `sparql,entailment,51,19,0,0` (51 pass, 19 fail).
- Net delta over the two-day window: **+11 PASS, -15 FAIL** on the
  SPARQL entailment suite.
- Tonight's commits (since 14:00 2026-04-24) verified via `git log --oneline`:
  Theta (`12a19a6`), Iota (`df37857`), Kappa (`cb33a5b`), Eta (`2d17cfc`),
  Gamma (`cf1c9cf`), N (`f454860`), M (`e1a0465`).

## Comment body (markdown, ~370 words)

See file `2026-04-24-issue-58-status-comment.md` (built inline below for posting).

## RIF scope decision

Per CLAUDE.md rule #1 ("F* is the source of truth") and the project's
verified-OWL-RL trajectory: RIF Core is a separate rule language
(production rules over RDF), not an entailment regime. Implementing it
would require an entirely separate rule engine and verification effort
that is out of scope for a verified SPARQL/OWL-RL implementation. The
2 RIF tests in `third_party/testing/w3c/sparql/sparql11/entailment/`
will be permanent SKIPs.

## Surprises

- The SPARQL entailment suite only ever had ~22 OWL-relevant tests (not
  the headline "28") — the rest of the original 19 fails were the simple
  family + paper-sparqldl + parent series that all landed via rewriter
  wins. The 2 RIF tests stay in the FAIL column on the entailment
  category but are conceptually a separate scope.
- Tonight's "62/4" matches Issue #58 well: only 4 entailment fails remain
  (paper-Q3 + 3 RIF/DL holdouts), and tomorrow's localized DISTINCT fix
  for simple4/5/7 over-produce-by-1 should clear those without further
  closure work.
- Latest `cf1c9cf` is from before Eta's cardinality wiring — the score
  may notch up when the next sweep runs. The status comment quotes the
  committed `latest.csv` as gospel per the prompt's instructions.
