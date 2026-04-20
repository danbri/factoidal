# Known Performance Issues

## Turtle parser is too slow for real-world input

Measured on 2026-04-17 after the ballyhoo Parser.TurtleScanner integration:

| N triples | File size | Time |
|-----------|-----------|------|
| 1,000     | 56 KB     | 25 seconds |
| 10,000    | 576 KB    | > 8 minutes (killed) |
| ~700,000  | 35.8 MB   | > 6 minutes (never observed to finish) |

The scanner integration (span-based tokens, ASCII fast path, tail-recursive
list accumulation via `rev_prepend`) helped vs. the pre-ballyhoo parser, but
the per-triple constant is still on the order of 25 ms for short triples —
roughly 40 triples/s. Scaling to 10k triples appears super-linear, suggesting
an `O(n*k)` or worse path somewhere beneath F*'s extraction (likely in the
`FStar_String.sub` / `Z.t` arithmetic that gets threaded through every char
operation).

**Working around this:**
- For real data (tens of MB+), use the HDT or COTTAS binary backends
  (`Parser.BallyhooHDT`, `Parser.BallyhooCOTTAS`, already on main). These
  bypass Turtle parsing entirely. **Caveat:** neither is a verified F\*
  reader today — the F\* modules fix the API shape via `assume val`, and
  the HDT path shells out to the external `hdtSearch` CLI. See
  `docs/designissues/2026-04-19-hdt-fstar-status.md` for the full audit
  before relying on these for anything other than existing use cases.
- The architectural path in `docs/designissues/turtle-text-scanner.md`
  still has steps 4 (chunk-resumable scanning) and 5 (revisit doc-level
  parsing) as future work. Chunk-resumable won't fix the per-char
  constant, but may unlock streaming/incremental use.
- **The structural plan** lives in
  `docs/designissues/2026-04-19-turtle-parser-speed.md` — three named
  bottlenecks (`nat`→`Z.t` positions, eager `span_to_string`, O(n)
  list append in the grammar) and a phased A/B/C/D plan to close the
  ~250× gap. Read that before starting new Turtle perf work so we
  stop spending cycles on constant-factor tweaks to the scanner.
- Solving this may ultimately require either (a) replacing hot extracted
  string primitives with direct OCaml Bytes operations (via a narrow
  `assume val` boundary), or (b) a hand-written non-F* tokenizer that
  feeds the verified grammar layer. Both would require per-project-rule
  discussion since they weaken the verified surface. The speed plan
  argues Phase B (machine-int positions) is the verified-friendly
  alternative that should be tried first.

Ad-hoc parse tests MUST be capped at 10 minutes per rule #17
(see `anti-patterns.md`).
