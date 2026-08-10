# FastString re-founding migration (G4; owner-approved)

Owner: "Ok good migration plan - lets do this!" (2026-08-10), under the
four binding constraints in
[2026-08-09-sparql-e2e-proofs-plan.md](2026-08-09-sparql-e2e-proofs-plan.md)
§ Fast-path re-founding constraints. Full survey detail (op inventory,
1251 call sites across 31 modules, patch-89 anatomy, extraction
split-brain, benchmark harness state) is in the G4 program records;
this doc carries the decisions and the step gates.

## Decisions

- **Definitional model over FStar.String with a spec-level UTF-8 codec**
  (`Parser.FastString.Spec.fst`: `utf8_enc_char` / `utf8_bytes` /
  `utf8_decode_at` / `is_cp_boundary`), NOT a byte-list re-representation
  (rejected: 31 consumer modules take `string`; list indexing recreates
  O(n²)). All 8 axioms become theorems; residual assume val =
  `unsafe_char_of_d7ff` only (ulib char_of_int off-by-one, documented).
- **Pure definitions are the semantics, not the hot path.** History:
  BatUTF8-backed String ops measured 61.9–123 triples/s (2026-04-20
  profile, 99.9% CPU in BatUTF8); FastString restored ~104–108k tps at
  100k–1M. The fast OCaml returns as a rule-11(b) Option-B realisation:
  extracted spec functions stay alive under `fs_*_spec` names; the
  patch overrides `fs_*` with today's bodies; DELETABILITY = delete the
  patch and the spec bodies take over, slower never wrong.
- **Equivalence obligation**: property-test harness
  (`parser_fast_string_equivalence.ml`) — random ASCII, valid
  multi-byte UTF-8, adversarial invalid UTF-8 (truncations, bare
  continuations, overlongs, surrogates, 0xF5+ leads); `fs_op == fs_op_spec`
  on all inputs (byte_sub on the boundary-aligned clamp domain, with
  documented XFAIL rows off-domain — F\* strings cannot represent
  invalid UTF-8, so codepoint-splitting slices diverge by necessity).
  Runs in CI beside the hash-witness precedents AND under node/jsoo
  parity (bytes-as-JS-chars convention is part of the stated domain).
- **String.concat ulib gap**: local proved `concat_spec` (fold over
  `^`), zero new axioms; migrate only proof-critical call sites
  (Parser.JSON ×1, SPARQL.Protocol ×7); 328 other uses stay put.

## Steps (commit-sized; verify + benchmark gate each)

0. Freeze baselines (bench-turtle-metrics RUNS=5 +
   bench-parse-serialize), same-host discipline. GATE for the whole
   program: >10% median regression on any turtle fixture or 100k/1M
   parse rows (serialize rows gated at 10k — pre-existing dump-nq
   superlinearity) triggers/blocks per constraint 2.
1. `Parser.FastString.Spec.fst` — codec + lemma kit, additive,
   proof-only.
2. Re-found ops: new `Parser.FastString.fsti` (same names/signatures —
   consumers untouched, definitions opaque to their SMT contexts),
   assume vals → Spec-backed lets, patch 89 cut to
   `unsafe_char_of_d7ff` only. Expected+recorded: massive regression
   (constraint 1's own evidence). NEVER MERGED ALONE —
3. — merges WITH the Option-B realisation patch
   (experimental_ocaml_glue, rule 11(b)) + equivalence harness.
   Benchmark must return to within threshold of step 0.
4. `Parser.FastString.Axioms.fst` companion proves all 8 vals —
   axiom module stops being assumption-bearing, zero consumer churn;
   close/morph #358; obsolescence sweep.
5. Base-case lemma pack + `concat_spec`; unblocks the SRJ text bridge
   (M4) and N-Triples parser-side proofs (M1-adjacent).
6. Boundary-audit reclassification, parity run, doc sweep.

## Unblock map

Step 4 → N-Triples parser lemmas, N-Quads/TriG line proofs, streaming
chunk-fold (concat theorems power carry composition). Step 5 → SRJ
text-level composition. Token round-trip (SPARQL tokenizer) never
blocked — it doesn't use FastString.

## Risks (carried into briefs)

jsoo UTF-16 convention (equivalence runs under node parity);
`fs_cp_at` decoder must mirror `fs_cp_at_impl` branch-for-branch
(adversarial diff is the check); `.fsti` opacity against verify-time
fuel blowups (#273's verify-time analogue); FastString is near the
dependency root — steps 2-3 cascade the full .checked tree
(background build, COMMIT-FIRST); per-host benchmark honesty (never
pair numbers across container recycles).
