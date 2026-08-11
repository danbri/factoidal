# Review kernel

Curated core of [`theorem-registry.md`](theorem-registry.md) for issue
#403 (G1), delivered under the M5 fold-in
([`designissues/2026-08-09-sparql-e2e-proofs-plan.md`](designissues/2026-08-09-sparql-e2e-proofs-plan.md), owner 2026-08-09: "Yes fold it in").

The strongest 1-4 theorem statements per G4 stage (parser, expressions, filters, modifiers, results, streaming) plus the G3 entailment/closure chain — the minimal set a W3C-domain expert can read end to end in one sitting, each with its exact domain and honest boundary. Every statement below was read from the current tree while writing this document; file:line references point at the commit on branch `review-kernel`, checked out from `origin/claude/main`. Not a summary of every proof (the registry has ~140 rows), not a claim of complete coverage — §8 states what these theorems do not reach.

## Contents

1. [Parser](#1-parser) — 2. [Expressions](#2-expressions) —
3. [Filters](#3-filters) — 4. [Modifiers](#4-modifiers) —
5. [Results](#5-results) — 6. [Streaming](#6-streaming) —
7. [Entailment/closure chain](#7-entailmentclosure-chain-corerdfs) —
8. [What the kernel does not cover](#8-what-the-kernel-does-not-cover) —
9. [Trust surface](#9-trust-surface) —
10. [Override guarantee](#10-override-guarantee--how-to-re-check-this-document)

## 1. Parser (4 statements)

**1.1 Tokenizer round-trip.** `SPARQL11.Parser.TokenRoundTrip.fst:1364-1366`:

```fstar
val tokenize_fragment_roundtrip (ts : list (t:token{token_in_fragment t}))
  : Lemma (ensures tokenize (print_tokens ts) == List.Tot.map widen_token ts @ [Tok_EOF])
```

`tokenize` is the shipping lexer (`SPARQL11.Parser.fst:1170`, opened directly, not reimplemented). Domain: token lists built from the single/two-character delimiter and operator tokens (`{}()[] . ; ,`, `* / | ^ ! ? + - = != < <= > >= && || ^^`, bare `?`) — print then re-tokenize recovers the original list plus `Tok_EOF`. Does not cover: keyword tokens (`SELECT`, `WHERE`, ...), variables, IRIs, literals — those reach the lexer via `scan_word`/`keyword_of_word`, a different path the fragment's combinators don't touch (in-file FINDING, lines 17-35).

**1.2 ASK+BGP query round-trip, token level.** `SPARQL11.Parser.AskBgpRoundTrip.fst:618-628`:

```fstar
val parse_select_query_token_level
    (b : bgp{bgp_in_fragment_1 b /\ List.Tot.length b >= 1}) (fuel : nat)
  : Lemma
      (requires fuel >= ask_bgp_fuel_cost (List.Tot.length b))
      (ensures parse_select_query [] None fuel
                 (Tok_ASK :: (Tok_LBRACE :: (bgp_tokens_1 b @ [Tok_RBRACE; Tok_EOF])))
               == ParseOk ({ q_base = None; q_prefixes = []; q_form = QF_Ask;
                             q_dataset = []; q_pattern = GP_BGP b;
                             q_group_by = None; q_having = None;
                             q_modifier = default_modifier; q_values = None })
                          [Tok_EOF])
```

`parse_select_query` is the shipping parser's query entry point (`SPARQL11.Parser.fst:3631`). Domain: `ASK { <flat BGP> }` for any non-empty BGP in a stated fragment (`bgp_in_fragment_1` — plain triple patterns, no property paths, no nested groups), fuel ≥ `n + 11` (`ask_bgp_fuel_cost`, line 179; `n` = triple count, derived from the real call chain). Does not cover: SELECT, non-flat WHERE clauses, or the string-to-token step (§8.1). Proved via ~35 lemmas through the parser's own verb/subject/object dispatch — a proof about the parser, not a transcription of it.

**1.3 N-Triples round-trip, concrete.** `RDF.NTriples.RoundTrip.fst:612-614`:

```fstar
let checkpoint_a_closed_triple_round_trip (_:unit)
  : Lemma (parse_triple (nq_line_for_triple_default_graph target_triple) 0
           == ParseOk target_triple 16)
```

Both `parse_triple` (`Parser.NTriples.fst:644`) and the serializer are the real shipping functions. Domain: one concrete all-IRI triple (`<x:> <y:> <z:> .`) — parsing the serializer's own output recovers it exactly. Does not cover: literals, blank nodes, or an arbitrary IRI — §1.4 generalizes along the IRI axis.

**1.4 N-Triples IRI round-trip, symbolic.** `RDF.NTriples.RoundTrip.fst:875-881`:

```fstar
val lemma_term_iri_round_trip_build_string
    (cs : list FStar.Char.char{all_ascii cs /\ chars_all is_iri_body_char cs})
  : Lemma
      (requires is_iri (build_string cs))
      (ensures
        parse_object (nq_term_to_string (T_IRI (build_string cs))) 0
          == ParseOk (T_IRI (build_string cs)) (FStar.List.Tot.length cs + 2))
```

`nq_term_to_string` is `RDF.NQuads.Serialize.fst:107`. Domain: any ASCII IRI of `is_iri_body_char`-safe characters (no escapes, no `>`, no controls) — arbitrary, not fixed. Does not cover: non-ASCII IRI content, or "any string equals the rebuild of its own codepoints" (§8.3).

## 2. Expressions (2 statements)

**2.1 Evaluator congruence.** `SPARQL11.Algebra.Refinement.fst:507-509`:

```fstar
let rec lemma_eval_expr_congr (base : option wf_iri) (e : expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_expr_with_base base e mu == eval_expr_with_base base e mu')
          (decreases e)
```

Domain: unconditional over the entire ~74-constructor `expr` grammar (arithmetic, comparison, string functions, EXISTS/NOT EXISTS, aggregates, COALESCE, IN, regex, CONCAT, ...) — structural induction proves the real evaluator `eval_expr_with_base` (`SPARQL11.Algebra.fst` Part 8) treats a solution mapping as a mathematical function, not a concrete list. Does not cover: the literal shipping wrapper `eval_expr_ebv` directly (§8.2).

**2.2 EBV/type-error divergences.** `SPARQL11.Expression.Refinement.fst` (proof-only, an independent §17.2.2/§17.3 transcription): 17 agreement lemmas on conforming operator classes, plus two named divergences — EX-1 (`langString`'s EBV is truthy in the engine where §17.2.2 specifies a Type Error) and EX-2 (`And`/`Or`/`Not` never raise a type error in the engine, collapsing the spec's three-valued table). These are machine-checked witnesses of where the engine diverges from the spec, not passing tests that hide the divergence. Does not cover: full agreement between engine and transcription — 17 lemmas is a partial map.

## 3. Filters (3 statements)

**3.1 Soundness + completeness, unconditional.** `SPARQL11.Algebra.Refinement.fst:374-397`:

```fstar
let rec theorem_filter_sound (base : option wf_iri) (e : expr)
      (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (filter_solutions base e omega))
          (ensures  List.Tot.memP mu omega /\ eval_expr_ebv base e mu == true)
          (decreases omega)

let rec theorem_filter_complete (base : option wf_iri) (e : expr)
      (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu omega /\ eval_expr_ebv base e mu == true)
          (ensures  List.Tot.memP mu (filter_solutions base e omega))
          (decreases omega)
```

`filter_solutions` (`SPARQL11.Algebra.fst:7336`) and `eval_expr_ebv` (`:4488`) are the shipping FILTER path. Domain: unconditional, any expression, any solution list — §18.5's set-membership characterization of the real evaluator. Does not cover: multiplicity (bag-level) — §3.2.

**3.2 Cardinality, at the transparent evaluator twin.** `SPARQL11.Algebra.Refinement.fst:644-649`:

```fstar
let theorem_filter_card_eval_expr_with_base
      (base : option wf_iri) (e : expr) (omega : list S.smap)
  : Lemma (ensures S.filter_card_spec (eval_expr_ebv_transparent base e) omega
                     (List.Tot.filter (eval_expr_ebv_transparent base e) omega))
```

Domain: unconditional, at `eval_expr_ebv_transparent` — the shipping wrapper's own body copied verbatim minus its `[@@ irreducible]` attribute. Does not cover: the literal `eval_expr_ebv` symbol directly — FINDING FC-1: `eval_expr_ebv`/`eval_expr_fwd` are deliberately `irreducible` (`SPARQL11.Algebra.fst` ~4487/4491, to keep the ~600-line evaluator body out of unrelated proofs' SMT context), and no technique tried (`assert_norm`, `norm [delta_only]`, `nbe`, blanket `delta`) crosses back to the literal symbol. `theorem_filter_card` on the literal path stays hypothesis-carrying (`fexpr_congr e` as an explicit premise). Read this as: §3.1 reaches the shipping code; §3.2 reaches a byte-identical twin of it, not the literal symbol.

## 4. Modifiers (4 statements)

**4.1 ORDER BY — permutation, unconditional.** `SPARQL11.Algebra.Refinement.fst:1682-1686` (`theorem_sort_solutions_permutation`, ensures `forall mu. S.mult mu (sort_solutions base conds omega) == S.mult mu omega`). `sort_solutions` is `SPARQL11.Algebra.fst:5519`. Any conditions, any input, at the multiset level — reorders without adding/dropping rows. Does not cover: that the output is sorted — §4.2.

**4.2 ORDER BY — sortedness, conditional, refuted fragment.** `SPARQL11.Algebra.Refinement.fst:1901-1907` (`theorem_sort_solutions_sorted`, requires `totality_on` + `transitivity_on` the comparator over `omega`, ensures `sorted_by`). Same-kind IRI comparisons discharge cleanly via the string axioms (§9). By machine-checked counterexample, numeric comparisons with an unparseable literal break transitivity — FINDING SR-4: `sparql_order` reads a failed numeric parse as a tie regardless of which side failed (witness: `ER_Num 5`, unparseable `ER_Dec`, `ER_Num 3` — two adjacent ties, one non-tie). The unconditional statement is false, not unproven.

**4.3 LIMIT/OFFSET, unconditional.** `SPARQL11.Algebra.Refinement.fst:2028-2059` (`theorem_slice_solutions_window`/`_length`). All four `None`/`Some` offset×limit combinations — row `i` of the output is row `i+offset` of the input; output length is §18.4's guarded arithmetic. `slice_solutions` is `SPARQL11.Algebra.fst:5595`.

**4.4 DISTINCT and Project.** `theorem_distinct_complete` (`:2301`, requires each input mapping's domain has no repeats) and `theorem_project_card` (`:1177`, fully unconditional). `distinct_solutions`/`project_solutions` are `SPARQL11.Algebra.fst:5584`/`:5627`. Does not cover: `theorem_distinct_card` — FINDING SR-3: DISTINCT's dedup uses `rdf_term_eq` (RDF-1.1 value equality, case-insensitive lang tags) where the cardinality spec needs exact equality, the same gap SR-1/SR-2 name elsewhere. Recorded SPEC FALSE, not attempted further.

## 5. Results (2 statements)

**5.1 SRJ tree-layer round-trip.** `SPARQL.Protocol.RoundTrip.fst:420-423` (`lemma_json_val_of_response_roundtrip`). Exact JSON-*value* equality (not text) for the IRI + plain/typed-literal fragment (`rows_in_fragment`) — blank nodes, RDF 1.2 triple terms, directional language literals not yet covered.

**5.2 SRJ text-layer serialization, N rows, symbolic.** `SPARQL.Protocol.RoundTrip.fst:809-815`:

```fstar
let lemma_srj_n_rows (vars : list string) (rows : list binding_row)
  : Lemma (ensures
             serialise_response_json vars rows ==
               "{\"head\":{\"vars\":[" ^ json_var_list vars ^ "]},"
                 ^ "\"results\":{\"bindings\":["
                 ^ json_rows_joined rows
                 ^ "]}}")
```

`serialise_response_json` is the real shipping serializer (`SPARQL.Protocol.fst:909`). Unconditional — any vars, any rows, any length including zero — pins the exact wire text. Does not cover: parsing that text back symbolically — blocked on the same `FStar.String.sub` content gap named in §8.3; §5.1 is the proved direction for that.

## 6. Streaming (3 statements)

**6.1 Single chunk = batch.** `RDF.NQuads.Streaming.fst:690-695` (`theorem_stream_eq_batch_single_chunk`). Unconditional on content — any chunk with no newline, or ending in one — no hypothesis on well-formedness, escapes, or RDF shape.

**6.2 Multi-chunk = batch (the terabyte-file theorem).** `RDF.NQuads.Streaming.fst:2119-2123`:

```fstar
val theorem_stream_eq_batch
    (chunks : list string) (ws_list : list (list line_witness & list line_witness))
  : Lemma
      (requires stream_fold_wf "" chunks ws_list)
      (ensures stream_parse chunks == batch_parse (concat_all chunks))
```

Domain: any chunk list, any split, given a caller-supplied witness-chain (`ws_list`) proving each boundary lands cleanly — `stream_fold_wf` is a real obligation (threads line-classification through every boundary), not a rubber stamp. `stream_parse` folds `Parser.NQuads.fold_nquads_acc` in bounded memory; `batch_parse` is the shipping non-streaming `parse_nquads`. Does not cover: deriving `ws_list` automatically from raw bytes — a caller must supply it; the theorem proves that IF the split is well-formed, streaming and batch agree exactly.

**6.3 Consumer-layer homomorphism.** `RDF.NQuads.Streaming.fst:2950-2956` (`theorem_stream_consume_dataset_eq_batch`) — folding parsed quads into dataset state chunk-by-chunk, only `(consumer-state, stream_state)` retained between chunks, matches batch parsing (same `stream_fold_wf` premise). Does not cover: a fully generic consumer type at full multi-chunk generality simultaneously — the dataset-specific instance is proved, the fully-generic product is scoped future work.

## 7. Entailment/closure chain (corerdfs)

The kernel spans the whole engine, not only G4. This is the bidirectional chain that makes "the closure operator computes what RDFS entailment means" a theorem, not an assertion.

**7.1 rho-df saturation iff (abstract operator).** `RDF.Entailment.RDFS.Completeness.fst:662-666`:

```fstar
val rho_df_saturation_iff (g c e : list triple)
  : Lemma (requires rho_df_frag_graph c /\ rho_df_closed c /\
                    graph_tt_free e /\ is_subgraph g c /\
                    rho_df_entails g c)
          (ensures  rho_df_entails g e <==> simple_entailment_spec c e)
```

Domain: for ANY closure `c` that is fragment-preserving, closed, extensive, and sound over `g`, model-theoretic `rho_df_entailment` is equivalent to the checkable syntactic `simple_entailment_spec c e`. ρdf (subPropertyOf/subClassOf/type/domain/range — Muñoz, Pérez & Gutierrez 2009) is the minimal deductive system excluding RDFS's reflexivity rows (§8.4). Does not cover: full RDFS entailment — machine-checked witness `rho_df_entailment_strictly_stronger` shows the naive "closure then simple-entailment" statement against unrestricted RDFS interpretations is FALSE (registry FINDING C-1).

**7.2 rho-df closure decides (the shipping operator).** `RDF.Entailment.RDFS.RhoDFClosure.fst:1704-1715`:

```fstar
val rho_df_closure_decides (g e : rdf_graph) (fuel : nat)
  : Lemma
    (requires (let c = rho_df_closure g fuel in
               rho_df_chain_canonical g /\ rho_df_chain_wf g /\
               rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
               rho_df_subclass_subjects_iri c /\
               no_dup_keys (rho_df_closure_step_pre_dedup c) /\
               no_repeats_p c /\ no_repeats_p (rho_df_closure_step c) /\
               graph_len (rho_df_closure_step c) = graph_len c /\
               graph_tt_free e))
    (ensures  (let c = rho_df_closure g fuel in
               rho_df_entails g e <==> simple_entailment_spec c e))
```

Instantiates §7.1 with `rho_df_closure` — the six-rule operator built from the SAME `rdfs_rule_*` functions the shipping engine runs (rdfs2/3/5/7/9/11). The nine hypotheses are structural well-formedness conditions, not semantic restrictions. Does not cover: rdfs1/4a/4b/8/13 (shipping's 13-row closure includes them; they're axiomatic/resource-typing rows outside the ρdf fragment) and rdfs6/rdfs10/rdfs12 (§8.4).

**7.3 Composed to SPARQL query answers.** `SPARQL11.EntailmentRegime.RDFS.fst:1005-1018` (`theorem_rdfs_regime_bgp_exact_answer`):

```fstar
val theorem_rdfs_regime_bgp_exact_answer
      (g : rdf_graph) (q : bgp) (mu : solution_mapping) (fuel : nat)
  : Lemma
    (requires (let c = RC.rho_df_closure g fuel in
               BR.bgp_frag q /\ BR.graph_frag c /\
               graph_ground (instantiate_bgp q mu) /\
               rho_df_decides_hyps g fuel /\ bgp_instantiable q mu))
    (ensures  (let c = RC.rho_df_closure g fuel in
               (exists (muo : solution_mapping).
                  memP muo (eval_bgp q c) /\
                  instantiate_bgp q muo == instantiate_bgp q mu)
               <==>
               CP.rho_df_entails g (instantiate_bgp q mu)))
```

Composes §7.2 (`rho_df_decides_hyps` is exactly its nine clauses) with BGP-matching sound+complete at the shipping `eval_bgp` (`SPARQL11.Algebra.fst:2846`): for ground answers on the fragment, the evaluator's answer set over the closure IS the RDFS regime's answer set — an actual query-answering guarantee, the M3 target. Does not cover: non-ground answers (completeness is scoped to ground answers by design — a weaker list-membership statement was refuted first, finding RT-5); the ASK entry point over the selective index store has its own sibling theorem rather than inheriting this one automatically.

**7.4 Boundary: OWL/RDFS-Plus are per-rule, not chain-complete.** The registry's OWL 2 RL/RDF section (84 engine functions) and the RDFS-Plus tier (`rdfs_plus_closure`, `RDF.Entailment.RDFSPlus.fst:85`) extend this chain with per-rule licensing + truth certificates (26 of 34 `[row]` licensing, 33 of ~36 attempted truth obligations proved, per the registry's 2026-08-06 entries) but carry **no** §7.1-style bidirectional saturation theorem: `owl:sameAs` breaks the Herbrand construction §7.1's completeness proof uses (task #10's embedding problem). An OWL-entailed answer is a per-rule certificate, not one closure-level guarantee.

## 8. What the kernel does not cover

| # | Gap | Detail |
|---|---|---|
| 8.1 | String-to-token composition (parser edge) | Every §1 theorem starts from an already-tokenized input or a narrow symbolic string. The literal `string -> AST` composition is blocked on a real ulib gap: `FStar.String.sub`'s type gives only the *length* of a substring result, nothing about its *characters*. Task #52 migrated the lexer's 13 call sites from `String.sub` to `Parser.FastString.fs_byte_sub` (fully proved, §9), closing two probes previously recorded impossible — the full composition remains future work. |
| 8.2 | The `irreducible` boundary (expression/filter edge) | §3.2's FINDING FC-1 pattern recurs: entry points marked `[@@ irreducible]` on purpose (keeps large recursive definitions out of unrelated proofs' SMT search) get theorems restated against a verbatim "transparent twin" instead of the literal symbol — same code by construction, not a reimplementation, but expect this pattern before trusting a symbol name alone. |
| 8.3 | Three ulib string walls | `FStar.String.concat` shipped with zero equations (closed by `Parser.FastString.ConcatSpec.fst`'s `concat_spec`); symbolic `^` associativity/identity doesn't reduce for Z3 on symbolic operands even though it does on literals (closed for SRJ/N-Triples by `ConcatSpec.fst`'s `lemma_strcat_assoc`/`_empty_l`/`_empty_r`); `s == build_string (codes_of s)` is sharper and still open — a self-recursive Lemma cannot use `list_of_string`/`string_of_list` inside its own recursive call (confirmed by isolated probes, including a plain `int` function). Toolchain-shaped; kept internal per owner steer, not filed upstream. |
| 8.4 | rdfs6/rdfs10 unsound by design, not gap | Proved spec-level truth theorems but **no sound shipping engine rule**: the shipping approximation (`rdfs_reflexivity_axioms`, `P rdfs:subPropertyOf P` for every typed property) is machine-checked UNSOUND (`owl_reflexivity_axioms_not_rdfs_sound`, finding RS-1) — an RDFS interpretation may read `owl:ObjectProperty` as an arbitrary IRI. §7's ρdf fragment excludes these rows for this reason, matching the literature's own exclusion. |
| 8.5 | One live `admit()`, outside kernel scope | `RDF.CottasStore.PresenceBitmap.fst:164`'s comment reads "This is `admit()`'d... intentional", but the function body (line 209) is `()`, not `admit()` — stale comment, not a live violation (confirmed by direct read while writing this document). COTTAS storage backend, outside every section above; noted only because iron rule #10 claims zero carve-outs and a reader should be able to check that. |

## 9. Trust surface

| What | Where | Status |
|---|---|---|
| `unsafe_char_of_d7ff` | `Parser.FastString.CharBoundary.fst:57` | `assume val` — the **sole** surviving one in the FastString family after the 2026-08-10/11 re-founding. Exists because `FStar.Char.char_of_int`'s ulib type excludes U+D7FF by an off-by-one in its own refinement (`i < 0xd7ff` should read `<=`); no F* term can inhabit the needed type without `admit`/`magic`. OCaml realisation is a one-line constant, documented at the same location. |
| `RDF.Indexed.StringOrder.fsti` | 3 axioms (#347) | `FStar.String.compare`'s totality/antisymmetry/transitivity, unspecified in ulib. Backs §4.2's IRI-fragment sortedness and §7's index lookups. DO-NOT-WIDEN banner in-file. |
| `assume val` realisations, tree-wide | ~135 (direct count, `^\s*assume val` across `*.fst`/`*.fsti`, this session) | Registry's own figure is "approximately 146" (also citing 141 and ~148) and explicitly says re-count before quoting a precise number — 135 is another data point in that family, not a correction. Large majority are the COTTAS/HDT storage I/O layer (rule #11(a) pure I/O), outside every section above. |
| Extraction step | `fstar.exe --codegen OCaml` | Every proof above is about F\* source; the binding to the running binary is extraction, not re-verified. Mitigated by W3C test suites (below) and the hash-witness round-trip pattern for byte-layout claims. |
| `make verify-rdf-mt` | 26 modules, `formal/fstar/Makefile:73-91` | Every module cited §1-§7 is in this list. **Drift found**: the registry's own Trust-surface section (line 614-626) lists only 20 modules — predates the G3 M3/M4 SPARQL-algebra landings, missing `RDF.Entailment.RDFS.Completeness`, `RDF.Entailment.RDFS.RhoDFClosure`, `SPARQL11.Algebra.Spec`, `SPARQL11.Algebra.Refinement`, `SPARQL11.Algebra.BGPRefinement`, `SPARQL11.EntailmentRegime.RDFS`. Confirmed reading `Makefile:73-91` directly; reported, not fixed here (this document is additive). |
| Proof-only modules | `SPARQL11.Parser.TokenRoundTrip.fst`, `SPARQL11.Parser.AskBgpRoundTrip.fst`, `RDF.NTriples.RoundTrip.fst`, `RDF.NQuads.Streaming.fst`, `SPARQL.Protocol.RoundTrip.fst`, `SPARQL11.Expression.Refinement.fst` | Verified by `make <file>.checked` / whole-corpus `make verify` (module list is `$(wildcard *.fst)`), but not in `build-ocaml.sh`'s extraction list — nothing here is extracted. Proofs *about* the extracted modules they `open` directly (confirmed per-citation above), never reimplementations. |
| Test-suite gates | W3C SPARQL/RDF/OWL/RDFS conformance | Exercise the EXTRACTED, running engine — the check that proofs match observed behavior. Numbers move independently of this document; see `skills/test-suites/SKILL.md`. Most recent full-corpus figures in the registry (2026-08-11): SPARQL 631 pass 0 fail (of 631), RDF 1031 pass 0 fail (of 1031). |

## 10. Override guarantee — how to re-check this document

**Claim**: nothing outside this document overrides what it states — every statement above is a real F\* `Lemma` that type-checks under z3 4.13.3 with no escape hatch.

1. **No `--lax`, no `--admit_smt_queries`, no bare `admit()` behind any theorem cited.** Verified this session (`grep -rn '#(set|push)-options.*--lax'` and the same for `--admit_smt_queries`, over `formal/fstar/*.fst *.fsti`): **zero** matches tree-wide — every occurrence of either string is inside a comment (mostly compliance banners), never a live pragma. Iron rule #10's "no carve-outs" claim holds as stated. The one live `admit()` in the tree (§8.5) is outside every module cited here.

2. **Re-verify the kernel's own modules**: `eval $(opam env --switch=fstar)`, then from `formal/fstar/`: `make verify-rdf-mt` (26 modules, §7 + the SPARQL algebra spine) plus `make <file>.fst.checked` for each of `SPARQL11.Parser.TokenRoundTrip`, `SPARQL11.Parser.AskBgpRoundTrip`, `RDF.NTriples.RoundTrip`, `RDF.NQuads.Streaming`, `SPARQL.Protocol.RoundTrip`, `SPARQL11.Expression.Refinement`. Each target succeeds silently (already `.checked`, digest-valid) or re-runs the real proof. A nonzero exit is this document's central claim failing, not a flaky test.

3. **Re-verify the whole corpus** (hours cold, seconds warm — Makefile header comment): `make -j$(nproc) verify`. This is what `.github/workflows/clean-room-build.yml` runs weekly from a bare clone (Sunday 03:00 UTC) — catches "verifies locally but not from a clean tree," independent of any committed `.checked` cache.

4. **Confirm extraction agrees with the proofs** by running the W3C suites (`skills/test-suites/SKILL.md`) — the check that extraction (§9, the one unproved link) has not silently diverged from source.

A claim here that a future reader finds does not match the tree — a moved file:line, a changed signature, a dropped hypothesis — is itself a finding: report it the way the registry's own maintenance discipline requires ("a stale registry is worse than none").
