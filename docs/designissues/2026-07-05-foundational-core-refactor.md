# 2026-07-05 — A skimmable foundational core: RDF.Graph.Executable and SPARQL11.Algebra stratification

> **Owner addition (2026-07-05, axiomatic triples):** the RDF/RDFS
> axiomatic triple sets that W3C publishes at the namespace documents
> and in RDF Semantics §9 (e.g. `rdfs:range rdfs:range rdfs:Class .`)
> currently have no declarative representation in the tree — their
> consequences are hard-coded as closure rules
> (`rdfs_rule_range` et al.), reflexivity axioms are harvested
> programmatically, and OWL 2 RL's Table 5 is a generating code block
> with omissions documented only in comments. The `RDF.Vocabulary`
> module proposed below gains a companion `RDF.Vocabulary.Axioms`:
> the finite axiomatic tables as literal F\* triple lists, auditable
> line-by-line against the spec text, consumed by the closures as a
> seed graph. Only the genuinely infinite families (`rdf:_n`
> container membership) stay rule-generated, with a comment citing
> the spec's own note on infinitude. Gate: rdf-mt + OWL catalog
> scores byte-exact after the switch.

## Status

Design proposal, no code changes. Extends the roadmap in
[`skills/fstar-module-style/SKILL.md`](../../skills/fstar-module-style/SKILL.md)
("Planned stratification") and the audit in
[`2026-05-08-foundational-fstar-tier.md`](2026-05-08-foundational-fstar-tier.md)
with a concrete module design, a dependency-ordered migration sequence,
and blast-radius numbers measured against the tree as of this writing
(106 `.fst` files, 61,952 lines). Two agents are mid-flight on ShEx
files; nothing here touches those.

## 0. The owner's ask

> "We need to be able to glance at the foundational area and skim a
> refreshingly simple set of definitions that cover the core concepts
> constituting rdf, rdfs, URIs/IRIs, and the building blocks of
> SPARQL. Terms, Properties, Graphs, Datasets, Bnodes etc etc or
> however we have carved things in fstar. Currently the fstar mixes
> implementation, algorithm, interface etc too freely."

This is not a new initiative — it converges with an already-declared
standing priority. `docs/claude-rules/current-state.md` §Standing
priorities item 4 (owner directive, 2026-07-04) already names four
reusable foundation modules to extract (`RDF.IRI`, `XSD.Datatypes`,
`RDF.Unicode`, `RDF.LanguageTag`), and slice 1 of one of them
(`XSD.Datatypes.fst`, moved out of `SHACL.Validation.fst`) landed today
— see
[`2026-07-05-xsd-datatypes-module.md`](2026-07-05-xsd-datatypes-module.md).
A second precedent landed today too: `RDF.Dataset.Graphs.fst`, a
27-line accessor module over `RDF.Graph.Executable`'s existing
`rdf_dataset` type (see
[`2026-07-05-graphs-api-design.md`](2026-07-05-graphs-api-design.md)).

This doc folds both threads — the type-level split
(`RDF.Graph.Executable` → `RDF.Term`/`RDF.Triple`/`RDF.Graph`) and the
reusable-foundation-module thread (`RDF.IRI`/`XSD.Datatypes`/
`RDF.Unicode`/`RDF.LanguageTag`) — into one ordered plan, and adds the
piece neither covers yet: splitting the SPARQL algebra AST from its
evaluator, and a `RDF.Vocabulary` module for the scattered
`rdf:`/`rdfs:`/`owl:`/`xsd:` constants.

## 1. Survey — where things are defined today

Zero `.fsti` files exist in the tree (`find formal/fstar -name
'*.fsti'` returns nothing). All ~106 modules are flat `.fst` files;
"interface" today means "the top of the file, if you keep reading."

### 1.1 Where the core RDF types live

Everything is in one module:
[`RDF.Graph.Executable.fst`](../../formal/fstar/RDF.Graph.Executable.fst)
(5,236 lines) defines `bnode_id`, `iri`, `wf_iri`, `literal`,
`wf_literal`, `rdf_term`, `subject`, `triple`, `rdf_graph`,
`named_graph`, `rdf_dataset`, plus their equality functions
(lines 1-159). Everything downstream references these constructors —
**53 of 106 `.fst` modules** `open RDF.Graph.Executable` directly, and
it appears third in `build-ocaml.sh`'s `COMMON_MODULES`/`FSTAR_MODULES`
lists (right after `RDF.Format`), i.e. before almost everything else in
the extraction order.

### 1.2 Where IRI logic lives — duplicated, not shared

Two independent implementations of RFC 3986 reference resolution exist
today:

- [`Parser.IRI.fst`](../../formal/fstar/Parser.IRI.fst) (447 lines) —
  `parse_iri`, `remove_dot_segments`, `merge_paths`,
  `transform_references`, `recompose`, `resolve_iri_v2`.
- [`SPARQL11.IRI.Resolve.fst`](../../formal/fstar/SPARQL11.IRI.Resolve.fst)
  (276 lines) — its own `jir_remove_dot_segments`, `jir_merge`,
  `resolve_iri`, deliberately **not** sharing code with `Parser.IRI`.
  The module's banner explains why: it was factored out of
  `SPARQL11.Algebra.fst` and kept dependency-free of Algebra by
  duplicating "tiny and stable" helpers — a decision the file itself
  flags as provisional ("consolidation into a shared helper module is
  a separate cleanup").

This is the concrete instance behind current-state.md's "`RDF.IRI`
(RFC 3986/3987; today: `SPARQL11.IRI.Resolve` + `Parser.IRI` +
per-parser fragments)" line — two full RFC 3986 implementations, not
one with two call sites.

### 1.3 Where vocabulary constants live — three separate blocks, one file

`RDF.Graph.Executable.fst` itself contains three separate vocabulary
blocks, sequentially, none of them a distinct module:

- Lines 806-875: RDFS constants (`rdfs_subClassOf`, `rdfs_domain`,
  `rdf_type`, `rdfs_Class`, container-membership properties).
- Lines 1212-1420 (interleaved with OWL-RL rule code):
  `owl_Class`, `owl_ObjectProperty`, `owl_sameAs`,
  `owl_TransitiveProperty`, and ~20 more OWL constants.
- Lines 2216-2283 and 4007-4098: OWL restriction-vocabulary constants
  (`owl_Restriction_iri`, `owl_someValuesFrom_iri`, …) and XSD
  datatype-hierarchy constants (`xsd_long`, `xsd_nonNegativeInteger`,
  `xsd_hierarchy_edges`).

Separately, [`OWL.Vocabulary.fst`](../../formal/fstar/OWL.Vocabulary.fst)
(119 lines) is a **fourth** OWL/RDF vocabulary block, already split out
as its own module — but as a workaround for a two-copy duplication bug
(#209: the same OWL IRIs were defined once in `Tableau.fst` and once in
`OWL.QueryRewrite.fst` with `_iri`-suffixed names), not as part of a
deliberate vocabulary-consolidation plan. `OWL.QueryRewrite.fst` still
keeps its own `_iri`-suffixed forwarders per current-state.md item 4's
still-open follow-up ("Migrate `OWL.QueryRewrite._iri` constants to
`OWL.Vocabulary`" per the 2026-05-08 audit) — four vocabulary homes for
what should be one readable table per RDF/RDFS/OWL/XSD.

### 1.4 Where SPARQL's algebra AST and evaluator live

[`SPARQL11.Algebra.fst`](../../formal/fstar/SPARQL11.Algebra.fst)
(5,797 lines, the single largest module) is not purely an AST module —
type definitions (`triple_pattern`, `expr`, `property_path`,
`group_graph_pattern`, `query_form`, `update_op`, `sparql_update`) occupy
roughly lines 132-748 (~620 lines, 11% of the file). The remaining
~5,150 lines (89%) are evaluation: `eval_result` + the effective-boolean-value
machinery, the built-in function library (`fn_isLiteral`, date
functions, `string_encode_uri`), numeric promotion/casting, property-path
evaluation, solution-sequence sorting/aggregation, and
`apply_update_op`/`apply_delete_where` (SPARQL Update application). 12
modules `open SPARQL11.Algebra` directly.

Even the triple-pattern/BGP types are duplicated, not shared: `var_name`,
`pattern_term`, `pattern_subject`, `triple_pattern`, `bgp`, and
`solution_mapping` are defined **twice** — once in
`RDF.Graph.Executable.fst` (lines 556-586) and again in
`SPARQL11.Algebra.fst` (lines 284-363, the canonical copy `open`ed by
everything else). This is the clearest instance of "implementation
mixes into the wrong module" the owner is pointing at: a fragment of
SPARQL algebra sits inside the RDF foundational module for no
architectural reason — `RDF.Graph.Executable.fst`'s own `sparql_value`/
`comp_op`/`filter_expr_eval`/`bind_eval`/`sparql_concat` block
(lines 586-800, ~215 lines) is FILTER/BIND evaluation logic, not an RDF
core concept, and no code outside that file appears to consume it (its
`var_name`/`triple_pattern` types are shadowed by `SPARQL11.Algebra`'s
once a caller opens both).

### 1.5 Category breakdown, four biggest modules

Rough classification by line count (core types / spec algorithm /
engine pragmatics / vocabulary constants / helper soup), read from each
file's own structure via `grep -n '^let \|^type '`:

| Module | Lines | Core types | Spec algorithm | Pragmatics | Vocabulary | Helper soup |
|---|---:|---:|---:|---:|---:|---:|
| `RDF.Graph.Executable` | 5,236 | ~160 (3%) | ~2,285 (44%) RDFS/OWL-RL closure + XSD lexical/entailment | ~400 (8%) `indexed_graph`/bucket-map | ~350 (7%) RDFS+OWL+XSD constants | ~245 (5%) misplaced SPARQL FILTER/BIND fragment (§1.4); remainder is OWL-RL rule bodies |
| `SPARQL11.Algebra` | 5,797 | ~620 (11%) | ~4,600 (79%) eval/functions/casts/property-path/update | — (perf lives in `SPARQL.Plan.*`/`SPARQL.Eval.*`) | 0 (lives in `RDF.Graph.Executable`) | ~580 (10%) string/date parsing utilities |
| `SHACL.Validation` | 2,848 | ~50 (2%) | ~2,200 (77%) constraint eval + SPARQL-based validators | — | ~400 (14%) `sh:*` constants | ~200 (7%) path-eval helpers; already imports `XSD.Datatypes` |
| `RDF.Canonical` | 2,069 | ~50 (2%) | ~1,900 (92%) RDFC-1.0 HFDQ/HNDQ | ~120 (6%) sort/dedup | 0 | — |

`RDF.Canonical.fst` is the model to emulate: one spec algorithm, its
supporting helpers, no vocabulary block, no unrelated fragment from
another domain. `RDF.Graph.Executable.fst` is the opposite extreme:
core types are 3% of the file the "foundational tier" audit
(§1.1) treats as a single all-or-nothing unit.

### 1.6 KaRaMeL-compatibility signal

Per [`2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md)
§2.2, the smallest/purest `noeq`-free modules are the first C-build
candidates: `RDF.Format.fst` (92 lines), `Parser.IRI.fst` (447 lines).
Today's `RDF.Graph.Executable.fst` cannot join that list — `noeq type
literal`/`rdf_term`/`triple` at the top force KaRaMeL rejection of the
*entire* module, so the OWL-RL closure code that is 44% of the file
blocks C-extraction of the 3% that's actually portable. Splitting
types out is a second, independent argument beyond readability: it
unblocks the C-build track for the part of the foundational tier
that's cleanly extractable.

## 2. Design — the foundational layer

Six new/reorganized modules. Naming follows the existing dotted-prefix
convention (`RDF.*`, `SPARQL.*`) — no new `Impl`/`Core` suffix
convention is introduced without justification (see Open decision 1).

### 2.1 `RDF.Term.fst` — the term algebra

Contents: `bnode_id`, `iri`, `is_iri`/`wf_iri`, `literal`/`literal_wf`/
`wf_literal`, `rdf_term`, `subject`, plus `subject_eq`/`lang_tag_eq`/
`literal_eq`/`rdf_term_eq`/`literal_value_eq` and their reflexivity
lemmas. This is `RDF.Graph.Executable.fst` lines 1-159 essentially
verbatim, no new proof obligations — a copy-move, not a rewrite. Does
NOT include `datatype_value_eq` (XSD value-space equality; that's
`XSD.Datatypes`'s job per the already-declared follow-up in
[`2026-07-05-xsd-datatypes-module.md`](2026-07-05-xsd-datatypes-module.md)
§Migration order item 1) or `lang_tag_option_eq` (moves to
`RDF.LanguageTag` once that module exists, per the same doc's
"How RDF.LanguageTag / RDF.Unicode relate" section — this doc does not
re-litigate that call, just confirms it).

One screen-page (~160 lines): every concrete RDF term kind, decidable
equality, nothing else. No indexing, no closure rules, no SPARQL.

### 2.2 `RDF.Triple.fst` and `RDF.Graph.fst`

`RDF.Triple.fst`: the `triple` record + `triple_eq` +
`add_triple_if_new`/`add_triple_unchecked` (currently lines 128-138 and
931-942). `RDF.Graph.fst`: `rdf_graph`, `named_graph`, `rdf_dataset`,
`lookup_named_graph`, `empty_graph`/`empty_dataset`, `graph_add`/
`graph_remove`/`graph_union`, `find_objects`/`find_subjects`,
`graph_bnodes`, `rename_*_bnodes` family, `graph_dedup_sort`. This
matches the 2026-05-08 audit's proposed split exactly (§"1. Split
RDF.Graph.Executable", table); this doc adds the concrete line ranges
that audit didn't have yet.

Each is one screen-page-ish (~150-250 lines) — a human reads "what is a
triple, what is a graph, what is a dataset" without wading through
OWL-RL.

### 2.3 `RDF.Indexed.fst` (pragmatics companion)

The `indexed_graph`/`bucket_map` machinery (lines 286-514, ~230 lines)
is an acceleration structure for `find_objects`/`find_subjects` — a
textbook pragmatics module per the fstar-module-style skill's tier
split. It depends on `RDF.Term`/`RDF.Triple`/`RDF.Graph`, not the
reverse (the naive `find_objects`/`find_subjects` already exist as the
reference implementation at lines 898-920). This is the first
"beautify" instance of the §4 pattern: a correctness lemma of the
shape `find_objects_indexed g s p == find_objects g s p` (exact
statement is migration work) documents that the fast path matches the
naive one, following the recovery-plan pattern already adopted
elsewhere.

### 2.4 `RDFS.Closure.fst` and `OWL.Closure.fst`

Exactly the 2026-05-08 audit's proposal: `RDFS.Closure.fst` gets
`rdfs_closure_step` and the five `rdfs_rule_*` functions (currently
lines 990-1199, wired via `RDF.Indexed`'s `indexed_graph`).
`OWL.Closure.fst` gets the ~40 `owl_rule_*` functions,
`owl_rl_closure_step`/`owl_rl_closure`/`owl_rl_closure_with_reflexivity`,
and the entailment-regime dispatch (`entailment_closure`,
`regime_rdf`/`regime_rdfs`/`regime_owl_rl`/`regime_owl_direct` —
currently lines 1199-4760 and 5211-5236). This is the single biggest
line-count move: ~3,850 of `RDF.Graph.Executable.fst`'s 5,236 lines
(73%) leave the foundational module. After this move, "foundational"
means `RDF.Term` + `RDF.Triple` + `RDF.Graph` + `RDF.Indexed` at
roughly 800-900 lines — the 2026-05-08 audit projected "~800 LoC
instead of ~3500," which turns out to be an undercount of the
denominator: the module has grown to 5,236 lines since that audit (more
`owl_rule_*` functions landed in the interim), so the post-split core
is proportionally smaller than estimated (~17%, was ~23%).

### 2.5 `XSD.Axioms.fst` (already-scoped follow-up, restated)

The XSD lexical-normalization + datatype-hierarchy + consistency-check
code at lines 4760-5211 (`normalize_integer_lexical`,
`normalize_decimal_lexical`, `datatype_value_eq`, `xsd_is_subtype`,
`is_inconsistent`, `xsd_hierarchy_edges`) is the remaining piece of
`RDF.Graph.Executable.fst` this doc has not assigned. Per
[`2026-07-05-xsd-datatypes-module.md`](2026-07-05-xsd-datatypes-module.md)
§"What did NOT move", `datatype_value_eq` + its two normalize helpers
already move to `XSD.Datatypes.fst` as follow-up slice work — no fifth
XSD home proposed here. `is_inconsistent`/`xsd_is_subtype`/
`xsd_hierarchy_edges` are OWL-RL-adjacent value-space checks, not
vocabulary, so a sibling `XSD.Axioms` (Open decision 4).

### 2.6 `RDF.Vocabulary.fst` — one table, not four

Consolidates §1.3's four scattered vocabulary blocks
(`RDF.Graph.Executable`'s three inline blocks + `OWL.Vocabulary.fst`)
into one module with labeled sections: RDF core (`rdf:type`,
`rdf:first`/`rdf:rest`/`rdf:nil`), RDFS (`rdfs:subClassOf`,
`rdfs:domain`, …), OWL (`owl:sameAs`, `owl:Restriction`,
`owl:someValuesFrom`, …), XSD datatype IRIs. `OWL.Vocabulary.fst`'s
own banner already states the goal ("this module is the single source
of truth") — `RDF.Vocabulary` widens that from "OWL, without
duplication" to "RDF/RDFS/OWL/XSD, in one place." `OWL.Vocabulary.fst`
becomes a thin re-export or is retired (Open decision 2).
`OWL.QueryRewrite.fst`'s still-open `_iri`-suffixed duplicate
forwarders (§1.3) retire in the same slice.

### 2.7 `RDF.IRI.fst` — one RFC 3986 implementation, not two

Per current-state.md item 4: consolidate `Parser.IRI.fst` and
`SPARQL11.IRI.Resolve.fst`'s independent `jir_*`/non-`jir_*`
implementations into one. `Parser.IRI.fst` is the more complete
surface (447 lines: full parse + resolve + recompose) and already
foundational-tier per the 2026-05-08 audit; `SPARQL11.IRI.Resolve.fst`
becomes a thin forwarder or its 12 callers switch to `RDF.IRI` directly
(same choice as §2.6, Open decision 2). JSON-LD phases 3-4 need this
module ("extraction of those two leads," current-state.md item 4) —
not a cosmetic win, it removes a real fork risk (a bug fixed in one RFC
3986 implementation and not the other, silently).

### 2.8 `SPARQL.Terms.fst` (algebra AST, separated from evaluation)

The type-only ~620 lines from `SPARQL11.Algebra.fst` (§1.4): `var_name`,
`pattern_term`, `pattern_subject`, `triple_pattern`, `bgp`, `comp_op`,
`arith_op`, `aggregate_fn`, `expr`, `property_path`,
`group_graph_pattern`, `order_condition`, `select_item`/`select_clause`,
`group_condition`, `query_form`, `dataset_clause`, `graph_ref`,
`update_op`, `sparql_update`. `SPARQL11.Algebra.fst` keeps `eval_result`,
the function library, and everything after — it becomes purely the
evaluator over `SPARQL.Terms`'s AST, the "AST vs evaluation semantics"
split the 2026-05-08 audit names as "less urgent" but doesn't rule out.
`RDF.Graph.Executable`'s duplicate `var_name`/`triple_pattern`/`bgp`/
`solution_mapping` block (§1.4, lines 556-586) is deleted outright, not
moved — grep confirms no caller outside that file uses its copy. The
FILTER/BIND fragment (lines 586-800) needs a caller audit before
deciding its fate (Open decision 5) — may be dead code, in which case
deletion is simpler than migration.

### 2.9 `.fsti` policy for this layer

None of the six modules above get a `.fsti` in this pass. The
fstar-module-style skill's policy stands: `.fsti` earns its keep when
hiding a representation forces clients through an abstract signature
(the storage-backend case). The foundational types are *meant* to be
transparent — `RDF.Term.fst`'s `rdf_term` variant tags are
pattern-matched directly by 53+ modules; wrapping them behind a
signature would force every call site through accessor functions for
no correctness gain, and (per §1.6) plain transparent records extract
cleanest to C. Revisit `.fsti` only if a genuine abstraction-boundary
need appears — not preemptively. Explicit call, not a default: see
Open decision 3.

## 3. Migration mechanics

### 3.1 What actually breaks on a split

Renaming/splitting `RDF.Graph.Executable` ripples through four
independent surfaces, each measured against the tree as it exists
today:

1. **`build-ocaml.sh`'s three lists.** `RDF_Graph_Executable.ml` sits
   in the extract loop, `COMMON_MODULES`, and `FSTAR_MODULES`. Six new
   names replace one entry in each — mechanical, but every list-add
   historically causes merge conflicts with concurrent PRs (per the
   2026-05-07 debt-reduction plan's note on alphabetizing the list).
2. **51 extracted/hand-written `.ml` files** reference
   `RDF_Graph_Executable.*` by qualified name. Regenerated by
   re-extraction, not hand-edited — low-risk if extract runs for every
   affected module, but it forces "recompile everything"
   (`needs_rebuild_from_sources` fires a full recompile the moment any
   `.ml` is newer than a binary).
3. **11 hand-written OCaml patch files** in
   `minimal_regrettable_glue_code_each_with_an_open_issue/*.sh`
   hardcode `RDF_Graph_Executable.wf_iri`/`.rdf_graph`/
   `.solution_mapping` as qualified references (confirmed:
   `57_service_client_bind.sh`, `62_forward_ref_wiring.sh`, + 9
   others). These need updating to the new module names — the
   migration's real hand-editing surface, and the step most likely to
   be a silent breakage if missed (a stale reference fails loudly at
   `ocamlopt` with "Unbound module," but only once someone compiles).
4. **11 `bin/<consumer>/*.ml` files** (`factoidal_cli.ml`,
   `w3c_runner.ml`, `owl_runner.ml`, `rdfc10_runner.ml`,
   `shacl_runner.ml`, `shex_runner.ml`, `rif_runner.ml`,
   `factoidal_http.ml`, `factoidal_dump_nq.ml`,
   `factoidal_explain.ml`, `entry_jsoo.ml`) reference
   `RDF_Graph_Executable`/`SPARQL11_Algebra` directly and need their
   `open` lines updated — mechanical, real time cost.

### 3.2 Verification cost estimate

Measured data point (fast-verify-extract skill): `SPARQL11.Algebra.fst`
(5,777 lines) takes ~40s for a full cold re-verify.
`RDF.Graph.Executable.fst` is comparable in size (5,236 lines); budget
the same order of magnitude.

Splitting redistributes this cost rather than removing it — six new
modules each pay their own first-time verify, but cumulative SMT cost
is roughly conserved (same lemmas, partitioned across files). The real
new cost is **dependent cascade**: a dependency's content change
invalidates every dependent's `.checked` digest (F* embeds dependency
digests in `.checked`), even when the dependent's own re-verification
is fast. With 53 modules opening `RDF.Graph.Executable` today, changing
its `open` line to `open RDF.Term open RDF.Triple open RDF.Graph`
edits the SOURCE of all 53 (the `open` line itself), so all 53 pay a
real `fstar.exe` invocation — most fast, since only the `open` changed.
The `--dep full` + Kahn-layered parallel scheduler already implemented
in `build-ocaml.sh` (fast-verify-extract skill's "P1") is the tool for
this: it computes the DAG once and runs each layer through `xargs -P`,
so 53 mostly-independent modules parallelize rather than serialize.

Budget one full `./build-ocaml.sh extract` per migration step (this
migration is not the warm no-op case) plus the full W3C battery. On
the measured 7-layer/23-25-15-15-9-7-2-module DAG shape, the widest
layer (25 modules) dominates wall-clock — low-single-digit minutes per
step on a 4-core box, not the ~25-minute cold-CI figure (that's
toolchain-cold; this is `.checked`-cold for one hub's dependents, on an
otherwise warm cache).

### 3.3 Move order — minimize blast radius per step

Ordered so each step's battery gate is the smallest that actually
proves the step correct, and so no step depends on a later one:

| Step | What moves | New/changed modules | Blast radius | Gate |
|---|---|---|---|---|
| 1 | `RDF.IRI` consolidation (§2.7) | `RDF.IRI.fst` (from `Parser.IRI.fst`, renamed); `SPARQL11.IRI.Resolve.fst` → thin forwarder or retired | Low — `Parser.IRI` already has few dependents outside parsers; `SPARQL11.IRI.Resolve`'s 12 callers keep their call sites if forwarding, or need one `open` swap each if retired | Full RDF parser suite (NT/Turtle/NQuads/TriG/RDFXML) + SPARQL base-IRI resolution tests unchanged |
| 2 | `RDF.Vocabulary` consolidation (§2.6) | `RDF.Vocabulary.fst` (new); `OWL.Vocabulary.fst` → forwarder/retired; `OWL.QueryRewrite.fst`'s `_iri` duplicates retired | Low — pure constant re-homing, no logic change; grep-verifiable that every constant's IRI string byte-matches its old definition | OWL 2 RL PE/NE/Consistency/Inconsistency suites unchanged (these are the tests most sensitive to a mistyped vocabulary IRI) |
| 3 | `RDF.Indexed` extraction (§2.3) | `RDF.Indexed.fst` (from `RDF.Graph.Executable.fst` lines 286-514) | Low-medium — `RDF.Graph.Executable` shrinks by ~230 lines but keeps its own identity; dependents needing indexing gain one new `open` | Full RDF + SPARQL suites (indexing feeds `find_objects_indexed`/`find_subjects_indexed`, used by closure rules) |
| 4 | `SPARQL.Terms` split (§2.8) | `SPARQL.Terms.fst` (new, AST types); `SPARQL11.Algebra.fst` keeps evaluator only; `RDF.Graph.Executable`'s duplicate BGP-type block deleted | Medium — 12 direct `SPARQL11.Algebra` dependents need an added `open SPARQL.Terms` (or it re-exports transitively — see Open decision 6) | Full SPARQL 1.1 query + update suites (631 tests) — this is the step most likely to touch a real evaluator call site by accident |
| 5 | `RDF.Term`/`RDF.Triple`/`RDF.Graph` split (§2.1-2.2) | Three new modules; `RDF.Graph.Executable.fst` becomes a re-export shim initially (see below) | High — 53 direct dependents, all four surfaces in §3.1 | Full battery: RDF 1031, SPARQL 631, OWL 2 RL all suites, RDFC-1.0 86, SHACL 98+22, RIF, ShEx — everything that touches a triple |
| 6 | `RDFS.Closure`/`OWL.Closure`/`XSD.Axioms` extraction (§2.4-2.5) | Three new modules; `RDF.Graph.Executable.fst` (or its successor re-export shim) drops closure code entirely | High but narrower than step 5 — closure code's callers are the OWL/RDFS suites specifically, not every RDF-touching module | OWL 2 RL full suite (PE/NE/Consistency/Inconsistency) + rdf-mt entailment-regime suite + RDFS closure regression |
| 7 | Retire the `RDF.Graph.Executable` re-export shim | Delete the shim; every remaining `open RDF.Graph.Executable` becomes explicit `open RDF.Term`/`RDF.Triple`/`RDF.Graph` (+ `RDF.Indexed`/`RDFS.Closure`/`OWL.Closure` where actually used) | High in file-count (touches all 53 original dependents' `open` lines) but each edit is one line, grep-and-replace mechanical, no logic change | Full battery, once, as a final confirmation — this step is pure `open`-line hygiene |

Step 5's shim is the key risk-reduction move: instead of splitting
`RDF.Graph.Executable.fst` and simultaneously updating 53 dependents'
`open` lines in one commit, land the three new modules FIRST with
`RDF.Graph.Executable.fst` rewritten to `open RDF.Term open RDF.Triple
open RDF.Graph` and re-export every name those 53 dependents currently
use (thin `let` aliases, or F*'s `include` if it fits — needs a
one-file experiment before relying on it). This makes step 5 a pure
type-relocation with **zero** dependent-facing change — all 53 files'
`open RDF.Graph.Executable` still resolves to what they used before,
verified by the same full battery, and only step 7 (mechanical, no
logic touched) later removes the indirection. Same shim pattern
`XSD.Datatypes.fst`'s slice 1 already used (`SHACL.Validation.fst`
keeps thin re-export `let`s) — precedent already validated in this
tree.

### 3.4 Effort estimate

Per CLAUDE.md's Agent Work Strategy (commit-sized subagent scope):
steps 1-2 are S (under 2h, mechanical re-homing); step 3 is S-M; step
4 is M (needs the caller audit, Open decision 5); step 5 is M given
the shim (L without it); step 6 is M-L (largest line count, mechanical
once the step-5 shim exists); step 7 is S (grep-and-replace, one
battery run). Total: roughly 2-3 weeks of focused single-agent work
across ~9-10 commit-sized PRs — comparable in scale to the
query-planning recovery plan's own estimate for a similarly-sized
restructuring.

## 4. The beautify pass

### 4.1 Banner convention

Every module in the foundational layer opens with (in order):
`module X.Y` (line 1); a `//`-comment banner (per the hard 2026-07-04
comment-syntax rule — no `(* *)` in new code) stating what the module
defines and what it deliberately excludes plus where that lives
instead (`RDF.Dataset.Graphs.fst`'s banner already does this — "This
is a pragmatics/accessor module ... every definition below is a Tot
composition of existing RDF.Graph.Executable accessors" — use as house
style); a linked reference to the design doc realized, if any
(`OWL.Vocabulary.fst`'s "Per #209 (Tableau audit)..." pattern); `open`
statements, narrowest-dependency-first.

### 4.2 Section ordering within a module

Types → decidable equality + reflexivity lemmas → spec functions (the
module's actual algorithm) → pragmatics (if any stayed local) →
nothing after pragmatics. `RDF.Canonical.fst` (§1.5) already reads
close to this shape; `RDF.Graph.Executable.fst` inverts it today
(types first, then 4,000+ lines of mixed closure-rules/vocabulary/
pragmatics with no section boundary beyond `(** ===... *)` banners
that mark topic changes — "RDFS CLOSURE" then "OWL VOCABULARY" — not
tier changes).

### 4.3 What moves to pragmatics companions

Per the fstar-module-style skill's rule ("never let a pragmatic
concern leak into a core module when it can be a separate module the
core knows nothing about"), the clearest candidate this survey
surfaces is `RDF.Indexed.fst` (§2.3): an acceleration structure with
zero semantic content and a correctness-lemma opportunity.
`RDF.Graph.fst`'s `find_objects`/`find_subjects` stay the reference
implementation; `RDF.Indexed.fst` depends on `RDF.Graph`, never the
reverse.

### 4.4 What this pass does NOT attempt

No renaming of already-reasonably-scoped modules (`RDF.Canonical`,
`RDF.NQuads.Serialize`, `RDF.List.Helpers`) — they already match the
target shape (§1.5's table). No split of `SHACL.Validation.fst`; its
dependence on `SPARQL11.Algebra.expr` (`sh:sparql`/custom constraints,
`Alg.expr` at line 2161) means it should follow, not lead, the
`SPARQL.Terms` split (step 4) — doing both at once multiplies blast
radius for no gain.

## 5. Open decisions

1. **Naming: two-segment (`RDF.Term`/`RDF.Graph`) vs. deeper dotted
   names?** This doc uses two-segment names throughout, matching the
   2026-05-08 audit's proposal and the landed `RDF.Dataset.Graphs`/
   `RDF.Dataset.Merge` precedent. Confirm before step 5 — renaming
   after the fact repeats the whole blast-radius exercise.

2. **Shim-then-retire vs. rename-once for `OWL.Vocabulary` and
   `SPARQL11.IRI.Resolve`.** §2.6/§2.7 leave open whether these become
   permanent thin forwarders or get retired with callers updated.
   Precedent (`XSD.Datatypes` slice 1) kept the forwarder; a forwarder
   is one more file a reader has to learn is "not the real
   definition," so this is a real choice, not foregone.

3. **`.fsti` for `RDF.Term`/`RDF.Graph`, revisited later?** §2.9
   argues against `.fsti` now. If a future need appears (a second term
   representation for a specialized store), does the boundary get
   added retroactively, or does a parallel concrete type appear
   instead (as `RDF.CottasStore.*` do today)? Tree precedent favors
   the latter; flagged so a future agent doesn't re-derive this.

4. **`is_inconsistent`/`xsd_is_subtype`/`xsd_hierarchy_edges` home:
   `XSD.Datatypes.fst` itself, or a sibling `XSD.Axioms.fst`?** (§2.5)
   `XSD.Datatypes.fst`'s declared scope is "value spaces, canonical
   forms, numeric promotion" — `is_inconsistent` uses XSD value-space
   equality but is OWL/RDFS-adjacent, not a datatype concept itself.
   Leaning toward a sibling module; not decided here.

5. **Is `RDF.Graph.Executable`'s FILTER/BIND fragment (lines 586-800)
   live code or dead?** (§1.4, §2.8) A caller audit (grep every use of
   `filter_expr_eval`/`apply_bind`/`sparql_concat` outside its own
   definition site) should run before step 4 — if unused, deletion in
   its own tiny PR is simpler than migrating dead code.

6. **Does `SPARQL.Terms` need explicit `open`ing by `SPARQL11.Algebra`'s
   12 dependents, or should `SPARQL11.Algebra` re-export the AST types
   so existing call sites are unaffected?** (§3.3 step 4) The step-5
   shim pattern generalizes here — recommend the same re-export
   approach, deferring the explicit migration to a step-7-equivalent
   hygiene pass once the risk of simultaneous multi-file change is gone.

7. **Does `SPARQL11.Parser.fst`'s `--admit_smt_queries` debt (~65% of
   that file, standing priority 3) block any step here?** No step
   touches `SPARQL11.Parser.fst` directly — it consumes
   `SPARQL.Terms`'s AST as a producer, so step 4 changes its `open`
   line, not its proof obligations. Confirm by grepping whether any
   admitted query depends on names that migrate — otherwise the
   admitted status could mask a real breakage silently.

8. **"Properties" in the owner's phrasing — a distinct
   `rdf_property` type, or does `wf_iri` already cover it?** Today a
   predicate is simply a `wf_iri` in predicate position — no separate
   `property` type exists, and this doc doesn't propose inventing one
   (RDF 1.1 doesn't distinguish "property" as a term kind — it's a
   role an IRI plays). Flagging because the directive names
   "Properties" alongside "Terms, Graphs, Datasets, Bnodes" as a peer
   concept; confirm in review that "no new type" is the intended
   reading, not a request for one (which would be a larger,
   non-behavior-preserving change out of scope here).
