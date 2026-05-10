# Issue #65 Migration Plan — BASE IRI Resolution

**Date**: 2026-05-10
**Tracker**: GitHub issue #65
**Parent epic**: #200 Section H (VIOLATION-SEM tail)
**Status**: ready for implementation; estimated 3 days

## 1. What the patch does today

`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/65_base_iri_resolution.sh` (257 lines) is a post-extraction `sed`/regex patcher that bolts BASE-IRI tracking onto two extracted OCaml files. Three concrete edits:

1. **`SPARQL11_Algebra.ml`** — declares an OCaml-level `let current_base_iri_ref : wf_iri option ref = ref None` immediately above `eval_expr`, then surgically rewrites the body of `eval_select_query` to save/restore the ref around query evaluation (`current_base_iri_ref := q1.q_base; … ; current_base_iri_ref := saved_base`), and rewrites the `E_IRI_fn` case of `eval_expr` to call `resolve_iri base s` when the ref holds `Some base`.
2. **`SPARQL11_Parser.ml`** — injects an OCaml-level helper `resolve_tok_iri : string -> string` that calls `SPARQL11_Algebra.resolve_iri` against the ref when a `Tok_IRI` is relative, then *globally* regex-rewrites every `| Tok_IRI i -> if RDF_Graph_Executable.is_iri i …` block to bind `let ri = resolve_tok_iri i in` and substitute `ri` into ten different downstream constructor sites (`PS_IRI`, `PT_IRI`, `PP_IRI`, `E_IRI`, `T_IRI`, `DC_Default`, `DC_Named`, `parse_func_call`, etc.).
3. **`parse_prologue`** — adds `SPARQL11_Algebra.current_base_iri_ref := Some iri` inside the BASE branch so the rest of parsing can see the directive.

The driver also reaches into `current_base_iri_ref` from `bin/w3c-runner/w3c_runner.ml` (lines 75–97 and 1567–1619): the runner sets the ref to the `file://` URI of the query file before parsing, and `w3c_runner.ml` already calls `SPARQL11_Parser.parse_sparql_with_base init_base q_text` — so the ref's *only remaining* job at runtime is to (a) carry the BASE through `eval_expr E_IRI_fn`, and (b) cover the FROM/FROM NAMED case where parsing happens before the `q_base` field is set on the `query` record.

## 2. F\* signatures the patch realises

Despite the patch's framing, **none of the operations are `assume val`s**. The F\* side already has concrete implementations of every algorithm the patch invokes:

| Identifier in patch | F\* status | Location |
|---|---|---|
| `SPARQL11_Algebra.resolve_iri : wf_iri -> string -> wf_iri` | **Already pure F\*** | `SPARQL11.Algebra.fst:1679` |
| `SPARQL11_Algebra.resolve_query_iri : option wf_iri -> string -> option wf_iri` | **Already pure F\*** | `SPARQL11.Algebra.fst:1723` |
| `RDF_Graph_Executable.is_iri : string -> bool` | **Already pure F\*** | `RDF.Graph.Executable.fst:26` |
| `string_to_iri : string -> option wf_iri` | **Already pure F\*** | `RDF.Graph.Executable.fst:51` (proxied in `SPARQL11.Algebra.fst:51`) |
| `resolve_relative_iri_token` / `resolve_relative_iri_tokens` | **Already pure F\*** | `SPARQL11.Algebra.fst:680, 688` |
| `q_base : option wf_iri` field of `query` | **Already in F\* AST** | `SPARQL11.Algebra.fst:581` |
| `parse_sparql_with_base : option wf_iri -> string -> parse_result query` | **Already pure F\*** | `SPARQL11.Parser.fst:3323` |
| `parse_sparql_update_with_base` | **Already pure F\*** | `SPARQL11.Parser.fst:3922` |
| `current_base_iri_ref : wf_iri option ref` | OCaml-only mutable | injected by the patch + consumed by `w3c_runner.ml` |
| `resolve_tok_iri : string -> string` | OCaml-only | injected by the patch |

So the boundary-audit row's "MIGRATE — `SPARQL11.IRI.Resolve.fst`" is *misleading*: the resolution algorithm is already in F\*. **What's actually OCaml-only is the threading of the BASE through the post-prologue parse stream and the `E_IRI_fn` evaluator.** Issue #65's body says exactly this: "Add base IRI parameter to eval_expr and parse functions in F\*, threading it through the call chain."

## 3. Proposed F\* module layout

Given the analysis above, do **not** create a new `SPARQL11.IRI.Resolve.fst` *just* to host the algorithm. The pure RFC 3986/3987 algorithm already lives at `SPARQL11.Algebra.fst:1679`. The migration is a *threading exercise*, not an algorithm port. Two minimal options:

**Option A — Reader-monad style threading (preferred):**
- Add an explicit `base : option wf_iri` parameter to `eval_expr` (and the `eval_*` mutual block). Already in `eval_select_query`'s scope as `q.q_base`.
- For the parser, rely on the existing `resolve_relative_iri_tokens base ts'` pre-pass at `SPARQL11.Parser.fst:2467` (already invoked by `parse_select_query`). The OCaml regex injection becomes redundant.
- Delete `current_base_iri_ref` and `resolve_tok_iri` after auditing call sites.

**Option B — Tiny state-holder module if Option A's churn is too large:**
- New file `SPARQL11.Parser.BaseIRIState.fst` declaring `assume val current_base : ref (option wf_iri)` plus `get_base : unit -> ML (option wf_iri)` and `with_base : option wf_iri -> (unit -> ML 'a) -> ML 'a`. This explicitly reifies the OCaml mutable as an `ML`-effected F\* binding, brings it into the `assume val` registry, and lets the call sites stay shallow. Still a `VIOLATION-SEM` per Iron Rule #11 but at least typed and discoverable.

The boundary audit's recommended `SPARQL11.IRI.Resolve.fst` makes sense only if we choose to *factor out* the existing `resolve_iri`/`resolve_query_iri`/`resolve_relative_iri_token{,s}` cluster from `SPARQL11.Algebra.fst` into its own module — orthogonal to fixing #65, but worth doing as a cleanup because IRI resolution is tangled with the algebra module today (it sits at line 1679 of a 5840-line file).

**Recommendation: Option A + factor-out cleanup.** Net result is one new module `SPARQL11.IRI.Resolve.fst` (extracted from existing code, no new logic), one extended `eval_expr` signature, zero new `assume val`s, and patch #65 deleted.

## 4. Step-by-step migration plan

### Step 1 — Cleanup move (no behaviour change)
Move `find_scheme_end`, `find_slash_from`, `find_last_slash`, `take_chars`, `remove_fragment`, `resolve_iri`, `resolve_query_iri`, `resolve_relative_iri_token`, `resolve_relative_iri_tokens` from `SPARQL11.Algebra.fst:1660–1726` into a new `SPARQL11.IRI.Resolve.fst`. Add `open SPARQL11.IRI.Resolve` to `SPARQL11.Algebra.fst` and `SPARQL11.Parser.fst`.

This is purely a refactor: the ML extraction surface is identical except for the module prefix.

### Step 2 — Thread `base` through `eval_expr`
Change `eval_expr : expr -> solution_mapping -> expr_result` to `eval_expr : option wf_iri -> expr -> solution_mapping -> expr_result`. The `E_IRI_fn` arm becomes pure:

```fstar
| E_IRI_fn e1 ->
  (match eval_expr base e1 mu with
   | ER_Term (T_IRI i) -> ER_Term (T_IRI i)
   | ER_Term (T_Literal l) ->
     let s = lit_lexical l in
     (match base with
      | Some b -> ER_Term (T_IRI (resolve_iri b s))
      | None ->
        (match string_to_iri s with
         | Some i -> ER_Term (T_IRI i)
         | None -> ER_Error))
   | _ -> ER_Error)
```

Mechanical churn elsewhere: every recursive `eval_expr e mu` call in `eval_expr` and every `eval_*` peer that calls `eval_expr` must thread `base`. Grep for `eval_expr ` returns ~70 sites in `SPARQL11.Algebra.fst`; each is a one-token addition.

`eval_select_query` already has `q.q_base` in scope, so the pass-through is `eval_pattern q.q_base q.q_pattern …` instead of saving/restoring a mutable.

### Step 3 — Drop the parser regex injection
Verify that the existing F\* `resolve_relative_iri_tokens base ts'` pass (`SPARQL11.Parser.fst:2467`, called once per query in `parse_select_query` and once per update operation in the update parser at `:3865`) covers every `Tok_IRI` site that the OCaml patch rewrites. Spot-check: `DC_Default`/`DC_Named`, `PS_IRI`, `PT_IRI`, `PP_IRI`, datatype IRIs after `^^`. The pre-pass is line 680's `resolve_relative_iri_token`; confirm it walks every variant of `token` that carries a `Tok_IRI`. If any are missed (likely for datatype IRIs since the patch has special handling for `Tok_IRI dt` in HATHAT context), extend `resolve_relative_iri_token` to cover them.

### Step 4 — Delete `current_base_iri_ref` and `resolve_tok_iri`
Once Steps 2–3 land and the W3C test suite is green, the OCaml mutable is unreachable. Delete:
- The `current_base_iri_ref` reads in `bin/w3c-runner/w3c_runner.ml` (lines 75–97, 1567–1619) — these become dead code because `parse_sparql_with_base init_base q_text` already threads the BASE through F\*.
- The patch file `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/65_base_iri_resolution.sh`.
- The corresponding `bash …/65_base_iri_resolution.sh` invocation in `formal/fstar/build-ocaml.sh` (coordinate with the parallel #200 Section F migration thread to avoid merge conflict — this file is being rewritten there).

### Step 5 — Boundary audit + close issue
Update `docs/designissues/fstar-ocaml-boundary-audit.md` row for #65 to RETIRED with the closing commit hash. Close GitHub issue #65 with a back-reference to the closing commit.

## 5. Test impact

W3C test suite has **31 `.rq` files containing a `BASE` directive** under `third_party/testing/w3c/sparql/`. The most directly load-bearing manifests:

| Manifest | What it covers |
|---|---|
| `sparql/sparql10/basic/manifest.ttl` | `base-prefix-{1..5}.rq` — canonical positive BASE-resolution tests. |
| `sparql/sparql11/basic-update/manifest.ttl` | BASE in update prologue (multi-operation re-declaration). |
| `sparql/sparql11/protocol/manifest.ttl` | Service-URI-as-BASE per §4.1.1.1 (the `init_base` parameter). |
| `sparql/sparql12/lang-basedir/manifest.ttl` | SPARQL 1.2 `BASE` in directive position. |
| `sparql/sparql11/functions/iri{01,02}.rq` | `IRI()` / `URI()` constructor — the `E_IRI_fn` arm fixed in Step 2. |
| `sparql/sparql10/syntax-sparql{1,2}/syntax-{lit,general}-*.rq` | Syntax-only BASE acceptance tests (~24 files). |
| `sparql/sparql11/construct/` | `constructwhere04` — explicitly called out in patch comments as the FROM-without-BASE regression case. |

If Step 3's audit misses a `Tok_IRI` call site, the regression typically manifests as: a relative IRI like `<x>` reaching the algebra layer un-resolved, then `string_to_iri "x"` returns `None`, the triple match fails, and the test returns an empty solution sequence. Catch this by running the W3C runner against each affected manifest before and after the migration.

## 6. Estimated effort + risks

**Estimate: 3 days** for a careful engineer who knows the F\* module already. Breakdown:

- Day 1: Step 1 (refactor move) + Step 2 signature change. Mechanical but ~70 `eval_expr` callsites; F\* will compile-error you through the list.
- Day 2: Step 3 audit + parser cleanup. The risk concentrate is here: the OCaml regex patch handles `DC_Default`, `DC_Named`, `parse_func_call`, datatype IRIs separately because the F\* `resolve_relative_iri_tokens` pre-pass might not currently cover all of them. Need to read `resolve_relative_iri_token` (`SPARQL11.Algebra.fst:680`) and verify every `Tok_IRI`-bearing token variant is rewritten.
- Day 3: Step 4 deletion + W3C suite rerun + documentation updates.

**Spec-corner risks:**

1. **BASE in updates with multiple operations.** SPARQL 1.1 Update §4 allows `PREFIX`/`BASE` to recur between `;`-separated operations. The F\* update parser at `:3865` already calls `resolve_relative_iri_tokens base' ts'` per operation, so this is likely OK — but worth a focused test.
2. **BASE in nested groups.** SPARQL 1.1 §4.1.1.1 says BASE only appears in the prologue, not in nested `GROUP BY` or sub-SELECT contexts. The current F\* code respects this (sub-SELECTs receive `init_base = None` per the comment at `:2457`). Keep this invariant when threading `base` through `eval_subselect`.
3. **RFC 3986 vs 3987.** The current `resolve_iri` is described in its own comment as a "simplified implementation covering common SPARQL cases" — it handles the four major reference forms (absolute, fragment, absolute-path, relative-path) but does not implement the full RFC 3986 §5.2.4 `remove_dot_segments` algorithm, and IRIs (3987) are treated as opaque strings. Migration #65 inherits this limitation; do **not** try to also fix it in the same PR. File a follow-up issue for full §5.2.4 compliance.
4. **Service URI as BASE.** Per the comment at `SPARQL11.Parser.fst:3320`, the protocol runner supplies the service URI as `init_base`. The OCaml runner today derives this via `file_to_base_uri` (a `file://` URI from the query path) — that's an `ASSUME-IO` boundary and stays in OCaml. **Do not migrate `file_to_base_uri`** — it's the legitimate I/O boundary for "where did this query text come from", and trying to push it into F\* would re-introduce a `VIOLATION-SEM` of the opposite kind (filesystem effects in pure code).
5. **Coordination with parallel #200 Section F work.** The main conversation today is editing `formal/fstar/build-ocaml.sh` and `bin/factoidal-http/factoidal_http.ml`. The Step 4 deletion of the `bash …/65_base_iri_resolution.sh` call in `build-ocaml.sh` will conflict; sequence so #65 lands *after* the Section F PR merges.

## 7. Next-PR sketch

Title: `Issue #65: thread BASE IRI through eval_expr in F*; retire patch 65_base_iri_resolution.sh`

Files touched:
- **NEW**: `formal/fstar/SPARQL11.IRI.Resolve.fst` (~80 lines, lifted verbatim from `SPARQL11.Algebra.fst:1660–1726`).
- **EDIT**: `formal/fstar/SPARQL11.Algebra.fst` — remove the lifted block; add `open SPARQL11.IRI.Resolve`; change `eval_expr` signature to take `option wf_iri` first parameter; thread through ~70 callsites; rewrite `E_IRI_fn` arm to use the parameter; rewrite `eval_select_query` to pass `q.q_base` instead of mutating a ref.
- **EDIT**: `formal/fstar/SPARQL11.Parser.fst` — verify `resolve_relative_iri_token` covers every `Tok_IRI`-carrying variant the OCaml patch rewrites; extend if needed; add `open SPARQL11.IRI.Resolve`. No signature changes; the existing pre-pass is already correct in shape.
- **EDIT**: `bin/w3c-runner/w3c_runner.ml` — delete reads/writes of `SPARQL11_Algebra.current_base_iri_ref` (already redundant once the parser's `init_base` parameter is the single source of truth); keep `file_to_base_uri` (legitimate I/O).
- **DELETE**: `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/65_base_iri_resolution.sh`.
- **EDIT**: `formal/fstar/build-ocaml.sh` — drop the `bash …/65_base_iri_resolution.sh "$OUTDIR"` line. **Coordinate with #200 Section F.**
- **EDIT**: `docs/designissues/fstar-ocaml-boundary-audit.md` row 185 — mark RETIRED with commit hash.

CI gate: full W3C suite (sparql10/basic, sparql11/basic-update, sparql11/protocol, sparql12/lang-basedir, sparql11/construct, sparql11/functions/iri*) must pass with zero new failures.

---

**Verdict: 3-day migration.** Not a 1-day job because of the ~70-site mechanical churn through `eval_expr` callers and the audit step on `resolve_relative_iri_token` coverage, but well short of week-scale because the resolution algorithm is already in F\* and the W3C harness already drives the typed `parse_sparql_with_base` entry point.
