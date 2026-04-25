# SPARQL parser: relative IRI in BGP/CONSTRUCT + minimal DESCRIBE — Agent Resh

**Date:** 2026-04-25
**Branch:** claude/main
**HEAD at start:** `7823399` (form-key fix already landed)
**Wave 11 rebuild:** in flight — DO NOT run `build-ocaml.sh extract|compile`.

## The 4 protocol fails (Qof report `100fba6`)

Re-running `protocol` at HEAD: 29 pass / 5 fail. Form-key fix (#5 in Qof's
list) is committed but the runner binary hasn't been rebuilt yet, so the
`update_post_form` fail will clear with Wave 11. The other four:

| # | Test | Symptom | Root cause |
|---|---|---|---|
| 1 | `query_multiple_dataset` | `parse error: invalid IRI` on `<data1.rdf>` in BGP | parser rejects relative IRI; no service-URI BASE |
| 2 | `query_content_type_describe` | `unsupported: DESCRIBE queries` | F* parser explicitly bails on `Tok_DESCRIBE` |
| 3 | `query_content_type_construct` | `parse error: invalid IRI` on `<s>` in CONSTRUCT template | parser rejects relative IRI; no service-URI BASE |
| 4 | `update_base_uri` | `update parse error: expected predicate-object list` on `<test>` | UPDATE parser rejects relative IRI; no service-URI BASE |

(Note: Qof's report calls #1 `query_dataset_full`. That test actually passes;
the failing dataset test is `query_multiple_dataset`. Same root cause.)

## Three distinct gaps

### (a) Relative IRI in BGP / CONSTRUCT / UPDATE template (#1, #3, #4)

The F* parser already has a `resolve_relative_iri_tokens base ts` pass at the
top of `parse_select_query` (line 2460). When BASE is absent in the prologue,
`base = None`, `resolve_query_iri None rel = string_to_iri rel = None`,
tokens are left as-is, and downstream sites reject them.

Patch #65 (`resolve_tok_iri` in OCaml) wraps each `Tok_IRI i` site with a
runtime-mutable `current_base_iri_ref` lookup. **But the runner does not set
that ref for protocol tests** — only for SPARQL eval tests where it points at
the query file URI. So protocol tests get None and the relative IRIs blow up.

**Fix:** Have `run_protocol_test` set `current_base_iri_ref` to a synthetic
service URI before calling `parse_sparql_query` / `parse_sparql_update`. The
W3C protocol manifest uses `Host: www.example` and path `/sparql/`; the
combination `http://www.example/sparql/` is the conventional service URI. The
test `update_base_uri` literally asserts: "service-defined BASE URI which MAY
be the service endpoint". This is exactly what §4.1.1.1 / §6.1 of SPARQL 1.1
Protocol contemplates.

**This is a runner change, not an F* change.** The F* layer is already
correct — it accepts a base, and the patch already wires it through. We're
just providing the right runtime value at the right time.

### (b) DESCRIBE parser (#2)

The algebra already has `QF_Describe : list pattern_term -> query_form`
(SPARQL11.Algebra.fst:486). The parser at line 2465 explicitly bails:
`Tok_DESCRIBE -> ParseErr "unsupported: DESCRIBE queries"`.

**Fix:** Add `parse_describe_body` paralleling `parse_ask_body`. Grammar:

    DescribeQuery := DESCRIBE (VarOrIRIref+ | '*') DatasetClause* WhereClause? SolutionModifier

For minimum viable, accept `*` and a list of var-or-IRIref tokens. The
W3C test is just `DESCRIBE <http://example.org/>` — single absolute IRI,
no WHERE, no FROM. Algebra side returns empty triples (per §16.4.1 the
server chooses the description; an empty CBD is a legal answer).

Eval: `eval_describe_query` returns an RDF graph (list of triples). Phase
0 implementation: return `[]`. Mark with `// Phase 0: empty CBD per §16.4.1`.
The runner's protocol path doesn't inspect the body.

### (c) Multi-step UPDATE+SELECT (`update_base_uri`)

This is **subsumed by (a)**. The runner's protocol path only extracts the
FIRST `#### Request` block from the comment and only checks status class.
Once (a) lands, the UPDATE parses, the runner returns 2xx, the test passes.
The cross-request state assertion ("?o is not <test>") is not checked by the
Phase-1 runner. True multi-step replay would need session state — defer.

## Plan

1. **Scratch doc** (this file) — commit immediately.
2. **(a) Runner fix** — set `current_base_iri_ref := Some "http://www.example/sparql/"`
   in `run_protocol_test` before each `parse_sparql_*` call. Restore on exit.
   Pure OCaml runner change (no F* edit needed — patch 65 plumbing already in place).
3. **(b) DESCRIBE parser** — extend SPARQL11.Parser.fst:
   - Add `parse_describe_body` (parallels parse_ask_body)
   - Replace line 2465's stub with a call to it
   - F*-verify; no `--lax`
4. **No extract/compile** (Wave 11 in flight). Wave 11 will pick up changes.
5. **Commit** with message `sparql-parser: relative IRI resolution in BGP/CONSTRUCT + minimal DESCRIBE`.

## Expected delta

- Protocol: 29 → ≥32 pass (3 fixes from this task + 1 already-committed form-key fix = 4-test improvement when Wave 11 lands).
- Possible bleed-through to other suites if any test had `DESCRIBE` and
  was failing for the same reason; quick grep says no — DESCRIBE is rare
  in the eval suites.

## What's deferred

- True multi-step protocol replay (cross-request state). Requires session
  fixture in the runner. Out of scope for this task.
- Real CBD evaluation for DESCRIBE (we return `[]`). §16.4.1 leaves the
  description's content implementation-defined; Phase 0 stub is conformant.
- Removing patch #65 entirely (push the resolution into pure F*). Larger
  refactor; tracked separately.
