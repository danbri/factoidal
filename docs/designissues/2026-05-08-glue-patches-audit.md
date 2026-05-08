# Glue Patches Audit (#200 Section E)

**Date:** 2026-05-08

This doc classifies every shell patch the build pipeline applies to
F\*-extracted OCaml. Two source dirs:

1. `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
   (15 patches) — patches with an open elimination issue.
2. `formal/fstar/experimental_ocaml_glue/`
   (13 .sh + 1 .c) — COTTAS / on-disk index runtime; the
   F\*-purity-unwind area.

**Total:** 29 patches.

The audit produces a verdict for each:

- **ASSUME-OK** — legitimate `assume val` realisation per CLAUDE.md
  rule #11 (pure I/O, host call-out, vendored crypto).
- **ASSUME-OK-PROVISIONAL** — currently #11-shaped but the underlying
  F\* gap should be closed eventually.
- **VIOLATION** — smuggles RDF/SPARQL/OWL/byte-layout semantic logic
  the verified library boundary forbids. Must be migrated to F\*
  before rule #11's caveat can be dropped (Section H).
- **NEEDS-AUDIT** — header alone is ambiguous; the patch script body
  needs a deeper read before classification.

## Block A — `minimal_regrettable_glue_code_each_with_an_open_issue/`

| Patch | Issue | Verdict | Notes |
|---|---|---|---|
| `53_blank_node_variable_rewriting.sh` | [#53](https://github.com/danbri/factoidal/issues/53) | **VIOLATION** | bnode-to-variable rewrite for entailment regimes lives in the runner. Semantic logic; must move to `OWL.QueryRewrite.fst` or a sibling F\* module. The patch's own README entry calls it `KNOWN VIOLATION`. |
| `57_service_client_bind.sh` | [#57](https://github.com/danbri/factoidal/issues/57) | ASSUME-OK | SERVICE clause HTTP client realisation. Pure I/O call-out per #11(a). |
| `62_forward_ref_wiring.sh` | [#62](https://github.com/danbri/factoidal/issues/62) | ASSUME-OK | Threads forward references the F\* extractor cannot emit. Pure plumbing, no decisions. |
| `63_regex_hash_uuid_stubs.sh` | [#63](https://github.com/danbri/factoidal/issues/63) | ASSUME-OK | Regex (host engine), SHA hashes (vendored crypto), UUID generation (host RNG). All three #11-acceptable. |
| `64_sparql_parser_escape_stubs.sh` | [#64](https://github.com/danbri/factoidal/issues/64) | ASSUME-OK-PROVISIONAL | String-escape primitives. Functions are total + pure; should lift to F\* as the unicode-handling story matures. |
| `65_base_iri_resolution.sh` | [#65](https://github.com/danbri/factoidal/issues/65) | ASSUME-OK-PROVISIONAL | Threads base-IRI through the parser via a global ref. The stateful pattern is a workaround for missing reader-monad; the IRI-resolution algorithm itself belongs in F\*. |
| `66_zero_length_property_path.sh` | [#66](https://github.com/danbri/factoidal/issues/66) | **VIOLATION** | SPARQL property-path semantics fix — zero-length path `?s :p* ?s` should bind `?s` to every node. This is operational semantics, must be in `SPARQL11.Algebra.fst`. |
| `67_rdfxml_validation.sh` | [#67](https://github.com/danbri/factoidal/issues/67) | **VIOLATION** | RDF/XML validation rules (rejecting prohibited constructs per the spec). Per CLAUDE.md rule #4, parsers are F\*; the validation rules are part of the parser's spec. |
| `68_unicode_boundary_workarounds.sh` | [#68](https://github.com/danbri/factoidal/issues/68) | ASSUME-OK | Works around F\*'s `char` precondition `< 0xD7FF` (vs Unicode's `< 0xD800`). Pure type-system gap; resolution is a tighter F\* refinement. |
| `69_runner_io_glue.sh` | [#69](https://github.com/danbri/factoidal/issues/69) | ASSUME-OK | Adjustments to `w3c_runner.ml`. The runner is consumer scope (`bin/w3c-runner/`), so #11 doesn't bite. The patch should retire by being inlined into the runner source. |
| `89_fast_string_primitives.sh` | [#89](https://github.com/danbri/factoidal/issues/89) | ASSUME-OK | Performance primitives for `Parser.FastString`. Each function is `assume val foo : ... -> Tot bar` with a host-engine call-out body. #11(c). |
| `95_stack_safe_list_ops.sh` | [#95](https://github.com/danbri/factoidal/issues/95) | **VIOLATION-MINOR** | Replaces three F\*-extracted list ops with tail-recursive OCaml. Mechanical rewrites preserving observational equivalence — no semantic change — but the F\* sources should be rewritten in tail-rec form so the patch can be deleted. Bookkeeping issue, not a correctness gap. |
| `103_parquet_ascii_string_fast_path.sh` | [#103](https://github.com/danbri/factoidal/issues/103) | ASSUME-OK | Parquet decoder fast-path. F\* ships a slow correct version; OCaml replaces with a faster equivalent. Performance optimisation only — but should ideally reduce to a `--codegen` hint, not a string-replacement patch. |
| `181_shacl_validate_stub.sh` | [#181](https://github.com/danbri/factoidal/issues/181) | ASSUME-OK | No-op placeholder for the SHACL Phase 1 skeleton. Discharges rule #3 bookkeeping. Will shrink to wire only `eval_sparql_target_select` in Phase 2. |
| `202_now_ms.sh` | [#202](https://github.com/danbri/factoidal/issues/202) | ASSUME-OK | Wall-clock for the time-budget evaluator. #11(a) — pure I/O. |

**Block A score:** 11 ASSUME-OK · 4 VIOLATION (one minor)

The four VIOLATIONs are:

- **#53** (bnode-variable rewriting) — entailment regime bookkeeping.
- **#66** (zero-length property paths) — SPARQL semantics.
- **#67** (RDF/XML validation rules) — parser spec.
- **#95** (stack-safe list ops) — mechanical rewrites; F\* source should
  be tail-rec.

## Block B — `experimental_ocaml_glue/`

These patches realise the COTTAS / on-disk index / Parquet runtime.
Most claim rule #11(c) compliance via "thin dispatch shim" framing.
The COTTAS migration is its own track ([recovery
plan](2026-05-07-query-planning-fstar-recovery.md)).

| Patch | Verdict | Notes |
|---|---|---|
| `ballyhoo_hdt_runtime.sh` | ASSUME-OK | HDT format adapter; format reader I/O. |
| `cottas_column_seq_runtime.sh` | ASSUME-OK | `cottas_column` abstract type + `Array.length` / `Array.unsafe_get`. Self-describes #11(c). |
| `cottas_inmem_encoder_runtime.sh` | ASSUME-OK-WIP | Phase A scaffold (stub returns None). Phase A.5 will need re-audit when the encoder is filled out — encoder body must be byte-layout in F\*, not OCaml (per #11). |
| `cottas_ondisk_runtime.sh` | ASSUME-OK | Self-describes Phase A+B migration to F\* (11/13 + 2/2 lookups now `Tot` in F\*). What's left here is I/O glue. |
| `cottas_ondisk_z_lazy_open.sh` | ASSUME-OK | _Reaudit 2026-05-08:_ pure caching policy + lazy initialisation. The patch defers `collect_distinct` work for the subjects/objects parquet columns until the first lookup; predicates + graphs stay eager. Lookup results unchanged. State plumbing only — rule #11(c). |
| `cottas_ondisk_zzzzz_ondisk_index.sh` | ASSUME-OK | mmap + byte-range I/O primitives (`mmap_companion_open`, `read_companion_u32_le`, etc.) realising 6 `assume val`s. Pure I/O. |
| `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` | **VIOLATION** | _Reaudit 2026-05-08:_ companion-file WRITER for `<cottas>.p.offsets` with end-to-end OCaml byte layout (magic `0x4f544f43`, version, num_rgs × num_predicates u64 offset table, packed u32 row-position data). The patch self-acknowledges "as a follow-up belongs in F\* as `RDF.CottasStore.OnDiskOffsetIdx`". Same canonical violation as `compound_po_writer.sh` — issue #100. |
| `cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh` | **VIOLATION** | Companion-file WRITER. CLAUDE.md rule #11 explicitly forbids byte-layout in OCaml: "the byte assembly belongs in F\* (`serialize : data -> Tot (list u8)`), and the OCaml side reduces to `write_bytes`." This patch builds the `<cottas>.po.presence` file format end-to-end in OCaml. The patch self-claims "rule-#11(b)" but rule #11 has no (b) for companion-file writers — that taxonomy slot doesn't exist. |
| `cottas_ondisk_zzzzzzzzzzzzzzzzz_token_lookup_runtime.sh` | ASSUME-OK | Hashtbl-based token-id lookup; thin dispatch over OCaml-side `Hashtbl<token, int>` infrastructure. Self-describes #11(c). |
| `cottas_pagecache_global_runtime.sh` | ASSUME-OK | Process-level LRU page cache `ref` cell. F\* reasons about LRU semantics via pure helpers; OCaml owns only the storage cell. #11(c). |
| `cottas_runtime.sh` | ASSUME-OK | Backend-hook caches; Parquet probing logic stays in F\*. |
| `parquet_footer_runtime.sh` | ASSUME-OK | File I/O glue; footer parsing in F\*. |
| `util_log_runtime.sh` | ASSUME-OK | `emit` (logging) realisation. Pure I/O #11(a). |
| `parquet_zstd_stubs.c` | ASSUME-OK | Vendored zstd C stubs — host call-out. |

**Block B score** _(after 2026-05-08 reaudit of the two NEEDS-AUDIT
entries)_: 12 ASSUME-OK (one WIP) · 2 VIOLATION

Two confirmed VIOLATIONs (both same canonical pattern — companion
file with byte-layout assembled in OCaml):

- `cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh` (issue #104,
  handle nun4) — `<cottas>.po.presence` writer.
- `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (issue #100, handle
  Lamed3) — `<cottas>.p.offsets` writer.

Both should reduce to a thin `write_bytes` over an F\* `serialize`
function (`RDF.CottasStore.OnDiskOffsetIdx.serialize_offsets` and a
sister `RDF.CottasStore.OnDiskCompoundPo.serialize_compound_po`).

NEEDS-AUDIT cleared (`cottas_ondisk_z_lazy_open.sh` upgraded to
ASSUME-OK after deeper read — see Block B table).

## Aggregate

| Category | Block A | Block B | Total |
|---|---|---|---|
| ASSUME-OK | 11 | 12 | 23 |
| ASSUME-OK-PROVISIONAL | 2 (#64, #65) | 0 | 2 |
| ASSUME-OK-WIP | 0 | 1 (inmem encoder) | 1 |
| VIOLATION | 4 (#53, #66, #67, #95) | 2 (po-writer, lamed3) | 6 |
| NEEDS-AUDIT | 0 | 0 (cleared 2026-05-08) | 0 |
| **Total** | **15** | **14** (incl. .c) | **29** |

(Two WIP/PROVISIONAL count under ASSUME-OK in the aggregate.)

**Update 2026-05-08:** Both NEEDS-AUDIT entries resolved.
`cottas_ondisk_z_lazy_open.sh` is ASSUME-OK (caching policy only).
`cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` is VIOLATION (companion
file byte layout assembled in OCaml, same shape as #104). Total
VIOLATION count: 5 → 6.

## Recovery Order

To drop the rule #11 caveat (Section H), the 5 confirmed VIOLATIONs
must be migrated to F\*. Estimated effort:

1. **#95** stack-safe list ops — **1 day**. Mechanical:
   rewrite three F\* defs in tail-rec form (e.g. `triple_matches_bound`
   → `List.fold_left`, `list_filter_map` → tail-rec accumulator).
   Smallest commit; ship first.

2. **#66** zero-length property paths — **2 days**. Audit
   `SPARQL11.Algebra.fst` `eval_property_path`; add the universal
   binding for the empty path. Test on the existing W3C
   property-path suite.

3. **#67** RDF/XML validation rules — **3 days**. Reject prohibited
   constructs in `Parser.RDFXML.fst`. Test against the rdf-xml W3C
   suite.

4. **#53** bnode-variable rewriting — **5 days**. Move to
   `SPARQL.Query.Analysis.fst` or a new `OWL.QueryRewrite.BNodes`
   module. Coordinates with the entailment regime dispatch.

5. **#104** compound po writer — **1 week**. Define
   `serialize_compound_po : compound_po -> Tot (list u8)` in F\*,
   prove header invariants (magic, version, sentinel), reduce the
   OCaml side to `write_bytes`. Add a hash round-trip CI test
   ([io-verification pattern](2026-05-07-io-verification-and-third-party.md)).

6. **#100 / Lamed3** offsets writer — **3 days** _(after #104 lands)_.
   Same shape as #104; once the F\* serialise + round-trip pattern is
   in place, this is a pure copy-paste of the format definition into
   `RDF.CottasStore.OnDiskOffsetIdx.fst`. Format: magic
   `0x4f544f43` (`COTO`), version, num_rgs × num_predicates u64
   offset table, packed u32 row-position data.

**Total:** ~3.5 weeks of focused work, parallelisable to ~2 weeks if
two engineers split blocks A and B.

After landing 1–5 plus auditing the two NEEDS-AUDIT entries (which
may turn out to be fine), the rule #11 caveat in CLAUDE.md can move
from the iron-rule body to the historical-notes section, and the
qualifier can be removed from READMEs / talks / PRs.

## Next Concrete Step

File issue #237: "Section E recovery — the 5 confirmed VIOLATION
patches as a tracked workstream", with checkboxes for items 1–5
above and links back to the existing per-patch issues.
