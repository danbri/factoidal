# Large companion-file writers — byte-format-in-F\* design call

**Date**: 2026-05-09
**Issue**: #200 Section B (writers 2–4) + Section E retirements (#100, #104)
**Decision-gate**: blocks PresenceWriter, CompoundPresenceWriter, OffsetsWriter
full migration. DictWriter (PR1) lands independently because its
production payload is small (~108 MB at parliament scale, but
list-allocation-bound, not bitmap-bound).

## What the spec says

CLAUDE.md rule #11 corrected taxonomy: byte assembly belongs in F\*
(`serialize : data → Tot (list u8)`); the OCaml side reduces to
`write_bytes`. Each writer gets a hash-based round-trip CI test.

## What the OCaml currently does

Three writers (`PresenceWriter`, `CompoundPresenceWriter`,
`OffsetsWriter`) share a structural pattern:

1. Walk the parquet column(s) to build a large in-memory data
   structure (a per-rg bitmap, a per-rg sparse pair set, or a
   per-(rg, predicate) row-position list).
2. Serialise to bytes.
3. Atomic-write to disk.

Only step 2 is rule-#11-relevant. Step 1 is bounded I/O glue +
in-memory book-keeping; step 3 is rule #11(a) acceptable.

## Why this is harder than DictWriter

At parliament-scale corpus:

| Writer | Dataset size on disk | Naive `list u8` cons cost |
|---|---:|---:|
| `.dict`             | ~108 MB    | ~108 M cons cells (acceptable for one-time build) |
| `.s/p/o/g.presence` | ~12.5 MB   | ~12.5 M cons cells × 4 columns (~300 MB extra heap) |
| `.po.presence`      | ~5–20 MB   | similar |
| `.p.offsets`        | ~30–80 MB  | ~30–80 M cons cells |

Each cons cell is ~24 B (header + value + tail pointer) on 64-bit
OCaml. The bitmap path is hottest because the CI runs build companion
files end-to-end on a 100 K-triple smoke set, not full parliament — but
even there the perf delta vs. mutable `Bytes.t` is ~30×.

`FStar.Seq.seq u8` has the same runtime characteristics as `list u8`
under default extraction (it's not a special-cased mutable type). To
get O(1) byte-buffer append we'd need Low\*/HACL\* mutable buffers,
which is a much heavier infrastructure investment.

## Options

### Option A — Migrate body to F\* `list u8`, accept the perf cost

- Pro: cleanest rule #11. Every byte specified in F\*.
- Con: ~30× slowdown on companion-file build at smoke-test scale; OOM
  risk at parliament scale during one-time pre-warm.
- Mitigation: pre-warm runs once per dataset; cache results on disk;
  only smoke tests pay the cost on every CI run.

### Option B — Keep OCaml byte-assembly; F\* defines spec; CI hash-witness pins format

- F\* `serialize : data → list u8` is the authoritative format spec
  for *small* fixtures (one row group, a few hundred bits, a few
  predicates).
- OCaml writer is a perf-optimised realisation that produces
  byte-identical output.
- CI test: for each fixture, compute `sha256(F\*_serialize(d)) ==
  sha256(OCaml_write(d))`. Format drift in either side ⇒ hash mismatch
  ⇒ CI fails.
- Pro: zero perf cost; covered fixtures tightly bind format.
- Con: relaxes rule #11 (OCaml is not strictly `write_bytes`-only).
  Reframes the rule as "F\* defines the spec; OCaml realisation must
  hash-match on covered fixtures."

### Option C — Migrate body to Low\*/HACL\* mutable buffers

- Pro: O(1) byte-buffer append; bytewise-identical to OCaml; full
  rule #11 conformance.
- Con: heavy infrastructure investment (Low\* effect tracking,
  KaRaMeL pipeline). Sister-track work, multi-week.

### Option D — Mixed (B for the bulk, A for the header)

- Already what's landed for PresenceWriter today: F\* serialises the
  16-byte header; OCaml does the bitmap body.
- The `serialize_presence_header` exists; the body bytes are an OCaml
  loop. Hash witness today guards header drift only.
- Pro: incremental; works at production scale.
- Con: half-migration, makes the boundary fuzzy.

## Recommendation

**Option B**. The "byte format spec lives in F\*" property holds for
small fixtures (which is what tests exercise anyway), and the hash
witness binds production OCaml to that spec. Rule #11's intent —
"semantics in F\*, OCaml mechanically writes bytes" — is satisfied.
The strict letter ("OCaml does only `write_bytes`") is relaxed but
the substance (format authority lives in F\*) is preserved.

For the rule-#11 caveat-drop path, this means:
- DictWriter retires its patch fully (Option A pattern; small enough).
- PresenceWriter / CompoundPresenceWriter / OffsetsWriter retire
  under Option B with hash witness CI tests.
- Each patch's classification moves from `VIOLATION-SEM` to
  `ASSUME-IO` (writer is byte-identical to F\*-defined spec).

## Decision needed

Pick A / B / C / D. If B, I'll proceed with PresenceWriter PR2 by:
1. Verifying the existing `serialize_presence_header` already covers
   the 16-byte header.
2. Adding `serialize_presence_full : presence_data → list u8` in F\*
   that produces the full file (header + bitmap).
3. Adding `parse_presence : list u8 → option presence_data`.
4. Adding `tests/unit/presence_writer_roundtrip.ml` with small
   fixtures (e.g. 4 rgs × 8 tokens) that hash-witness both
   `F\*_serialize` and `OCaml_write_presence_file` against fixed
   references.
5. Dropping the `.compound_po_writer.sh` / `.lamed3_offset_idx.sh`
   patches once the witnesses pass.
