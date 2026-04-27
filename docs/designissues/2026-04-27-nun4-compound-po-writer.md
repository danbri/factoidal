# Compound `(p, o)` presence-bitmap WRITER — implementation notes

**Date:** 2026-04-27
**Issue:** #104 (writer half; reader follows in a separate commit)
**Handle:** nun4 (writer-only follow-up to design doc
`2026-04-26-nun4-compound-po-bitmap-design.md`)
**Patch file:** `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh`
**Status:** WRITER ONLY. No reader code; query results unchanged.

## What this delivers

A new sibling companion file `<cottas>.po.presence` produced at boot by
the `Cottas_compound_po_writer` OCaml module, hooked into
`Cottas_companion_boot.prewarm_via_companions` immediately after the
existing `lamed3` `.p.offsets` writer.

The reader path is **deliberately deferred** to a future patch. This run
just ensures the file gets built (or rebuilt on dimension mismatch) and
sits on disk waiting for consumers.

## File format — `<cottas>.po.presence`

Little-endian throughout.

```
Header (20 bytes):
  [ magic   : u32  'COPO' = 0x4f504f43 (LE)         ]
  [ version : u32  layout version, currently 1      ]
  [ num_rgs : u32                                    ]
  [ pred_dict_size : u32  cross-check vs .p.dict    ]
  [ obj_dict_size  : u32  cross-check vs .o.dict    ]

Index:
  [ rg_offsets : u64[num_rgs + 1]
                  byte offsets into the file where each rg's pair-list
                  begins; the trailing entry is the end-of-file sentinel. ]

Pair data (per rg, sorted lex (p_id, o_id)):
  [ pairs : u64[]
            per pair: bytes 0..3 = o_id (u32 LE)
                      bytes 4..7 = p_id (u32 LE)
            so the whole u64-LE = (p_id << 32) | o_id, and ascending
            u64 sort == lex (p_id, o_id) — perfect for binary search
            on a packed mmap'd region. ]
```

Total header + index = 20 + 8*(num_rgs + 1) bytes (= 236 bytes for
parliament's 26 rgs). Pair-data follows.

### Why u64-per-pair (and not u32 with a 24/24 bit-split)?

The design doc considered both. Parliament's 232 preds × 956 K objs
fits a 24/24 split, but u64-per-pair removes the dict-size question
entirely (preds and objs each fit in u32, no bit-tetris). Cost: 2×
the pair-data size vs u32 packing. For parliament: ≈ 3.14 M pair
entries worst case (every quad distinct (p, o)) × 8 = ≈ 25 MB.
In practice many quads share a `(p, o)` so the file is smaller.

## Token-id contract

The `(p_id, o_id)` written into the file live in **the same id-space as
Vav3's per-column `.p.dict` / `.o.dict` token ids** — i.e. dict-token
position (dictionary tokens are sorted lex ascending; id = lex position).

The writer constructs both `pred_tok_to_id` and `obj_tok_to_id` Hashtbls
by walking the `.p.dict` and `.o.dict` headers via the F\*-extracted
`RDF_CottasStore_OnDiskIndex.dict_decode_token`. This is the **same id
space** that `RDF_CottasStore_PresenceBitmap.rg_could_contain_token`
consumes, so a future reader patch composes cleanly with Psi3's
per-column gate.

The writer does NOT introduce a new tokenisation. No new `assume val`
declarations were added.

## Boot integration

The writer is invoked from
`Cottas_companion_boot.prewarm_via_companions`, immediately AFTER the
existing `lamed3` `Cottas_offset_idx.ensure_offsets_built` hook. The
insertion is wrapped in a try/with — if the writer raises (e.g. dict
header missing), it logs `[compound-po-WARN]` and continues; nothing
else this run depends on the file.

Source location after the patch applies:
`formal/fstar/ocaml-output/RDF_CottasStore.ml` inside
`module Cottas_companion_boot = struct`, in the `prewarm_via_companions`
let-binding (4 lines added after the lamed3 try/with block). See the
`new_hook` block in the patch script for the exact diff.

## Idempotency

`ensure_compound_po_built`:

1. Reads `.p.dict` / `.o.dict` headers to learn `pred_dict_size` and
   `obj_dict_size`.
2. Reads `.p.presence` header (or falls back to parquet rg-count probe)
   to learn `num_rgs`.
3. If the existing `<cottas>.po.presence` file is present AND its
   header's (magic, version, num_rgs, pred_dict_size, obj_dict_size)
   match what we just learned, **skip** rebuild.
4. Otherwise, build the file: per rg, decode the predicate column
   (`col=1`) and object column (`col=2`), walk in lockstep, encode
   `(p_id, o_id)` via the dict tok-to-id maps, dedup via Hashtbl,
   sort, emit.

Stale-file detection: a corpus reload that changes either dict size
will flip the header check and trigger a rebuild.

## Rule compliance

- **Rule #11(b):** companion-file writer in OCaml glue is allowed when
  the reader path lives in F\*. Reader is deferred to a future patch
  (planned F\* module `RDF.CottasStore.CompoundPresenceBitmap.fst`),
  so the glue here is exclusively pure I/O — no decisions about what
  to compute, only how to read/write bytes.
- **Rule #15:** no RDF/SPARQL semantic logic in the patch. The writer
  only enumerates `(p_id, o_id)` pairs that already exist in the
  per-column dict / parquet column data; no new semantics.
- **Rule #13:** the patch never edits `formal/fstar/ocaml-output/*.ml`
  directly. It is applied post-extraction by `ocaml-patches.sh`.
- **No `assume val` added.** The writer reuses existing extracted
  primitives only.

## Open questions for human review

1. **Worst-case file size on a future dense corpus.** Section 6a of the
   design doc reserves a per-rg encoding tag for switching to a flat
   bitmap when sparse-roaring degenerates. This patch does NOT
   implement that switch — every rg is encoded sparse. Recommend
   landing the encoding-tag follow-up only after we observe a corpus
   that triggers it. (Today: parliament-class.)
2. **Producer-side proof obligation `compound_built_correctly`.** The
   informal argument is "for every rg, decode the predicate + object
   columns row-by-row; emit the (p_id, o_id) pair iff both decode to
   non-null tokens that are in the corresponding dicts." A debug
   self-check at first open ("decode 100 random rows, verify their
   (p, o) is in the bitmap") is cheap and worth adding when the
   reader lands.
3. **Boot cost on parliament.** Two column decodes per rg × 26 rgs
   ≈ same per-rg cost as Vav3's existing column walk. The writer
   piggybacks on the existing decode caches (no new mmaps). Expect
   ~10-30s additional boot on parliament; one-time, persists forever.
   Not measured this run because reader is absent (no perf comparison
   to make yet).

## Future work (not this patch)

- F\* module `RDF.CottasStore.CompoundPresenceBitmap.fst` per design
  doc Section 2 (open / read-only API + soundness lemma).
- Reader redirect at `mem5_estimate_fast_inner` and
  `search_fast_inner` per design doc Section 4.
- Eventual writer migration F\*-side (Section 3 producer-proof gap).
