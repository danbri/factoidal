#!/bin/bash
# In-memory bytes store, stage 1 (docs/designissues/2026-07-06-inmemory-
# bytes-store.md, §2.1/§3 stage list item 1) — "confirm the seam holds".
#
# `experimental_ocaml_glue/parquet_footer_runtime.sh` already realises
# `parquet_read_tail_hex`/`parquet_read_range_hex` on top of a single
# process-wide, path-keyed byte cache (`__mim2_file_bytes_cache`, the
# "Mim2" cache from issue #100 Phases B+C): the first read for a given
# path slurps the whole file once; every later probe is a `String.sub`
# against the cached string. The design doc's finding: nothing about
# that cache actually requires the key to be a real filesystem path —
# it's an opaque cache key. This patch adds ONE new entry point,
# `register_memory_buffer`, that seeds the SAME cache under a synthetic
# handle with no backing file, so every existing `parquet_read_*` probe
# (and everything in RDF.CottasStore.fst built on top of them) works
# unmodified against bytes that were never written to disk.
#
# Rule #11(a) conformance: this is pure I/O/cache plumbing — a
# `Hashtbl.replace` on the SAME table the existing assume-val
# realisations already populate via `Sys.file_exists`/`open_in_bin`.
# No new decode/query/semantic logic; it does not even touch an F*
# `assume val` signature (no F* source change needed for this stage —
# `register_memory_buffer` is new OCaml-side API surface, the same
# pattern `Cottas_ondisk_runtime`'s helper functions already use for
# functions with no F* declaration of their own).
#
# Must run AFTER parquet_footer_runtime.sh (alphabetical order in this
# directory already guarantees `parquet_footer_runtime.sh` <
# `parquet_footer_zz_register_memory_buffer.sh`), since it depends on
# `__mim2_file_bytes_cache` existing in the extracted file already.
#
# Idempotency: re-running on an already-patched file is a no-op
# (skip-if-marker pattern, same as every sibling patch in this
# directory).

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parquet_Footer.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping in-memory-buffer registration glue" >&2
  exit 0
fi

if grep -q 'let register_memory_buffer' "$FILE"; then
  echo "  In-memory-buffer registration glue already present."
  exit 0
fi

if ! grep -q '__mim2_file_bytes_cache : (string, string) Hashtbl.t' "$FILE"; then
  echo "  Warning: __mim2_file_bytes_cache not found in $FILE;" >&2
  echo "  parquet_footer_runtime.sh must run first (or its shape changed)." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

anchor = "let __mim2_file_bytes_cache : (string, string) Hashtbl.t = Hashtbl.create 7\n"
if anchor not in content:
    raise SystemExit("register_memory_buffer: __mim2_file_bytes_cache anchor not found")

insertion = anchor + '''
(* In-memory bytes store, stage 1 (docs/designissues/2026-07-06-
   inmemory-bytes-store.md). Seed the SAME process-wide cache
   `__mim2_load_file_bytes`/`parquet_read_*` already consult, under a
   synthetic handle that names no real file. Every later
   `parquet_read_tail_hex`/`parquet_read_range_hex` call for `handle`
   is served straight out of this cache -- the `Sys.file_exists`
   fallback in `__mim2_load_file_bytes` is never reached for a handle
   registered here, because the cache lookup happens first.

   Last-registration-wins (`Hashtbl.replace`, not `Hashtbl.add`):
   re-registering the same handle with new bytes is well-defined and
   intentional (lets a caller rebind a synthetic handle to fresh bytes
   without restarting the process), matching how a real file's cache
   entry would need an explicit invalidation to pick up an on-disk
   change too -- this backend is no less consistent than the file
   backend it shares a cache with. *)
let register_memory_buffer (handle : Prims.string) (raw_bytes : Prims.string) : unit =
  Hashtbl.replace __mim2_file_bytes_cache handle raw_bytes
'''

content = content.replace(anchor, insertion, 1)
path.write_text(content)
sys.stderr.write("  [parquet_footer_zz_register_memory_buffer] register_memory_buffer added\n")
PYEOF
