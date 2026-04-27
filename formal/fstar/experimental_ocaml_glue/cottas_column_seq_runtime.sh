#!/bin/bash
# RDF.CottasStore.ColumnSeq runtime realisation — Phase 2.5a (issue #118).
#
# Realises the four `assume val` declarations in
# RDF.CottasStore.ColumnSeq.fst:
#
#   - `cottas_column` (abstract type)         -> alias for string option array
#   - `cottas_column_length`                  -> Array.length
#   - `cottas_column_get`                     -> Array.unsafe_get
#   - `probe_parquet_column_decode_in_row_group_seq`
#                                             -> calls existing list-shape
#                                                Parquet_Footer decoder, then
#                                                Array.of_list
#
# Rule #11(c) compliant: thin glue, no semantic decisions. The F*
# spec layer reasons about lengths and indices; the OCaml realisation
# is mechanical type-coercion.
#
# This patch does NOT modify any existing function. Phase 2.5b will
# refactor hot-path functions (filter_zipped_rows etc.) to consume
# the new shape.

set -euo pipefail

OUTDIR="$1"

# The patch operates on the extracted ColumnSeq module.
ML="$OUTDIR/RDF_CottasStore_ColumnSeq.ml"

if [ ! -f "$ML" ]; then
  echo "  [column-seq-runtime] WARN: $ML not found; skipping"
  echo "         (F* extract may not have produced RDF.CottasStore.ColumnSeq yet)"
  exit 0
fi

if grep -q '__COLUMN_SEQ_RUNTIME_APPLIED__' "$ML"; then
  echo "  [column-seq-runtime] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# 1. Replace the abstract type stub with a concrete OCaml alias.
#    F* extracts `assume new type cottas_column : Type0` as roughly:
#      type cottas_column
#    (empty type body). We replace with:
#      type cottas_column = string FStar_Pervasives_Native.option array
# ----------------------------------------------------------------------

# Possible extracted forms (F* may emit any of these depending on
# version): try each.
abstract_type_candidates = [
    "type cottas_column\n",
    "type cottas_column = unit\n",
    "type cottas_column = Prims.unit\n",
]
type_replaced = False
new_type = "type cottas_column = string FStar_Pervasives_Native.option array (* __COLUMN_SEQ_RUNTIME_APPLIED__ *)\n"
for cand in abstract_type_candidates:
    if cand in content:
        content = content.replace(cand, new_type, 1)
        type_replaced = True
        sys.stderr.write(f"  [column-seq-runtime] replaced abstract type ({cand.strip()!r}) with array alias\n")
        break

if not type_replaced:
    sys.stderr.write("  [column-seq-runtime] WARN: cottas_column abstract-type stub not found; module may already define it differently\n")

# ----------------------------------------------------------------------
# 2. Replace the `cottas_column_length` failwith stub with Array.length.
# ----------------------------------------------------------------------

len_old_candidates = [
    # F* 2025.x extracts assume_vals as direct lets:
    'let cottas_column_length (uu___ : cottas_column) : Prims.nat=\n  failwith\n    "Not yet implemented: RDF.CottasStore.ColumnSeq.cottas_column_length"\n',
    # Older shapes (kept for compat):
    'let cottas_column_length : cottas_column -> Prims.nat =\n  fun _ -> failwith "Not yet implemented:cottas_column_length"\n',
    'let cottas_column_length :\n  cottas_column -> Prims.nat =\n  fun uu___ -> failwith "Not yet implemented:RDF.CottasStore.ColumnSeq.cottas_column_length"\n',
    'let (cottas_column_length : cottas_column -> Prims.nat) =\n  fun uu___ -> failwith "Not yet implemented:cottas_column_length"\n',
]
len_new = '''let cottas_column_length (c : cottas_column) : Prims.nat =
  Z.of_int (Array.length c)
'''
len_replaced = False
for cand in len_old_candidates:
    if cand in content:
        content = content.replace(cand, len_new, 1)
        len_replaced = True
        sys.stderr.write("  [column-seq-runtime] replaced cottas_column_length stub with Array.length\n")
        break

if not len_replaced:
    sys.stderr.write("  [column-seq-runtime] WARN: cottas_column_length stub not found in any of the expected shapes\n")

# ----------------------------------------------------------------------
# 3. Replace the `cottas_column_get` failwith stub with array indexing.
# ----------------------------------------------------------------------

get_old_candidates = [
    # F* 2025.x: direct let.
    'let cottas_column_get (c : cottas_column) (i : Prims.nat) :\n  Prims.string FStar_Pervasives_Native.option=\n  failwith "Not yet implemented: RDF.CottasStore.ColumnSeq.cottas_column_get"\n',
    # Older shapes:
    'let cottas_column_get : cottas_column -> Prims.nat -> string FStar_Pervasives_Native.option =\n  fun _ -> fun _ -> failwith "Not yet implemented:cottas_column_get"\n',
    'let cottas_column_get :\n  cottas_column ->\n    Prims.nat -> string FStar_Pervasives_Native.option\n  =\n  fun uu___ ->\n    fun uu___1 ->\n      failwith "Not yet implemented:RDF.CottasStore.ColumnSeq.cottas_column_get"\n',
    'let (cottas_column_get :\n  cottas_column ->\n    Prims.nat -> string FStar_Pervasives_Native.option)\n  =\n  fun uu___ ->\n    fun uu___1 ->\n      failwith "Not yet implemented:cottas_column_get"\n',
]
get_new = '''let cottas_column_get (c : cottas_column) (i : Prims.nat)
  : string FStar_Pervasives_Native.option =
  Array.unsafe_get c (Z.to_int i)
'''
get_replaced = False
for cand in get_old_candidates:
    if cand in content:
        content = content.replace(cand, get_new, 1)
        get_replaced = True
        sys.stderr.write("  [column-seq-runtime] replaced cottas_column_get stub with Array.unsafe_get\n")
        break

if not get_replaced:
    sys.stderr.write("  [column-seq-runtime] WARN: cottas_column_get stub not found in any expected shape\n")

# ----------------------------------------------------------------------
# 4. Replace the parquet decoder stub with one that calls the existing
#    list-shape decoder + Array.of_list.
# ----------------------------------------------------------------------

decode_old_candidates = [
    # F* 2025.x: direct let.
    'let probe_parquet_column_decode_in_row_group_seq (path : Prims.string)\n  (rg_index : Prims.nat) (col_index : Prims.nat) :\n  cottas_column FStar_Pervasives_Native.option=\n  failwith\n    "Not yet implemented: RDF.CottasStore.ColumnSeq.probe_parquet_column_decode_in_row_group_seq"\n',
    # Older shapes:
    'let probe_parquet_column_decode_in_row_group_seq :\n  Prims.string ->\n    Prims.nat ->\n      Prims.nat -> cottas_column FStar_Pervasives_Native.option\n  =\n  fun uu___ ->\n    fun uu___1 ->\n      fun uu___2 ->\n        failwith\n          "Not yet implemented:RDF.CottasStore.ColumnSeq.probe_parquet_column_decode_in_row_group_seq"\n',
    'let (probe_parquet_column_decode_in_row_group_seq :\n  Prims.string ->\n    Prims.nat ->\n      Prims.nat -> cottas_column FStar_Pervasives_Native.option)\n  =\n  fun uu___ ->\n    fun uu___1 ->\n      fun uu___2 ->\n        failwith\n          "Not yet implemented:probe_parquet_column_decode_in_row_group_seq"\n',
    'let probe_parquet_column_decode_in_row_group_seq : Prims.string -> Prims.nat -> Prims.nat -> cottas_column FStar_Pervasives_Native.option =\n  fun _ -> fun _ -> fun _ -> failwith "Not yet implemented:probe_parquet_column_decode_in_row_group_seq"\n',
]
decode_new = '''let probe_parquet_column_decode_in_row_group_seq
    (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  : cottas_column FStar_Pervasives_Native.option =
  match Parquet_Footer.probe_parquet_column_decode_in_row_group
          path rg_index col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some lst ->
    FStar_Pervasives_Native.Some (Array.of_list lst)
'''
decode_replaced = False
for cand in decode_old_candidates:
    if cand in content:
        content = content.replace(cand, decode_new, 1)
        decode_replaced = True
        sys.stderr.write("  [column-seq-runtime] replaced probe_parquet_column_decode_in_row_group_seq stub with Array.of_list realisation\n")
        break

if not decode_replaced:
    sys.stderr.write("  [column-seq-runtime] WARN: probe_parquet_column_decode_in_row_group_seq stub not found in any expected shape\n")

n_applied = sum([type_replaced, len_replaced, get_replaced, decode_replaced])
sys.stderr.write(f"  [column-seq-runtime] applied {n_applied}/4 substitutions\n")

if n_applied < 4:
    # Don't fatal-out — the missing pieces will trigger failwith at runtime
    # and surface clearly. Useful for iterating on the patch.
    sys.stderr.write("  [column-seq-runtime] some substitutions missed; expect runtime failwith if those code paths run.\n")

path.write_text(content)
PYEOF

echo "  Cottas column-seq runtime realisation applied."
