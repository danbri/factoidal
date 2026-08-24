open Prims
type cottas_column = unit
let cottas_column_length (uu___ : cottas_column) : Prims.nat=
  failwith
    "Not yet implemented: RDF.CottasStore.ColumnSeq.cottas_column_length"
let cottas_column_get (c : cottas_column) (i : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  failwith "Not yet implemented: RDF.CottasStore.ColumnSeq.cottas_column_get"
let probe_parquet_column_decode_in_row_group_seq (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  cottas_column FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.ColumnSeq.probe_parquet_column_decode_in_row_group_seq"
let probe_parquet_column_decode_in_row_group_seq_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  cottas_column FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.ColumnSeq.probe_parquet_column_decode_in_row_group_seq_from_table"
let rec column_to_list_acc (c : cottas_column) (i : Prims.nat)
  (acc : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  if i = Prims.int_zero
  then acc
  else
    (let i' = i - Prims.int_one in
     if i' < (cottas_column_length c)
     then
       let cell = cottas_column_get c i' in
       column_to_list_acc c i' (cell :: acc)
     else column_to_list_acc c i' acc)
let column_to_list (c : cottas_column) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  column_to_list_acc c (cottas_column_length c) []
type parquet_decoded_cells_pred_t = unit
