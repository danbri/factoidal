open Prims
let rec encode_aux (xs : Spec.u16_val Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | x::[] -> Prims.string_of_int x
  | x::rest ->
      Prims.strcat (Prims.string_of_int x)
        (Prims.strcat "," (encode_aux rest))
let encode (c : Container_Array.array_container) : Prims.string= encode_aux c
let split_commas (s : Prims.string) : Prims.string Prims.list=
  FStar_String.split [44] s
let parse_u16 (s : Prims.string) :
  Spec.u16_val FStar_Pervasives_Native.option=
  match FStar_Parse.int_of_string s with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some n ->
      if (n >= Prims.int_zero) && (n < Spec.pow16)
      then FStar_Pervasives_Native.Some n
      else FStar_Pervasives_Native.None
let rec parse_and_insert (xs : Prims.string Prims.list)
  (acc : Container_Array.array_container) :
  Container_Array.array_container FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.Some acc
  | s::rest ->
      (match parse_u16 s with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some v ->
           if
             ((FStar_List_Tot_Base.length acc) < Spec.array_max_cardinality)
               || (Container_Array.array_contains acc v)
           then
             let acc' = Container_Array.array_insert acc v in
             parse_and_insert rest acc'
           else FStar_Pervasives_Native.None)
let decode (s : Prims.string) :
  Container_Array.array_container FStar_Pervasives_Native.option=
  if s = ""
  then FStar_Pervasives_Native.Some Container_Array.array_empty
  else parse_and_insert (split_commas s) Container_Array.array_empty
let write_to_file (path : Prims.string) (c : Container_Array.array_container)
  : unit=
  let fd = FStar_IO.open_write_file path in
  FStar_IO.write_string fd (encode c); FStar_IO.close_write_file fd
let read_from_file (path : Prims.string) :
  Container_Array.array_container FStar_Pervasives_Native.option=
  let fd = FStar_IO.open_read_file path in
  let line =
    try (fun uu___ -> match () with | () -> FStar_IO.read_line fd) ()
    with | FStar_IO.EOF -> "" | uu___1 -> "" in
  FStar_IO.close_read_file fd; decode line
let example : Container_Array.array_container=
  [(Prims.of_int (7));
  (Prims.of_int (42));
  (Prims.of_int (50));
  (Prims.of_int (100))]
