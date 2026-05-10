open Prims
let rec list_is_prefix : 'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun prefix lst ->
    match (prefix, lst) with
    | ([], uu___) -> true
    | (uu___, []) -> false
    | (x::xs, y::ys) -> (x = y) && (list_is_prefix xs ys)
let rec list_contains_sublist :
  'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun needle haystack ->
    match haystack with
    | [] -> Prims.uu___is_Nil needle
    | uu___::rest ->
        (list_is_prefix needle haystack) ||
          (list_contains_sublist needle rest)
let string_contains (s : Prims.string) (sub : Prims.string) : Prims.bool=
  list_contains_sublist (FStar_String.list_of_string sub)
    (FStar_String.list_of_string s)
let string_to_iri (s : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let rec find_scheme_end (cs : FStar_Char.char Prims.list) (pos : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | c1::c2::c3::rest ->
      if
        ((c1 = (FStar_Char.char_of_int (Prims.of_int (58)))) &&
           (c2 = (FStar_Char.char_of_int (Prims.of_int (47)))))
          && (c3 = (FStar_Char.char_of_int (Prims.of_int (47))))
      then FStar_Pervasives_Native.Some (pos + (Prims.of_int (3)))
      else find_scheme_end (c2 :: c3 :: rest) (pos + Prims.int_one)
  | uu___ -> FStar_Pervasives_Native.None
let rec find_slash_from (cs : FStar_Char.char Prims.list) (pos : Prims.nat)
  (cur : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (cur >= pos) && (c = (FStar_Char.char_of_int (Prims.of_int (47))))
      then FStar_Pervasives_Native.Some cur
      else find_slash_from rest pos (cur + Prims.int_one)
let rec find_last_slash (cs : FStar_Char.char Prims.list) (cur : Prims.nat)
  (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if c = (FStar_Char.char_of_int (Prims.of_int (47)))
      then
        find_last_slash rest (cur + Prims.int_one)
          (FStar_Pervasives_Native.Some cur)
      else find_last_slash rest (cur + Prims.int_one) last
let rec take_chars (n : Prims.nat) (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::rest -> c :: (take_chars (n - Prims.int_one) rest))
let rec remove_fragment (cs : FStar_Char.char Prims.list)
  (last_hash : Prims.nat FStar_Pervasives_Native.option) (cur : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last_hash
  | c::rest ->
      if c = (FStar_Char.char_of_int (Prims.of_int (35)))
      then
        remove_fragment rest (FStar_Pervasives_Native.Some cur)
          (cur + Prims.int_one)
      else remove_fragment rest last_hash (cur + Prims.int_one)
let resolve_iri (base : RDF_Graph_Executable.wf_iri)
  (relative : Prims.string) : RDF_Graph_Executable.wf_iri=
  let base_chars = FStar_String.list_of_string base in
  let rel_chars = FStar_String.list_of_string relative in
  if string_contains relative "://"
  then base
  else
    if (FStar_String.strlen relative) = Prims.int_zero
    then base
    else
      (let result_chars =
         let first_char = FStar_List_Tot_Base.hd rel_chars in
         if first_char = (FStar_Char.char_of_int (Prims.of_int (35)))
         then
           match remove_fragment base_chars FStar_Pervasives_Native.None
                   Prims.int_zero
           with
           | FStar_Pervasives_Native.Some hash_pos ->
               RDF_List_Helpers.append_tr (take_chars hash_pos base_chars)
                 rel_chars
           | FStar_Pervasives_Native.None ->
               RDF_List_Helpers.append_tr base_chars rel_chars
         else
           if first_char = (FStar_Char.char_of_int (Prims.of_int (47)))
           then
             (match find_scheme_end base_chars Prims.int_zero with
              | FStar_Pervasives_Native.Some after_scheme ->
                  (match find_slash_from base_chars after_scheme
                           Prims.int_zero
                   with
                   | FStar_Pervasives_Native.Some auth_end ->
                       RDF_List_Helpers.append_tr
                         (take_chars auth_end base_chars) rel_chars
                   | FStar_Pervasives_Native.None ->
                       RDF_List_Helpers.append_tr base_chars rel_chars)
              | FStar_Pervasives_Native.None ->
                  RDF_List_Helpers.append_tr base_chars rel_chars)
           else
             (match find_last_slash base_chars Prims.int_zero
                      FStar_Pervasives_Native.None
              with
              | FStar_Pervasives_Native.Some slash_pos ->
                  RDF_List_Helpers.append_tr
                    (take_chars (slash_pos + Prims.int_one) base_chars)
                    rel_chars
              | FStar_Pervasives_Native.None ->
                  RDF_List_Helpers.append_tr base_chars
                    (RDF_List_Helpers.append_tr
                       [FStar_Char.char_of_int (Prims.of_int (47))] rel_chars)) in
       let result = FStar_String.string_of_list result_chars in
       if RDF_Graph_Executable.is_iri result then result else base)
let resolve_query_iri
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (rel : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match base with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (resolve_iri b rel)
  | FStar_Pervasives_Native.None -> string_to_iri rel
