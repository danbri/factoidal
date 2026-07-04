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
let jir_byte_at (input : Prims.string) (pos : Prims.nat) : Prims.int=
  if pos < (Parser_FastString.fs_byte_length input)
  then Parser_FastString.fs_byte_at input pos
  else (Prims.of_int (-1))
let jir_b_colon : Prims.int= (Prims.of_int (0x3A))
let jir_b_slash : Prims.int= (Prims.of_int (0x2F))
let jir_b_question : Prims.int= (Prims.of_int (0x3F))
let jir_b_hash : Prims.int= (Prims.of_int (0x23))
let jir_drop (s : Prims.string) (k : Prims.nat) : Prims.string=
  let n = Parser_FastString.fs_byte_length s in
  if k >= n then "" else Parser_FastString.fs_byte_sub s k (n - k)
let jir_starts_with (s : Prims.string) (prefix : Prims.string) : Prims.bool=
  let pl = Parser_FastString.fs_byte_length prefix in
  ((Parser_FastString.fs_byte_length s) >= pl) &&
    ((Parser_FastString.fs_byte_sub s Prims.int_zero pl) = prefix)
let rec jir_find_byte (s : Prims.string) (b : Prims.int) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then FStar_Pervasives_Native.None
     else
       if (jir_byte_at s pos) = b
       then FStar_Pervasives_Native.Some pos
       else jir_find_byte s b (pos + Prims.int_one) (fuel - Prims.int_one))
let jir_find (s : Prims.string) (b : Prims.int) (from : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  jir_find_byte s b from
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let rec jir_find_last_byte (s : Prims.string) (b : Prims.int)
  (pos : Prims.nat) (best : Prims.nat FStar_Pervasives_Native.option)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then best
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then best
     else
       (let best' =
          if (jir_byte_at s pos) = b
          then FStar_Pervasives_Native.Some pos
          else best in
        jir_find_last_byte s b (pos + Prims.int_one) best'
          (fuel - Prims.int_one)))
let jir_find_last (s : Prims.string) (b : Prims.int) :
  Prims.nat FStar_Pervasives_Native.option=
  jir_find_last_byte s b Prims.int_zero FStar_Pervasives_Native.None
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let jir_is_alpha (b : Prims.int) : Prims.bool=
  ((b >= (Prims.of_int (0x41))) && (b <= (Prims.of_int (0x5A)))) ||
    ((b >= (Prims.of_int (0x61))) && (b <= (Prims.of_int (0x7A))))
let jir_is_digit (b : Prims.int) : Prims.bool=
  (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
let jir_is_scheme_byte (b : Prims.int) : Prims.bool=
  ((((jir_is_alpha b) || (jir_is_digit b)) || (b = (Prims.of_int (0x2B)))) ||
     (b = (Prims.of_int (0x2D))))
    || (b = (Prims.of_int (0x2E)))
let rec jir_scheme_scan (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then FStar_Pervasives_Native.None
     else
       (let b = jir_byte_at s pos in
        if b = jir_b_colon
        then FStar_Pervasives_Native.Some pos
        else
          if jir_is_scheme_byte b
          then jir_scheme_scan s (pos + Prims.int_one) (fuel - Prims.int_one)
          else FStar_Pervasives_Native.None))
let jir_find_scheme_colon (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  let n = Parser_FastString.fs_byte_length s in
  if n = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if Prims.op_Negation (jir_is_alpha (jir_byte_at s Prims.int_zero))
    then FStar_Pervasives_Native.None
    else jir_scheme_scan s Prims.int_zero (n + Prims.int_one)
let jir_split_ref (s : Prims.string) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  let n0 = Parser_FastString.fs_byte_length s in
  let uu___ =
    match jir_find s jir_b_hash Prims.int_zero with
    | FStar_Pervasives_Native.Some i ->
        ((Parser_FastString.fs_byte_sub s Prims.int_zero i),
          (FStar_Pervasives_Native.Some
             (Parser_FastString.fs_byte_sub s (i + Prims.int_one)
                ((n0 - i) - Prims.int_one))))
    | FStar_Pervasives_Native.None -> (s, FStar_Pervasives_Native.None) in
  match uu___ with
  | (s1, frag) ->
      let n1 = Parser_FastString.fs_byte_length s1 in
      let uu___1 =
        match jir_find s1 jir_b_question Prims.int_zero with
        | FStar_Pervasives_Native.Some i ->
            ((Parser_FastString.fs_byte_sub s1 Prims.int_zero i),
              (FStar_Pervasives_Native.Some
                 (Parser_FastString.fs_byte_sub s1 (i + Prims.int_one)
                    ((n1 - i) - Prims.int_one))))
        | FStar_Pervasives_Native.None -> (s1, FStar_Pervasives_Native.None) in
      (match uu___1 with
       | (s2, query) ->
           let uu___2 =
             match jir_find_scheme_colon s2 with
             | FStar_Pervasives_Native.Some i ->
                 ((FStar_Pervasives_Native.Some
                     (Parser_FastString.fs_byte_sub s2 Prims.int_zero i)),
                   (jir_drop s2 (i + Prims.int_one)))
             | FStar_Pervasives_Native.None ->
                 (FStar_Pervasives_Native.None, s2) in
           (match uu___2 with
            | (scheme, rest) ->
                let nr = Parser_FastString.fs_byte_length rest in
                let uu___3 =
                  if
                    ((nr >= (Prims.of_int (2))) &&
                       ((jir_byte_at rest Prims.int_zero) = jir_b_slash))
                      && ((jir_byte_at rest Prims.int_one) = jir_b_slash)
                  then
                    let rest2 = jir_drop rest (Prims.of_int (2)) in
                    match jir_find rest2 jir_b_slash Prims.int_zero with
                    | FStar_Pervasives_Native.Some i ->
                        ((FStar_Pervasives_Native.Some
                            (Parser_FastString.fs_byte_sub rest2
                               Prims.int_zero i)),
                          (Parser_FastString.fs_byte_sub rest2 i
                             ((Parser_FastString.fs_byte_length rest2) - i)))
                    | FStar_Pervasives_Native.None ->
                        ((FStar_Pervasives_Native.Some rest2), "")
                  else (FStar_Pervasives_Native.None, rest) in
                (match uu___3 with
                 | (authority, path) ->
                     (scheme, authority, path, query, frag))))
let jir_remove_last_segment (output : Prims.string) : Prims.string=
  match jir_find_last output jir_b_slash with
  | FStar_Pervasives_Native.Some i ->
      Parser_FastString.fs_byte_sub output Prims.int_zero i
  | FStar_Pervasives_Native.None -> ""
let jir_first_path_segment (input : Prims.string) :
  (Prims.string * Prims.string)=
  let n = Parser_FastString.fs_byte_length input in
  let start =
    if
      (n > Prims.int_zero) &&
        ((jir_byte_at input Prims.int_zero) = jir_b_slash)
    then Prims.int_one
    else Prims.int_zero in
  match jir_find input jir_b_slash start with
  | FStar_Pervasives_Native.Some i ->
      ((Parser_FastString.fs_byte_sub input Prims.int_zero i),
        (Parser_FastString.fs_byte_sub input i (n - i)))
  | FStar_Pervasives_Native.None -> (input, "")
let rec jir_remove_dot_segments_loop (input : Prims.string)
  (output : Prims.string) (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then output
  else
    if (Parser_FastString.fs_byte_length input) = Prims.int_zero
    then output
    else
      if jir_starts_with input "../"
      then
        jir_remove_dot_segments_loop (jir_drop input (Prims.of_int (3)))
          output (fuel - Prims.int_one)
      else
        if jir_starts_with input "./"
        then
          jir_remove_dot_segments_loop (jir_drop input (Prims.of_int (2)))
            output (fuel - Prims.int_one)
        else
          if jir_starts_with input "/./"
          then
            jir_remove_dot_segments_loop
              (FStar_String.concat ""
                 ["/"; jir_drop input (Prims.of_int (3))]) output
              (fuel - Prims.int_one)
          else
            if input = "/."
            then
              jir_remove_dot_segments_loop "/" output (fuel - Prims.int_one)
            else
              if jir_starts_with input "/../"
              then
                jir_remove_dot_segments_loop
                  (FStar_String.concat ""
                     ["/"; jir_drop input (Prims.of_int (4))])
                  (jir_remove_last_segment output) (fuel - Prims.int_one)
              else
                if input = "/.."
                then
                  jir_remove_dot_segments_loop "/"
                    (jir_remove_last_segment output) (fuel - Prims.int_one)
                else
                  if (input = ".") || (input = "..")
                  then
                    jir_remove_dot_segments_loop "" output
                      (fuel - Prims.int_one)
                  else
                    (let uu___9 = jir_first_path_segment input in
                     match uu___9 with
                     | (seg, rest) ->
                         jir_remove_dot_segments_loop rest
                           (FStar_String.concat "" [output; seg])
                           (fuel - Prims.int_one))
let jir_remove_dot_segments (path : Prims.string) : Prims.string=
  jir_remove_dot_segments_loop path ""
    ((Parser_FastString.fs_byte_length path) + Prims.int_one)
let jir_merge (base_has_authority : Prims.bool) (base_path : Prims.string)
  (ref_path : Prims.string) : Prims.string=
  if
    base_has_authority &&
      ((Parser_FastString.fs_byte_length base_path) = Prims.int_zero)
  then FStar_String.concat "" ["/"; ref_path]
  else
    (match jir_find_last base_path jir_b_slash with
     | FStar_Pervasives_Native.Some i ->
         FStar_String.concat ""
           [Parser_FastString.fs_byte_sub base_path Prims.int_zero
              (i + Prims.int_one);
           ref_path]
     | FStar_Pervasives_Native.None -> ref_path)
let resolve_iri (base : RDF_Graph_Executable.wf_iri)
  (relative : Prims.string) : RDF_Graph_Executable.wf_iri=
  let uu___ = jir_split_ref base in
  match uu___ with
  | (bscheme, bauth, bpath, bquery, _bfrag) ->
      let uu___1 = jir_split_ref relative in
      (match uu___1 with
       | (rscheme, rauth, rpath, rquery, rfrag) ->
           let uu___2 =
             match rscheme with
             | FStar_Pervasives_Native.Some rs ->
                 ((FStar_Pervasives_Native.Some rs), rauth,
                   (jir_remove_dot_segments rpath), rquery)
             | FStar_Pervasives_Native.None ->
                 (match rauth with
                  | FStar_Pervasives_Native.Some ra ->
                      (bscheme, (FStar_Pervasives_Native.Some ra),
                        (jir_remove_dot_segments rpath), rquery)
                  | FStar_Pervasives_Native.None ->
                      if
                        (Parser_FastString.fs_byte_length rpath) =
                          Prims.int_zero
                      then
                        (bscheme, bauth, bpath,
                          ((match rquery with
                            | FStar_Pervasives_Native.Some uu___3 -> rquery
                            | FStar_Pervasives_Native.None -> bquery)))
                      else
                        (let is_abs =
                           ((Parser_FastString.fs_byte_length rpath) >
                              Prims.int_zero)
                             &&
                             ((jir_byte_at rpath Prims.int_zero) =
                                jir_b_slash) in
                         let merged_path =
                           if is_abs
                           then jir_remove_dot_segments rpath
                           else
                             jir_remove_dot_segments
                               (jir_merge
                                  (FStar_Pervasives_Native.uu___is_Some bauth)
                                  bpath rpath) in
                         (bscheme, bauth, merged_path, rquery))) in
           (match uu___2 with
            | (t_scheme, t_auth, t_path, t_query) ->
                let result =
                  FStar_String.concat ""
                    [(match t_scheme with
                      | FStar_Pervasives_Native.Some sc ->
                          FStar_String.concat "" [sc; ":"]
                      | FStar_Pervasives_Native.None -> "");
                    (match t_auth with
                     | FStar_Pervasives_Native.Some a ->
                         FStar_String.concat "" ["//"; a]
                     | FStar_Pervasives_Native.None -> "");
                    t_path;
                    (match t_query with
                     | FStar_Pervasives_Native.Some q ->
                         FStar_String.concat "" ["?"; q]
                     | FStar_Pervasives_Native.None -> "");
                    (match rfrag with
                     | FStar_Pervasives_Native.Some f ->
                         FStar_String.concat "" ["#"; f]
                     | FStar_Pervasives_Native.None -> "")] in
                if RDF_Graph_Executable.is_iri result then result else base))
let resolve_query_iri
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (rel : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match base with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (resolve_iri b rel)
  | FStar_Pervasives_Native.None -> string_to_iri rel
