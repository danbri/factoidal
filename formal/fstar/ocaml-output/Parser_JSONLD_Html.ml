open Prims
let lc_byte (b : Prims.nat) : Prims.nat=
  if (b >= (Prims.of_int (0x41))) && (b <= (Prims.of_int (0x5A)))
  then b + (Prims.of_int (0x20))
  else b
let sat_sub (a : Prims.nat) (b : Prims.nat) : Prims.nat=
  if a >= b then a - b else Prims.int_zero
let rec ci_match_at (pat : Prims.string) (plen : Prims.nat)
  (html : Prims.string) (hlen : Prims.nat) (pos : Prims.nat) (i : Prims.nat)
  : Prims.bool=
  if i >= plen
  then true
  else
    if (pos + i) >= hlen
    then false
    else
      if
        (lc_byte (Parser_FastString.fs_byte_at html (pos + i))) =
          (Parser_FastString.fs_byte_at pat i)
      then ci_match_at pat plen html hlen pos (i + Prims.int_one)
      else false
let rec ci_find (pat : Prims.string) (plen : Prims.nat) (html : Prims.string)
  (hlen : Prims.nat) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (fuel = Prims.int_zero) || (pos >= hlen)
  then FStar_Pervasives_Native.None
  else
    if ci_match_at pat plen html hlen pos Prims.int_zero
    then FStar_Pervasives_Native.Some pos
    else
      ci_find pat plen html hlen (pos + Prims.int_one) (fuel - Prims.int_one)
let rec find_byte (s : Prims.string) (slen : Prims.nat) (pos : Prims.nat)
  (b : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (fuel = Prims.int_zero) || (pos >= slen)
  then FStar_Pervasives_Native.None
  else
    if (Parser_FastString.fs_byte_at s pos) = b
    then FStar_Pervasives_Native.Some pos
    else find_byte s slen (pos + Prims.int_one) b (fuel - Prims.int_one)
let extract_attr (opentag : Prims.string) (name : Prims.string)
  (nlen : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  let olen = Parser_FastString.fs_byte_length opentag in
  match ci_find name nlen opentag olen Prims.int_zero olen with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some p ->
      let qpos = p + nlen in
      if qpos >= olen
      then FStar_Pervasives_Native.None
      else
        (let q = Parser_FastString.fs_byte_at opentag qpos in
         if (q = (Prims.of_int (0x22))) || (q = (Prims.of_int (0x27)))
         then
           match find_byte opentag olen (qpos + Prims.int_one) q olen with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ep ->
               FStar_Pervasives_Native.Some
                 (Parser_FastString.fs_byte_sub opentag
                    (qpos + Prims.int_one)
                    (sat_sub ep (qpos + Prims.int_one)))
         else FStar_Pervasives_Native.None)
let extract_id (opentag : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  extract_attr opentag "id=" (Prims.of_int (3))
let extract_html_base (html : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let hlen = Parser_FastString.fs_byte_length html in
  match ci_find "<base" (Prims.of_int (5)) html hlen Prims.int_zero hlen with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some bp ->
      (match find_byte html hlen (bp + (Prims.of_int (5)))
               (Prims.of_int (0x3E)) hlen
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some gt ->
           extract_attr
             (Parser_FastString.fs_byte_sub html bp
                ((sat_sub gt bp) + Prims.int_one)) "href=" (Prims.of_int (5)))
let rec collect_scripts (html : Prims.string) (hlen : Prims.nat)
  (pos : Prims.nat) (fuel : Prims.nat)
  (acc :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  : (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (match ci_find "<script" (Prims.of_int (7)) html hlen pos hlen with
     | FStar_Pervasives_Native.None -> FStar_List_Tot_Base.rev acc
     | FStar_Pervasives_Native.Some sp ->
         (match find_byte html hlen (sp + (Prims.of_int (7)))
                  (Prims.of_int (0x3E)) hlen
          with
          | FStar_Pervasives_Native.None -> FStar_List_Tot_Base.rev acc
          | FStar_Pervasives_Native.Some gt ->
              let opentag =
                Parser_FastString.fs_byte_sub html sp
                  ((sat_sub gt sp) + Prims.int_one) in
              let cstart = gt + Prims.int_one in
              (match ci_find "</script" (Prims.of_int (8)) html hlen cstart
                       hlen
               with
               | FStar_Pervasives_Native.None -> FStar_List_Tot_Base.rev acc
               | FStar_Pervasives_Native.Some ep ->
                   let content =
                     Parser_FastString.fs_byte_sub html cstart
                       (sat_sub ep cstart) in
                   let otlen = Parser_FastString.fs_byte_length opentag in
                   let is_ld =
                     FStar_Pervasives_Native.uu___is_Some
                       (ci_find "application/ld+json" (Prims.of_int (19))
                          opentag otlen Prims.int_zero otlen) in
                   let acc' =
                     if is_ld
                     then ((extract_id opentag), content) :: acc
                     else acc in
                   collect_scripts html hlen (ep + (Prims.of_int (8)))
                     (fuel - Prims.int_one) acc')))
let rec find_script_by_id
  (scripts :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  (fid : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match scripts with
  | [] -> FStar_Pervasives_Native.None
  | (FStar_Pervasives_Native.Some i, c)::rest ->
      if i = fid
      then FStar_Pervasives_Native.Some c
      else find_script_by_id rest fid
  | (FStar_Pervasives_Native.None, uu___)::rest -> find_script_by_id rest fid
let is_ws (b : Prims.nat) : Prims.bool=
  (((b = (Prims.of_int (0x20))) || (b = (Prims.of_int (0x09)))) ||
     (b = (Prims.of_int (0x0A))))
    || (b = (Prims.of_int (0x0D)))
let rec first_nonws (s : Prims.string) (slen : Prims.nat) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if (fuel = Prims.int_zero) || (pos >= slen)
  then FStar_Pervasives_Native.None
  else
    if is_ws (Parser_FastString.fs_byte_at s pos)
    then first_nonws s slen (pos + Prims.int_one) (fuel - Prims.int_one)
    else FStar_Pervasives_Native.Some pos
let rec last_nonws (s : Prims.string) (slen : Prims.nat) (pos : Prims.int)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if (fuel = Prims.int_zero) || (pos < Prims.int_zero)
  then FStar_Pervasives_Native.None
  else
    (let p =
       if (pos >= Prims.int_zero) && (pos < slen)
       then pos
       else Prims.int_zero in
     if
       ((pos >= Prims.int_zero) && (pos < slen)) &&
         (Prims.op_Negation (is_ws (Parser_FastString.fs_byte_at s p)))
     then FStar_Pervasives_Native.Some p
     else last_nonws s slen (pos - Prims.int_one) (fuel - Prims.int_one))
let splice_if_array (c : Prims.string) : Prims.string=
  let clen = Parser_FastString.fs_byte_length c in
  match ((first_nonws c clen Prims.int_zero clen),
          (last_nonws c clen (clen - Prims.int_one) clen))
  with
  | (FStar_Pervasives_Native.Some i, FStar_Pervasives_Native.Some j) ->
      if
        (((Parser_FastString.fs_byte_at c i) = (Prims.of_int (0x5B))) &&
           ((Parser_FastString.fs_byte_at c j) = (Prims.of_int (0x5D))))
          && (j > (i + Prims.int_one))
      then
        Parser_FastString.fs_byte_sub c (i + Prims.int_one)
          (sat_sub j (i + Prims.int_one))
      else c
  | (uu___, uu___1) -> c
let rec join_contents
  (scripts :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  : Prims.string=
  match scripts with
  | [] -> ""
  | (uu___, c)::[] -> splice_if_array c
  | (uu___, c)::rest ->
      Prims.strcat (splice_if_array c)
        (Prims.strcat "," (join_contents rest))
let json_array_of
  (scripts :
    (Prims.string FStar_Pervasives_Native.option * Prims.string) Prims.list)
  : Prims.string= Prims.strcat "[" (Prims.strcat (join_contents scripts) "]")
let extract_jsonld_from_html (html : Prims.string)
  (fragment : Prims.string FStar_Pervasives_Native.option)
  (extract_all : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  let hlen = Parser_FastString.fs_byte_length html in
  let scripts = collect_scripts html hlen Prims.int_zero hlen [] in
  match fragment with
  | FStar_Pervasives_Native.Some fid -> find_script_by_id scripts fid
  | FStar_Pervasives_Native.None ->
      (match scripts with
       | [] ->
           if extract_all
           then FStar_Pervasives_Native.Some "[]"
           else FStar_Pervasives_Native.None
       | first::uu___ ->
           if extract_all
           then FStar_Pervasives_Native.Some (json_array_of scripts)
           else
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.snd first))
