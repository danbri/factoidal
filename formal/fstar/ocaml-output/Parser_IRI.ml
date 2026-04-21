open Prims
type iri_parts =
  {
  ip_scheme: Prims.string FStar_Pervasives_Native.option ;
  ip_authority: Prims.string FStar_Pervasives_Native.option ;
  ip_path: Prims.string ;
  ip_query: Prims.string FStar_Pervasives_Native.option ;
  ip_fragment: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkiri_parts__item__ip_scheme (projectee : iri_parts) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ip_scheme; ip_authority; ip_path; ip_query; ip_fragment;_} -> ip_scheme
let __proj__Mkiri_parts__item__ip_authority (projectee : iri_parts) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ip_scheme; ip_authority; ip_path; ip_query; ip_fragment;_} ->
      ip_authority
let __proj__Mkiri_parts__item__ip_path (projectee : iri_parts) :
  Prims.string=
  match projectee with
  | { ip_scheme; ip_authority; ip_path; ip_query; ip_fragment;_} -> ip_path
let __proj__Mkiri_parts__item__ip_query (projectee : iri_parts) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ip_scheme; ip_authority; ip_path; ip_query; ip_fragment;_} -> ip_query
let __proj__Mkiri_parts__item__ip_fragment (projectee : iri_parts) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ip_scheme; ip_authority; ip_path; ip_query; ip_fragment;_} ->
      ip_fragment
let rec find_colon (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat=
  let len = Parser_FastString.fs_byte_length s in
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= len
    then len
    else
      if (Parser_FastString.fs_byte_at s pos) = (Prims.of_int (0x3A))
      then pos
      else find_colon s (pos + Prims.int_one) (fuel - Prims.int_one)
let rec find_authority_end_iri (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length s in
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= len
    then len
    else
      (let b = Parser_FastString.fs_byte_at s pos in
       if
         ((b = (Prims.of_int (0x2F))) || (b = (Prims.of_int (0x3F)))) ||
           (b = (Prims.of_int (0x23)))
       then pos
       else
         find_authority_end_iri s (pos + Prims.int_one)
           (fuel - Prims.int_one))
let rec find_path_end_iri (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length s in
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= len
    then len
    else
      (let b = Parser_FastString.fs_byte_at s pos in
       if (b = (Prims.of_int (0x3F))) || (b = (Prims.of_int (0x23)))
       then pos
       else find_path_end_iri s (pos + Prims.int_one) (fuel - Prims.int_one))
let rec find_hash_iri (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat)
  : Prims.nat=
  let len = Parser_FastString.fs_byte_length s in
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= len
    then len
    else
      if (Parser_FastString.fs_byte_at s pos) = (Prims.of_int (0x23))
      then pos
      else find_hash_iri s (pos + Prims.int_one) (fuel - Prims.int_one)
let rec find_slash_iri (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length s in
  if fuel = Prims.int_zero
  then pos
  else
    if pos >= len
    then len
    else
      if (Parser_FastString.fs_byte_at s pos) = (Prims.of_int (0x2F))
      then pos
      else find_slash_iri s (pos + Prims.int_one) (fuel - Prims.int_one)
let is_ascii_alpha (b : Prims.nat) : Prims.bool=
  ((b >= (Prims.of_int (0x41))) && (b <= (Prims.of_int (0x5A)))) ||
    ((b >= (Prims.of_int (0x61))) && (b <= (Prims.of_int (0x7A))))
let is_scheme_tail_byte (b : Prims.nat) : Prims.bool=
  ((((is_ascii_alpha b) ||
       ((b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))))
      || (b = (Prims.of_int (0x2B))))
     || (b = (Prims.of_int (0x2D))))
    || (b = (Prims.of_int (0x2E)))
let rec scheme_tail_ok (s : Prims.string) (pos : Prims.nat)
  (stop : Prims.nat) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    if pos >= stop
    then true
    else
      if
        Prims.op_Negation
          (is_scheme_tail_byte (Parser_FastString.fs_byte_at s pos))
      then false
      else scheme_tail_ok s (pos + Prims.int_one) stop (fuel - Prims.int_one)
let scheme_valid (s : Prims.string) (colon_pos : Prims.nat) : Prims.bool=
  if colon_pos = Prims.int_zero
  then false
  else
    if
      Prims.op_Negation
        (is_ascii_alpha (Parser_FastString.fs_byte_at s Prims.int_zero))
    then false
    else scheme_tail_ok s Prims.int_one colon_pos (colon_pos + Prims.int_one)
let parse_iri (s : Prims.string) : iri_parts FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length s in
  let colon_pos = find_colon s Prims.int_zero (len + Prims.int_one) in
  let first_delim_pos =
    find_authority_end_iri s Prims.int_zero (len + Prims.int_one) in
  let uu___ =
    if
      ((colon_pos < len) && (colon_pos < first_delim_pos)) &&
        (scheme_valid s colon_pos)
    then
      ((FStar_Pervasives_Native.Some
          (Parser_FastString.fs_byte_sub s Prims.int_zero colon_pos)),
        (colon_pos + Prims.int_one))
    else (FStar_Pervasives_Native.None, Prims.int_zero) in
  match uu___ with
  | (scheme_opt, rest_start) ->
      let rest_start1 = if rest_start <= len then rest_start else len in
      let uu___1 =
        if
          (((rest_start1 + Prims.int_one) < len) &&
             ((Parser_FastString.fs_byte_at s rest_start1) =
                (Prims.of_int (0x2F))))
            &&
            ((Parser_FastString.fs_byte_at s (rest_start1 + Prims.int_one)) =
               (Prims.of_int (0x2F)))
        then
          let auth_start = rest_start1 + (Prims.of_int (2)) in
          let auth_start1 = if auth_start <= len then auth_start else len in
          let auth_end =
            find_authority_end_iri s auth_start1
              ((len - auth_start1) + Prims.int_one) in
          let auth_len =
            if auth_end >= auth_start1
            then auth_end - auth_start1
            else Prims.int_zero in
          ((FStar_Pervasives_Native.Some
              (Parser_FastString.fs_byte_sub s auth_start1 auth_len)),
            auth_end)
        else (FStar_Pervasives_Native.None, rest_start1) in
      (match uu___1 with
       | (auth_opt, after_auth) ->
           let after_auth1 = if after_auth <= len then after_auth else len in
           let path_end =
             find_path_end_iri s after_auth1
               ((len - after_auth1) + Prims.int_one) in
           let path_len =
             if path_end >= after_auth1
             then path_end - after_auth1
             else Prims.int_zero in
           let path = Parser_FastString.fs_byte_sub s after_auth1 path_len in
           let uu___2 =
             if
               (path_end < len) &&
                 ((Parser_FastString.fs_byte_at s path_end) =
                    (Prims.of_int (0x3F)))
             then
               let q_start = path_end + Prims.int_one in
               let q_start1 = if q_start <= len then q_start else len in
               let q_end =
                 find_hash_iri s q_start1 ((len - q_start1) + Prims.int_one) in
               let q_len =
                 if q_end >= q_start1
                 then q_end - q_start1
                 else Prims.int_zero in
               ((FStar_Pervasives_Native.Some
                   (Parser_FastString.fs_byte_sub s q_start1 q_len)), q_end)
             else (FStar_Pervasives_Native.None, path_end) in
           (match uu___2 with
            | (query_opt, after_query) ->
                let after_query1 =
                  if after_query <= len then after_query else len in
                let frag_opt =
                  if
                    (after_query1 < len) &&
                      ((Parser_FastString.fs_byte_at s after_query1) =
                         (Prims.of_int (0x23)))
                  then
                    let f_start = after_query1 + Prims.int_one in
                    let f_start1 = if f_start <= len then f_start else len in
                    let f_len =
                      if len >= f_start1
                      then len - f_start1
                      else Prims.int_zero in
                    FStar_Pervasives_Native.Some
                      (Parser_FastString.fs_byte_sub s f_start1 f_len)
                  else FStar_Pervasives_Native.None in
                FStar_Pervasives_Native.Some
                  {
                    ip_scheme = scheme_opt;
                    ip_authority = auth_opt;
                    ip_path = path;
                    ip_query = query_opt;
                    ip_fragment = frag_opt
                  }))
let rec remove_dot_segments_step (input : Prims.string) (pos : Prims.nat)
  (out : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev out
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos > len
     then FStar_List_Tot_Base.rev out
     else
       if pos = len
       then FStar_List_Tot_Base.rev out
       else
         (let pos_ref = if pos <= len then pos else len in
          let slash_pos =
            find_slash_iri input pos_ref ((len - pos_ref) + Prims.int_one) in
          let has_slash = slash_pos < len in
          let seg_end = slash_pos in
          let seg_len =
            if seg_end >= pos_ref then seg_end - pos_ref else Prims.int_zero in
          let seg = Parser_FastString.fs_byte_sub input pos_ref seg_len in
          let seg_with_slash =
            if has_slash then FStar_String.concat "" [seg; "/"] else seg in
          let next_pos = if has_slash then slash_pos + Prims.int_one else len in
          let out' =
            if seg = "."
            then
              (if has_slash
               then out
               else
                 (match out with
                  | [] -> ["/"]
                  | uu___4 -> "/" ::
                      ((match out with | uu___5::rest -> rest | [] -> []))))
            else
              if seg = ".."
              then
                (let popped =
                   match out with | uu___4::rest -> rest | [] -> [] in
                 if has_slash then popped else "/" :: popped)
              else seg_with_slash :: out in
          remove_dot_segments_step input next_pos out' (fuel - Prims.int_one)))
let remove_dot_segments (path : Prims.string) : Prims.string=
  let len = Parser_FastString.fs_byte_length path in
  let segs =
    remove_dot_segments_step path Prims.int_zero []
      (len + (Prims.of_int (2))) in
  FStar_String.concat "" segs
let rec find_last_slash_iri (s : Prims.string) (pos : Prims.nat) : Prims.nat=
  if pos = Prims.int_zero
  then Prims.int_zero
  else
    (let idx = pos - Prims.int_one in
     if
       (idx < (Parser_FastString.fs_byte_length s)) &&
         ((Parser_FastString.fs_byte_at s idx) = (Prims.of_int (0x2F)))
     then pos
     else find_last_slash_iri s idx)
let merge_paths (base : iri_parts) (ref_path : Prims.string) : Prims.string=
  let auth_defined =
    match base.ip_authority with
    | FStar_Pervasives_Native.Some uu___ -> true
    | FStar_Pervasives_Native.None -> false in
  if
    auth_defined &&
      ((Parser_FastString.fs_byte_length base.ip_path) = Prims.int_zero)
  then FStar_String.concat "" ["/"; ref_path]
  else
    (let bp = base.ip_path in
     let bp_len = Parser_FastString.fs_byte_length bp in
     let cut = find_last_slash_iri bp bp_len in
     let prefix = Parser_FastString.fs_byte_sub bp Prims.int_zero cut in
     FStar_String.concat "" [prefix; ref_path])
let transform_references (base : iri_parts) (r : iri_parts) : iri_parts=
  match r.ip_scheme with
  | FStar_Pervasives_Native.Some uu___ ->
      {
        ip_scheme = (r.ip_scheme);
        ip_authority = (r.ip_authority);
        ip_path = (remove_dot_segments r.ip_path);
        ip_query = (r.ip_query);
        ip_fragment = (r.ip_fragment)
      }
  | FStar_Pervasives_Native.None ->
      (match r.ip_authority with
       | FStar_Pervasives_Native.Some uu___ ->
           {
             ip_scheme = (base.ip_scheme);
             ip_authority = (r.ip_authority);
             ip_path = (remove_dot_segments r.ip_path);
             ip_query = (r.ip_query);
             ip_fragment = (r.ip_fragment)
           }
       | FStar_Pervasives_Native.None ->
           if (Parser_FastString.fs_byte_length r.ip_path) = Prims.int_zero
           then
             let q =
               match r.ip_query with
               | FStar_Pervasives_Native.Some uu___ -> r.ip_query
               | FStar_Pervasives_Native.None -> base.ip_query in
             {
               ip_scheme = (base.ip_scheme);
               ip_authority = (base.ip_authority);
               ip_path = (base.ip_path);
               ip_query = q;
               ip_fragment = (r.ip_fragment)
             }
           else
             (let new_path =
                if
                  ((Parser_FastString.fs_byte_length r.ip_path) >
                     Prims.int_zero)
                    &&
                    ((Parser_FastString.fs_byte_at r.ip_path Prims.int_zero)
                       = (Prims.of_int (0x2F)))
                then remove_dot_segments r.ip_path
                else remove_dot_segments (merge_paths base r.ip_path) in
              {
                ip_scheme = (base.ip_scheme);
                ip_authority = (base.ip_authority);
                ip_path = new_path;
                ip_query = (r.ip_query);
                ip_fragment = (r.ip_fragment)
              }))
let recompose (t : iri_parts) : Prims.string=
  let scheme_part =
    match t.ip_scheme with
    | FStar_Pervasives_Native.Some s -> FStar_String.concat "" [s; ":"]
    | FStar_Pervasives_Native.None -> "" in
  let auth_part =
    match t.ip_authority with
    | FStar_Pervasives_Native.Some a -> FStar_String.concat "" ["//"; a]
    | FStar_Pervasives_Native.None -> "" in
  let query_part =
    match t.ip_query with
    | FStar_Pervasives_Native.Some q -> FStar_String.concat "" ["?"; q]
    | FStar_Pervasives_Native.None -> "" in
  let frag_part =
    match t.ip_fragment with
    | FStar_Pervasives_Native.Some f -> FStar_String.concat "" ["#"; f]
    | FStar_Pervasives_Native.None -> "" in
  FStar_String.concat ""
    [scheme_part; auth_part; t.ip_path; query_part; frag_part]
let resolve_iri_v2 (base : Prims.string) (ref_ : Prims.string) :
  Prims.string=
  match parse_iri base with
  | FStar_Pervasives_Native.None -> ref_
  | FStar_Pervasives_Native.Some b ->
      (match parse_iri ref_ with
       | FStar_Pervasives_Native.None -> ref_
       | FStar_Pervasives_Native.Some r ->
           recompose (transform_references b r))
