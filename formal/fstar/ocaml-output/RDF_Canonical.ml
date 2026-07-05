open Prims
let hash_sha256 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha256 s
let hash_sha384 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha384 s
type hash_algorithm =
  | HA_SHA256 
  | HA_SHA384 
let uu___is_HA_SHA256 (projectee : hash_algorithm) : Prims.bool=
  match projectee with | HA_SHA256 -> true | uu___ -> false
let uu___is_HA_SHA384 (projectee : hash_algorithm) : Prims.bool=
  match projectee with | HA_SHA384 -> true | uu___ -> false
let apply_hash (alg : hash_algorithm) (s : Prims.string) : Prims.string=
  match alg with | HA_SHA256 -> hash_sha256 s | HA_SHA384 -> hash_sha384 s
let hash_algorithm_of_string (s : Prims.string) : hash_algorithm=
  if s = "SHA384" then HA_SHA384 else HA_SHA256
let hex_digit_uc (n : Prims.nat) : FStar_Char.char=
  if n < (Prims.of_int (10))
  then FStar_Char.char_of_int ((Prims.of_int (0x30)) + n)
  else
    if n < (Prims.of_int (16))
    then
      FStar_Char.char_of_int
        ((Prims.of_int (0x41)) + (n - (Prims.of_int (10))))
    else FStar_Char.char_of_int (Prims.of_int (0x30))
let escape_lit_special_byte (b : Prims.nat) : Prims.bool=
  ((((((((b = (Prims.of_int (0x5C))) || (b = (Prims.of_int (0x22)))) ||
          (b = (Prims.of_int (0x0A))))
         || (b = (Prims.of_int (0x0D))))
        || (b = (Prims.of_int (0x09))))
       || (b = (Prims.of_int (0x08))))
      || (b = (Prims.of_int (0x0C))))
     || (b < (Prims.of_int (0x20))))
    || (b = (Prims.of_int (0x7F)))
let escape_lit_byte (b : Prims.nat) : Prims.string=
  if b = (Prims.of_int (0x5C))
  then "\\\\"
  else
    if b = (Prims.of_int (0x22))
    then "\\\""
    else
      if b = (Prims.of_int (0x0A))
      then "\\n"
      else
        if b = (Prims.of_int (0x0D))
        then "\\r"
        else
          if b = (Prims.of_int (0x09))
          then "\\t"
          else
            if b = (Prims.of_int (0x08))
            then "\\b"
            else
              if b = (Prims.of_int (0x0C))
              then "\\f"
              else
                (let n1 = (mod) (b / (Prims.of_int (16))) (Prims.of_int (16)) in
                 let n0 = (mod) b (Prims.of_int (16)) in
                 FStar_String.string_of_list
                   [FStar_Char.char_of_int (Prims.of_int (0x5C));
                   FStar_Char.char_of_int (Prims.of_int (0x75));
                   FStar_Char.char_of_int (Prims.of_int (0x30));
                   FStar_Char.char_of_int (Prims.of_int (0x30));
                   hex_digit_uc n1;
                   hex_digit_uc n0])
let rec escape_lit_walk (s : Prims.string) (len : Prims.nat)
  (run_start : Prims.nat) (pos : Prims.nat) (acc : Prims.string) :
  Prims.string=
  if pos >= len
  then
    (if pos > run_start
     then
       Prims.strcat acc
         (Parser_FastString.fs_byte_sub s run_start (pos - run_start))
     else acc)
  else
    (let b = Parser_FastString.fs_byte_at s pos in
     if escape_lit_special_byte b
     then
       let run =
         if pos > run_start
         then Parser_FastString.fs_byte_sub s run_start (pos - run_start)
         else "" in
       escape_lit_walk s len (pos + Prims.int_one) (pos + Prims.int_one)
         (Prims.strcat acc (Prims.strcat run (escape_lit_byte b)))
     else escape_lit_walk s len run_start (pos + Prims.int_one) acc)
let escape_lit (s : Prims.string) : Prims.string=
  escape_lit_walk s (Parser_FastString.fs_byte_length s) Prims.int_zero
    Prims.int_zero ""
let canon_term (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
  | RDF_Graph_Executable.T_Literal l ->
      let lex = escape_lit l.RDF_Graph_Executable.lexical_form in
      (match l.RDF_Graph_Executable.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\"" (Prims.strcat lex (Prims.strcat "\"@" tag))
       | FStar_Pervasives_Native.None ->
           if
             l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_string
           then Prims.strcat "\"" (Prims.strcat lex "\"")
           else
             Prims.strcat "\""
               (Prims.strcat lex
                  (Prims.strcat "\"^^<"
                     (Prims.strcat l.RDF_Graph_Executable.datatype ">"))))
let canon_subject (s : RDF_Graph_Executable.subject) : Prims.string=
  match s with
  | RDF_Graph_Executable.S_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let is_bnode_graph_label (gi : RDF_Graph_Executable.iri) : Prims.bool=
  let n = FStar_String.strlen gi in
  if n < (Prims.of_int (2))
  then false
  else (FStar_String.sub gi Prims.int_zero (Prims.of_int (2))) = "_:"
let bnode_of_graph_label (gi : RDF_Graph_Executable.iri) :
  RDF_Graph_Executable.bnode_id=
  let n = FStar_String.strlen gi in
  if n < (Prims.of_int (2))
  then gi
  else FStar_String.sub gi (Prims.of_int (2)) (n - (Prims.of_int (2)))
let canon_graph_name (gi : RDF_Graph_Executable.iri) : Prims.string=
  if is_bnode_graph_label gi
  then Prims.strcat "_:" (bnode_of_graph_label gi)
  else Prims.strcat "<" (Prims.strcat gi ">")
let canon_quad
  (graph_name : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (t : RDF_Graph_Executable.triple) : Prims.string=
  let g =
    match graph_name with
    | FStar_Pervasives_Native.Some gi ->
        Prims.strcat " " (canon_graph_name gi)
    | FStar_Pervasives_Native.None -> "" in
  Prims.strcat (canon_subject t.RDF_Graph_Executable.s)
    (Prims.strcat " <"
       (Prims.strcat t.RDF_Graph_Executable.p
          (Prims.strcat "> "
             (Prims.strcat (canon_term t.RDF_Graph_Executable.o)
                (Prims.strcat g " .\n")))))
type qquad =
  (RDF_Graph_Executable.iri FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple)
let rec attach_graph_rev_onto
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (ts : RDF_Graph_Executable.triple Prims.list) (acc : qquad Prims.list) :
  qquad Prims.list=
  match ts with
  | [] -> acc
  | hd::tl -> attach_graph_rev_onto g tl ((g, hd) :: acc)
let attach_graph
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option)
  (ts : RDF_Graph_Executable.triple Prims.list) : qquad Prims.list=
  FStar_List_Tot_Base.rev (attach_graph_rev_onto g ts [])
let rec flatten_named_rev_onto
  (named : RDF_Graph_Executable.named_graph Prims.list)
  (acc : qquad Prims.list) : qquad Prims.list=
  match named with
  | [] -> acc
  | ng::rest ->
      flatten_named_rev_onto rest
        (attach_graph_rev_onto
           (FStar_Pervasives_Native.Some (ng.RDF_Graph_Executable.ng_name))
           ng.RDF_Graph_Executable.ng_graph acc)
let flatten_named (named : RDF_Graph_Executable.named_graph Prims.list) :
  qquad Prims.list= FStar_List_Tot_Base.rev (flatten_named_rev_onto named [])
let dataset_quads (ds : RDF_Graph_Executable.rdf_dataset) : qquad Prims.list=
  FStar_List_Tot_Base.rev
    (flatten_named_rev_onto ds.RDF_Graph_Executable.ds_named
       (attach_graph_rev_onto FStar_Pervasives_Native.None
          ds.RDF_Graph_Executable.ds_default []))
let bnodes_in_quad (qq : qquad) : RDF_Graph_Executable.bnode_id Prims.list=
  let uu___ = qq in
  match uu___ with
  | (g, t) ->
      let l1 =
        match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_BNode b -> [b]
        | uu___1 -> [] in
      let l2 =
        match t.RDF_Graph_Executable.o with
        | RDF_Graph_Executable.T_BNode b -> [b]
        | uu___1 -> [] in
      let l3 =
        match g with
        | FStar_Pervasives_Native.Some gi ->
            if is_bnode_graph_label gi then [bnode_of_graph_label gi] else []
        | FStar_Pervasives_Native.None -> [] in
      FStar_List_Tot_Base.op_At l1 (FStar_List_Tot_Base.op_At l2 l3)
let qquad_key (q : qquad) : Prims.string=
  let uu___ = q in match uu___ with | (g, t) -> canon_quad g t
let rewrite_subject_for_hfdq (target : RDF_Graph_Executable.bnode_id)
  (s : RDF_Graph_Executable.subject) : RDF_Graph_Executable.subject=
  match s with
  | RDF_Graph_Executable.S_BNode b ->
      if b = target
      then RDF_Graph_Executable.S_BNode "a"
      else RDF_Graph_Executable.S_BNode "z"
  | RDF_Graph_Executable.S_IRI uu___ -> s
let rewrite_term_for_hfdq (target : RDF_Graph_Executable.bnode_id)
  (t : RDF_Graph_Executable.rdf_term) : RDF_Graph_Executable.rdf_term=
  match t with
  | RDF_Graph_Executable.T_BNode b ->
      if b = target
      then RDF_Graph_Executable.T_BNode "a"
      else RDF_Graph_Executable.T_BNode "z"
  | uu___ -> t
let rewrite_triple_for_hfdq (target : RDF_Graph_Executable.bnode_id)
  (t : RDF_Graph_Executable.triple) : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s =
      (rewrite_subject_for_hfdq target t.RDF_Graph_Executable.s);
    RDF_Graph_Executable.p = (t.RDF_Graph_Executable.p);
    RDF_Graph_Executable.o =
      (rewrite_term_for_hfdq target t.RDF_Graph_Executable.o)
  }
let quad_mentions_bnode (target : RDF_Graph_Executable.bnode_id) (q : qquad)
  : Prims.bool=
  let uu___ = q in
  match uu___ with
  | (g, t) ->
      ((match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_BNode b -> b = target
        | uu___1 -> false) ||
         (match t.RDF_Graph_Executable.o with
          | RDF_Graph_Executable.T_BNode b -> b = target
          | uu___1 -> false))
        ||
        ((match g with
          | FStar_Pervasives_Native.Some gi ->
              (is_bnode_graph_label gi) &&
                ((bnode_of_graph_label gi) = target)
          | FStar_Pervasives_Native.None -> false))
let rec quads_for_bnode_acc (target : RDF_Graph_Executable.bnode_id)
  (qs : qquad Prims.list) (acc : qquad Prims.list) : qquad Prims.list=
  match qs with
  | [] -> FStar_List_Tot_Base.rev acc
  | q::rest ->
      if quad_mentions_bnode target q
      then quads_for_bnode_acc target rest (q :: acc)
      else quads_for_bnode_acc target rest acc
let quads_for_bnode (target : RDF_Graph_Executable.bnode_id)
  (qs : qquad Prims.list) : qquad Prims.list=
  quads_for_bnode_acc target qs []
let rewrite_graph_for_hfdq (target : RDF_Graph_Executable.bnode_id)
  (g : RDF_Graph_Executable.iri FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match g with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some gi ->
      if is_bnode_graph_label gi
      then
        let lbl = bnode_of_graph_label gi in
        (if lbl = target
         then FStar_Pervasives_Native.Some "_:a"
         else FStar_Pervasives_Native.Some "_:z")
      else FStar_Pervasives_Native.Some gi
let render_for_hfdq (target : RDF_Graph_Executable.bnode_id) (q : qquad) :
  Prims.string=
  let uu___ = q in
  match uu___ with
  | (g, t) ->
      canon_quad (rewrite_graph_for_hfdq target g)
        (rewrite_triple_for_hfdq target t)
let rec render_all_for_hfdq (target : RDF_Graph_Executable.bnode_id)
  (qs : qquad Prims.list) : Prims.string Prims.list=
  match qs with
  | [] -> []
  | q::rest -> (render_for_hfdq target q) ::
      (render_all_for_hfdq target rest)
let rec str_le_from (a : Prims.string) (b : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let la = Parser_FastString.fs_byte_length a in
     let lb = Parser_FastString.fs_byte_length b in
     if pos >= la
     then true
     else
       if pos >= lb
       then false
       else
         (let ca = Parser_FastString.fs_byte_at a pos in
          let cb = Parser_FastString.fs_byte_at b pos in
          if ca < cb
          then true
          else
            if ca > cb
            then false
            else str_le_from a b (pos + Prims.int_one) (fuel - Prims.int_one)))
let str_le (a : Prims.string) (b : Prims.string) : Prims.bool=
  let la = Parser_FastString.fs_byte_length a in
  let lb = Parser_FastString.fs_byte_length b in
  let m = if la < lb then lb else la in
  str_le_from a b Prims.int_zero (m + Prims.int_one)
let str_eq (a : Prims.string) (b : Prims.string) : Prims.bool= a = b
let str_compare (a : Prims.string) (b : Prims.string) : Prims.int=
  if a = b
  then Prims.int_zero
  else if str_le a b then (Prims.of_int (-1)) else Prims.int_one
let rec str_list_length_acc (xs : Prims.string Prims.list) (acc : Prims.nat)
  : Prims.nat=
  match xs with
  | [] -> acc
  | uu___::tl -> str_list_length_acc tl (acc + Prims.int_one)
let str_list_length (xs : Prims.string Prims.list) : Prims.nat=
  str_list_length_acc xs Prims.int_zero
let rec split_at_acc (n : Prims.nat) (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) :
  (Prims.string Prims.list * Prims.string Prims.list)=
  match xs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | hd::tl ->
      if n = Prims.int_zero
      then ((FStar_List_Tot_Base.rev acc), xs)
      else split_at_acc (n - Prims.int_one) tl (hd :: acc)
let rec merge_sorted_acc (xs : Prims.string Prims.list)
  (ys : Prims.string Prims.list) (fuel : Prims.nat)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then
    FStar_List_Tot_Base.op_At (FStar_List_Tot_Base.rev acc)
      (FStar_List_Tot_Base.op_At xs ys)
  else
    (match (xs, ys) with
     | ([], []) -> FStar_List_Tot_Base.rev acc
     | ([], hd::tl) ->
         merge_sorted_acc [] tl (fuel - Prims.int_one) (hd :: acc)
     | (hd::tl, []) ->
         merge_sorted_acc tl [] (fuel - Prims.int_one) (hd :: acc)
     | (hx::tx, hy::ty) ->
         if str_le hx hy
         then merge_sorted_acc tx ys (fuel - Prims.int_one) (hx :: acc)
         else merge_sorted_acc xs ty (fuel - Prims.int_one) (hy :: acc))
let rec merge_sort_with_fuel (xs : Prims.string Prims.list)
  (depth_fuel : Prims.nat) : Prims.string Prims.list=
  match xs with
  | [] -> []
  | uu___::[] -> xs
  | uu___::uu___1::uu___2 ->
      if depth_fuel = Prims.int_zero
      then xs
      else
        (let n = str_list_length xs in
         let uu___4 = split_at_acc (n / (Prims.of_int (2))) xs [] in
         match uu___4 with
         | (left, right) ->
             let sorted_left =
               merge_sort_with_fuel left (depth_fuel - Prims.int_one) in
             let sorted_right =
               merge_sort_with_fuel right (depth_fuel - Prims.int_one) in
             let fuel =
               (str_list_length sorted_left) + (str_list_length sorted_right) in
             merge_sorted_acc sorted_left sorted_right fuel [])
let insertion_sort (xs : Prims.string Prims.list) : Prims.string Prims.list=
  merge_sort_with_fuel xs ((str_list_length xs) + Prims.int_one)
let concat_strings (xs : Prims.string Prims.list) : Prims.string=
  FStar_String.concat "" xs
let rec generic_list_length_acc :
  'a . 'a Prims.list -> Prims.nat -> Prims.nat =
  fun xs acc ->
    match xs with
    | [] -> acc
    | uu___::tl -> generic_list_length_acc tl (acc + Prims.int_one)
let generic_list_length (xs : 'a Prims.list) : Prims.nat=
  generic_list_length_acc xs Prims.int_zero
let rec generic_split_at_acc :
  'a .
    Prims.nat ->
      'a Prims.list -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun n xs acc ->
    match xs with
    | [] -> ((FStar_List_Tot_Base.rev acc), [])
    | hd::tl ->
        if n = Prims.int_zero
        then ((FStar_List_Tot_Base.rev acc), xs)
        else generic_split_at_acc (n - Prims.int_one) tl (hd :: acc)
let rec generic_merge_acc :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> Prims.nat -> 'a Prims.list -> 'a Prims.list
  =
  fun le xs ys fuel acc ->
    if fuel = Prims.int_zero
    then
      FStar_List_Tot_Base.op_At (FStar_List_Tot_Base.rev acc)
        (FStar_List_Tot_Base.op_At xs ys)
    else
      (match (xs, ys) with
       | ([], []) -> FStar_List_Tot_Base.rev acc
       | ([], hd::tl) ->
           generic_merge_acc le [] tl (fuel - Prims.int_one) (hd :: acc)
       | (hd::tl, []) ->
           generic_merge_acc le tl [] (fuel - Prims.int_one) (hd :: acc)
       | (hx::tx, hy::ty) ->
           if le hx hy
           then generic_merge_acc le tx ys (fuel - Prims.int_one) (hx :: acc)
           else generic_merge_acc le xs ty (fuel - Prims.int_one) (hy :: acc))
let rec generic_merge_sort_with_fuel :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> Prims.nat -> 'a Prims.list
  =
  fun le xs depth_fuel ->
    match xs with
    | [] -> []
    | uu___::[] -> xs
    | uu___::uu___1::uu___2 ->
        if depth_fuel = Prims.int_zero
        then xs
        else
          (let n = generic_list_length xs in
           let uu___4 = generic_split_at_acc (n / (Prims.of_int (2))) xs [] in
           match uu___4 with
           | (left, right) ->
               let sorted_left =
                 generic_merge_sort_with_fuel le left
                   (depth_fuel - Prims.int_one) in
               let sorted_right =
                 generic_merge_sort_with_fuel le right
                   (depth_fuel - Prims.int_one) in
               let fuel =
                 (generic_list_length sorted_left) +
                   (generic_list_length sorted_right) in
               generic_merge_acc le sorted_left sorted_right fuel [])
let generic_stable_sort (le : 'a -> 'a -> Prims.bool) (xs : 'a Prims.list) :
  'a Prims.list=
  generic_merge_sort_with_fuel le xs
    ((generic_list_length xs) + Prims.int_one)
let rec tag_qquads_with_key (qs : qquad Prims.list)
  (acc : (Prims.string * qquad) Prims.list) :
  (Prims.string * qquad) Prims.list=
  match qs with
  | [] -> acc
  | q::rest -> tag_qquads_with_key rest (((qquad_key q), q) :: acc)
let keyed_qquad_le (a : (Prims.string * qquad)) (b : (Prims.string * qquad))
  : Prims.bool=
  str_le (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst b)
let rec dedup_sorted_keyed_qquads_acc
  (xs : (Prims.string * qquad) Prims.list) (acc : qquad Prims.list) :
  qquad Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | (uu___, q)::[] -> FStar_List_Tot_Base.rev (q :: acc)
  | (k1, q1)::(k2, q2)::rest ->
      if k1 = k2
      then dedup_sorted_keyed_qquads_acc ((k2, q2) :: rest) acc
      else dedup_sorted_keyed_qquads_acc ((k2, q2) :: rest) (q1 :: acc)
let dedup_qquads (qs : qquad Prims.list) : qquad Prims.list=
  dedup_sorted_keyed_qquads_acc
    (generic_stable_sort keyed_qquad_le (tag_qquads_with_key qs [])) []
let rec dedup_sorted_strings2_acc (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | x::[] -> FStar_List_Tot_Base.rev (x :: acc)
  | x::y::rest ->
      if x = y
      then dedup_sorted_strings2_acc (y :: rest) acc
      else dedup_sorted_strings2_acc (y :: rest) (x :: acc)
let dedup_strings (xs : Prims.string Prims.list) : Prims.string Prims.list=
  dedup_sorted_strings2_acc (generic_stable_sort str_le xs) []
let rec all_bnodes_acc (acc : RDF_Graph_Executable.bnode_id Prims.list)
  (qs : qquad Prims.list) : RDF_Graph_Executable.bnode_id Prims.list=
  match qs with
  | [] -> acc
  | q::rest ->
      all_bnodes_acc (FStar_List_Tot_Base.rev_acc (bnodes_in_quad q) acc)
        rest
let dataset_bnodes (ds : RDF_Graph_Executable.rdf_dataset) :
  RDF_Graph_Executable.bnode_id Prims.list=
  dedup_strings
    (FStar_List_Tot_Base.rev (all_bnodes_acc [] (dataset_quads ds)))
let rec tag_bnodes_with_quad (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (q : qquad) (acc : (RDF_Graph_Executable.bnode_id * qquad) Prims.list) :
  (RDF_Graph_Executable.bnode_id * qquad) Prims.list=
  match bs with
  | [] -> acc
  | b::rest -> tag_bnodes_with_quad rest q ((b, q) :: acc)
let rec qquad_bnode_pairs_acc (qs : qquad Prims.list)
  (acc : (RDF_Graph_Executable.bnode_id * qquad) Prims.list) :
  (RDF_Graph_Executable.bnode_id * qquad) Prims.list=
  match qs with
  | [] -> acc
  | q::rest ->
      qquad_bnode_pairs_acc rest
        (tag_bnodes_with_quad (dedup_strings (bnodes_in_quad q)) q acc)
let bnq_pair_le (a : (RDF_Graph_Executable.bnode_id * qquad))
  (b : (RDF_Graph_Executable.bnode_id * qquad)) : Prims.bool=
  str_le (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst b)
let rec group_sorted_bnq_acc
  (xs : (RDF_Graph_Executable.bnode_id * qquad) Prims.list)
  (cur_b : RDF_Graph_Executable.bnode_id) (cur_qs : qquad Prims.list)
  (acc : (RDF_Graph_Executable.bnode_id * qquad Prims.list) Prims.list) :
  (RDF_Graph_Executable.bnode_id * qquad Prims.list) Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev ((cur_b, cur_qs) :: acc)
  | (b, q)::rest ->
      if b = cur_b
      then group_sorted_bnq_acc rest cur_b (q :: cur_qs) acc
      else group_sorted_bnq_acc rest b [q] ((cur_b, cur_qs) :: acc)
let bnode_quads_index (qs : qquad Prims.list) :
  (RDF_Graph_Executable.bnode_id * qquad Prims.list) Prims.list=
  match generic_stable_sort bnq_pair_le (qquad_bnode_pairs_acc qs []) with
  | [] -> []
  | (b0, q0)::rest -> group_sorted_bnq_acc rest b0 [q0] []
let compute_hfdq (alg : hash_algorithm)
  (target : RDF_Graph_Executable.bnode_id) (qs : qquad Prims.list) :
  Prims.string=
  let mentioning = quads_for_bnode target qs in
  let rendered = render_all_for_hfdq target mentioning in
  let sorted = insertion_sort rendered in
  apply_hash alg (concat_strings sorted)
let digit_char (d : Prims.nat) : Prims.string=
  if d = Prims.int_zero
  then "0"
  else
    if d = Prims.int_one
    then "1"
    else
      if d = (Prims.of_int (2))
      then "2"
      else
        if d = (Prims.of_int (3))
        then "3"
        else
          if d = (Prims.of_int (4))
          then "4"
          else
            if d = (Prims.of_int (5))
            then "5"
            else
              if d = (Prims.of_int (6))
              then "6"
              else
                if d = (Prims.of_int (7))
                then "7"
                else if d = (Prims.of_int (8)) then "8" else "9"
let rec nat_to_string_acc (n : Prims.nat) (acc : Prims.string)
  (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then acc
  else
    if n < (Prims.of_int (10))
    then Prims.strcat (digit_char n) acc
    else
      (let q = n / (Prims.of_int (10)) in
       let r = (mod) n (Prims.of_int (10)) in
       nat_to_string_acc q (Prims.strcat (digit_char r) acc)
         (fuel - Prims.int_one))
let nat_to_string (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "0"
  else nat_to_string_acc n "" (n + Prims.int_one)
type issuer_state =
  {
  is_prefix: Prims.string ;
  is_counter: Prims.nat ;
  is_issued: (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list }
let __proj__Mkissuer_state__item__is_prefix (projectee : issuer_state) :
  Prims.string=
  match projectee with | { is_prefix; is_counter; is_issued;_} -> is_prefix
let __proj__Mkissuer_state__item__is_counter (projectee : issuer_state) :
  Prims.nat=
  match projectee with | { is_prefix; is_counter; is_issued;_} -> is_counter
let __proj__Mkissuer_state__item__is_issued (projectee : issuer_state) :
  (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list=
  match projectee with | { is_prefix; is_counter; is_issued;_} -> is_issued
let empty_issuer : issuer_state=
  { is_prefix = "c14n"; is_counter = Prims.int_zero; is_issued = [] }
let empty_temp_issuer : issuer_state=
  { is_prefix = "b"; is_counter = Prims.int_zero; is_issued = [] }
let rec lookup_issued (b : RDF_Graph_Executable.bnode_id)
  (xs : (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = b then FStar_Pervasives_Native.Some v else lookup_issued b rest
let issue_identifier (st : issuer_state) (b : RDF_Graph_Executable.bnode_id)
  : (issuer_state * Prims.string)=
  match lookup_issued b st.is_issued with
  | FStar_Pervasives_Native.Some v -> (st, v)
  | FStar_Pervasives_Native.None ->
      let label = Prims.strcat st.is_prefix (nat_to_string st.is_counter) in
      let st' =
        {
          is_prefix = (st.is_prefix);
          is_counter = (st.is_counter + Prims.int_one);
          is_issued = (FStar_List_Tot_Base.op_At st.is_issued [(b, label)])
        } in
      (st', label)
let issue_fresh (st : issuer_state) (b : RDF_Graph_Executable.bnode_id) :
  issuer_state=
  let label = Prims.strcat st.is_prefix (nat_to_string st.is_counter) in
  {
    is_prefix = (st.is_prefix);
    is_counter = (st.is_counter + Prims.int_one);
    is_issued = ((b, label) :: (st.is_issued))
  }
type bn_hfdq_pair = (RDF_Graph_Executable.bnode_id * Prims.string)
let compute_hfdq_from_quads (alg : hash_algorithm)
  (target : RDF_Graph_Executable.bnode_id) (qs : qquad Prims.list) :
  Prims.string=
  let rendered = render_all_for_hfdq target qs in
  let sorted = insertion_sort rendered in
  apply_hash alg (concat_strings sorted)
let rec compute_all_hfdq_from_index (alg : hash_algorithm)
  (idx : (RDF_Graph_Executable.bnode_id * qquad Prims.list) Prims.list) :
  bn_hfdq_pair Prims.list=
  match idx with
  | [] -> []
  | (b, qlist)::rest -> (b, (compute_hfdq_from_quads alg b qlist)) ::
      (compute_all_hfdq_from_index alg rest)
let compute_all_hfdq (alg : hash_algorithm) (qs : qquad Prims.list) :
  bn_hfdq_pair Prims.list=
  compute_all_hfdq_from_index alg (bnode_quads_index qs)
let rec lookup_hfdq (b : RDF_Graph_Executable.bnode_id)
  (xs : bn_hfdq_pair Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | (k, h)::rest -> if k = b then h else lookup_hfdq b rest
let nbr_position_tag (target : RDF_Graph_Executable.bnode_id) (q : qquad) :
  Prims.string=
  let uu___ = q in
  match uu___ with
  | (g, t) ->
      let s_bn =
        match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_BNode b -> FStar_Pervasives_Native.Some b
        | uu___1 -> FStar_Pervasives_Native.None in
      let o_bn =
        match t.RDF_Graph_Executable.o with
        | RDF_Graph_Executable.T_BNode b -> FStar_Pervasives_Native.Some b
        | uu___1 -> FStar_Pervasives_Native.None in
      let g_is_target =
        match g with
        | FStar_Pervasives_Native.Some gi ->
            (is_bnode_graph_label gi) && ((bnode_of_graph_label gi) = target)
        | FStar_Pervasives_Native.None -> false in
      let so_pos =
        match (s_bn, o_bn) with
        | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.Some ob)
            ->
            if (sb = target) && (ob = target)
            then FStar_Pervasives_Native.Some "ss"
            else
              if sb = target
              then FStar_Pervasives_Native.Some "o"
              else
                if ob = target
                then FStar_Pervasives_Native.Some "s"
                else FStar_Pervasives_Native.None
        | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.None) ->
            if sb = target
            then FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some "s"
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some ob) ->
            if ob = target
            then FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some "o"
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            FStar_Pervasives_Native.None in
      (match so_pos with
       | FStar_Pervasives_Native.Some p -> p
       | FStar_Pervasives_Native.None ->
           if g_is_target
           then
             (match s_bn with
              | FStar_Pervasives_Native.Some uu___1 -> "s"
              | FStar_Pervasives_Native.None ->
                  (match o_bn with
                   | FStar_Pervasives_Native.Some uu___1 -> "o"
                   | FStar_Pervasives_Native.None -> "_"))
           else "g")
let graph_bnode_of (q : qquad) :
  RDF_Graph_Executable.bnode_id FStar_Pervasives_Native.option=
  let uu___ = q in
  match uu___ with
  | (g, uu___1) ->
      (match g with
       | FStar_Pervasives_Native.Some gi ->
           if is_bnode_graph_label gi
           then FStar_Pervasives_Native.Some (bnode_of_graph_label gi)
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let related_bnode (target : RDF_Graph_Executable.bnode_id) (q : qquad) :
  RDF_Graph_Executable.bnode_id FStar_Pervasives_Native.option=
  let uu___ = q in
  match uu___ with
  | (uu___1, t) ->
      let s_bn =
        match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_BNode b -> FStar_Pervasives_Native.Some b
        | uu___2 -> FStar_Pervasives_Native.None in
      let o_bn =
        match t.RDF_Graph_Executable.o with
        | RDF_Graph_Executable.T_BNode b -> FStar_Pervasives_Native.Some b
        | uu___2 -> FStar_Pervasives_Native.None in
      let g_bn = graph_bnode_of q in
      let so_other =
        match (s_bn, o_bn) with
        | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.Some ob)
            ->
            if (sb = target) && (ob = target)
            then FStar_Pervasives_Native.None
            else
              if sb = target
              then FStar_Pervasives_Native.Some ob
              else
                if ob = target
                then FStar_Pervasives_Native.Some sb
                else FStar_Pervasives_Native.None
        | (FStar_Pervasives_Native.Some sb, FStar_Pervasives_Native.None) ->
            if sb = target
            then FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some sb
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some ob) ->
            if ob = target
            then FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some ob
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            FStar_Pervasives_Native.None in
      (match so_other with
       | FStar_Pervasives_Native.Some uu___2 -> so_other
       | FStar_Pervasives_Native.None ->
           (match g_bn with
            | FStar_Pervasives_Native.Some gb ->
                if gb = target
                then
                  (match s_bn with
                   | FStar_Pervasives_Native.Some sb ->
                       FStar_Pervasives_Native.Some sb
                   | FStar_Pervasives_Native.None -> o_bn)
                else FStar_Pervasives_Native.Some gb
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let hash_related_blank_node (alg : hash_algorithm) (pos : Prims.string)
  (pred : Prims.string) (identifier : Prims.string) : Prims.string=
  let input =
    Prims.strcat pos
      (Prims.strcat
         (if pos <> "g" then Prims.strcat "<" (Prims.strcat pred ">") else "")
         identifier) in
  apply_hash alg input
let nbr_contribution (target : RDF_Graph_Executable.bnode_id) (q : qquad)
  (key_of : RDF_Graph_Executable.bnode_id -> Prims.string) : Prims.string=
  let uu___ = q in
  match uu___ with
  | (uu___1, t) ->
      let pos = nbr_position_tag target q in
      let pred = t.RDF_Graph_Executable.p in
      let rk =
        match related_bnode target q with
        | FStar_Pervasives_Native.None -> "_"
        | FStar_Pervasives_Native.Some rb -> key_of rb in
      Prims.strcat pos
        (Prims.strcat "|" (Prims.strcat pred (Prims.strcat "|" rk)))
let rec nbr_contributions (target : RDF_Graph_Executable.bnode_id)
  (qs : qquad Prims.list)
  (key_of : RDF_Graph_Executable.bnode_id -> Prims.string) :
  Prims.string Prims.list=
  match qs with
  | [] -> []
  | q::rest -> (nbr_contribution target q key_of) ::
      (nbr_contributions target rest key_of)
let compute_nbr_hash (target : RDF_Graph_Executable.bnode_id)
  (qs : qquad Prims.list)
  (key_of : RDF_Graph_Executable.bnode_id -> Prims.string) : Prims.string=
  let mentioning = quads_for_bnode target qs in
  let contribs = nbr_contributions target mentioning key_of in
  let sorted = insertion_sort contribs in hash_sha256 (concat_strings sorted)
let rec compute_all_nbr1 (qs : qquad Prims.list)
  (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (hfdq_table : bn_hfdq_pair Prims.list) : bn_hfdq_pair Prims.list=
  match bs with
  | [] -> []
  | b::rest ->
      let key_of rb = lookup_hfdq rb hfdq_table in
      let h = compute_nbr_hash b qs key_of in (b, h) ::
        (compute_all_nbr1 qs rest hfdq_table)
let rec compute_all_nbr2 (qs : qquad Prims.list)
  (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (nbr1_table : bn_hfdq_pair Prims.list) : bn_hfdq_pair Prims.list=
  match bs with
  | [] -> []
  | b::rest ->
      let key_of rb = lookup_hfdq rb nbr1_table in
      let h = compute_nbr_hash b qs key_of in (b, h) ::
        (compute_all_nbr2 qs rest nbr1_table)
let rec compute_all_nbr3 (qs : qquad Prims.list)
  (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (nbr2_table : bn_hfdq_pair Prims.list) : bn_hfdq_pair Prims.list=
  match bs with
  | [] -> []
  | b::rest ->
      let key_of rb = lookup_hfdq rb nbr2_table in
      let h = compute_nbr_hash b qs key_of in (b, h) ::
        (compute_all_nbr3 qs rest nbr2_table)
type bn_full_key =
  {
  bk_orig: RDF_Graph_Executable.bnode_id ;
  bk_hfdq: Prims.string ;
  bk_nbr1: Prims.string ;
  bk_nbr2: Prims.string ;
  bk_nbr3: Prims.string }
let __proj__Mkbn_full_key__item__bk_orig (projectee : bn_full_key) :
  RDF_Graph_Executable.bnode_id=
  match projectee with
  | { bk_orig; bk_hfdq; bk_nbr1; bk_nbr2; bk_nbr3;_} -> bk_orig
let __proj__Mkbn_full_key__item__bk_hfdq (projectee : bn_full_key) :
  Prims.string=
  match projectee with
  | { bk_orig; bk_hfdq; bk_nbr1; bk_nbr2; bk_nbr3;_} -> bk_hfdq
let __proj__Mkbn_full_key__item__bk_nbr1 (projectee : bn_full_key) :
  Prims.string=
  match projectee with
  | { bk_orig; bk_hfdq; bk_nbr1; bk_nbr2; bk_nbr3;_} -> bk_nbr1
let __proj__Mkbn_full_key__item__bk_nbr2 (projectee : bn_full_key) :
  Prims.string=
  match projectee with
  | { bk_orig; bk_hfdq; bk_nbr1; bk_nbr2; bk_nbr3;_} -> bk_nbr2
let __proj__Mkbn_full_key__item__bk_nbr3 (projectee : bn_full_key) :
  Prims.string=
  match projectee with
  | { bk_orig; bk_hfdq; bk_nbr1; bk_nbr2; bk_nbr3;_} -> bk_nbr3
let rec lookup_pair (b : RDF_Graph_Executable.bnode_id)
  (xs : bn_hfdq_pair Prims.list) : Prims.string=
  match xs with
  | [] -> ""
  | (k, v)::rest -> if k = b then v else lookup_pair b rest
let rec build_full_keys (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (hfdq_t : bn_hfdq_pair Prims.list) (nbr1_t : bn_hfdq_pair Prims.list)
  (nbr2_t : bn_hfdq_pair Prims.list) (nbr3_t : bn_hfdq_pair Prims.list) :
  bn_full_key Prims.list=
  match bs with
  | [] -> []
  | b::rest ->
      {
        bk_orig = b;
        bk_hfdq = (lookup_pair b hfdq_t);
        bk_nbr1 = (lookup_pair b nbr1_t);
        bk_nbr2 = (lookup_pair b nbr2_t);
        bk_nbr3 = (lookup_pair b nbr3_t)
      } :: (build_full_keys rest hfdq_t nbr1_t nbr2_t nbr3_t)
let full_key_le (a : bn_full_key) (b : bn_full_key) : Prims.bool=
  if a.bk_hfdq <> b.bk_hfdq
  then str_le a.bk_hfdq b.bk_hfdq
  else
    if a.bk_nbr1 <> b.bk_nbr1
    then str_le a.bk_nbr1 b.bk_nbr1
    else
      if a.bk_nbr2 <> b.bk_nbr2
      then str_le a.bk_nbr2 b.bk_nbr2
      else
        if a.bk_nbr3 <> b.bk_nbr3
        then str_le a.bk_nbr3 b.bk_nbr3
        else str_le a.bk_orig b.bk_orig
let rec insert_full_key (x : bn_full_key) (xs : bn_full_key Prims.list) :
  bn_full_key Prims.list=
  match xs with
  | [] -> [x]
  | hd::tl ->
      if full_key_le x hd then x :: xs else hd :: (insert_full_key x tl)
let rec sort_full_keys (xs : bn_full_key Prims.list) :
  bn_full_key Prims.list=
  match xs with | [] -> [] | hd::tl -> insert_full_key hd (sort_full_keys tl)
let pair_compare (a : bn_hfdq_pair) (b : bn_hfdq_pair) : Prims.int=
  let uu___ = a in
  match uu___ with
  | (oa, ha) ->
      let uu___1 = b in
      (match uu___1 with
       | (ob, hb) ->
           if ha = hb
           then
             (if oa = ob
              then Prims.int_zero
              else
                if str_le oa ob then (Prims.of_int (-1)) else Prims.int_one)
           else if str_le ha hb then (Prims.of_int (-1)) else Prims.int_one)
let sort_pairs (xs : bn_hfdq_pair Prims.list) : bn_hfdq_pair Prims.list=
  FStar_List_Tot_Base.sortWith pair_compare xs
let rec assign_in_order (st : issuer_state) (xs : bn_hfdq_pair Prims.list) :
  issuer_state=
  match xs with
  | [] -> st
  | (orig, uu___)::rest ->
      let uu___1 = issue_identifier st orig in
      (match uu___1 with | (st', uu___2) -> assign_in_order st' rest)
let rec assign_full_in_order (st : issuer_state)
  (xs : bn_full_key Prims.list) : issuer_state=
  match xs with
  | [] -> st
  | k::rest ->
      let uu___ = issue_identifier st k.bk_orig in
      (match uu___ with | (st', uu___1) -> assign_full_in_order st' rest)
type bn_lookup_tree =
  | BLT_Leaf 
  | BLT_Node of (bn_lookup_tree * RDF_Graph_Executable.bnode_id *
  Prims.string * bn_lookup_tree) 
let uu___is_BLT_Leaf (projectee : bn_lookup_tree) : Prims.bool=
  match projectee with | BLT_Leaf -> true | uu___ -> false
let uu___is_BLT_Node (projectee : bn_lookup_tree) : Prims.bool=
  match projectee with | BLT_Node _0 -> true | uu___ -> false
let __proj__BLT_Node__item___0 (projectee : bn_lookup_tree) :
  (bn_lookup_tree * RDF_Graph_Executable.bnode_id * Prims.string *
    bn_lookup_tree)=
  match projectee with | BLT_Node _0 -> _0
let rec bn_lookup_tree_of_sorted (xs : bn_hfdq_pair Prims.list)
  (n : Prims.nat) : bn_lookup_tree=
  if n = Prims.int_zero
  then BLT_Leaf
  else
    (let mid = n / (Prims.of_int (2)) in
     let uu___1 = generic_split_at_acc mid xs [] in
     match uu___1 with
     | (left, rest) ->
         (match rest with
          | [] -> BLT_Leaf
          | (k, v)::right ->
              BLT_Node
                ((bn_lookup_tree_of_sorted left mid), k, v,
                  (bn_lookup_tree_of_sorted right ((n - mid) - Prims.int_one)))))
let build_bn_lookup_tree
  (mapping : (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list) :
  bn_lookup_tree=
  let sorted =
    generic_stable_sort
      (fun a b ->
         str_le (FStar_Pervasives_Native.fst a)
           (FStar_Pervasives_Native.fst b)) mapping in
  bn_lookup_tree_of_sorted sorted (generic_list_length sorted)
let rec bn_lookup_tree_find (b : RDF_Graph_Executable.bnode_id)
  (t : bn_lookup_tree) : Prims.string FStar_Pervasives_Native.option=
  match t with
  | BLT_Leaf -> FStar_Pervasives_Native.None
  | BLT_Node (l, k, v, r) ->
      if b = k
      then FStar_Pervasives_Native.Some v
      else
        if str_le b k
        then bn_lookup_tree_find b l
        else bn_lookup_tree_find b r
let relabel_subject (mapping : bn_lookup_tree)
  (s : RDF_Graph_Executable.subject) : RDF_Graph_Executable.subject=
  match s with
  | RDF_Graph_Executable.S_IRI uu___ -> s
  | RDF_Graph_Executable.S_BNode b ->
      (match bn_lookup_tree_find b mapping with
       | FStar_Pervasives_Native.Some lbl -> RDF_Graph_Executable.S_BNode lbl
       | FStar_Pervasives_Native.None -> s)
let relabel_term (mapping : bn_lookup_tree)
  (t : RDF_Graph_Executable.rdf_term) : RDF_Graph_Executable.rdf_term=
  match t with
  | RDF_Graph_Executable.T_BNode b ->
      (match bn_lookup_tree_find b mapping with
       | FStar_Pervasives_Native.Some lbl -> RDF_Graph_Executable.T_BNode lbl
       | FStar_Pervasives_Native.None -> t)
  | uu___ -> t
let relabel_triple (mapping : bn_lookup_tree)
  (t : RDF_Graph_Executable.triple) : RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s =
      (relabel_subject mapping t.RDF_Graph_Executable.s);
    RDF_Graph_Executable.p = (t.RDF_Graph_Executable.p);
    RDF_Graph_Executable.o = (relabel_term mapping t.RDF_Graph_Executable.o)
  }
let relabel_graph (mapping : bn_lookup_tree)
  (g : RDF_Graph_Executable.rdf_graph) : RDF_Graph_Executable.rdf_graph=
  FStar_List_Tot_Base.map (relabel_triple mapping) g
let relabel_graph_name (mapping : bn_lookup_tree)
  (gi : RDF_Graph_Executable.iri) : RDF_Graph_Executable.iri=
  if is_bnode_graph_label gi
  then
    let lbl = bnode_of_graph_label gi in
    match bn_lookup_tree_find lbl mapping with
    | FStar_Pervasives_Native.Some new_lbl -> Prims.strcat "_:" new_lbl
    | FStar_Pervasives_Native.None -> gi
  else gi
let relabel_named_graph (mapping : bn_lookup_tree)
  (ng : RDF_Graph_Executable.named_graph) : RDF_Graph_Executable.named_graph=
  {
    RDF_Graph_Executable.ng_name =
      (relabel_graph_name mapping ng.RDF_Graph_Executable.ng_name);
    RDF_Graph_Executable.ng_graph =
      (relabel_graph mapping ng.RDF_Graph_Executable.ng_graph)
  }
let relabel_dataset
  (mapping : (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list)
  (ds : RDF_Graph_Executable.rdf_dataset) : RDF_Graph_Executable.rdf_dataset=
  let tree = build_bn_lookup_tree mapping in
  {
    RDF_Graph_Executable.ds_default =
      (relabel_graph tree ds.RDF_Graph_Executable.ds_default);
    RDF_Graph_Executable.ds_named =
      (FStar_List_Tot_Base.map (relabel_named_graph tree)
         ds.RDF_Graph_Executable.ds_named)
  }
type bucket = (Prims.string * RDF_Graph_Executable.bnode_id Prims.list)
let rec bucket_insert (k : Prims.string) (b : RDF_Graph_Executable.bnode_id)
  (xs : bucket Prims.list) : bucket Prims.list=
  match xs with
  | [] -> [(k, [b])]
  | (k', members)::rest ->
      if k = k'
      then (k', (FStar_List_Tot_Base.op_At members [b])) :: rest
      else
        if str_le k k'
        then (k, [b]) :: xs
        else (k', members) :: (bucket_insert k b rest)
let lookup_issued2 (b : RDF_Graph_Executable.bnode_id)
  (canon_st : issuer_state) (local_st : issuer_state) :
  Prims.string FStar_Pervasives_Native.option=
  match lookup_issued b canon_st.is_issued with
  | FStar_Pervasives_Native.Some lbl -> FStar_Pervasives_Native.Some lbl
  | FStar_Pervasives_Native.None -> lookup_issued b local_st.is_issued
let related_components (target : RDF_Graph_Executable.bnode_id) (q : qquad) :
  (Prims.string * RDF_Graph_Executable.bnode_id) Prims.list=
  let uu___ = q in
  match uu___ with
  | (uu___1, t) ->
      let s_e =
        match t.RDF_Graph_Executable.s with
        | RDF_Graph_Executable.S_BNode b ->
            if b <> target then [("s", b)] else []
        | uu___2 -> [] in
      let o_e =
        match t.RDF_Graph_Executable.o with
        | RDF_Graph_Executable.T_BNode b ->
            if b <> target then [("o", b)] else []
        | uu___2 -> [] in
      let g_e =
        match graph_bnode_of q with
        | FStar_Pervasives_Native.Some b ->
            if b <> target then [("g", b)] else []
        | FStar_Pervasives_Native.None -> [] in
      FStar_List_Tot_Base.op_At s_e (FStar_List_Tot_Base.op_At o_e g_e)
let rec insert_related_entries (alg : hash_algorithm)
  (entries : (Prims.string * RDF_Graph_Executable.bnode_id) Prims.list)
  (pred : Prims.string) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (acc : bucket Prims.list) : bucket Prims.list=
  match entries with
  | [] -> acc
  | (pos, rb)::rest ->
      let identifier =
        match lookup_issued2 rb canon_st local_st with
        | FStar_Pervasives_Native.Some lbl -> Prims.strcat "_:" lbl
        | FStar_Pervasives_Native.None -> lookup_hfdq rb hfdq_table in
      let k = hash_related_blank_node alg pos pred identifier in
      insert_related_entries alg rest pred hfdq_table canon_st local_st
        (bucket_insert k rb acc)
let rec build_buckets_for (alg : hash_algorithm)
  (target : RDF_Graph_Executable.bnode_id) (qs : qquad Prims.list)
  (hfdq_table : bn_hfdq_pair Prims.list) (canon_st : issuer_state)
  (local_st : issuer_state) (acc : bucket Prims.list) : bucket Prims.list=
  match qs with
  | [] -> acc
  | q::rest ->
      if Prims.op_Negation (quad_mentions_bnode target q)
      then build_buckets_for alg target rest hfdq_table canon_st local_st acc
      else
        (let uu___1 = q in
         match uu___1 with
         | (uu___2, t) ->
             let entries = related_components target q in
             let acc' =
               insert_related_entries alg entries t.RDF_Graph_Executable.p
                 hfdq_table canon_st local_st acc in
             build_buckets_for alg target rest hfdq_table canon_st local_st
               acc')
let rec remove_first (x : RDF_Graph_Executable.bnode_id)
  (xs : RDF_Graph_Executable.bnode_id Prims.list) :
  RDF_Graph_Executable.bnode_id Prims.list=
  match xs with
  | [] -> []
  | hd::tl -> if hd = x then tl else hd :: (remove_first x tl)
let rec take_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n xs ->
    if n = Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | hd::tl -> hd :: (take_n (n - Prims.int_one) tl))
let rec insert_at_all (x : RDF_Graph_Executable.bnode_id)
  (ys : RDF_Graph_Executable.bnode_id Prims.list) :
  RDF_Graph_Executable.bnode_id Prims.list Prims.list=
  match ys with
  | [] -> [[x]]
  | hd::tl -> (x :: ys) ::
      (FStar_List_Tot_Base.map (fun zs -> hd :: zs) (insert_at_all x tl))
let rec permutations (xs : RDF_Graph_Executable.bnode_id Prims.list) :
  RDF_Graph_Executable.bnode_id Prims.list Prims.list=
  match xs with
  | [] -> [[]]
  | hd::tl ->
      let sub = permutations tl in
      FStar_List_Tot_Base.fold_left
        (fun acc p -> FStar_List_Tot_Base.op_At acc (insert_at_all hd p)) []
        sub
let rec mem_bnode (b : RDF_Graph_Executable.bnode_id)
  (xs : RDF_Graph_Executable.bnode_id Prims.list) : Prims.bool=
  match xs with | [] -> false | hd::tl -> (hd = b) || (mem_bnode b tl)
let rec build_path_labels (canon_st : issuer_state) (local_st : issuer_state)
  (perm : RDF_Graph_Executable.bnode_id Prims.list) (path : Prims.string)
  (recursion : RDF_Graph_Executable.bnode_id Prims.list) :
  (Prims.string * issuer_state * RDF_Graph_Executable.bnode_id Prims.list)=
  match perm with
  | [] -> (path, local_st, recursion)
  | b::rest ->
      (match lookup_issued2 b canon_st local_st with
       | FStar_Pervasives_Native.Some lbl ->
           build_path_labels canon_st local_st rest
             (Prims.strcat path (Prims.strcat "_:" lbl)) recursion
       | FStar_Pervasives_Native.None ->
           let uu___ = issue_identifier local_st b in
           (match uu___ with
            | (local1, lbl) ->
                build_path_labels canon_st local1 rest
                  (Prims.strcat path (Prims.strcat "_:" lbl))
                  (FStar_List_Tot_Base.op_At recursion [b])))
let rec hndq_run (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (target : RDF_Graph_Executable.bnode_id) : (Prims.string * issuer_state)=
  if fuel = Prims.int_zero
  then ("", local_st)
  else
    (let buckets =
       build_buckets_for alg target qs hfdq_table canon_st local_st [] in
     walk_buckets alg (fuel - Prims.int_one) qs hfdq_table canon_st local_st
       buckets "")
and walk_buckets (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (buckets : bucket Prims.list) (data : Prims.string) :
  (Prims.string * issuer_state)=
  match buckets with
  | [] -> ((apply_hash alg data), local_st)
  | (k, members)::rest ->
      let data1 = Prims.strcat data k in
      let perms = permutations (take_n (Prims.of_int (6)) members) in
      let uu___ =
        best_permutation alg fuel qs hfdq_table canon_st local_st perms in
      (match uu___ with
       | (best_hash, best_st) ->
           let data2 = Prims.strcat data1 best_hash in
           walk_buckets alg fuel qs hfdq_table canon_st best_st rest data2)
and best_permutation (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (perms : RDF_Graph_Executable.bnode_id Prims.list Prims.list) :
  (Prims.string * issuer_state)=
  match perms with
  | [] -> ("", local_st)
  | p::rest ->
      let uu___ = walk_perm alg fuel qs hfdq_table canon_st local_st p "" in
      (match uu___ with
       | (h, st') ->
           pick_best alg fuel qs hfdq_table canon_st local_st rest h st')
and pick_best (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st_initial : issuer_state)
  (perms : RDF_Graph_Executable.bnode_id Prims.list Prims.list)
  (best_hash : Prims.string) (best_st : issuer_state) :
  (Prims.string * issuer_state)=
  match perms with
  | [] -> (best_hash, best_st)
  | p::rest ->
      let uu___ =
        walk_perm alg fuel qs hfdq_table canon_st local_st_initial p "" in
      (match uu___ with
       | (h, st') ->
           let uu___1 =
             if (str_le h best_hash) && (h <> best_hash)
             then (h, st')
             else (best_hash, best_st) in
           (match uu___1 with
            | (best_hash', best_st') ->
                pick_best alg fuel qs hfdq_table canon_st local_st_initial
                  rest best_hash' best_st'))
and walk_perm (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (perm : RDF_Graph_Executable.bnode_id Prims.list) (path : Prims.string) :
  (Prims.string * issuer_state)=
  let uu___ = build_path_labels canon_st local_st perm path [] in
  match uu___ with
  | (path1, local1, recursion) ->
      walk_recursion alg fuel qs hfdq_table canon_st local1 recursion path1
and walk_recursion (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state) (local_st : issuer_state)
  (recursion : RDF_Graph_Executable.bnode_id Prims.list)
  (path : Prims.string) : (Prims.string * issuer_state)=
  match recursion with
  | [] -> (path, local_st)
  | b::rest ->
      let uu___ = issue_identifier local_st b in
      (match uu___ with
       | (local1, lbl) ->
           let uu___1 =
             if fuel = Prims.int_zero
             then ("", local1)
             else
               hndq_run alg (fuel - Prims.int_one) qs hfdq_table canon_st
                 local1 b in
           (match uu___1 with
            | (sub_hash, local2) ->
                walk_recursion alg fuel qs hfdq_table canon_st local2 rest
                  (Prims.strcat path
                     (Prims.strcat "_:"
                        (Prims.strcat lbl
                           (Prims.strcat "<" (Prims.strcat sub_hash ">")))))))
let hfdq_pair_le (a : bn_hfdq_pair) (b : bn_hfdq_pair) : Prims.bool=
  let uu___ = a in
  match uu___ with
  | (uu___1, ha) ->
      let uu___2 = b in (match uu___2 with | (uu___3, hb) -> str_le ha hb)
let rec group_sorted_hfdq_acc (xs : bn_hfdq_pair Prims.list)
  (cur_h : Prims.string)
  (cur_members : RDF_Graph_Executable.bnode_id Prims.list)
  (acc : bucket Prims.list) : bucket Prims.list=
  match xs with
  | [] ->
      FStar_List_Tot_Base.rev ((cur_h, (FStar_List_Tot_Base.rev cur_members))
        :: acc)
  | (b, h)::rest ->
      if h = cur_h
      then group_sorted_hfdq_acc rest cur_h (b :: cur_members) acc
      else
        group_sorted_hfdq_acc rest h [b]
          ((cur_h, (FStar_List_Tot_Base.rev cur_members)) :: acc)
let group_by_hfdq (bs : RDF_Graph_Executable.bnode_id Prims.list)
  (table : bn_hfdq_pair Prims.list) : bucket Prims.list=
  match generic_stable_sort hfdq_pair_le table with
  | [] -> []
  | (b0, h0)::rest -> group_sorted_hfdq_acc rest h0 [b0] []
let rec filter_unissued (st : issuer_state)
  (xs : RDF_Graph_Executable.bnode_id Prims.list) :
  RDF_Graph_Executable.bnode_id Prims.list=
  match xs with
  | [] -> []
  | b::rest ->
      (match lookup_issued b st.is_issued with
       | FStar_Pervasives_Native.Some uu___ -> filter_unissued st rest
       | FStar_Pervasives_Native.None -> b :: (filter_unissued st rest))
let rec explore_members (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (canon_st : issuer_state)
  (members : RDF_Graph_Executable.bnode_id Prims.list) :
  (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list)
    Prims.list=
  match members with
  | [] -> []
  | m::rest ->
      (match lookup_issued m canon_st.is_issued with
       | FStar_Pervasives_Native.Some uu___ ->
           explore_members alg fuel qs hfdq_table canon_st rest
       | FStar_Pervasives_Native.None ->
           let uu___ = issue_identifier empty_temp_issuer m in
           (match uu___ with
            | (local1, uu___1) ->
                let uu___2 =
                  hndq_run alg fuel qs hfdq_table canon_st local1 m in
                (match uu___2 with
                 | (h, local2) -> (h, (local2.is_issued)) ::
                     (explore_members alg fuel qs hfdq_table canon_st rest))))
let rec insert_result_stable
  (x :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list))
  (xs :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list) Prims.list)
  :
  (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list)
    Prims.list=
  match xs with
  | [] -> [x]
  | (k, v)::rest ->
      let uu___ = x in
      (match uu___ with
       | (xk, uu___1) ->
           if str_le k xk
           then (k, v) :: (insert_result_stable x rest)
           else x :: xs)
let rec sort_results_stable_acc
  (acc :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list) Prims.list)
  (xs :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list) Prims.list)
  :
  (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list)
    Prims.list=
  match xs with
  | [] -> acc
  | x::rest -> sort_results_stable_acc (insert_result_stable x acc) rest
let sort_results_stable
  (xs :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list) Prims.list)
  :
  (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list)
    Prims.list=
  sort_results_stable_acc [] xs
let rec replay_one (canon_st : issuer_state)
  (temp_issued : (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list) :
  issuer_state=
  match temp_issued with
  | [] -> canon_st
  | (b, uu___)::rest ->
      let uu___1 = issue_identifier canon_st b in
      (match uu___1 with | (canon_st', uu___2) -> replay_one canon_st' rest)
let rec replay_all (canon_st : issuer_state)
  (results :
    (Prims.string * (RDF_Graph_Executable.bnode_id * Prims.string)
      Prims.list) Prims.list)
  : issuer_state=
  match results with
  | [] -> canon_st
  | (uu___, temp_issued)::rest ->
      replay_all (replay_one canon_st temp_issued) rest
let process_collision_members (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (st : issuer_state) (members : RDF_Graph_Executable.bnode_id Prims.list) :
  issuer_state=
  let results = explore_members alg fuel qs hfdq_table st members in
  let sorted = sort_results_stable results in replay_all st sorted
let rec assign_singletons (st : issuer_state) (groups : bucket Prims.list) :
  issuer_state=
  match groups with
  | [] -> st
  | (uu___, b::[])::rest -> assign_singletons (issue_fresh st b) rest
  | (uu___, uu___1)::rest -> assign_singletons st rest
let rec process_collision_groups (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (st : issuer_state) (groups : bucket Prims.list) : issuer_state=
  match groups with
  | [] -> st
  | (uu___, uu___1::[])::rest ->
      process_collision_groups alg fuel qs hfdq_table st rest
  | (uu___, members)::rest ->
      let unissued = filter_unissued st members in
      let st' = process_collision_members alg fuel qs hfdq_table st unissued in
      process_collision_groups alg fuel qs hfdq_table st' rest
let walk_groups (alg : hash_algorithm) (fuel : Prims.nat)
  (qs : qquad Prims.list) (hfdq_table : bn_hfdq_pair Prims.list)
  (st : issuer_state) (groups : bucket Prims.list) : issuer_state=
  let st1 = assign_singletons st groups in
  process_collision_groups alg fuel qs hfdq_table st1 groups
let build_canonical_mapping_alg (alg : hash_algorithm)
  (ds : RDF_Graph_Executable.rdf_dataset) :
  (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list=
  let qs = dedup_qquads (dataset_quads ds) in
  let bs = dataset_bnodes ds in
  let hfdq_table = compute_all_hfdq alg qs in
  let groups = group_by_hfdq bs hfdq_table in
  let fuel = (FStar_List_Tot_Base.length bs) + Prims.int_one in
  let final_state = walk_groups alg fuel qs hfdq_table empty_issuer groups in
  let issued_count = FStar_List_Tot_Base.length final_state.is_issued in
  let bs_count = FStar_List_Tot_Base.length bs in
  let leftover =
    if issued_count = bs_count then [] else filter_unissued final_state bs in
  let leftover_pairs =
    FStar_List_Tot_Base.map (fun b -> (b, (lookup_hfdq b hfdq_table)))
      leftover in
  let leftover_sorted = sort_pairs leftover_pairs in
  let final_state' = assign_in_order final_state leftover_sorted in
  final_state'.is_issued
let build_canonical_mapping (ds : RDF_Graph_Executable.rdf_dataset) :
  (RDF_Graph_Executable.bnode_id * Prims.string) Prims.list=
  build_canonical_mapping_alg HA_SHA256 ds
let canonicalize_alg (alg : hash_algorithm)
  (ds : RDF_Graph_Executable.rdf_dataset) : RDF_Graph_Executable.rdf_dataset=
  let mapping = build_canonical_mapping_alg alg ds in
  relabel_dataset mapping ds
let canonicalize (ds : RDF_Graph_Executable.rdf_dataset) :
  RDF_Graph_Executable.rdf_dataset= canonicalize_alg HA_SHA256 ds
let rec render_quads_acc (qs : qquad Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match qs with
  | [] -> FStar_List_Tot_Base.rev acc
  | (g, t)::rest -> render_quads_acc rest ((canon_quad g t) :: acc)
let render_quads (qs : qquad Prims.list) : Prims.string Prims.list=
  render_quads_acc qs []
let rec dedup_sorted_strings_acc (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> FStar_List_Tot_Base.rev acc
  | x::[] -> FStar_List_Tot_Base.rev (x :: acc)
  | x::y::rest ->
      if x = y
      then dedup_sorted_strings_acc (y :: rest) acc
      else dedup_sorted_strings_acc (y :: rest) (x :: acc)
let dedup_sorted_strings (xs : Prims.string Prims.list) :
  Prims.string Prims.list= dedup_sorted_strings_acc xs []
let canonical_nquads (ds : RDF_Graph_Executable.rdf_dataset) : Prims.string=
  let qs = dataset_quads ds in
  let lines = render_quads qs in
  let sorted = insertion_sort lines in
  let deduped = dedup_sorted_strings sorted in concat_strings deduped
let canonicalize_to_nquads_alg (alg : hash_algorithm)
  (ds : RDF_Graph_Executable.rdf_dataset) : Prims.string=
  canonical_nquads (canonicalize_alg alg ds)
let canonicalize_to_nquads (ds : RDF_Graph_Executable.rdf_dataset) :
  Prims.string= canonicalize_to_nquads_alg HA_SHA256 ds
let canonicalize_named_graph (ds : RDF_Graph_Executable.rdf_dataset)
  (name : RDF_Dataset_Graphs.graph_ref) :
  Prims.string FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.lookup_named_graph name
          ds.RDF_Graph_Executable.ds_named
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some g ->
      FStar_Pervasives_Native.Some
        (canonicalize_to_nquads
           {
             RDF_Graph_Executable.ds_default = g;
             RDF_Graph_Executable.ds_named = []
           })
