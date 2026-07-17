open Prims
type vresult =
  | VPass 
  | VFail 
  | VUnsupported 
let uu___is_VPass (projectee : vresult) : Prims.bool=
  match projectee with | VPass -> true | uu___ -> false
let uu___is_VFail (projectee : vresult) : Prims.bool=
  match projectee with | VFail -> true | uu___ -> false
let uu___is_VUnsupported (projectee : vresult) : Prims.bool=
  match projectee with | VUnsupported -> true | uu___ -> false
let vand (a : vresult) (b : vresult) : vresult=
  match (a, b) with
  | (VFail, uu___) -> VFail
  | (uu___, VFail) -> VFail
  | (VUnsupported, uu___) -> VUnsupported
  | (uu___, VUnsupported) -> VUnsupported
  | uu___ -> VPass
let vor (a : vresult) (b : vresult) : vresult=
  match (a, b) with
  | (VPass, uu___) -> VPass
  | (uu___, VPass) -> VPass
  | (VUnsupported, uu___) -> VUnsupported
  | (uu___, VUnsupported) -> VUnsupported
  | uu___ -> VFail
let code (c : FStar_String.char) : Prims.int= FStar_Char.int_of_char c
let is_dig (c : FStar_String.char) : Prims.bool=
  let n = code c in (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let dv (c : FStar_String.char) : Prims.nat=
  let n = (code c) - (Prims.of_int (48)) in
  if (n >= Prims.int_zero) && (n <= (Prims.of_int (9)))
  then n
  else Prims.int_zero
let rec nat_of_digits (cs : FStar_String.char Prims.list) (acc : Prims.nat) :
  Prims.nat=
  match cs with
  | [] -> acc
  | c::r -> nat_of_digits r ((acc * (Prims.of_int (10))) + (dv c))
let rec pow10 (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec take_digits (cs : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)=
  match cs with
  | c::r ->
      if is_dig c
      then
        let uu___ = take_digits r in
        (match uu___ with | (ds, rest) -> ((c :: ds), rest))
      else ([], cs)
  | [] -> ([], [])
let parse_num_rational (s : Prims.string) :
  (Prims.int * Prims.pos) FStar_Pervasives_Native.option=
  let cs0 = FStar_String.list_of_string s in
  let uu___ =
    match cs0 with
    | c::r -> if c = 45 then (true, r) else (false, cs0)
    | [] -> (false, cs0) in
  match uu___ with
  | (neg, cs1) ->
      let uu___1 = take_digits cs1 in
      (match uu___1 with
       | (ipart, cs2) ->
           let uu___2 =
             match cs2 with
             | c::r -> if c = 46 then take_digits r else ([], cs2)
             | [] -> ([], cs2) in
           (match uu___2 with
            | (fpart, cs3) ->
                let k = FStar_List_Tot_Base.length fpart in
                let exp_i =
                  match cs3 with
                  | c::r ->
                      if (c = 101) || (c = 69)
                      then
                        let uu___3 =
                          match r with
                          | d::rr ->
                              if d = 43
                              then (Prims.int_one, rr)
                              else
                                if d = 45
                                then ((Prims.of_int (-1)), rr)
                                else (Prims.int_one, r)
                          | [] -> (Prims.int_one, r) in
                        (match uu___3 with
                         | (esign, r1) ->
                             let uu___4 = take_digits r1 in
                             (match uu___4 with
                              | (ed, uu___5) ->
                                  esign * (nat_of_digits ed Prims.int_zero)))
                      else Prims.int_zero
                  | [] -> Prims.int_zero in
                if
                  ((FStar_List_Tot_Base.length ipart) = Prims.int_zero) &&
                    (k = Prims.int_zero)
                then FStar_Pervasives_Native.None
                else
                  (let mag =
                     nat_of_digits (FStar_List_Tot_Base.append ipart fpart)
                       Prims.int_zero in
                   let mant = if neg then - mag else mag in
                   let eff = exp_i - k in
                   if eff >= Prims.int_zero
                   then
                     let e = eff in
                     FStar_Pervasives_Native.Some
                       ((mant * (pow10 e)), Prims.int_one)
                   else
                     (let e = - eff in
                      FStar_Pervasives_Native.Some (mant, (pow10 e))))))
let rat_lt (a : (Prims.int * Prims.pos)) (b : (Prims.int * Prims.pos)) :
  Prims.bool=
  ((FStar_Pervasives_Native.fst a) * (FStar_Pervasives_Native.snd b)) <
    ((FStar_Pervasives_Native.fst b) * (FStar_Pervasives_Native.snd a))
let rat_le (a : (Prims.int * Prims.pos)) (b : (Prims.int * Prims.pos)) :
  Prims.bool=
  ((FStar_Pervasives_Native.fst a) * (FStar_Pervasives_Native.snd b)) <=
    ((FStar_Pervasives_Native.fst b) * (FStar_Pervasives_Native.snd a))
let is_int_val (r : (Prims.int * Prims.pos)) : Prims.bool=
  let n = FStar_Pervasives_Native.fst r in
  let d = FStar_Pervasives_Native.snd r in
  (n - ((n / d) * d)) = Prims.int_zero
let is_multiple (v : (Prims.int * Prims.pos)) (d : (Prims.int * Prims.pos)) :
  Prims.bool=
  let a = (FStar_Pervasives_Native.fst v) * (FStar_Pervasives_Native.snd d) in
  let b = (FStar_Pervasives_Native.snd v) * (FStar_Pervasives_Native.fst d) in
  if b = Prims.int_zero then false else (a - ((a / b) * b)) = Prims.int_zero
let rat_floor (r : (Prims.int * Prims.pos)) : Prims.int=
  (FStar_Pervasives_Native.fst r) / (FStar_Pervasives_Native.snd r)
let num_eq (a : Prims.string) (b : Prims.string) : Prims.bool=
  match ((parse_num_rational a), (parse_num_rational b)) with
  | (FStar_Pervasives_Native.Some (n1, d1), FStar_Pervasives_Native.Some
     (n2, d2)) -> (n1 * d2) = (n2 * d1)
  | (uu___, uu___1) -> a = b
let inst_rat (v : Parser_JSON.json_val) :
  (Prims.int * Prims.pos) FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JNumber s -> parse_num_rational s
  | uu___ -> FStar_Pervasives_Native.None
let rec json_equal (a : Parser_JSON.json_val) (b : Parser_JSON.json_val)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (a, b) with
     | (Parser_JSON.JNull, Parser_JSON.JNull) -> true
     | (Parser_JSON.JBool x, Parser_JSON.JBool y) -> x = y
     | (Parser_JSON.JString x, Parser_JSON.JString y) -> x = y
     | (Parser_JSON.JNumber x, Parser_JSON.JNumber y) -> num_eq x y
     | (Parser_JSON.JArray xs, Parser_JSON.JArray ys) ->
         jeq_list xs ys (fuel - Prims.int_one)
     | (Parser_JSON.JObject xs, Parser_JSON.JObject ys) ->
         ((FStar_List_Tot_Base.length xs) = (FStar_List_Tot_Base.length ys))
           && (jeq_obj xs ys (fuel - Prims.int_one))
     | (uu___1, uu___2) -> false)
and jeq_list (xs : Parser_JSON.json_val Prims.list)
  (ys : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (xs, ys) with
     | ([], []) -> true
     | (x::xr, y::yr) ->
         (json_equal x y (fuel - Prims.int_one)) &&
           (jeq_list xr yr (fuel - Prims.int_one))
     | (uu___1, uu___2) -> false)
and jeq_obj (xs : (Prims.string * Parser_JSON.json_val) Prims.list)
  (ys : (Prims.string * Parser_JSON.json_val) Prims.list) (fuel : Prims.nat)
  : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match xs with
     | [] -> true
     | (k, v)::xr ->
         (match FStar_List_Tot_Base.find
                  (fun uu___1 -> match uu___1 with | (kk, uu___2) -> kk = k)
                  ys
          with
          | FStar_Pervasives_Native.Some (uu___1, v') ->
              (json_equal v v' (fuel - Prims.int_one)) &&
                (jeq_obj xr ys (fuel - Prims.int_one))
          | FStar_Pervasives_Native.None -> false))
let jeq (a : Parser_JSON.json_val) (b : Parser_JSON.json_val) : Prims.bool=
  json_equal a b
    (((Parser_JSON.json_size a) + (Parser_JSON.json_size b)) +
       (Prims.of_int (2)))
let rec all_unique (xs : Parser_JSON.json_val Prims.list) : Prims.bool=
  match xs with
  | [] -> true
  | h::t ->
      (Prims.op_Negation (FStar_List_Tot_Base.existsb (fun x -> jeq h x) t))
        && (all_unique t)
let rec enum_member (inst : Parser_JSON.json_val)
  (vs : Parser_JSON.json_val Prims.list) : Prims.bool=
  match vs with
  | [] -> false
  | e::tl -> (jeq inst e) || (enum_member inst tl)
let rec unescape_ptr (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | 126::49::r -> 47 :: (unescape_ptr r)
  | 126::48::r -> 126 :: (unescape_ptr r)
  | c::r -> c :: (unescape_ptr r)
  | [] -> []
let unescape_token (t : Prims.string) : Prims.string=
  FStar_String.string_of_list (unescape_ptr (FStar_String.list_of_string t))
let parse_index (t : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string t in
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | uu___ ->
      if FStar_List_Tot_Base.for_all is_dig cs
      then FStar_Pervasives_Native.Some (nat_of_digits cs Prims.int_zero)
      else FStar_Pervasives_Native.None
let rec resolve_pointer (doc : Parser_JSON.json_val)
  (toks : Prims.string Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match toks with
  | [] -> FStar_Pervasives_Native.Some doc
  | t::rest ->
      let key = unescape_token t in
      (match doc with
       | Parser_JSON.JObject fs ->
           (match FStar_List_Tot_Base.find
                    (fun uu___ -> match uu___ with | (k, uu___1) -> k = key)
                    fs
            with
            | FStar_Pervasives_Native.Some (uu___, v) ->
                resolve_pointer v rest
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | Parser_JSON.JArray xs ->
           (match parse_index key with
            | FStar_Pervasives_Native.Some i ->
                (match FStar_List_Tot_Base.nth xs i with
                 | FStar_Pervasives_Native.Some v -> resolve_pointer v rest
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
let hexv (c : FStar_String.char) : Prims.nat FStar_Pervasives_Native.option=
  let n = code c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (n - (Prims.of_int (48)))
  else
    if (n >= (Prims.of_int (97))) && (n <= (Prims.of_int (102)))
    then FStar_Pervasives_Native.Some (n - (Prims.of_int (87)))
    else
      if (n >= (Prims.of_int (65))) && (n <= (Prims.of_int (70)))
      then FStar_Pervasives_Native.Some (n - (Prims.of_int (55)))
      else FStar_Pervasives_Native.None
let rec pct_decode (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | 37::h1::h2::r ->
      (match ((hexv h1), (hexv h2)) with
       | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b) ->
           let v = (a * (Prims.of_int (16))) + b in
           (FStar_Char.char_of_int v) :: (pct_decode r)
       | (uu___, uu___1) -> 37 :: (pct_decode (h1 :: h2 :: r)))
  | c::r -> c :: (pct_decode r)
  | [] -> []
let frag_tokens (f : Prims.string) : Prims.string Prims.list=
  let decoded =
    FStar_String.string_of_list (pct_decode (FStar_String.list_of_string f)) in
  match FStar_String.split [47] decoded with
  | uu___::toks -> FStar_List_Tot_Base.map unescape_token toks
  | [] -> []
let rec split_at_hash (cs : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), FStar_Pervasives_Native.None)
  | 35::r ->
      ((FStar_List_Tot_Base.rev acc), (FStar_Pervasives_Native.Some r))
  | c::r -> split_at_hash r (c :: acc)
let split_fragment (s : Prims.string) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option)=
  match split_at_hash (FStar_String.list_of_string s) [] with
  | (before, FStar_Pervasives_Native.Some after) ->
      ((FStar_String.string_of_list before),
        (FStar_Pervasives_Native.Some (FStar_String.string_of_list after)))
  | (before, FStar_Pervasives_Native.None) ->
      ((FStar_String.string_of_list before), FStar_Pervasives_Native.None)
let base_of (s : Prims.string) : Prims.string=
  FStar_Pervasives_Native.fst (split_fragment s)
let is_alpha (c : FStar_String.char) : Prims.bool=
  let n = code c in
  ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
    ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122))))
let rec scheme_colon (cs : FStar_String.char Prims.list) : Prims.bool=
  match cs with
  | [] -> false
  | 58::uu___ -> true
  | c::r ->
      if ((c = 47) || (c = 63)) || (c = 35) then false else scheme_colon r
let is_absolute_ref (s : Prims.string) : Prims.bool=
  match FStar_String.list_of_string s with
  | c::uu___ ->
      (is_alpha c) && (scheme_colon (FStar_String.list_of_string s))
  | [] -> false
let rec take_to_slash (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with | [] -> [] | 47::uu___ -> [] | c::r -> c :: (take_to_slash r)
let rec take_to_colon (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with | [] -> [] | 58::uu___ -> [] | c::r -> c :: (take_to_colon r)
let rec split_scheme_sep (cs : FStar_String.char Prims.list)
  (acc : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)
    FStar_Pervasives_Native.option=
  match cs with
  | 58::47::47::r ->
      FStar_Pervasives_Native.Some ((FStar_List_Tot_Base.rev acc), r)
  | c::r -> split_scheme_sep r (c :: acc)
  | [] -> FStar_Pervasives_Native.None
let scheme_authority (base : Prims.string) : Prims.string=
  match split_scheme_sep (FStar_String.list_of_string (base_of base)) [] with
  | FStar_Pervasives_Native.Some (sch, rest) ->
      Prims.strcat (FStar_String.string_of_list sch)
        (Prims.strcat "://"
           (FStar_String.string_of_list (take_to_slash rest)))
  | FStar_Pervasives_Native.None -> base_of base
let scheme_prefix (base : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (take_to_colon (FStar_String.list_of_string (base_of base)))
let rec dir_prefix (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | [] -> []
  | c::r ->
      if FStar_List_Tot_Base.mem 47 r
      then c :: (dir_prefix r)
      else if c = 47 then [47] else []
let base_dir (base : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (dir_prefix (FStar_String.list_of_string (base_of base)))
let resolve_uri (base : Prims.string) (r : Prims.string) : Prims.string=
  if r = ""
  then base_of base
  else
    if is_absolute_ref r
    then r
    else
      (match FStar_String.list_of_string r with
       | 35::uu___2 -> Prims.strcat (base_of base) r
       | 47::47::uu___2 ->
           Prims.strcat (scheme_prefix base) (Prims.strcat ":" r)
       | 47::uu___2 -> Prims.strcat (scheme_authority base) r
       | uu___2 -> Prims.strcat (base_dir base) r)
let id_base (base : Prims.string) (idval : Prims.string) : Prims.string=
  base_of (resolve_uri base idval)
type refctx =
  {
  idreg: (Prims.string * Parser_JSON.json_val) Prims.list ;
  anchreg: (Prims.string * Parser_JSON.json_val) Prims.list }
let __proj__Mkrefctx__item__idreg (projectee : refctx) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with | { idreg; anchreg;_} -> idreg
let __proj__Mkrefctx__item__anchreg (projectee : refctx) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with | { idreg; anchreg;_} -> anchreg
let rec lookup_reg (k : Prims.string)
  (l : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match l with
  | [] -> FStar_Pervasives_Native.None
  | (kk, v)::tl ->
      if kk = k then FStar_Pervasives_Native.Some v else lookup_reg k tl
let frag_is_pointer (f : Prims.string) : Prims.bool=
  match FStar_String.list_of_string f with | c::uu___ -> c = 47 | [] -> false
let resolve_ref (ctx : refctx) (base : Prims.string) (r : Prims.string) :
  (Parser_JSON.json_val * Prims.string) FStar_Pervasives_Native.option=
  let target = resolve_uri base r in
  match split_fragment target with
  | (tbase, FStar_Pervasives_Native.None) ->
      (match lookup_reg tbase ctx.idreg with
       | FStar_Pervasives_Native.Some n ->
           FStar_Pervasives_Native.Some (n, tbase)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (tbase, FStar_Pervasives_Native.Some f) ->
      if f = ""
      then
        (match lookup_reg tbase ctx.idreg with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (n, tbase)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if frag_is_pointer f
        then
          (match lookup_reg tbase ctx.idreg with
           | FStar_Pervasives_Native.Some doc ->
               (match resolve_pointer doc (frag_tokens f) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some (n, tbase)
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else
          (match lookup_reg target ctx.anchreg with
           | FStar_Pervasives_Native.Some n ->
               FStar_Pervasives_Native.Some (n, tbase)
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec collect_ids (base : Prims.string) (node : Parser_JSON.json_val)
  (fuel : Prims.nat) :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  if fuel = Prims.int_zero
  then ([], [])
  else
    (match node with
     | Parser_JSON.JObject fs ->
         let uu___1 =
           match Parser_JSON.json_get_field "$id" node with
           | FStar_Pervasives_Native.Some (Parser_JSON.JString v) ->
               let resolved = resolve_uri base v in
               (match split_fragment resolved with
                | (rb, FStar_Pervasives_Native.Some a) ->
                    if (rb = base) && (a <> "")
                    then (base, [], [(resolved, node)])
                    else
                      (rb, [(rb, node)],
                        (if a = "" then [] else [(resolved, node)]))
                | (rb, FStar_Pervasives_Native.None) ->
                    (rb, [(rb, node)], []))
           | uu___2 -> (base, [], []) in
         (match uu___1 with
          | (nbase, sids, sanch) ->
              let uu___2 = collect_ids_fields nbase fs (fuel - Prims.int_one) in
              (match uu___2 with
               | (cids, canch) ->
                   ((FStar_List_Tot_Base.append sids cids),
                     (FStar_List_Tot_Base.append sanch canch))))
     | Parser_JSON.JArray xs ->
         collect_ids_list base xs (fuel - Prims.int_one)
     | uu___1 -> ([], []))
and collect_ids_fields (base : Prims.string)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) (fuel : Prims.nat)
  :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  if fuel = Prims.int_zero
  then ([], [])
  else
    (match fs with
     | [] -> ([], [])
     | (uu___1, v)::tl ->
         let uu___2 = collect_ids base v (fuel - Prims.int_one) in
         (match uu___2 with
          | (a1, b1) ->
              let uu___3 = collect_ids_fields base tl (fuel - Prims.int_one) in
              (match uu___3 with
               | (a2, b2) ->
                   ((FStar_List_Tot_Base.append a1 a2),
                     (FStar_List_Tot_Base.append b1 b2)))))
and collect_ids_list (base : Prims.string)
  (xs : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  if fuel = Prims.int_zero
  then ([], [])
  else
    (match xs with
     | [] -> ([], [])
     | v::tl ->
         let uu___1 = collect_ids base v (fuel - Prims.int_one) in
         (match uu___1 with
          | (a1, b1) ->
              let uu___2 = collect_ids_list base tl (fuel - Prims.int_one) in
              (match uu___2 with
               | (a2, b2) ->
                   ((FStar_List_Tot_Base.append a1 a2),
                     (FStar_List_Tot_Base.append b1 b2)))))
let last_dollar (cs : FStar_String.char Prims.list) : Prims.bool=
  match FStar_List_Tot_Base.rev cs with
  | 36::92::uu___ -> false
  | 36::uu___ -> true
  | uu___ -> false
let ecma_match (pat : Prims.string) (s : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  let pchars = FStar_String.list_of_string pat in
  let starts = match pchars with | c::uu___ -> c = 94 | [] -> false in
  let ends = last_dollar pchars in
  match Regex_XSDPattern.parse_xsd_pattern pat with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some r ->
      let scs = Regex_XSDPattern.cps_of_string s in
      let re =
        if starts && ends
        then r
        else
          if starts
          then Regex_Syntax.R_Cat (r, Regex_Exec.dot_star)
          else
            if ends
            then Regex_Syntax.R_Cat (Regex_Exec.dot_star, r)
            else Regex_Exec.contains r in
      FStar_Pervasives_Native.Some (Regex_Exec.matches_norm re scs)
let rec key_matches_any (k : Prims.string) (pats : Prims.string Prims.list) :
  Prims.bool=
  match pats with
  | [] -> false
  | p::tl ->
      (match ecma_match p k with
       | FStar_Pervasives_Native.Some true -> true
       | uu___ -> key_matches_any k tl)
let pattern_bad (schema : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_field "pattern" schema with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString p) ->
      FStar_Pervasives_Native.uu___is_None
        (Regex_XSDPattern.parse_xsd_pattern p)
  | FStar_Pervasives_Native.Some uu___ -> true
  | FStar_Pervasives_Native.None -> false
let rec any_pat_unparseable
  (pps : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match pps with
  | [] -> false
  | (r, uu___)::tl ->
      (FStar_Pervasives_Native.uu___is_None
         (Regex_XSDPattern.parse_xsd_pattern r))
        || (any_pat_unparseable tl)
let patprops_bad (schema : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_field "patternProperties" schema with
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject pps) ->
      any_pat_unparseable pps
  | FStar_Pervasives_Native.Some uu___ -> true
  | FStar_Pervasives_Native.None -> false
let inst_matches_type (v : Parser_JSON.json_val) (t : Prims.string) :
  Prims.bool=
  match t with
  | "null" -> Parser_JSON.uu___is_JNull v
  | "boolean" -> Parser_JSON.uu___is_JBool v
  | "string" -> Parser_JSON.uu___is_JString v
  | "object" -> Parser_JSON.uu___is_JObject v
  | "array" -> Parser_JSON.uu___is_JArray v
  | "number" -> Parser_JSON.uu___is_JNumber v
  | "integer" ->
      (match v with
       | Parser_JSON.JNumber s ->
           (match parse_num_rational s with
            | FStar_Pervasives_Native.Some r -> is_int_val r
            | FStar_Pervasives_Native.None -> false)
       | uu___ -> false)
  | uu___ -> false
let type_ok (v : Parser_JSON.json_val) (tv : Parser_JSON.json_val) :
  Prims.bool=
  match tv with
  | Parser_JSON.JString t -> inst_matches_type v t
  | uu___ -> false
let lookup (k : Prims.string)
  (l : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun uu___ -> match uu___ with | (kk, uu___1) -> kk = k) l
  with
  | FStar_Pervasives_Native.Some (uu___, v) -> FStar_Pervasives_Native.Some v
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let has_key (k : Prims.string)
  (l : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (lookup k l)
let rec drop_n : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then l
    else
      (match l with | [] -> [] | uu___1::t -> drop_n (n - Prims.int_one) t)
let rec zip_pairs :
  'a 'b . 'a Prims.list -> 'b Prims.list -> ('a * 'b) Prims.list =
  fun xs ys ->
    match (xs, ys) with
    | (x::xr, y::yr) -> (x, y) :: (zip_pairs xr yr)
    | (uu___, uu___1) -> []
let names_present (fs : (Prims.string * Parser_JSON.json_val) Prims.list)
  (names : Parser_JSON.json_val Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun nv ->
       match nv with | Parser_JSON.JString n -> has_key n fs | uu___ -> false)
    names
let check_local (schema : Parser_JSON.json_val) (inst : Parser_JSON.json_val)
  : vresult=
  let get k = Parser_JSON.json_get_field k schema in
  let c_type =
    match get "type" with
    | FStar_Pervasives_Native.None -> VPass
    | FStar_Pervasives_Native.Some (Parser_JSON.JString t) ->
        if inst_matches_type inst t then VPass else VFail
    | FStar_Pervasives_Native.Some (Parser_JSON.JArray ts) ->
        if FStar_List_Tot_Base.existsb (type_ok inst) ts
        then VPass
        else VFail
    | FStar_Pervasives_Native.Some uu___ -> VUnsupported in
  let c_enum =
    match get "enum" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JArray vs) ->
        if enum_member inst vs then VPass else VFail
    | uu___ -> VPass in
  let c_const =
    match get "const" with
    | FStar_Pervasives_Native.Some cv -> if jeq inst cv then VPass else VFail
    | FStar_Pervasives_Native.None -> VPass in
  let c_required =
    match ((get "required"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JArray names),
       Parser_JSON.JObject fs) ->
        if names_present fs names then VPass else VFail
    | (uu___, uu___1) -> VPass in
  let c_minprops =
    match ((get "minProperties"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JObject fs) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if (FStar_List_Tot_Base.length fs) >= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  let c_maxprops =
    match ((get "maxProperties"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JObject fs) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if (FStar_List_Tot_Base.length fs) <= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  let c_minitems =
    match ((get "minItems"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JArray xs) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if (FStar_List_Tot_Base.length xs) >= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  let c_maxitems =
    match ((get "maxItems"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JArray xs) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if (FStar_List_Tot_Base.length xs) <= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  let c_uniq =
    match ((get "uniqueItems"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JBool true),
       Parser_JSON.JArray xs) -> if all_unique xs then VPass else VFail
    | (uu___, uu___1) -> VPass in
  let c_min =
    match get "minimum" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JNumber ms) ->
        (match ((inst_rat inst), (parse_num_rational ms)) with
         | (FStar_Pervasives_Native.Some iv, FStar_Pervasives_Native.Some mv)
             -> if rat_le mv iv then VPass else VFail
         | (uu___, uu___1) -> VPass)
    | uu___ -> VPass in
  let c_max =
    match get "maximum" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JNumber xs) ->
        (match ((inst_rat inst), (parse_num_rational xs)) with
         | (FStar_Pervasives_Native.Some iv, FStar_Pervasives_Native.Some xv)
             -> if rat_le iv xv then VPass else VFail
         | (uu___, uu___1) -> VPass)
    | uu___ -> VPass in
  let c_exmin =
    match get "exclusiveMinimum" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JNumber ms) ->
        (match ((inst_rat inst), (parse_num_rational ms)) with
         | (FStar_Pervasives_Native.Some iv, FStar_Pervasives_Native.Some mv)
             -> if rat_lt mv iv then VPass else VFail
         | (uu___, uu___1) -> VPass)
    | uu___ -> VPass in
  let c_exmax =
    match get "exclusiveMaximum" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JNumber xs) ->
        (match ((inst_rat inst), (parse_num_rational xs)) with
         | (FStar_Pervasives_Native.Some iv, FStar_Pervasives_Native.Some xv)
             -> if rat_lt iv xv then VPass else VFail
         | (uu___, uu___1) -> VPass)
    | uu___ -> VPass in
  let c_mult =
    match get "multipleOf" with
    | FStar_Pervasives_Native.Some (Parser_JSON.JNumber ds) ->
        (match ((inst_rat inst), (parse_num_rational ds)) with
         | (FStar_Pervasives_Native.Some iv, FStar_Pervasives_Native.Some
            dvr) -> if is_multiple iv dvr then VPass else VFail
         | (uu___, uu___1) -> VPass)
    | uu___ -> VPass in
  let c_minlen =
    match ((get "minLength"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JString str) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if
               (FStar_List_Tot_Base.length (FStar_String.list_of_string str))
                 >= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  let c_maxlen =
    match ((get "maxLength"), inst) with
    | (FStar_Pervasives_Native.Some (Parser_JSON.JNumber s),
       Parser_JSON.JString str) ->
        (match parse_num_rational s with
         | FStar_Pervasives_Native.Some r ->
             if
               (FStar_List_Tot_Base.length (FStar_String.list_of_string str))
                 <= (rat_floor r)
             then VPass
             else VFail
         | FStar_Pervasives_Native.None -> VPass)
    | (uu___, uu___1) -> VPass in
  FStar_List_Tot_Base.fold_left vand VPass
    [c_type;
    c_enum;
    c_const;
    c_required;
    c_minprops;
    c_maxprops;
    c_minitems;
    c_maxitems;
    c_uniq;
    c_min;
    c_max;
    c_exmin;
    c_exmax;
    c_mult;
    c_minlen;
    c_maxlen]
let rec validate_schema (ctx : refctx) (base : Prims.string)
  (schema : Parser_JSON.json_val) (inst : Parser_JSON.json_val)
  (fuel : Prims.nat) : vresult=
  if fuel = Prims.int_zero
  then VUnsupported
  else
    (let f1 = fuel - Prims.int_one in
     match schema with
     | Parser_JSON.JBool true -> VPass
     | Parser_JSON.JBool false -> VFail
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_field "$ref" schema with
          | FStar_Pervasives_Native.Some (Parser_JSON.JString r) ->
              (match resolve_ref ctx base r with
               | FStar_Pervasives_Native.None -> VUnsupported
               | FStar_Pervasives_Native.Some (sub, nbase) ->
                   validate_schema ctx nbase sub inst f1)
          | FStar_Pervasives_Native.Some uu___2 -> VUnsupported
          | FStar_Pervasives_Native.None ->
              let get k = Parser_JSON.json_get_field k schema in
              let base1 =
                match get "$id" with
                | FStar_Pervasives_Native.Some (Parser_JSON.JString i) ->
                    id_base base i
                | uu___2 -> base in
              if
                ((FStar_Pervasives_Native.uu___is_Some (get "format")) ||
                   (pattern_bad schema))
                  || (patprops_bad schema)
              then VUnsupported
              else
                (let c_local = check_local schema inst in
                 let c_pattern =
                   match ((get "pattern"), inst) with
                   | (FStar_Pervasives_Native.Some (Parser_JSON.JString p),
                      Parser_JSON.JString s) ->
                       (match ecma_match p s with
                        | FStar_Pervasives_Native.Some true -> VPass
                        | FStar_Pervasives_Native.Some false -> VFail
                        | FStar_Pervasives_Native.None -> VUnsupported)
                   | (uu___3, uu___4) -> VPass in
                 let c_props =
                   match ((get "properties"), inst) with
                   | (FStar_Pervasives_Native.Some (Parser_JSON.JObject ps),
                      Parser_JSON.JObject fs) ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_props ctx base1 ps fs f1)
                   | (uu___3, uu___4) -> VPass in
                 let c_patprops =
                   match ((get "patternProperties"), inst) with
                   | (FStar_Pervasives_Native.Some (Parser_JSON.JObject pps),
                      Parser_JSON.JObject fs) ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_patprops ctx base1 pps fs f1)
                   | (uu___3, uu___4) -> VPass in
                 let c_addprops =
                   match ((get "additionalProperties"), inst) with
                   | (FStar_Pervasives_Native.Some ap, Parser_JSON.JObject
                      fs) ->
                       let declared =
                         match get "properties" with
                         | FStar_Pervasives_Native.Some (Parser_JSON.JObject
                             ps) ->
                             FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst ps
                         | uu___3 -> [] in
                       let pats =
                         match get "patternProperties" with
                         | FStar_Pervasives_Native.Some (Parser_JSON.JObject
                             pps) ->
                             FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst pps
                         | uu___3 -> [] in
                       let extra =
                         FStar_List_Tot_Base.filter
                           (fun uu___3 ->
                              match uu___3 with
                              | (k, uu___4) ->
                                  (Prims.op_Negation
                                     (FStar_List_Tot_Base.mem k declared))
                                    &&
                                    (Prims.op_Negation
                                       (key_matches_any k pats))) fs in
                       (match ap with
                        | Parser_JSON.JBool true -> VPass
                        | Parser_JSON.JBool false ->
                            (match extra with | [] -> VPass | uu___3 -> VFail)
                        | uu___3 ->
                            FStar_List_Tot_Base.fold_left vand VPass
                              (results_over_instances ctx base1 ap
                                 (FStar_List_Tot_Base.map
                                    FStar_Pervasives_Native.snd extra) f1))
                   | (uu___3, uu___4) -> VPass in
                 let c_propnames =
                   match ((get "propertyNames"), inst) with
                   | (FStar_Pervasives_Native.Some pn, Parser_JSON.JObject
                      fs) ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_over_instances ctx base1 pn
                            (FStar_List_Tot_Base.map
                               (fun uu___3 ->
                                  match uu___3 with
                                  | (k, uu___4) -> Parser_JSON.JString k) fs)
                            f1)
                   | (uu___3, uu___4) -> VPass in
                 let c_deps =
                   match ((get "dependencies"), inst) with
                   | (FStar_Pervasives_Native.Some (Parser_JSON.JObject
                      deps), Parser_JSON.JObject fs) ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_deps ctx base1 deps fs inst f1)
                   | (uu___3, uu___4) -> VPass in
                 let c_items =
                   match ((get "items"), inst) with
                   | (FStar_Pervasives_Native.Some (Parser_JSON.JArray subs),
                      Parser_JSON.JArray xs) ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_pairs ctx base1 (zip_pairs subs xs) f1)
                   | (FStar_Pervasives_Native.Some sub, Parser_JSON.JArray
                      xs) ->
                       if
                         (Parser_JSON.uu___is_JObject sub) ||
                           (Parser_JSON.uu___is_JBool sub)
                       then
                         FStar_List_Tot_Base.fold_left vand VPass
                           (results_over_instances ctx base1 sub xs f1)
                       else VPass
                   | (uu___3, uu___4) -> VPass in
                 let c_additems =
                   match ((get "additionalItems"), (get "items"), inst) with
                   | (FStar_Pervasives_Native.Some ai,
                      FStar_Pervasives_Native.Some (Parser_JSON.JArray subs),
                      Parser_JSON.JArray xs) ->
                       let extra =
                         drop_n (FStar_List_Tot_Base.length subs) xs in
                       (match ai with
                        | Parser_JSON.JBool true -> VPass
                        | Parser_JSON.JBool false ->
                            (match extra with | [] -> VPass | uu___3 -> VFail)
                        | uu___3 ->
                            FStar_List_Tot_Base.fold_left vand VPass
                              (results_over_instances ctx base1 ai extra f1))
                   | (uu___3, uu___4, uu___5) -> VPass in
                 let c_contains =
                   match ((get "contains"), inst) with
                   | (FStar_Pervasives_Native.Some sub, Parser_JSON.JArray
                      xs) ->
                       let rs = results_over_instances ctx base1 sub xs f1 in
                       if FStar_List_Tot_Base.existsb (fun r -> r = VPass) rs
                       then VPass
                       else
                         if
                           FStar_List_Tot_Base.existsb
                             (fun r -> r = VUnsupported) rs
                         then VUnsupported
                         else VFail
                   | (uu___3, uu___4) -> VPass in
                 let c_allof =
                   match get "allOf" with
                   | FStar_Pervasives_Native.Some (Parser_JSON.JArray subs)
                       ->
                       FStar_List_Tot_Base.fold_left vand VPass
                         (results_over_schemas ctx base1 subs inst f1)
                   | uu___3 -> VPass in
                 let c_anyof =
                   match get "anyOf" with
                   | FStar_Pervasives_Native.Some (Parser_JSON.JArray subs)
                       ->
                       FStar_List_Tot_Base.fold_left vor VFail
                         (results_over_schemas ctx base1 subs inst f1)
                   | uu___3 -> VPass in
                 let c_oneof =
                   match get "oneOf" with
                   | FStar_Pervasives_Native.Some (Parser_JSON.JArray subs)
                       ->
                       let rs = results_over_schemas ctx base1 subs inst f1 in
                       if
                         FStar_List_Tot_Base.existsb
                           (fun r -> r = VUnsupported) rs
                       then VUnsupported
                       else
                         if
                           (FStar_List_Tot_Base.length
                              (FStar_List_Tot_Base.filter
                                 (fun r -> r = VPass) rs))
                             = Prims.int_one
                         then VPass
                         else VFail
                   | uu___3 -> VPass in
                 let c_not =
                   match get "not" with
                   | FStar_Pervasives_Native.Some s ->
                       (match validate_schema ctx base1 s inst f1 with
                        | VPass -> VFail
                        | VFail -> VPass
                        | VUnsupported -> VUnsupported)
                   | FStar_Pervasives_Native.None -> VPass in
                 let c_ite =
                   match get "if" with
                   | FStar_Pervasives_Native.None -> VPass
                   | FStar_Pervasives_Native.Some ci ->
                       (match validate_schema ctx base1 ci inst f1 with
                        | VUnsupported -> VUnsupported
                        | VPass ->
                            (match get "then" with
                             | FStar_Pervasives_Native.Some t ->
                                 validate_schema ctx base1 t inst f1
                             | FStar_Pervasives_Native.None -> VPass)
                        | VFail ->
                            (match get "else" with
                             | FStar_Pervasives_Native.Some e ->
                                 validate_schema ctx base1 e inst f1
                             | FStar_Pervasives_Native.None -> VPass)) in
                 FStar_List_Tot_Base.fold_left vand VPass
                   [c_local;
                   c_pattern;
                   c_props;
                   c_patprops;
                   c_addprops;
                   c_propnames;
                   c_deps;
                   c_items;
                   c_additems;
                   c_contains;
                   c_allof;
                   c_anyof;
                   c_oneof;
                   c_not;
                   c_ite]))
     | uu___1 -> VUnsupported)
and results_over_instances (ctx : refctx) (base : Prims.string)
  (sub : Parser_JSON.json_val) (xs : Parser_JSON.json_val Prims.list)
  (fuel : Prims.nat) : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match xs with
     | [] -> []
     | x::tl -> (validate_schema ctx base sub x (fuel - Prims.int_one)) ::
         (results_over_instances ctx base sub tl (fuel - Prims.int_one)))
and results_over_schemas (ctx : refctx) (base : Prims.string)
  (subs : Parser_JSON.json_val Prims.list) (inst : Parser_JSON.json_val)
  (fuel : Prims.nat) : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match subs with
     | [] -> []
     | s::tl -> (validate_schema ctx base s inst (fuel - Prims.int_one)) ::
         (results_over_schemas ctx base tl inst (fuel - Prims.int_one)))
and results_props (ctx : refctx) (base : Prims.string)
  (ps : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) (fuel : Prims.nat)
  : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match ps with
     | [] -> []
     | (pn, psub)::tl ->
         let rest = results_props ctx base tl fs (fuel - Prims.int_one) in
         (match lookup pn fs with
          | FStar_Pervasives_Native.Some pv ->
              (validate_schema ctx base psub pv (fuel - Prims.int_one)) ::
              rest
          | FStar_Pervasives_Native.None -> rest))
and results_patprops (ctx : refctx) (base : Prims.string)
  (pps : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) (fuel : Prims.nat)
  : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match pps with
     | [] -> []
     | (rgx, sub)::tl ->
         FStar_List_Tot_Base.append
           (results_patprop_one ctx base rgx sub fs (fuel - Prims.int_one))
           (results_patprops ctx base tl fs (fuel - Prims.int_one)))
and results_patprop_one (ctx : refctx) (base : Prims.string)
  (rgx : Prims.string) (sub : Parser_JSON.json_val)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) (fuel : Prims.nat)
  : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match fs with
     | [] -> []
     | (k, v)::tl ->
         let rest =
           results_patprop_one ctx base rgx sub tl (fuel - Prims.int_one) in
         (match ecma_match rgx k with
          | FStar_Pervasives_Native.Some true ->
              (validate_schema ctx base sub v (fuel - Prims.int_one)) :: rest
          | FStar_Pervasives_Native.Some false -> rest
          | FStar_Pervasives_Native.None -> VUnsupported :: rest))
and results_pairs (ctx : refctx) (base : Prims.string)
  (pairs : (Parser_JSON.json_val * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match pairs with
     | [] -> []
     | (sub, x)::tl ->
         (validate_schema ctx base sub x (fuel - Prims.int_one)) ::
         (results_pairs ctx base tl (fuel - Prims.int_one)))
and results_deps (ctx : refctx) (base : Prims.string)
  (deps : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list)
  (inst : Parser_JSON.json_val) (fuel : Prims.nat) : vresult Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match deps with
     | [] -> []
     | (pn, dv2)::tl ->
         let rest = results_deps ctx base tl fs inst (fuel - Prims.int_one) in
         if has_key pn fs
         then
           (match dv2 with
            | Parser_JSON.JArray names ->
                (if names_present fs names then VPass else VFail) :: rest
            | uu___1 ->
                (validate_schema ctx base dv2 inst (fuel - Prims.int_one)) ::
                rest)
         else rest)
let rec collect_externals
  (externals : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  match externals with
  | [] -> ([], [])
  | (u, doc)::tl ->
      let uu___ = collect_ids (base_of u) doc fuel in
      (match uu___ with
       | (a1, b1) ->
           let uu___1 = collect_externals tl fuel in
           (match uu___1 with
            | (a2, b2) ->
                ((FStar_List_Tot_Base.append ((u, doc) :: a1) a2),
                  (FStar_List_Tot_Base.append b1 b2))))
let root_base_of (schema : Parser_JSON.json_val) : Prims.string=
  match Parser_JSON.json_get_field "$id" schema with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString i) ->
      base_of (resolve_uri "" i)
  | uu___ -> ""
let build_ctx (externals : (Prims.string * Parser_JSON.json_val) Prims.list)
  (schema : Parser_JSON.json_val) : refctx=
  let rb = root_base_of schema in
  let cf =
    (Prims.of_int (100)) +
      ((Prims.of_int (4)) * (Parser_JSON.json_size schema)) in
  let uu___ = collect_ids rb schema cf in
  match uu___ with
  | (sids, sanch) ->
      let uu___1 = collect_externals externals cf in
      (match uu___1 with
       | (eids, eanch) ->
           let base_reg = ("", schema) ::
             (if rb = "" then [] else [(rb, schema)]) in
           {
             idreg =
               (FStar_List_Tot_Base.append base_reg
                  (FStar_List_Tot_Base.append sids eids));
             anchreg = (FStar_List_Tot_Base.append sanch eanch)
           })
let validate_ext
  (externals : (Prims.string * Parser_JSON.json_val) Prims.list)
  (schema : Parser_JSON.json_val) (inst : Parser_JSON.json_val) : vresult=
  let ctx = build_ctx externals schema in
  let n =
    ((Parser_JSON.json_size schema) + (Parser_JSON.json_size inst)) +
      (Prims.of_int (10)) in
  validate_schema ctx (root_base_of schema) schema inst
    ((n * n) + (Prims.of_int (5000)))
let validate (schema : Parser_JSON.json_val) (inst : Parser_JSON.json_val) :
  vresult= validate_ext [] schema inst
let validate_bool (schema : Parser_JSON.json_val)
  (inst : Parser_JSON.json_val) : Prims.bool=
  match validate schema inst with | VPass -> true | uu___ -> false
