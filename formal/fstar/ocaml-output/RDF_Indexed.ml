open Prims
type 'a bucket_map = (Prims.string * 'a Prims.list) Prims.list
let rec bucket_lookup : 'a . 'a bucket_map -> Prims.string -> 'a Prims.list =
  fun m k ->
    match m with
    | [] -> []
    | (k', v)::rest -> if k = k' then v else bucket_lookup rest k
let rec bucket_replace_acc :
  'a .
    'a bucket_map ->
      'a bucket_map -> Prims.string -> 'a Prims.list -> 'a bucket_map
  =
  fun acc m k v ->
    match m with
    | [] -> FStar_List_Tot_Base.rev_acc acc [(k, v)]
    | (k', v')::rest ->
        if k = k'
        then FStar_List_Tot_Base.rev_acc acc ((k, v) :: rest)
        else bucket_replace_acc ((k', v') :: acc) rest k v
let bucket_replace (m : 'a bucket_map) (k : Prims.string) (v : 'a Prims.list)
  : 'a bucket_map= bucket_replace_acc [] m k v
let bucket_push (m : 'a bucket_map) (k : Prims.string) (t : 'a) :
  'a bucket_map= bucket_replace m k (t :: (bucket_lookup m k))
let cmp_by_key (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (t1 : 'a) (t2 : 'a) : Prims.int=
  match ((key_of t1), (key_of t2)) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      Prims.int_zero
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
      (Prims.of_int (-1))
  | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
      Prims.int_one
  | (FStar_Pervasives_Native.Some k1, FStar_Pervasives_Native.Some k2) ->
      FStar_String.compare k1 k2
let rec group_sorted_aux :
  'a .
    ('a -> Prims.string FStar_Pervasives_Native.option) ->
      'a Prims.list ->
        Prims.string FStar_Pervasives_Native.option ->
          'a Prims.list -> 'a bucket_map -> 'a bucket_map
  =
  fun key_of ts cur_key cur_bucket acc ->
    match ts with
    | [] ->
        (match cur_key with
         | FStar_Pervasives_Native.Some k -> (k, cur_bucket) :: acc
         | FStar_Pervasives_Native.None -> acc)
    | t::rest ->
        (match key_of t with
         | FStar_Pervasives_Native.None ->
             group_sorted_aux key_of rest cur_key cur_bucket acc
         | FStar_Pervasives_Native.Some k ->
             (match cur_key with
              | FStar_Pervasives_Native.Some k0 ->
                  if k = k0
                  then
                    group_sorted_aux key_of rest cur_key (t :: cur_bucket)
                      acc
                  else
                    group_sorted_aux key_of rest
                      (FStar_Pervasives_Native.Some k) [t] ((k0, cur_bucket)
                      :: acc)
              | FStar_Pervasives_Native.None ->
                  group_sorted_aux key_of rest
                    (FStar_Pervasives_Native.Some k) [t] acc))
let build_bucket (key_of : 'a -> Prims.string FStar_Pervasives_Native.option)
  (ts : 'a Prims.list) : 'a bucket_map=
  let sorted = FStar_List_Tot_Base.sortWith (cmp_by_key key_of) ts in
  group_sorted_aux key_of sorted FStar_Pervasives_Native.None [] []
