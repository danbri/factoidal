open Prims
type query_entry =
  {
  qe_group: Prims.string ;
  qe_key: Prims.string ;
  qe_label: Prims.string ;
  qe_body: Prims.string }
let __proj__Mkquery_entry__item__qe_group (projectee : query_entry) :
  Prims.string=
  match projectee with | { qe_group; qe_key; qe_label; qe_body;_} -> qe_group
let __proj__Mkquery_entry__item__qe_key (projectee : query_entry) :
  Prims.string=
  match projectee with | { qe_group; qe_key; qe_label; qe_body;_} -> qe_key
let __proj__Mkquery_entry__item__qe_label (projectee : query_entry) :
  Prims.string=
  match projectee with | { qe_group; qe_key; qe_label; qe_body;_} -> qe_label
let __proj__Mkquery_entry__item__qe_body (projectee : query_entry) :
  Prims.string=
  match projectee with | { qe_group; qe_key; qe_label; qe_body;_} -> qe_body
type query_group =
  {
  qg_name: Prims.string ;
  qg_entries: query_entry Prims.list }
let __proj__Mkquery_group__item__qg_name (projectee : query_group) :
  Prims.string= match projectee with | { qg_name; qg_entries;_} -> qg_name
let __proj__Mkquery_group__item__qg_entries (projectee : query_group) :
  query_entry Prims.list=
  match projectee with | { qg_name; qg_entries;_} -> qg_entries
let strip_rq_suffix (s : Prims.string) : Prims.string=
  let len = Parser_FastString.fs_byte_length s in
  if len < (Prims.of_int (3))
  then s
  else
    (let b0 = Parser_FastString.fs_byte_at s (len - (Prims.of_int (3))) in
     let b1 = Parser_FastString.fs_byte_at s (len - (Prims.of_int (2))) in
     let b2 = Parser_FastString.fs_byte_at s (len - Prims.int_one) in
     if
       ((b0 = (Prims.of_int (0x2E))) && (b1 = (Prims.of_int (0x72)))) &&
         (b2 = (Prims.of_int (0x71)))
     then
       Parser_FastString.fs_byte_sub s Prims.int_zero
         (len - (Prims.of_int (3)))
     else s)
let parliament_label (group : Prims.string) (filename : Prims.string) :
  Prims.string=
  Prims.strcat group (Prims.strcat " / " (strip_rq_suffix filename))
let render_entry_chars (e : query_entry) : Prims.string=
  Prims.strcat "  {\"group\":\""
    (Prims.strcat (SPARQL_JSON_Escape.json_escape e.qe_group)
       (Prims.strcat "\",\"key\":\""
          (Prims.strcat (SPARQL_JSON_Escape.json_escape e.qe_key)
             (Prims.strcat "\",\"label\":\""
                (Prims.strcat (SPARQL_JSON_Escape.json_escape e.qe_label)
                   (Prims.strcat "\",\"body\":\""
                      (Prims.strcat
                         (SPARQL_JSON_Escape.json_escape e.qe_body) "\"}")))))))
let rec render_entries_acc (entries : query_entry Prims.list)
  (first : Prims.bool) (acc : Prims.string) : Prims.string=
  match entries with
  | [] -> acc
  | e::rest ->
      let sep = if first then "\n" else ",\n" in
      let acc' = Prims.strcat acc (Prims.strcat sep (render_entry_chars e)) in
      render_entries_acc rest false acc'
let render_queries_index (entries : query_entry Prims.list) : Prims.string=
  let body = render_entries_acc entries true "" in
  Prims.strcat "[" (Prims.strcat body "\n]\n")
let rec flatten_groups (groups : query_group Prims.list) :
  query_entry Prims.list=
  match groups with
  | [] -> []
  | g::rest -> FStar_List_Tot_Base.op_At g.qg_entries (flatten_groups rest)
