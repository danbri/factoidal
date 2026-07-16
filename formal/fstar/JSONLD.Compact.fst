module JSONLD.Compact

// ============================================================================
// JSON-LD 1.1 Compaction API (W3C JSON-LD 1.1 Processing Algorithms and
// API, Recommendation 16 July 2020, section "Compaction Algorithms"):
//
//   - Inverse Context Creation  (cmp_inverse below)
//   - IRI Compaction            (compact_iri)
//   - Term Selection            (cmp_select_term)
//   - Value Compaction          (compact_value)
//   - the Compaction Algorithm  (compact_elem / compact_map / the field
//                                and item folds)
//   - the JsonLdProcessor.compact() entry point (compact_document): expand
//     the input (Parser.JSONLD.expand_document — the same Expansion
//     Algorithm the expand/toRdf suites exercise), process the supplied
//     context (JSONLD.Context.context_process), compact, then re-attach
//     the ORIGINAL context value under "@context".
//
// Error model: option, same convention as JSONLD.Expand — None is an
// honest processing error (the compact suite's NegativeEvaluationTests:
// "compaction to list of lists" from a duplicate @list-container entry,
// "IRI confused with prefix" from compact_iri's step-9 check, "invalid
// @nest value", and every context-processing error surfaced by
// context_process itself) OR an out-of-scope feature. Fuel exhaustion is
// also None — an honest failure, never a wrong answer.
//
// All map lookups here are on EXPANDED-form JSON (literal "@id"/"@value"
// keys — expansion has already resolved aliases), so no alias-aware field
// lookup is needed on the input side; aliases only matter for OUTPUT keys
// (compact_iri on the keyword itself).
// ============================================================================

open FStar.List.Tot
open Parser.FastString
open RDF.Graph.Executable
open Parser.JSON
open JSONLD.Context
open JSONLD.Expand
open Parser.JSONLD

// ================================================================
// Options + small helpers
// ================================================================

// co_arrays: the API's compactArrays option (default true). co_rel: the
// API's compactToRelative option (default true) — whether vocab=false
// IRI compaction may relativize against the active context's base IRI.
type cmp_opts = { co_arrays : bool; co_rel : bool }

let rec cmp_lookup (#a:Type) (xs:list (string & a)) (k:string)
  : Tot (option a) (decreases xs) =
  match xs with
  | [] -> None
  | (k2, v) :: rest -> if k2 = k then Some v else cmp_lookup rest k

let cmp_field (fields:list (string & json_val)) (k:string) : option json_val =
  cmp_lookup fields k

let cmp_obj_field (v:json_val) (k:string) : option json_val =
  match v with
  | JObject fields -> cmp_field fields k
  | _ -> None

let cmp_is_scalar (v:json_val) : bool =
  match v with
  | JNull | JBool _ | JString _ | JNumber _ -> true
  | _ -> false

let cmp_is_value_object (v:json_val) : bool =
  match v with
  | JObject fields -> jexp_has_field "@value" fields
  | _ -> false

let cmp_is_list_object (v:json_val) : bool =
  match v with
  | JObject fields -> jexp_has_field "@list" fields
  | _ -> false

// Graph object in EXPANDED form: an "@graph" entry plus at most
// "@id"/"@index" siblings (JSON-LD 1.1 §"graph object"). Deliberately
// stricter than JSONLD.Expand.jexp_is_graph_object (which only asks "has
// @graph" — fine for expansion's uses, wrong for compaction's container
// dispatch).
let rec cmp_only_graph_keys (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> (k = "@graph" || k = "@id" || k = "@index") && cmp_only_graph_keys rest

let cmp_is_graph_object (v:json_val) : bool =
  match v with
  | JObject fields -> jexp_has_field "@graph" fields && cmp_only_graph_keys fields
  | _ -> false

let cmp_is_simple_graph (v:json_val) : bool =
  cmp_is_graph_object v &&
  (match v with
   | JObject fields -> not (jexp_has_field "@id" fields)
   | _ -> false)

let cmp_lower (s:string) : string = FStar.String.lowercase s

let cmp_concat (xs:list string) : string = FStar.String.concat "" xs

// "Shortest term first, ties broken lexicographically least" — the
// ordering both Inverse Context Creation (its term iteration order) and
// compact-IRI candidate preference use.
let cmp_term_less (a b:string) : bool =
  let la = fs_byte_length a in
  let lb = fs_byte_length b in
  if la < lb then true
  else if la > lb then false
  else string_lt a b

// s starts with (and is at least as long as) p.
let cmp_starts_with (s p:string) : bool =
  let lp = fs_byte_length p in
  fs_byte_length s >= lp && fs_byte_sub s 0 lp = p

let rec cmp_keys_only (fields:list (string & json_val)) (allowed:list string)
  : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> List.Tot.mem k allowed && cmp_keys_only rest allowed

let rec cmp_remove_key (xs:list (string & json_val)) (k:string)
  : Tot (list (string & json_val)) (decreases xs) =
  match xs with
  | [] -> []
  | (k2, v) :: rest -> if k2 = k then cmp_remove_key rest k else (k2, v) :: cmp_remove_key rest k

let rec cmp_replace_or_add (xs:list (string & json_val)) (k:string) (v:json_val)
  : Tot (list (string & json_val)) (decreases xs) =
  match xs with
  | [] -> [(k, v)]
  | (k2, v2) :: rest -> if k2 = k then (k2, v) :: rest else (k2, v2) :: cmp_replace_or_add rest k v

// ================================================================
// "Add value" (the API's spec-text "add value to entry" helper): merge a
// single compacted value into an accumulating field list, wrapping into /
// appending onto an array as required. as_array true forces array form on
// first insertion.
// ================================================================

let cmp_merge_into (existing v:json_val) : json_val =
  match existing with
  | JArray xs -> JArray (List.Tot.append xs [v])
  | x -> JArray [x; v]

let rec cmp_add_value (res:list (string & json_val)) (k:string) (v:json_val) (as_array:bool)
  : Tot (list (string & json_val)) (decreases res) =
  match res with
  | [] -> [(k, (if as_array then JArray [v] else v))]
  | (k2, v2) :: rest ->
    if k2 = k then (k2, cmp_merge_into v2 v) :: rest
    else (k2, v2) :: cmp_add_value rest k v as_array

let rec cmp_add_values (res:list (string & json_val)) (k:string) (vs:list json_val) (as_array:bool)
  : Tot (list (string & json_val)) (decreases vs) =
  match vs with
  | [] -> res
  | v :: rest -> cmp_add_values (cmp_add_value res k v as_array) k rest as_array

// An arbitrary compacted value: arrays SPREAD element-wise (matching the
// spec's per-element add-value semantics); an empty array claims the key
// with [] only if the key is not already present.
let cmp_generic_add (res:list (string & json_val)) (k:string) (v:json_val) (as_array:bool)
  : list (string & json_val) =
  match v with
  | JArray [] -> (match cmp_lookup res k with Some _ -> res | None -> List.Tot.append res [(k, JArray [])])
  | JArray xs -> cmp_add_values res k xs as_array
  | x -> cmp_add_value res k x as_array

// ================================================================
// Nest-target plumbing (JSON-LD 1.1 "@nest" in term definitions,
// td_nest): adds for a nest-carrying term land inside a map stored under
// the nest property's own key in the result.
// ================================================================

let cmp_nested_get (res:list (string & json_val)) (nest:option string)
  : list (string & json_val) =
  match nest with
  | None -> res
  | Some nk ->
    (match cmp_lookup res nk with
     | Some (JObject nf) -> nf
     | _ -> [])

let cmp_nested_put (res:list (string & json_val)) (nest:option string)
                   (nres:list (string & json_val))
  : list (string & json_val) =
  match nest with
  | None -> nres
  | Some nk -> cmp_replace_or_add res nk (JObject nres)

// ================================================================
// Term-definition views: container membership + the deduped,
// shortest-least-ordered term list.
// ================================================================

// The term's container mapping as a member LIST (e.g. ["@graph"; "@id";
// "@set"]). CK_None + td_set covers a bare "@container": "@set".
let cmp_container_list (td:term_def) : list string =
  let base =
    (match td.td_container with
     | CK_None -> []
     | CK_List -> ["@list"]
     | CK_Index -> ["@index"]
     | CK_Language -> ["@language"]
     | CK_Id -> ["@id"]
     | CK_Type -> ["@type"]
     | CK_Graph -> ["@graph"]
     | CK_GraphId -> ["@graph"; "@id"]
     | CK_GraphIndex -> ["@graph"; "@index"]) in
  if td.td_set then List.Tot.append base ["@set"] else base

// The inverse context's container KEY: the members sorted
// lexicographically and concatenated, "@none" when there are none
// (Inverse Context Creation step 3.2).
let cmp_container_key (td:term_def) : string =
  match jldctx_sort_strings (cmp_container_list td) with
  | [] -> "@none"
  | xs -> cmp_concat xs

let cmp_aprop_td (ac:active_context) (aprop:option string) : option term_def =
  match aprop with
  | Some p ->
    (match jldctx_find_term ac.ac_terms p with
     | Some td -> if td.td_iri = "@null" then None else Some td
     | None -> None)
  | None -> None

let cmp_container_of (ac:active_context) (aprop:option string) : list string =
  match cmp_aprop_td ac aprop with
  | Some td -> cmp_container_list td
  | None -> []

let cmp_has_container (ac:active_context) (aprop:option string) (c:string) : bool =
  List.Tot.mem c (cmp_container_of ac aprop)

// ac_terms accumulates redefinitions by PREPENDING (jldctx_find_term
// takes the first hit), so shadowed stale entries must be dropped before
// any whole-context iteration (inverse creation, compact-IRI prefix
// candidates).
let rec cmp_dedupe_terms (terms:list (string & term_def)) (seen:list string)
  : Tot (list (string & term_def)) (decreases terms) =
  match terms with
  | [] -> []
  | (k, td) :: rest ->
    if List.Tot.mem k seen then cmp_dedupe_terms rest seen
    else (k, td) :: cmp_dedupe_terms rest (k :: seen)

let rec cmp_insert_term (kv:(string & term_def)) (xs:list (string & term_def))
  : Tot (list (string & term_def)) (decreases xs) =
  match xs with
  | [] -> [kv]
  | y :: rest -> if cmp_term_less (fst kv) (fst y) then kv :: xs else y :: cmp_insert_term kv rest

let rec cmp_sort_terms (xs:list (string & term_def))
  : Tot (list (string & term_def)) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> cmp_insert_term x (cmp_sort_terms rest)

let cmp_live_terms (ac:active_context) : list (string & term_def) =
  cmp_dedupe_terms ac.ac_terms []

let cmp_ordered_terms (ac:active_context) : list (string & term_def) =
  cmp_sort_terms (cmp_live_terms ac)

// ================================================================
// Inverse Context Creation (spec §"Inverse Context Creation").
// Represented as nested association lists:
//   IRI -> container key -> { @language / @type / @any submaps } -> term
// Entries are inserted first-writer-wins while walking terms in
// shortest-least order, which realises the spec's "only add if no entry
// exists" preference for shorter terms.
// ================================================================

type inv_slot = | IS_Lang | IS_Type | IS_Any

type inv_maps = {
  im_language : list (string & string);
  im_type     : list (string & string);
  im_any      : list (string & string);
}

let inv_empty_maps : inv_maps = { im_language = []; im_type = []; im_any = [] }

type inverse_ctx = list (string & list (string & inv_maps))

let inv_add_if_absent (m:list (string & string)) (k v:string) : list (string & string) =
  match cmp_lookup m k with
  | Some _ -> m
  | None -> List.Tot.append m [(k, v)]

let inv_maps_add (maps:inv_maps) (slot:inv_slot) (k term:string) : inv_maps =
  match slot with
  | IS_Lang -> { maps with im_language = inv_add_if_absent maps.im_language k term }
  | IS_Type -> { maps with im_type = inv_add_if_absent maps.im_type k term }
  | IS_Any  -> { maps with im_any = inv_add_if_absent maps.im_any k term }

let rec inv_update_cont (conts:list (string & inv_maps)) (ckey:string) (slot:inv_slot) (k term:string)
  : Tot (list (string & inv_maps)) (decreases conts) =
  match conts with
  | [] -> [(ckey, inv_maps_add inv_empty_maps slot k term)]
  | (c, maps) :: rest ->
    if c = ckey then (c, inv_maps_add maps slot k term) :: rest
    else (c, maps) :: inv_update_cont rest ckey slot k term

let rec inv_update (inv:inverse_ctx) (iri ckey:string) (slot:inv_slot) (k term:string)
  : Tot inverse_ctx (decreases inv) =
  match inv with
  | [] -> [(iri, inv_update_cont [] ckey slot k term)]
  | (i, conts) :: rest ->
    if i = iri then (i, inv_update_cont conts ckey slot k term) :: rest
    else (i, conts) :: inv_update rest iri ckey slot k term

// The spec's language-and-direction key: both non-null -> "l_d"
// lowercased; language only -> lowercased language; direction only ->
// "_d"; both explicitly null -> "@null" (Inverse Context Creation 3.11).
let inv_lang_dir_key (lo:option string) (dopt:option string) : string =
  match lo, dopt with
  | Some l, Some d -> cmp_lower (cmp_concat [l; "_"; d])
  | Some l, None -> cmp_lower l
  | None, Some d -> cmp_concat ["_"; cmp_lower d]
  | None, None -> "@null"

// The (slot, key) insertions one term definition contributes (Inverse
// Context Creation steps 3.8-3.15). Every term ALSO contributes
// (IS_Any, "@none") — appended by the fold below (equivalent to the
// spec's seed-@any-at-container-map-creation, since first-writer-wins).
let inv_term_insertions (ac:active_context) (td:term_def) (default_lang_key:string)
  : list (inv_slot & string) =
  if td.td_reverse then [(IS_Type, "@reverse")]
  else
    match td.td_type_mapping with
    | Some "@none" -> [(IS_Lang, "@any"); (IS_Type, "@any")]
    | Some t -> [(IS_Type, t)]
    | None ->
      (match td.td_language, td.td_direction with
       | Some lo, Some dopt -> [(IS_Lang, inv_lang_dir_key lo dopt)]
       | Some lo, None ->
         [(IS_Lang, (match lo with Some l -> cmp_lower l | None -> "@null"))]
       | None, Some dopt ->
         [(IS_Lang, (match dopt with
                     | Some d -> cmp_concat ["_"; cmp_lower d]
                     | None -> "@none"))]
       | None, None ->
         (match ac.ac_direction with
          | Some d ->
            let lang_dir =
              cmp_lower (cmp_concat
                [(match ac.ac_language with Some l -> l | None -> "@none"); "_"; d]) in
            [(IS_Lang, lang_dir); (IS_Lang, "@none"); (IS_Type, "@none")]
          | None ->
            [(IS_Lang, default_lang_key); (IS_Lang, "@none"); (IS_Type, "@none")]))

let rec inv_apply_insertions (inv:inverse_ctx) (iri ckey name:string)
                             (ins:list (inv_slot & string))
  : Tot inverse_ctx (decreases ins) =
  match ins with
  | [] -> inv
  | (slot, k) :: rest -> inv_apply_insertions (inv_update inv iri ckey slot k name) iri ckey name rest

let rec inv_fold_terms (inv:inverse_ctx) (terms:list (string & term_def))
                       (ac:active_context) (default_lang_key:string)
  : Tot inverse_ctx (decreases terms) =
  match terms with
  | [] -> inv
  | (name, td) :: rest ->
    if td.td_iri = "@null" then inv_fold_terms inv rest ac default_lang_key
    else
      let ckey = cmp_container_key td in
      let ins = List.Tot.append (inv_term_insertions ac td default_lang_key)
                                [(IS_Any, "@none")] in
      inv_fold_terms (inv_apply_insertions inv td.td_iri ckey name ins) rest ac default_lang_key

let cmp_inverse (ac:active_context) : inverse_ctx =
  let default_lang_key =
    (match ac.ac_language with Some l -> cmp_lower l | None -> "@none") in
  inv_fold_terms [] (cmp_ordered_terms ac) ac default_lang_key

// ================================================================
// Term Selection (spec §"Term Selection").
// ================================================================

let inv_slot_map (maps:inv_maps) (tl:string) : list (string & string) =
  if tl = "@type" then maps.im_type
  else if tl = "@any" then maps.im_any
  else maps.im_language

let rec cmp_select_prefs (m:list (string & string)) (prefs:list string)
  : Tot (option string) (decreases prefs) =
  match prefs with
  | [] -> None
  | p :: rest ->
    (match cmp_lookup m p with
     | Some term -> Some term
     | None -> cmp_select_prefs m rest)

let rec cmp_select_term (conts:list (string & inv_maps)) (containers:list string)
                        (tl:string) (prefs:list string)
  : Tot (option string) (decreases containers) =
  match containers with
  | [] -> None
  | c :: rest ->
    (match cmp_lookup conts c with
     | Some maps ->
       (match cmp_select_prefs (inv_slot_map maps tl) prefs with
        | Some t -> Some t
        | None -> cmp_select_term conts rest tl prefs)
     | None -> cmp_select_term conts rest tl prefs)

// ================================================================
// IRI Compaction step 4's container/type-language preference assembly.
// ================================================================

// One @list item's (item language key, item type) for the common-
// language/type walk (IRI Compaction 4.6.4). "@none" = no preference
// signal; "@null" = an explicit no-language value.
let cmp_item_lang_type (it:json_val) : (string & string) =
  match it with
  | JObject f ->
    if jexp_has_field "@value" f then
      (match cmp_field f "@direction" with
       | Some (JString d) ->
         ((match cmp_field f "@language" with
           | Some (JString l) -> cmp_lower (cmp_concat [l; "_"; d])
           | _ -> cmp_concat ["_"; cmp_lower d]), "@none")
       | _ ->
         (match cmp_field f "@language" with
          | Some (JString l) -> (cmp_lower l, "@none")
          | _ ->
            (match cmp_field f "@type" with
             | Some (JString t) -> ("@none", t)
             | _ -> ("@null", "@none"))))
    else ("@none", "@id")
  | _ -> ("@none", "@id")

let rec cmp_list_common_walk (items:list json_val) (clang ctype:option string)
  : Tot (string & string) (decreases items) =
  match items with
  | [] ->
    ((match clang with Some c -> c | None -> "@none"),
     (match ctype with Some c -> c | None -> "@none"))
  | it :: rest ->
    let (il, ity) = cmp_item_lang_type it in
    let is_val = cmp_is_value_object it in
    let clang' =
      (match clang with
       | None -> Some il
       | Some c -> if c = il then Some c else (if is_val then Some "@none" else Some c)) in
    let ctype' =
      (match ctype with
       | None -> Some ity
       | Some c -> if c = ity then Some c else Some "@none") in
    cmp_list_common_walk rest clang' ctype'

// (containers, type/language slot, type/language value) for a property's
// value shape (IRI Compaction steps 4.3-4.12). tlv "@null" = the spec's
// null-normalised value.
let cmp_iri_selectors (ac:active_context) (value:option json_val) (rev:bool)
  : (list string & string & string) =
  let has_index =
    (match value with
     | Some (JObject f) -> jexp_has_field "@index" f
     | _ -> false) in
  let is_map = (match value with Some (JObject _) -> true | _ -> false) in
  let idx_pre =
    (match value with
     | Some (JObject f) ->
       if jexp_has_field "@index" f && not (cmp_is_graph_object (JObject f))
       then ["@index"; "@index@set"] else []
     | _ -> []) in
  let (mid, tl, tlv) =
    if rev then (["@set"], "@type", "@reverse")
    else
      (match value with
       | Some (JObject f) ->
         if jexp_has_field "@list" f then
           (let lst = (match cmp_field f "@list" with Some v -> jexp_as_array v | None -> []) in
            let cont_list = if jexp_has_field "@index" f then [] else ["@list"] in
            (match lst with
             | [] -> (cont_list, "@any", "@none")
             | _ ->
               let (cl, ct) = cmp_list_common_walk lst None None in
               if ct <> "@none" then (cont_list, "@type", ct)
               else (cont_list, "@language", cl)))
         else if cmp_is_graph_object (JObject f) then
           (let gi = jexp_has_field "@index" f in
            let gid = jexp_has_field "@id" f in
            (List.Tot.append
               (List.Tot.append
                  (List.Tot.append
                     (if gi then ["@graph@index"; "@graph@index@set"] else [])
                     (if gid then ["@graph@id"; "@graph@id@set"] else []))
                  (List.Tot.append
                     ["@graph"; "@graph@set"; "@set"]
                     (if gi then [] else ["@graph@index"; "@graph@index@set"])))
               (List.Tot.append
                  (if gid then [] else ["@graph@id"; "@graph@id@set"])
                  ["@index"; "@index@set"]),
             "@type", "@id"))
         else if jexp_has_field "@value" f then
           (let no_idx = not (jexp_has_field "@index" f) in
            let (langconts, tl0, tlv0) =
              (match cmp_field f "@direction" with
               | Some (JString d) ->
                 if no_idx then
                   (["@language"; "@language@set"], "@language",
                    (match cmp_field f "@language" with
                     | Some (JString l) -> cmp_lower (cmp_concat [l; "_"; d])
                     | _ -> cmp_concat ["_"; cmp_lower d]))
                 else
                   (match cmp_field f "@type" with
                    | Some (JString t) -> ([], "@type", t)
                    | _ -> ([], "@language", "@null"))
               | _ ->
                 (match cmp_field f "@language" with
                  | Some (JString l) ->
                    if no_idx then (["@language"; "@language@set"], "@language", cmp_lower l)
                    else
                      (match cmp_field f "@type" with
                       | Some (JString t) -> ([], "@type", t)
                       | _ -> ([], "@language", "@null"))
                  | _ ->
                    (match cmp_field f "@type" with
                     | Some (JString t) -> ([], "@type", t)
                     | _ -> ([], "@language", "@null")))) in
            (List.Tot.append langconts ["@set"], tl0, tlv0))
         else
           (["@id"; "@id@set"; "@type"; "@set@type"; "@set"], "@type", "@id")
       | _ -> (["@id"; "@id@set"; "@type"; "@set@type"; "@set"], "@type", "@id")) in
  let tail2 =
    if (not ac.ac_mode10) && (not is_map || not has_index)
    then ["@index"; "@index@set"] else [] in
  let tail3 =
    if (not ac.ac_mode10) &&
       (match value with
        | Some (JObject f) -> (match f with | [kv] -> fst kv = "@value" | _ -> false)
        | _ -> false)
    then ["@language"; "@language@set"] else [] in
  (List.Tot.append idx_pre
     (List.Tot.append mid
        (List.Tot.append ["@none"] (List.Tot.append tail2 tail3))),
   tl, tlv)

// The "_direction" suffix variant of a language_direction preference
// (IRI Compaction 4.18): "de_ltr" also tries "_ltr".
let cmp_underscore_suffix (s:string) : option string =
  let n = fs_byte_length s in
  let pos = fs_find_byte s 0x5F 0 in
  if pos < n then Some (fs_byte_sub s pos (n - pos)) else None

// ================================================================
// IRI Compaction (spec §"IRI Compaction"). depth bounds the single
// spec-mandated recursive probe (step 4.15: does the value's @id itself
// compact to a term that round-trips?) — that probe passes value=None so
// it cannot recurse again; depth 2 at every external call site.
//
// None = the "IRI confused with prefix" error (step 9): the IRI's
// scheme/prefix part names a prefix-capable term whose IRI mapping does
// NOT actually prefix this IRI (compact suite e002).
// ================================================================

let cmp_confused_with_prefix (ac:active_context) (iri:string) : bool =
  match jldctx_find_colon iri 0 (fs_byte_length iri + 1) with
  | None -> false
  | Some cpos ->
    if cpos > fs_byte_length iri then false
    else
      let pfx = fs_byte_sub iri 0 cpos in
      (match jldctx_find_term ac.ac_terms pfx with
       | Some td -> td.td_prefix && td.td_iri <> "@null" && not (cmp_starts_with iri td.td_iri)
       | None -> false)

let rec cmp_curie_loop (ac:active_context) (terms:list (string & term_def))
                       (iri:string) (has_value:bool) (best:option string)
  : Tot (option string) (decreases terms) =
  match terms with
  | [] -> best
  | (name, td) :: rest ->
    let li = fs_byte_length iri in
    let lt = fs_byte_length td.td_iri in
    // not td.td_prefix: the 1.1 API's prefix flag — a term may only
    // shorten an IRI as the prefix half of a compact IRI when its
    // definition grants prefix status. Deliberately NOT relaxed under
    // ac.ac_mode10: compact/tp001 ("Compact IRI will not use an
    // expanded term definition in 1.0", processingMode=json-ld-1.0,
    // specVersion=json-ld-1.1) pins that the 1.1 API keeps this gate
    // even in 1.0 processing mode, while the 1.0-era compact/t0038
    // ("Index map round-tripping", specVersion=json-ld-1.0) expects a
    // genuine 1.0 processor's opposite behavior — the two cannot both
    // pass from one processingMode-driven engine state, and tp001 is
    // the 1.1-suite conformance test. t0038 stays a documented skip in
    // bin/jsonld-compact-runner/jsonld_compact_runner.ml.
    let skip =
      Some? (jldctx_find_colon name 0 (fs_byte_length name + 1)) ||
      td.td_iri = "@null" || not td.td_prefix ||
      lt = 0 || li <= lt || not (cmp_starts_with iri td.td_iri) in
    if skip then cmp_curie_loop ac rest iri has_value best
    else
      let suffix = fs_byte_sub iri lt (li - lt) in
      let candidate = cmp_concat [name; ":"; suffix] in
      let usable =
        (match jldctx_find_term ac.ac_terms candidate with
         | None -> true
         | Some ctd -> (not has_value) && ctd.td_iri = iri) in
      let better =
        usable && (match best with
                   | None -> true
                   | Some b -> cmp_term_less candidate b) in
      cmp_curie_loop ac rest iri has_value (if better then Some candidate else best)

// Relative-reference construction against the active context's base IRI
// (IRI Compaction step 10 with compactToRelative): shared-segment
// stripping, "../" for unshared base directories, query/fragment
// reattachment, "./" for the degenerate empty result.
let rec cmp_split_slash_from (s:string) (pos:nat) (fuel:nat)
  : Tot (list string) (decreases fuel) =
  if fuel = 0 then []
  else
    let n = fs_byte_length s in
    let sl = fs_find_byte s 0x2F pos in
    if sl >= n then [fs_byte_sub s pos (if n >= pos then n - pos else 0)]
    else fs_byte_sub s pos (if sl >= pos then sl - pos else 0)
         :: cmp_split_slash_from s (sl + 1) (fuel - 1)

let cmp_split_slash (s:string) : list string =
  cmp_split_slash_from s 0 (fs_byte_length s + 1)

let rec cmp_strip_common (bs isegs:list string) (last:nat)
  : Tot (list string & list string) (decreases bs) =
  match bs, isegs with
  | b :: brest, i :: irest ->
    if b = i && List.Tot.length isegs > last then cmp_strip_common brest irest last
    else (bs, isegs)
  | _, _ -> (bs, isegs)

let rec cmp_repeat_dotdot (n:nat) : Tot string (decreases n) =
  if n = 0 then "" else cmp_concat ["../"; cmp_repeat_dotdot (n - 1)]

let rec cmp_join_slash (xs:list string) : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | [x] -> x
  | x :: rest -> cmp_concat [x; "/"; cmp_join_slash rest]

// Byte-level split of an IRI into (root, path, query?, fragment?) where
// root = scheme + ":" (+ "//" + authority when present). Local and
// minimal on purpose: RDF.IRI's full RFC 3986 parser sits behind an
// interface that only exports resolution, and relativization needs no
// more than this. Root "" means "no scheme found" (not relativizable).
let cmp_iri_split (s:string) : (string & string & option string & option string) =
  let n = fs_byte_length s in
  let h = fs_find_byte s 0x23 0 in
  let q0 = fs_find_byte s 0x3F 0 in
  let has_frag = h < n in
  let has_query = q0 < h && q0 < n in
  let frag =
    if has_frag && h + 1 <= n then Some (fs_byte_sub s (h + 1) (n - h - 1)) else None in
  let query =
    if has_query then
      (let qend = if h < n then h else n in
       if q0 + 1 <= qend then Some (fs_byte_sub s (q0 + 1) (qend - q0 - 1)) else Some "")
    else None in
  let pe0 = (if has_query then q0 else (if h < n then h else n)) in
  let pe : nat = if pe0 > n then n else pe0 in
  let c = fs_find_byte s 0x3A 0 in
  let sl = fs_find_byte s 0x2F 0 in
  let root_len : nat =
    if c >= n || c >= pe || sl < c then 0
    else
      (let after = c + 1 in
       if after + 1 < n && fs_byte_at s after = 0x2F && fs_byte_at s (after + 1) = 0x2F then
         (let a0 = after + 2 in
          let asl = fs_find_byte s 0x2F a0 in
          if asl < pe then asl else pe)
       else after) in
  let root_len : nat = if root_len > pe then pe else root_len in
  (fs_byte_sub s 0 root_len,
   fs_byte_sub s root_len (pe - root_len),
   query, frag)

let cmp_relativize (base iri:string) : string =
  let (broot, bpath, _, _) = cmp_iri_split base in
  let (iroot, ipath, iq, ifr) = cmp_iri_split iri in
  if broot = "" || broot <> iroot then iri
  else
    let bsegs = cmp_split_slash bpath in
    let isegs = cmp_split_slash ipath in
    let last : nat = if Some? iq || Some? ifr then 0 else 1 in
    let (brem, irem) = cmp_strip_common bsegs isegs last in
    let ups : nat =
      (let l = List.Tot.length brem in if l > 0 then l - 1 else 0) in
    let rel = cmp_concat [cmp_repeat_dotdot ups; cmp_join_slash irem] in
    let rel1 = (match iq with
                | Some q -> cmp_concat [rel; "?"; q]
                | None -> rel) in
    let rel2 = (match ifr with
                | Some fg -> cmp_concat [rel1; "#"; fg]
                | None -> rel1) in
    if rel2 = "" then "./"
    // a relative reference that would LOOK like a keyword gets an
    // explicit "./" prefix (compact/0111: "@special" -> "./@special")
    else if fs_byte_at rel2 0 = 0x40 then cmp_concat ["./"; rel2]
    else rel2

let rec compact_iri (ac:active_context) (co:cmp_opts) (iri:string)
                    (value:option json_val) (vocab rev:bool) (depth:nat)
  : Tot (option string) (decreases depth) =
  let inv = cmp_inverse ac in
  let term_sel : option string =
    if not vocab then None
    else
      (match cmp_lookup inv iri with
       | None -> None
       | Some conts ->
         let (containers, tl0, tlv) = cmp_iri_selectors ac value rev in
         let tl =
           (if tlv = "@none" && tl0 = "@any" then "@any" else tl0) in
         // preferred values (steps 4.13-4.18)
         let id_pref : option (list string) =
           if (tlv = "@id" || tlv = "@reverse") then
             (match value with
              | Some (JObject f) ->
                (match cmp_field f "@id" with
                 | Some (JString idv) ->
                   let cand =
                     (if depth > 0 then compact_iri ac co idv None true false (depth - 1)
                      else None) in
                   (match cand with
                    | Some ct ->
                      (match jldctx_find_term ac.ac_terms ct with
                       | Some ctd ->
                         if ctd.td_iri = idv
                         then Some ["@vocab"; "@id"; "@none"]
                         else Some ["@id"; "@vocab"; "@none"]
                       | None -> Some ["@id"; "@vocab"; "@none"])
                    | None -> Some ["@id"; "@vocab"; "@none"])
                 | _ -> None)
              | _ -> None)
           else None in
         let prefs_base =
           (match id_pref with
            | Some ps -> (if tlv = "@reverse" then "@reverse" :: ps else ps)
            | None ->
              (if tlv = "@reverse" then ["@reverse"; tlv; "@none"] else [tlv; "@none"])) in
         let prefs1 = List.Tot.append prefs_base ["@any"] in
         let prefs =
           (match cmp_underscore_suffix tlv with
            | Some u -> List.Tot.append prefs1 [u]
            | None -> prefs1) in
         cmp_select_term conts containers tl prefs) in
  match term_sel with
  | Some t -> Some t
  | None ->
    // step 5: vocabulary-mapping suffix
    let sfx : option string =
      if vocab then
        (match ac.ac_vocab with
         | Some vm ->
           let li = fs_byte_length iri in
           let lv = fs_byte_length vm in
           if lv > 0 && li > lv && cmp_starts_with iri vm then
             (let suffix = fs_byte_sub iri lv (li - lv) in
              match jldctx_find_term ac.ac_terms suffix with
              | Some _ -> None
              | None -> Some suffix)
           else None
         | None -> None)
      else None in
    (match sfx with
     | Some s -> Some s
     | None ->
       (match cmp_curie_loop ac (cmp_live_terms ac) iri (Some? value) None with
        | Some c -> Some c
        | None ->
          if cmp_confused_with_prefix ac iri then None
          else if (not vocab) && co.co_rel then
            (match ac.ac_base with
             | Some b -> Some (cmp_relativize b iri)
             | None -> Some iri)
          else Some iri))

// Keyword aliasing: a keyword contains no colon, so compact_iri cannot
// error on it — this total wrapper keeps call sites clean.
let cmp_alias_kw (ac:active_context) (co:cmp_opts) (kw:string) : string =
  match compact_iri ac co kw None true false 2 with
  | Some s -> s
  | None -> kw

// ================================================================
// Value Compaction (spec §"Value Compaction"). Returns the collapsed
// scalar when the active property's mappings license dropping the value-
// object wrapper; otherwise the (possibly re-keyed) map. None only on a
// compact_iri error inside.
// ================================================================

let compact_value (ac:active_context) (co:cmp_opts) (aprop:option string)
                  (vfields:list (string & json_val))
  : option json_val =
  let td = cmp_aprop_td ac aprop in
  let tmap = (match td with Some t -> t.td_type_mapping | None -> None) in
  let lang : option string =
    (match td with
     | Some t -> (match t.td_language with Some lo -> lo | None -> ac.ac_language)
     | None -> ac.ac_language) in
  let dir : option string =
    (match td with
     | Some t -> (match t.td_direction with Some dd -> dd | None -> ac.ac_direction)
     | None -> ac.ac_direction) in
  let has_index = jexp_has_field "@index" vfields in
  let preserve_index = has_index && not (cmp_has_container ac aprop "@index") in
  if jexp_has_field "@id" vfields && cmp_keys_only vfields ["@id"; "@index"] then
    // subject reference (step 6)
    (match cmp_field vfields "@id" with
     | Some (JString idv) ->
       if tmap = Some "@id" then
         (match compact_iri ac co idv None false false 2 with
          | Some s -> Some (JString s)
          | None -> None)
       else if tmap = Some "@vocab" then
         (match compact_iri ac co idv None true false 2 with
          | Some s -> Some (JString s)
          | None -> None)
       else Some (JObject vfields)
     | _ -> Some (JObject vfields))
  else if not (jexp_has_field "@value" vfields) then
    // a node object that reached here via its @id entry but is not a
    // bare reference: value compaction leaves it alone (the main
    // algorithm's map processing takes over)
    Some (JObject vfields)
  else
    let vval = (match cmp_field vfields "@value" with Some v -> v | None -> JNull) in
    let vtype_s = (match cmp_field vfields "@type" with Some (JString t) -> Some t | _ -> None) in
    let vlang_s = (match cmp_field vfields "@language" with Some (JString l) -> Some l | _ -> None) in
    let vdir_s = (match cmp_field vfields "@direction" with Some (JString d) -> Some d | _ -> None) in
    let tmap_none = (tmap = Some "@none") in
    let lang_matches =
      (match vlang_s, lang with
       | Some a, Some b -> cmp_lower a = cmp_lower b
       | None, None -> true
       | _, _ -> false) in
    let dir_matches =
      (match vdir_s, dir with
       | Some a, Some b -> cmp_lower a = cmp_lower b
       | None, None -> true
       | _, _ -> false) in
    let type_collapse = (Some? vtype_s && Some? tmap && vtype_s = tmap) in
    let value_is_string = JString? vval in
    if (not preserve_index) && (not tmap_none) && type_collapse then Some vval
    else if (not preserve_index) && (not tmap_none) && None? vtype_s
            && (not value_is_string) && None? vlang_s && None? vdir_s then Some vval
    else if (not preserve_index) && (not tmap_none) && None? vtype_s
            && lang_matches && dir_matches then Some vval
    else
      // keep the map, re-keyed through the active context's aliases,
      // with the datatype IRI compacted (steps 8.1 + 11)
      let idx_fields =
        (if preserve_index then
           (match cmp_field vfields "@index" with
            | Some ix -> [(cmp_alias_kw ac co "@index", ix)]
            | None -> [])
         else []) in
      let lang_fields =
        (match vlang_s with
         | Some l -> [(cmp_alias_kw ac co "@language", JString l)]
         | None -> []) in
      let dir_fields =
        (match vdir_s with
         | Some d -> [(cmp_alias_kw ac co "@direction", JString d)]
         | None -> []) in
      (match vtype_s with
       | Some t ->
         (match compact_iri ac co t None true false 2 with
          | None -> None
          | Some ct ->
            Some (JObject (List.Tot.append idx_fields
                    (List.Tot.append [(cmp_alias_kw ac co "@type", JString ct)]
                       [(cmp_alias_kw ac co "@value", vval)]))))
       | None ->
         Some (JObject (List.Tot.append idx_fields
                 (List.Tot.append lang_fields
                    (List.Tot.append dir_fields
                       [(cmp_alias_kw ac co "@value", vval)])))))

// The nest target for a compacted item property: Some None = no nesting;
// Some (Some nk) = nest under key nk; None = "invalid @nest value" (the
// term's @nest member neither is nor expands to the @nest keyword).
let cmp_nest_of (ac:active_context) (iap:string) : option (option string) =
  match jldctx_find_term ac.ac_terms iap with
  | Some td ->
    (match td.td_nest with
     | None -> Some None
     | Some nt ->
       if nt = "@nest" then Some (Some nt)
       else
         (match expand_iri ac nt true with
          | Some e -> if e = "@nest" then Some (Some nt) else None
          | None -> None))
  | None -> Some None

// Move reverse-capable properties out of a compacted @reverse map into
// the parent result (Compaction step 12.3.2).
let rec cmp_move_reverse (ac:active_context) (co:cmp_opts)
                         (rf:list (string & json_val))
                         (leftover res:list (string & json_val))
  : Tot (list (string & json_val) & list (string & json_val)) (decreases rf) =
  match rf with
  | [] -> (leftover, res)
  | (p, pv) :: rest ->
    (match jldctx_find_term ac.ac_terms p with
     | Some td ->
       if td.td_reverse then
         let as_arr = td.td_set || not co.co_arrays in
         let res1 =
           (match pv with
            | JArray xs -> cmp_add_values res p xs as_arr
            | x -> cmp_add_value res p x as_arr) in
         cmp_move_reverse ac co rest leftover res1
       else cmp_move_reverse ac co rest (List.Tot.append leftover [(p, pv)]) res
     | None -> cmp_move_reverse ac co rest (List.Tot.append leftover [(p, pv)]) res)

// @type output values are compacted against the TYPE-SCOPED context
// snapshot (Compaction step 12.2 — the pre-pop, pre-property-scoped
// active context), preserving input order.
let rec cmp_compact_types (tsc:active_context) (co:cmp_opts) (items:list json_val)
  : Tot (option (list string)) (decreases items) =
  match items with
  | [] -> Some []
  | JString t :: rest ->
    (match compact_iri tsc co t None true false 2 with
     | None -> None
     | Some ct ->
       (match cmp_compact_types tsc co rest with
        | Some cs -> Some (ct :: cs)
        | None -> None))
  | _ :: rest -> cmp_compact_types tsc co rest

let rec cmp_raw_type_names (items:list json_val) : Tot (list string) (decreases items) =
  match items with
  | [] -> []
  | JString t :: rest -> t :: cmp_raw_type_names rest
  | _ :: rest -> cmp_raw_type_names rest

// ================================================================
// The Compaction Algorithm (spec §"Compaction Algorithm") — the mutual
// group. Fuel decreases on every mutual call; exhaustion is None.
// ================================================================

#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
let rec compact_elem (ac:active_context) (aprop:option string) (elem:json_val)
                     (co:cmp_opts) (fuel:nat)
  : Tot (option json_val) (decreases fuel) =
  if fuel = 0 then None else
  match elem with
  | JNull | JBool _ | JString _ | JNumber _ -> Some elem
  | JArray items ->
    (match compact_items ac aprop items co (fuel - 1) with
     | None -> None
     | Some outs ->
       let collapse =
         co.co_arrays
         && (match outs with | [_] -> true | _ -> false)
         && aprop <> Some "@graph" && aprop <> Some "@set"
         && Nil? (cmp_container_of ac aprop) in
       if collapse then (match outs with | [x] -> Some x | _ -> Some (JArray outs))
       else Some (JArray outs))
  | JObject fields -> compact_map ac aprop fields co (fuel - 1)

and compact_items (ac:active_context) (aprop:option string) (items:list json_val)
                  (co:cmp_opts) (fuel:nat)
  : Tot (option (list json_val)) (decreases fuel) =
  if fuel = 0 then None else
  match items with
  | [] -> Some []
  | it :: rest ->
    (match compact_elem ac aprop it co (fuel - 1) with
     | None -> None
     | Some c ->
       (match compact_items ac aprop rest co (fuel - 1) with
        | None -> None
        | Some cs -> Some (c :: cs)))

and compact_map (ac0:active_context) (aprop:option string)
                (fields:list (string & json_val)) (co:cmp_opts) (fuel:nat)
  : Tot (option json_val) (decreases fuel) =
  if fuel = 0 then None else
  // step 4: snapshot the type-scoped context
  let tsc = ac0 in
  // step 5: pop a non-propagated context unless the element is a value
  // object or a bare node reference
  let is_value = jexp_has_field "@value" fields in
  let id_only = (match fields with | [kv] -> fst kv = "@id" | _ -> false) in
  let ac1 =
    (match ac0.ac_previous with
     | Some prev -> if is_value || id_only then ac0 else prev
     | None -> ac0) in
  // step 6: the active property's own scoped context (found in the
  // PRE-pop context, applied onto the popped one, override protected)
  let ac2_opt =
    (match cmp_aprop_td tsc aprop with
     | Some td ->
       (match td.td_scoped_context with
        | Some (scoped, def_url) ->
          apply_context_with_propagate ({ ac1 with ac_doc_url = def_url }) scoped true true
        | None -> Some ac1)
     | None -> Some ac1) in
  match ac2_opt with
  | None -> None
  | Some ac2 ->
    // step 7: value compaction for value objects and node references
    let has_id = jexp_has_field "@id" fields in
    let tmap2 = (match cmp_aprop_td ac2 aprop with Some t -> t.td_type_mapping | None -> None) in
    if is_value || has_id then
      (match compact_value ac2 co aprop fields with
       | None -> None
       | Some r ->
         if cmp_is_scalar r || tmap2 = Some "@json" then Some r
         else compact_map_body ac2 tsc aprop fields co (fuel - 1))
    else compact_map_body ac2 tsc aprop fields co (fuel - 1)

and compact_map_body (ac2 tsc:active_context) (aprop:option string)
                     (fields:list (string & json_val)) (co:cmp_opts) (fuel:nat)
  : Tot (option json_val) (decreases fuel) =
  if fuel = 0 then None else
  // step 8: a list object under an @list-container property compacts to
  // its bare item array
  if cmp_is_list_object (JObject fields) && cmp_has_container ac2 aprop "@list" then
    (match cmp_field fields "@list" with
     | Some lv -> compact_elem ac2 aprop lv co (fuel - 1)
     | None -> None)
  else
    let inside_rev = (aprop = Some "@reverse") in
    // step 11: apply the type-scoped contexts named by this node's
    // compacted @type terms (looked up in tsc, folded onto ac2, sorted,
    // propagate false)
    let raw_types = (match cmp_field fields "@type" with Some v -> jexp_as_array v | None -> []) in
    (match cmp_compact_types tsc co raw_types with
     | None -> None
     | Some ctype_names ->
       (match jldctx_apply_type_scoped tsc ac2 (jldctx_sort_strings ctype_names) false with
        | None -> None
        | Some (ac3a, any_non_prop) ->
          let ac3 = if any_non_prop then { ac3a with ac_previous = Some ac2 } else ac3a in
          (match compact_fields ac3 tsc aprop inside_rev fields [] co (fuel - 1) with
           | None -> None
           | Some res -> Some (JObject res))))

and compact_fields (ac tsc:active_context) (aprop:option string) (inside_rev:bool)
                   (pending:list (string & json_val)) (res:list (string & json_val))
                   (co:cmp_opts) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None else
  match pending with
  | [] -> Some res
  | (k, v) :: rest ->
    if k = "@id" then
      (match v with
       | JString s ->
         (match compact_iri ac co s None false false 2 with
          | None -> None
          | Some cs ->
            compact_fields ac tsc aprop inside_rev rest
              (List.Tot.append res [(cmp_alias_kw ac co "@id", JString cs)]) co (fuel - 1))
       | _ ->
         compact_fields ac tsc aprop inside_rev rest
           (List.Tot.append res [(cmp_alias_kw ac co "@id", v)]) co (fuel - 1))
    else if k = "@type" then
      (match cmp_compact_types tsc co (jexp_as_array v) with
       | None -> None
       | Some cts ->
         let alias = cmp_alias_kw ac co "@type" in
         let as_set =
           (not ac.ac_mode10) &&
           (match jldctx_find_term ac.ac_terms alias with
            | Some td -> td.td_set
            | None -> false) in
         let cv =
           (match cts with
            | [single] ->
              if co.co_arrays && not as_set then JString single
              else JArray [JString single]
            | xs -> JArray (List.Tot.map JString xs)) in
         compact_fields ac tsc aprop inside_rev rest
           (List.Tot.append res [(alias, cv)]) co (fuel - 1))
    else if k = "@reverse" then
      (match compact_elem ac (Some "@reverse") v co (fuel - 1) with
       | None -> None
       | Some cv ->
         (match cv with
          | JObject rf ->
            let (leftover, res1) = cmp_move_reverse ac co rf [] res in
            let res2 =
              (match leftover with
               | [] -> res1
               | _ -> List.Tot.append res1 [(cmp_alias_kw ac co "@reverse", JObject leftover)]) in
            compact_fields ac tsc aprop inside_rev rest res2 co (fuel - 1)
          | _ ->
            compact_fields ac tsc aprop inside_rev rest
              (List.Tot.append res [(cmp_alias_kw ac co "@reverse", cv)]) co (fuel - 1)))
    else if k = "@index" && cmp_has_container ac aprop "@index" then
      // step 12.5: the @index is re-expressed as the parent's map key
      compact_fields ac tsc aprop inside_rev rest res co (fuel - 1)
    else if k = "@index" || k = "@value" || k = "@language" || k = "@direction" then
      compact_fields ac tsc aprop inside_rev rest
        (List.Tot.append res [(cmp_alias_kw ac co k, v)]) co (fuel - 1)
    else if k = "@preserve" then
      // framing-only keyword; never present in expanded (non-framed) input
      compact_fields ac tsc aprop inside_rev rest res co (fuel - 1)
    else
      (match v with
       | JArray [] ->
         // step 12.7: preserve an empty property value as an empty array
         (match compact_iri ac co k (Some (JArray [])) true inside_rev 2 with
          | None -> None
          | Some iap ->
            (match cmp_nest_of ac iap with
             | None -> None
             | Some nest ->
               let nres = cmp_nested_get res nest in
               let nres1 =
                 (match cmp_lookup nres iap with
                  | Some _ -> nres
                  | None -> List.Tot.append nres [(iap, JArray [])]) in
               compact_fields ac tsc aprop inside_rev rest
                 (cmp_nested_put res nest nres1) co (fuel - 1)))
       | _ ->
         (match compact_prop_items ac k (jexp_as_array v) inside_rev res co (fuel - 1) with
          | None -> None
          | Some res1 -> compact_fields ac tsc aprop inside_rev rest res1 co (fuel - 1)))

and compact_prop_items (ac:active_context) (k:string) (items:list json_val)
                       (inside_rev:bool) (res:list (string & json_val))
                       (co:cmp_opts) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None else
  match items with
  | [] -> Some res
  | it :: rest ->
    (match compact_one_item ac k it inside_rev res co (fuel - 1) with
     | None -> None
     | Some res1 -> compact_prop_items ac k rest inside_rev res1 co (fuel - 1))

and compact_one_item (ac:active_context) (k:string) (item:json_val)
                     (inside_rev:bool) (res:list (string & json_val))
                     (co:cmp_opts) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None else
  match compact_iri ac co k (Some item) true inside_rev 2 with
  | None -> None
  | Some iap ->
    (match cmp_nest_of ac iap with
     | None -> None
     | Some nest ->
       let td_iap = jldctx_find_term ac.ac_terms iap in
       let container =
         (match td_iap with
          | Some td -> if td.td_iri = "@null" then [] else cmp_container_list td
          | None -> []) in
       let is_list = cmp_is_list_object item in
       let is_graph = cmp_is_graph_object item in
       let inner =
         if is_list then (match cmp_obj_field item "@list" with Some x -> x | None -> item)
         else if is_graph then (match cmp_obj_field item "@graph" with Some x -> x | None -> item)
         else item in
       (match compact_elem ac (Some iap) inner co (fuel - 1) with
        | None -> None
        | Some ci0 ->
          let nres = cmp_nested_get res nest in
          if is_list then
            (let ci_arr = (match ci0 with | JArray _ -> ci0 | x -> JArray [x]) in
             if not (List.Tot.mem "@list" container) then
               (let listobj =
                  List.Tot.append
                    [(cmp_alias_kw ac co "@list", ci_arr)]
                    (match cmp_obj_field item "@index" with
                     | Some ix -> [(cmp_alias_kw ac co "@index", ix)]
                     | None -> []) in
                cmp_item_add ac k iap container item (JObject listobj) nest res nres co (fuel - 1))
             else
               // an @list container holds AT MOST one list — a second is
               // the "compaction to list of lists" error (compact/e001)
               (match cmp_lookup nres iap with
                | Some _ -> None
                | None ->
                  Some (cmp_nested_put res nest (List.Tot.append nres [(iap, ci_arr)]))))
          else if is_graph then
            compact_graph_item ac k iap container item ci0 nest res nres co (fuel - 1)
          else
            cmp_item_add ac k iap container item ci0 nest res nres co (fuel - 1)))

and compact_graph_item (ac:active_context) (k iap:string) (container:list string)
                       (item ci0:json_val) (nest:option string)
                       (res nres:list (string & json_val))
                       (co:cmp_opts) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None else
  let as_set = List.Tot.mem "@set" container in
  let has_graph = List.Tot.mem "@graph" container in
  if has_graph && List.Tot.mem "@id" container then
    (let key_res =
       (match cmp_obj_field item "@id" with
        | Some (JString gid) -> compact_iri ac co gid None false false 2
        | _ -> compact_iri ac co "@none" None true false 2) in
     match key_res with
     | None -> None
     | Some keyk ->
       let mapObj = (match cmp_lookup nres iap with Some (JObject mf) -> mf | _ -> []) in
       // the compacted graph content is an array of graph NODES — spread
       // them into the map entry (t0084: single node collapses; @set
       // keeps the array)
       let mapObj1 = cmp_generic_add mapObj keyk ci0 as_set in
       Some (cmp_nested_put res nest (cmp_replace_or_add nres iap (JObject mapObj1))))
  else if has_graph && List.Tot.mem "@index" container && cmp_is_simple_graph item then
    (let keyk =
       (match cmp_obj_field item "@index" with
        | Some (JString ix) -> ix
        | _ -> cmp_alias_kw ac co "@none") in
     let mapObj = (match cmp_lookup nres iap with Some (JObject mf) -> mf | _ -> []) in
     let mapObj1 = cmp_generic_add mapObj keyk ci0 as_set in
     Some (cmp_nested_put res nest (cmp_replace_or_add nres iap (JObject mapObj1))))
  else if has_graph && cmp_is_simple_graph item then
    // multiple nodes of one simple graph re-wrap under @included
    (let ci1 =
       (match ci0 with
        | JArray xs -> if List.Tot.length xs > 1
                       then JObject [(cmp_alias_kw ac co "@included", ci0)]
                       else ci0
        | _ -> ci0) in
     let as_arr = (not co.co_arrays) || as_set in
     Some (cmp_nested_put res nest (cmp_generic_add nres iap ci1 as_arr)))
  else
    // no matching graph container: wrap explicitly as a graph object
    (let ci1 =
       (match ci0 with
        | JArray [x] -> if co.co_arrays then x else ci0
        | _ -> ci0) in
     let id_fields_opt =
       (match cmp_obj_field item "@id" with
        | Some (JString gid) ->
          (match compact_iri ac co gid None false false 2 with
           | Some cg -> Some [(cmp_alias_kw ac co "@id", JString cg)]
           | None -> None)
        | _ -> Some []) in
     match id_fields_opt with
     | None -> None
     | Some id_fields ->
       let gwrap =
         List.Tot.append
           [(cmp_alias_kw ac co "@graph", ci1)]
           (List.Tot.append id_fields
              (match cmp_obj_field item "@index" with
               | Some ix -> [(cmp_alias_kw ac co "@index", ix)]
               | None -> [])) in
       let as_arr = (not co.co_arrays) || as_set in
       Some (cmp_nested_put res nest (cmp_generic_add nres iap (JObject gwrap) as_arr)))

and cmp_item_add (ac:active_context) (k iap:string) (container:list string)
                 (item ci:json_val) (nest:option string)
                 (res nres:list (string & json_val))
                 (co:cmp_opts) (fuel:nat)
  : Tot (option (list (string & json_val))) (decreases fuel) =
  if fuel = 0 then None else
  let as_set = List.Tot.mem "@set" container in
  if List.Tot.mem "@language" container || List.Tot.mem "@index" container
     || List.Tot.mem "@id" container || List.Tot.mem "@type" container then
    (let mapObj = (match cmp_lookup nres iap with Some (JObject mf) -> mf | _ -> []) in
     let step_res : option (option string & json_val & bool) =
       // (map key if determined, adjusted compacted item, needs-@type-recompact)
       if List.Tot.mem "@language" container then
         (let ci' =
            (match item with
             | JObject f ->
               if jexp_has_field "@value" f
               then (match cmp_field f "@value" with Some vv -> vv | None -> ci)
               else ci
             | _ -> ci) in
          Some ((match cmp_obj_field item "@language" with
                 | Some (JString l) -> Some l
                 | _ -> None), ci', false))
       else if List.Tot.mem "@index" container then
         (match jldctx_find_term ac.ac_terms iap with
          | Some td ->
            (match td.td_index with
             | Some ik ->
               // property-valued index: pull the index property's first
               // value out of the compacted item as the map key. The
               // container key is tried under the RAW td_index spelling
               // first ("predicate", "ex:name" — how the property
               // usually appears in the compacted item, since the same
               // context that wrote the @index member also compacts the
               // property; compact/0112/0114), then under the
               // IRI-compaction of its expansion (the spec's
               // "reinitialize container key by IRI compacting index
               // key" — needed when td_index is spelled as an absolute
               // IRI, compact/0113).
               ((match ci with
                      | JObject cf ->
                        let ck_opt : option string =
                          (match cmp_lookup cf ik with
                           | Some _ -> Some ik
                           | None ->
                             (match expand_iri ac ik true with
                              | Some ikiri ->
                                (match compact_iri ac co ikiri None true false 2 with
                                 | Some ck -> Some ck
                                 | None -> None)
                              | None -> None)) in
                        (match ck_opt with
                         | None -> Some (None, ci, false)
                         | Some ck ->
                           (match cmp_lookup cf ck with
                            | Some kv ->
                              (match jexp_as_array kv with
                               | JString k0 :: others ->
                                 let cf1 =
                                   (match others with
                                    | [] -> cmp_remove_key cf ck
                                    | [o] -> cmp_replace_or_add cf ck o
                                    | os -> cmp_replace_or_add cf ck (JArray os)) in
                                 Some (Some k0, JObject cf1, false)
                               | _ -> Some (None, ci, false))
                            | None -> Some (None, ci, false)))
                      | _ -> Some (None, ci, false)))
             | None ->
               (let ci' =
                  (match ci with
                   | JObject cf -> JObject (cmp_remove_key cf (cmp_alias_kw ac co "@index"))
                   | _ -> ci) in
                Some ((match cmp_obj_field item "@index" with
                       | Some (JString ix) -> Some ix
                       | _ -> None), ci', false)))
          | None ->
            (let ci' =
               (match ci with
                | JObject cf -> JObject (cmp_remove_key cf (cmp_alias_kw ac co "@index"))
                | _ -> ci) in
             Some ((match cmp_obj_field item "@index" with
                    | Some (JString ix) -> Some ix
                    | _ -> None), ci', false)))
       else if List.Tot.mem "@id" container then
         (let idk = cmp_alias_kw ac co "@id" in
          match ci with
          | JObject cf ->
            Some ((match cmp_lookup cf idk with
                   | Some (JString s) -> Some s
                   | _ -> None), JObject (cmp_remove_key cf idk), false)
          | _ -> Some (None, ci, false))
       else
         // @type map
         (let tk = cmp_alias_kw ac co "@type" in
          match ci with
          | JObject cf ->
            (match cmp_lookup cf tk with
             | Some tv ->
               (match jexp_as_array tv with
                | JString k0 :: others ->
                  let cf1 =
                    (match others with
                     | [] -> cmp_remove_key cf tk
                     | [o] -> cmp_replace_or_add cf tk o
                     | os -> cmp_replace_or_add cf tk (JArray os)) in
                  Some (Some k0, JObject cf1, true)
                | _ -> Some (None, JObject (cmp_remove_key cf tk), true))
             | None -> Some (None, ci, true))
          | _ -> Some (None, ci, false)) in
     match step_res with
     | None -> None
     | Some (key_opt, ci1, type_recheck) ->
       // @type-map refinement: a bare {"@id": ...} remnant recompacts as
       // a node reference (possibly to a plain string)
       let ci2_opt : option json_val =
         if type_recheck then
           (match ci1 with
            | JObject [kv] ->
              if fst kv = cmp_alias_kw ac co "@id" && Some? (cmp_obj_field item "@id") then
                (match cmp_obj_field item "@id" with
                 | Some idv ->
                   (match compact_elem ac (Some iap) (JObject [("@id", idv)]) co (fuel - 1) with
                    | None -> None
                    | Some rec_ci ->
                      // a bare node-reference remnant in a type map
                      // compacts all the way to its @id string
                      // (compact/tm020, s002's mytype)
                      (match rec_ci with
                       | JObject [kv2] ->
                         if fst kv2 = cmp_alias_kw ac co "@id" then Some (snd kv2) else Some rec_ci
                       | _ -> Some rec_ci))
                 | None -> Some ci1)
              else Some ci1
            | _ -> Some ci1)
         else Some ci1 in
       (match ci2_opt with
        | None -> None
        | Some ci2 ->
          let keyk = (match key_opt with Some s -> s | None -> cmp_alias_kw ac co "@none") in
          let mapObj1 = cmp_add_value mapObj keyk ci2 as_set in
          Some (cmp_nested_put res nest (cmp_replace_or_add nres iap (JObject mapObj1)))))
  else
    (let as_arr =
       (not co.co_arrays) || as_set || List.Tot.mem "@list" container
       || (match ci with | JArray [] -> true | _ -> false)
       || k = "@list" || k = "@graph" in
     Some (cmp_nested_put res nest (cmp_generic_add nres iap ci as_arr)))

#pop-options

// ================================================================
// JsonLdProcessor.compact(): expand, process the supplied context,
// compact, re-attach the original context.
// ================================================================

// Is the supplied context value "empty" for the purposes of the final
// "@context" re-attachment (null / {} / [] / an array of nothing)?
let cmp_ctx_is_empty (ctx:json_val) : bool =
  match ctx with
  | JNull -> true
  | JObject [] -> true
  | JArray [] -> true
  | _ -> false

// input:            the JSON-LD document text (expanded by
//                   Parser.JSONLD.expand_document, so un-expanded input
//                   is fine too).
// ctx_doc:          the compaction context DOCUMENT text; its top-level
//                   "@context" member (or, failing that, the whole
//                   document value) is both processed and re-attached
//                   verbatim to the output.
// base:             the input document's base IRI (manifest option.base,
//                   or baseIri + input path) — seeds expansion AND the
//                   active context's base for relative-IRI compaction.
// ctx_url:          the context document's own URL (remote refs inside it
//                   resolve against this, not against base).
// compact_arrays:   the API's compactArrays option (default true).
// compact_to_rel:   the API's compactToRelative option (default true).
// processing_mode:  "json-ld-1.0" selects 1.0 mode, anything else 1.1
//                   (same convention as expand_document).
let compact_document (input ctx_doc:string) (base ctx_url:option string)
                     (compact_arrays compact_to_rel:bool)
                     (processing_mode:option string)
  : option json_val =
  match expand_document input base None processing_mode with
  | None -> None
  | Some expanded ->
    (match parse_json ctx_doc with
     | None -> None
     | Some ctx_root ->
       let ctx_val =
         (match ctx_root with
          | JObject cf -> (match cmp_field cf "@context" with Some c -> c | None -> ctx_root)
          | _ -> ctx_root) in
       let mode10 = (processing_mode = Some "json-ld-1.0") in
       let ac_seed =
         { empty_active_context with
           ac_base = base; ac_mode10 = mode10;
           ac_doc_url = (match ctx_url with Some u -> Some u | None -> base);
           ac_original_base = base } in
       (match context_process ac_seed ctx_val false jld_remote_context_fuel [] with
        | None -> None
        | Some ac ->
          let co = { co_arrays = compact_arrays; co_rel = compact_to_rel } in
          let fuel = op_Multiply 16 (json_size expanded) + 128 in
          (match compact_elem ac None expanded co fuel with
           | None -> None
           | Some compacted0 ->
             let compacted1 =
               (if compact_arrays then
                  (match compacted0 with
                   | JArray [] -> JObject []
                   | JArray [x] -> x
                   | other -> other)
                else compacted0) in
             let wrapped_opt =
               (match compacted1 with
                | JArray _ ->
                  Some (JObject [(cmp_alias_kw ac co "@graph", compacted1)])
                | JObject fs -> Some (JObject fs)
                | other -> Some other) in
             (match wrapped_opt with
              | None -> None
              | Some wrapped ->
                if cmp_ctx_is_empty ctx_val then Some wrapped
                else
                  (match wrapped with
                   | JObject fs -> Some (JObject (("@context", ctx_val) :: fs))
                   | other -> Some other)))))
