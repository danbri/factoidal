module JSONLD.Flatten

// ============================================================================
// JSON-LD 1.1 Flattening API (W3C JSON-LD 1.1 Processing Algorithms and
// API, Recommendation 16 July 2020, section "Flattening Algorithms"):
//
//   - Node Map Generation        (nmg below — API spec § 6.2): walk the
//     EXPANDED document, collecting every node's properties into a
//     per-graph node map keyed by node identifier, relabelling every
//     blank node identifier through the Generate Blank Node Identifier
//     issuer ("_:b0", "_:b1", … in first-issue order — the fixtures pin
//     the exact labels, so issue order follows the spec's step order:
//     @type items first, then @id, then @reverse / @graph / @included /
//     the remaining properties in code-point key order).
//   - the Flattening Algorithm   (jld_flatten_expanded — API spec § 6.1):
//     fold each named graph's nodes (ordered by id) under a `@graph`
//     entry of that graph's name-node in the default graph (graph names
//     ordered lexicographically), then emit the default graph's nodes
//     ordered by id, dropping nodes that consist ONLY of an `@id`.
//   - the JsonLdProcessor.flatten() entry point (flatten_document):
//     expand the input (Parser.JSONLD.expand_document — the same
//     Expansion Algorithm the expand/toRdf/compact suites exercise),
//     flatten, and — when the test supplies a context — compact the
//     flattened array with the landed Compaction machinery
//     (JSONLD.Compact.compact_elem), ensuring the result keeps a
//     top-level `@graph` (or its alias) and re-attaching the original
//     context value, mirroring JSONLD.Compact.compact_document's tail.
//
// Error model: option, same convention as JSONLD.Expand / JSONLD.Compact —
// None is an honest processing error (the flatten suite's single
// NegativeEvaluationTest: "conflicting indexes", raised when Node Map
// Generation step 6.8 sees two different @index values for one node id)
// OR fuel exhaustion (an honest failure, never a wrong answer).
//
// All map lookups here are on EXPANDED-form JSON (literal "@id"/"@value"
// keys — expansion has already resolved aliases); aliases only matter for
// the OUTPUT `@graph` key of the compaction step (cmp_alias_kw).
// ============================================================================

open FStar.List.Tot
open Parser.FastString
open RDF.Graph.Executable
open Parser.JSON
open JSONLD.Context
open JSONLD.Expand
open Parser.JSONLD
open JSONLD.Compact

// ================================================================
// Node map representation + small assoc helpers
// ================================================================

// A node's collected entries: "@id" first (always present), then
// "@type" / "@index" / properties in first-seen order. Emitted verbatim
// as a JObject — member order is insignificant under the suite's
// JCS-canonical comparison (Parser.JSONLD.jsonld_expanded_equal), but
// ARRAY order inside each property's value is significant and follows
// the spec's append order.
type nm_node = list (string & json_val)

// One graph's node map: node id -> node, in first-creation order
// (re-sorted by id at emission time — the spec's "ordered by id").
type nm_graph = list (string & nm_node)

// Whole-algorithm state: graph name -> graph ("@default" plus named
// graphs), the blank-node relabelling map (old label -> issued label),
// and the issuer counter.
type nm_state = {
  nm_graphs : list (string & nm_graph);
  nm_idmap  : list (string & string);
  nm_ctr    : nat;
}

let rec fl_lookup (#a:Type) (xs:list (string & a)) (k:string)
  : Tot (option a) (decreases xs) =
  match xs with
  | [] -> None
  | (k2, v) :: rest -> if k2 = k then Some v else fl_lookup rest k

// Replace k's value in place (preserving position) or append at the end.
let rec fl_upd (#a:Type) (xs:list (string & a)) (k:string) (v:a)
  : Tot (list (string & a)) (decreases xs) =
  match xs with
  | [] -> [(k, v)]
  | (k2, v2) :: rest -> if k2 = k then (k2, v) :: rest else (k2, v2) :: fl_upd rest k v

let rec fl_remove (#a:Type) (xs:list (string & a)) (k:string)
  : Tot (list (string & a)) (decreases xs) =
  match xs with
  | [] -> []
  | (k2, v2) :: rest -> if k2 = k then rest else (k2, v2) :: fl_remove rest k

// Insertion sort by key, code-point (byte-lexicographic) order — UTF-8
// byte order IS code point order, so string_lt realises the spec's
// "ordered lexicographically". Stable for equal keys.
let rec fl_insert_by_key (#a:Type) (kv:(string & a)) (xs:list (string & a))
  : Tot (list (string & a)) (decreases xs) =
  match xs with
  | [] -> [kv]
  | y :: rest ->
    if string_lt (fst kv) (fst y) then kv :: xs
    else y :: fl_insert_by_key kv rest

let rec fl_sort_by_key (#a:Type) (xs:list (string & a))
  : Tot (list (string & a)) (decreases xs) =
  match xs with
  | [] -> []
  | kv :: rest -> fl_insert_by_key kv (fl_sort_by_key rest)

// "value is already in the array" — the spec's duplicate check compares
// maps structurally; jsonld_expanded_equal (JCS canonical form) is that
// comparison: member order insignificant, array order significant,
// numbers by canonical value.
let rec fl_arr_contains (items:list json_val) (v:json_val)
  : Tot bool (decreases items) =
  match items with
  | [] -> false
  | hd :: tl -> jsonld_expanded_equal hd v || fl_arr_contains tl v

// ================================================================
// Node-level operations
// ================================================================

// Append v to node's prop array (creating the entry), skipping the
// append when dedup is set and an equal value is already present.
let node_append_prop (n:nm_node) (prop:string) (v:json_val) (dedup:bool) : nm_node =
  match fl_lookup n prop with
  | Some (JArray items) ->
    if dedup && fl_arr_contains items v then n
    else fl_upd n prop (JArray (items @ [v]))
  | Some other -> fl_upd n prop (JArray [other; v]) // non-array: defensive, never built here
  | None -> n @ [(prop, JArray [v])]

// Node Map Generation step 6.12.2: ensure the property entry exists
// (empty array) even if no value survives recursion.
let node_ensure_prop (n:nm_node) (prop:string) : nm_node =
  match fl_lookup n prop with
  | Some _ -> n
  | None -> n @ [(prop, JArray [])]

// Merge @type items into the node's @type array, skipping duplicates
// (step 6.7's "unless it already exists").
let rec fl_merge_type_items (existing:list json_val) (items:list json_val)
  : Tot (list json_val) (decreases items) =
  match items with
  | [] -> existing
  | hd :: tl ->
    if fl_arr_contains existing hd then fl_merge_type_items existing tl
    else fl_merge_type_items (existing @ [hd]) tl

let node_merge_types (n:nm_node) (items:list json_val) : nm_node =
  match fl_lookup n "@type" with
  | Some (JArray existing) -> fl_upd n "@type" (JArray (fl_merge_type_items existing items))
  | Some other -> fl_upd n "@type" (JArray (fl_merge_type_items [other] items))
  | None -> n @ [("@type", JArray (fl_merge_type_items [] items))]

// Step 6.8: a second, DIFFERENT @index for the same node id is the
// spec's "conflicting indexes" error (the suite's e001) — None.
let node_set_index (n:nm_node) (idx:json_val) : option nm_node =
  match fl_lookup n "@index" with
  | Some old -> if jsonld_expanded_equal old idx then Some n else None
  | None -> Some (n @ [("@index", idx)])

let node_has_only_id (n:nm_node) : bool =
  match n with
  | [(k, _)] -> k = "@id"
  | _ -> false

// ================================================================
// State-level operations
// ================================================================

let st_graph (st:nm_state) (g:string) : nm_graph =
  match fl_lookup st.nm_graphs g with
  | Some gr -> gr
  | None -> []

let st_put_graph (st:nm_state) (g:string) (gr:nm_graph) : nm_state =
  { st with nm_graphs = fl_upd st.nm_graphs g gr }

// Step 6.3: create graph[id] = { "@id": id } when absent (also registers
// the graph itself on first touch).
let st_ensure_node (st:nm_state) (g:string) (id:string) : nm_state =
  let gr = st_graph st g in
  match fl_lookup gr id with
  | Some _ -> st_put_graph st g gr
  | None -> st_put_graph st g (gr @ [(id, [("@id", JString id)])])

// Apply f to graph[id] (creating the node first if needed).
let st_node_update (st:nm_state) (g:string) (id:string) (f:nm_node -> nm_node) : nm_state =
  let gr = st_graph st g in
  match fl_lookup gr id with
  | Some n -> st_put_graph st g (fl_upd gr id (f n))
  | None -> st_put_graph st g (gr @ [(id, f [("@id", JString id)])])

// Add v to subject-node[aprop] when both an (IRI/bnode-string) active
// subject and an active property are in scope; a free-floating value
// with no subject is silently dropped (expansion has already removed
// the ones the spec drops — this is pure defence).
let st_add_value (st:nm_state) (agraph:string) (asubj:option json_val)
                 (aprop:option string) (v:json_val) (dedup:bool) : nm_state =
  match asubj, aprop with
  | Some (JString sid), Some p ->
    st_node_update st agraph sid (fun n -> node_append_prop n p v dedup)
  | _, _ -> st

// ================================================================
// Generate Blank Node Identifier (API spec § 7.2)
// ================================================================

// Relabel a specific existing blank node identifier: return its issued
// label if seen before, else issue "_:b<counter>" and record the mapping.
let fl_issue_keyed (st:nm_state) (old:string) : (string & nm_state) =
  match fl_lookup st.nm_idmap old with
  | Some nid -> (nid, st)
  | None ->
    let nid = String.concat "" ["_:b"; string_of_int st.nm_ctr] in
    (nid, { st with nm_idmap = st.nm_idmap @ [(old, nid)]; nm_ctr = st.nm_ctr + 1 })

// Issue a fresh label (the spec's issuer called with a null identifier —
// an anonymous node object with no @id).
let fl_issue_fresh (st:nm_state) : (string & nm_state) =
  (String.concat "" ["_:b"; string_of_int st.nm_ctr], { st with nm_ctr = st.nm_ctr + 1 })

// Node Map Generation step 3: relabel blank node identifiers among the
// element's @type items — this runs BEFORE @id issuance (the fixtures
// pin the resulting label order).
let rec fl_relabel_type_items (st:nm_state) (items:list json_val)
  : Tot (nm_state & list json_val) (decreases items) =
  match items with
  | [] -> (st, [])
  | JString s :: tl ->
    if jld_is_bnode_label s then
      let (nid, st1) = fl_issue_keyed st s in
      let (st2, tl') = fl_relabel_type_items st1 tl in
      (st2, JString nid :: tl')
    else
      let (st1, tl') = fl_relabel_type_items st tl in
      (st1, JString s :: tl')
  | hd :: tl ->
    let (st1, tl') = fl_relabel_type_items st tl in
    (st1, hd :: tl')

// Shape-preserving: a node object's @type is an array in expanded form,
// but a VALUE object's @type is a bare string — step 3 only substitutes
// blank node identifiers, it never re-shapes (flatten/0002 pins the
// value-object scalar staying scalar).
let fl_relabel_types (st:nm_state) (fields:list (string & json_val))
  : (nm_state & list (string & json_val)) =
  match fl_lookup fields "@type" with
  | Some (JArray items) ->
    let (st1, items') = fl_relabel_type_items st items in
    (st1, fl_upd fields "@type" (JArray items'))
  | Some (JString s) ->
    if jld_is_bnode_label s then
      let (nid, st1) = fl_issue_keyed st s in
      (st1, fl_upd fields "@type" (JString nid))
    else (st, fields)
  | _ -> (st, fields)

// ================================================================
// Node Map Generation (API spec § 6.2)
// ================================================================
//
// nmg element parameters mirror the spec's: node map (inside nm_state),
// active graph (a graph name), active subject (None, JString id, or —
// for the @reverse case — a JObject node reference), active property,
// and `acc` — the in-progress @list array (None = the spec's "list is
// null"). Returns the updated state and the updated accumulator.
// Fuel-threaded recursion, same convention as JSONLD.Compact.compact_elem;
// fuel exhaustion is None.

// The nmg_node body is one long spec-step pipeline (steps 6.1-6.12) —
// a single large VC; give z3 more headroom (no semantic change, no
// escape hatch: still a full proof, just a bigger resource budget).
#push-options "--z3rlimit 100"

let rec nmg (st:nm_state) (element:json_val) (agraph:string)
            (asubj:option json_val) (aprop:option string)
            (acc:option (list json_val)) (fuel:nat)
  : Tot (option (nm_state & option (list json_val))) (decreases fuel) =
  if fuel = 0 then None else
  match element with
  // Step 1: arrays — process each item in order.
  | JArray items -> nmg_items st items agraph asubj aprop acc (fuel - 1)
  | JObject fields0 ->
    // Step 3: relabel blank node identifiers among @type items.
    let (st, fields) = fl_relabel_types st fields0 in
    if jexp_has_field "@value" fields then
      // Step 4: value object.
      (match acc with
       | None -> Some (st_add_value st agraph asubj aprop (JObject fields) true, None)
       | Some xs -> Some (st, Some (xs @ [JObject fields])))
    else if jexp_has_field "@list" fields then
      // Step 5: list object — collect the nested items into a fresh
      // accumulator, then attach {"@list": [...]} where the spec says.
      (match fl_lookup fields "@list" with
       | None -> None // unreachable: jexp_has_field just held
       | Some lval ->
         (match nmg st lval agraph asubj aprop (Some []) (fuel - 1) with
          | Some (st1, Some litems) ->
            let result = JObject [("@list", JArray litems)] in
            (match acc with
             | None -> Some (st_add_value st1 agraph asubj aprop result false, None)
             | Some xs -> Some (st1, Some (xs @ [result])))
          | _ -> None))
    else
      // Step 6: node object.
      nmg_node st fields agraph asubj aprop acc (fuel - 1)
  // Scalars never appear in expanded form (expansion wraps every value
  // in a value object); drop defensively rather than error.
  | _ -> Some (st, acc)

and nmg_items (st:nm_state) (items:list json_val) (agraph:string)
              (asubj:option json_val) (aprop:option string)
              (acc:option (list json_val)) (fuel:nat)
  : Tot (option (nm_state & option (list json_val))) (decreases fuel) =
  if fuel = 0 then None else
  match items with
  | [] -> Some (st, acc)
  | hd :: tl ->
    (match nmg st hd agraph asubj aprop acc (fuel - 1) with
     | None -> None
     | Some (st1, acc1) -> nmg_items st1 tl agraph asubj aprop acc1 (fuel - 1))

// Step 6 body. `fields` arrives with @type already relabelled (step 3).
and nmg_node (st:nm_state) (fields:list (string & json_val)) (agraph:string)
             (asubj:option json_val) (aprop:option string)
             (acc:option (list json_val)) (fuel:nat)
  : Tot (option (nm_state & option (list json_val))) (decreases fuel) =
  if fuel = 0 then None else
  // Steps 6.1-6.2: determine id (relabelling blank node identifiers),
  // removing @id from element.
  let id_res : option (nm_state & string & list (string & json_val)) =
    (match fl_lookup fields "@id" with
     | Some (JString s) ->
       if jld_is_bnode_label s then
         let (nid, st1) = fl_issue_keyed st s in
         Some (st1, nid, fl_remove fields "@id")
       else Some (st, s, fl_remove fields "@id")
     | Some _ -> None // non-string @id cannot survive expansion
     | None ->
       let (nid, st1) = fl_issue_fresh st in
       Some (st1, nid, fields)) in
  match id_res with
  | None -> None
  | Some (st, id, fields) ->
    // Steps 6.3-6.4: ensure graph[id] exists.
    let st = st_ensure_node st agraph id in
    // Steps 6.5-6.6: link this node from where we came from.
    let (st, acc) =
      (match asubj with
       | Some (JObject reffields) ->
         // 6.5: reverse relationship — append the REFERENCING node's
         // reference to THIS node's active-property array (dedup).
         (match aprop with
          | Some p ->
            (st_node_update st agraph id
               (fun n -> node_append_prop n p (JObject reffields) true), acc)
          | None -> (st, acc))
       | _ ->
         (match aprop with
          | None -> (st, acc)
          | Some p ->
            let reference = JObject [("@id", JString id)] in
            (match acc with
             | Some xs -> (st, Some (xs @ [reference]))
             | None -> (st_add_value st agraph asubj (Some p) reference true, None)))) in
    // Step 6.7: merge @type into the node.
    let st =
      (match fl_lookup fields "@type" with
       | Some (JArray items) -> st_node_update st agraph id (fun n -> node_merge_types n items)
       | Some (JString s) -> st_node_update st agraph id (fun n -> node_merge_types n [JString s])
       | _ -> st) in
    let fields = fl_remove fields "@type" in
    // Step 6.8: @index (conflicting-indexes error surfaces as None).
    let idx_res : option (nm_state & list (string & json_val)) =
      (match fl_lookup fields "@index" with
       | Some idx ->
         let gr = st_graph st agraph in
         (match fl_lookup gr id with
          | Some n ->
            (match node_set_index n idx with
             | None -> None
             | Some n1 -> Some (st_put_graph st agraph (fl_upd gr id n1), fl_remove fields "@index"))
          | None -> Some (st, fl_remove fields "@index"))
       | None -> Some (st, fields)) in
    (match idx_res with
     | None -> None
     | Some (st, fields) ->
       // Step 6.9: @reverse — recurse into each reverse value with THIS
       // node's reference as active subject (map form ⇒ 6.5 above).
       let rev_res : option nm_state =
         (match fl_lookup fields "@reverse" with
          | Some (JObject rentries) ->
            nmg_reverse_entries st (jexp_sort_map_entries rentries) agraph id (fuel - 1)
          | Some _ -> None // @reverse must be a map in expanded form
          | None -> Some st) in
       (match rev_res with
        | None -> None
        | Some st ->
          let fields = fl_remove fields "@reverse" in
          // Step 6.10: @graph — recurse with id as the active graph.
          let graph_res : option nm_state =
            (match fl_lookup fields "@graph" with
             | Some gval ->
               (match nmg st gval id None None None (fuel - 1) with
                | Some (st1, _) -> Some st1
                | None -> None)
             | None -> Some st) in
          (match graph_res with
           | None -> None
           | Some st ->
             let fields = fl_remove fields "@graph" in
             // Step 6.11: @included — recurse in the SAME active graph,
             // with no active subject/property.
             let incl_res : option nm_state =
               (match fl_lookup fields "@included" with
                | Some ival ->
                  (match nmg st ival agraph None None None (fuel - 1) with
                   | Some (st1, _) -> Some st1
                   | None -> None)
                | None -> Some st) in
             (match incl_res with
              | None -> None
              | Some st ->
                let fields = fl_remove fields "@included" in
                // Step 6.12: remaining properties, code-point key order.
                (match nmg_props st (jexp_sort_map_entries fields) agraph id (fuel - 1) with
                 | None -> None
                 | Some st -> Some (st, acc))))))

and nmg_props (st:nm_state) (props:list (string & json_val)) (agraph:string)
              (id:string) (fuel:nat)
  : Tot (option nm_state) (decreases fuel) =
  if fuel = 0 then None else
  match props with
  | [] -> Some st
  | (p, v) :: tl ->
    // 6.12.1: properties that are blank node identifiers get relabelled
    // through the same issuer (generalized RDF).
    let (p', st) =
      if jld_is_bnode_label p then fl_issue_keyed st p else (p, st) in
    // 6.12.2: the property entry exists even if no value survives.
    let st = st_node_update st agraph id (fun n -> node_ensure_prop n p') in
    // 6.12.3: recurse with id as active subject.
    (match nmg st v agraph (Some (JString id)) (Some p') None (fuel - 1) with
     | None -> None
     | Some (st1, _) -> nmg_props st1 tl agraph id (fuel - 1))

and nmg_reverse_entries (st:nm_state) (entries:list (string & json_val))
                        (agraph:string) (id:string) (fuel:nat)
  : Tot (option nm_state) (decreases fuel) =
  if fuel = 0 then None else
  match entries with
  | [] -> Some st
  | (p, vals) :: tl ->
    (match nmg_reverse_values st (jld_as_array vals) p agraph id (fuel - 1) with
     | None -> None
     | Some st1 -> nmg_reverse_entries st1 tl agraph id (fuel - 1))

and nmg_reverse_values (st:nm_state) (vals:list json_val) (p:string)
                       (agraph:string) (id:string) (fuel:nat)
  : Tot (option nm_state) (decreases fuel) =
  if fuel = 0 then None else
  match vals with
  | [] -> Some st
  | v :: tl ->
    (match nmg st v agraph (Some (JObject [("@id", JString id)])) (Some p) None (fuel - 1) with
     | None -> None
     | Some (st1, _) -> nmg_reverse_values st1 tl p agraph id (fuel - 1))

#pop-options

// ================================================================
// Flattening Algorithm (API spec § 6.1)
// ================================================================

// Emit a sorted graph's nodes, dropping any that consist only of @id
// (steps 3.4 / 4's "unless node consists only of @id").
let rec fl_emit_nodes (nodes:list (string & nm_node))
  : Tot (list json_val) (decreases nodes) =
  match nodes with
  | [] -> []
  | (_, n) :: tl ->
    if node_has_only_id n then fl_emit_nodes tl
    else JObject n :: fl_emit_nodes tl

let rec fl_filter_named (graphs:list (string & nm_graph))
  : Tot (list (string & nm_graph)) (decreases graphs) =
  match graphs with
  | [] -> []
  | (g, gr) :: tl ->
    if g = "@default" then fl_filter_named tl else (g, gr) :: fl_filter_named tl

// Step 3: fold each named graph (ordered by name) under a @graph entry
// of its name-node in the default graph.
let rec fl_fold_named (dflt:nm_graph) (named:list (string & nm_graph))
  : Tot nm_graph (decreases named) =
  match named with
  | [] -> dflt
  | (gname, gr) :: tl ->
    let gnodes = fl_emit_nodes (fl_sort_by_key gr) in
    let dflt1 =
      (match fl_lookup dflt gname with
       | Some n -> fl_upd dflt gname (n @ [("@graph", JArray gnodes)])
       | None -> dflt @ [(gname, [("@id", JString gname); ("@graph", JArray gnodes)])]) in
    fl_fold_named dflt1 tl

// Flatten an EXPANDED document (a json_val, normally a JArray of node
// objects) to the ordered node array the flatten suite's context-free
// fixtures expect. None on a processing error (conflicting indexes) or
// fuel exhaustion.
let jld_flatten_expanded (expanded:json_val) : option (list json_val) =
  let fuel = op_Multiply 16 (json_size expanded) + 128 in
  let st0 = { nm_graphs = [("@default", [])]; nm_idmap = []; nm_ctr = 0 } in
  match nmg st0 expanded "@default" None None None fuel with
  | None -> None
  | Some (st, _) ->
    let dflt = st_graph st "@default" in
    let named = fl_sort_by_key (fl_filter_named st.nm_graphs) in
    let dflt1 = fl_fold_named dflt named in
    Some (fl_emit_nodes (fl_sort_by_key dflt1))

// ================================================================
// JsonLdProcessor.flatten(): expand, flatten, optionally compact.
// ================================================================

// input:            the JSON-LD document text (expanded here via
//                   Parser.JSONLD.expand_document).
// ctx_doc:          the OPTIONAL compaction context DOCUMENT text (the
//                   manifest's `context` file; most flatten tests have
//                   none and expect the bare flattened array).
// base:             the input document's base IRI (manifest option.base,
//                   or baseIri + input path) — seeds expansion AND the
//                   active context's base for relative-IRI compaction.
// ctx_url:          the context document's own URL (remote refs inside it
//                   resolve against this, not against base).
// compact_arrays:   the API's compactArrays option (default true) —
//                   only consulted when ctx_doc is supplied.
// processing_mode:  "json-ld-1.0" selects 1.0 mode, anything else 1.1
//                   (same convention as expand_document/compact_document).
let flatten_document (input:string) (ctx_doc:option string)
                     (base ctx_url:option string)
                     (compact_arrays:bool)
                     (processing_mode:option string)
  : option json_val =
  match expand_document input base None processing_mode with
  | None -> None
  | Some expanded ->
    (match jld_flatten_expanded expanded with
     | None -> None
     | Some flattened ->
       (match ctx_doc with
        | None -> Some (JArray flattened)
        | Some ctx_text ->
          // Spec § 6.1 step 6: compact the flattened array, ENSURING the
          // result keeps @graph (or its alias) at the top level, then
          // re-attach the original context — the same tail as
          // JSONLD.Compact.compact_document, minus its singleton
          // unwrapping (flatten's output shape is pinned to @graph).
          (match parse_json ctx_text with
           | None -> None
           | Some ctx_root ->
             let ctx_val =
               (match ctx_root with
                | JObject cf ->
                  (match cmp_field cf "@context" with Some c -> c | None -> ctx_root)
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
                let co = { co_arrays = compact_arrays; co_rel = true } in
                let farr = JArray flattened in
                let fuel = op_Multiply 16 (json_size farr) + 128 in
                (match compact_elem ac None farr co fuel with
                 | None -> None
                 | Some compacted0 ->
                   let garr =
                     (match compacted0 with
                      | JArray xs -> JArray xs
                      | other -> JArray [other]) in
                   let gkey = cmp_alias_kw ac co "@graph" in
                   if cmp_ctx_is_empty ctx_val then Some (JObject [(gkey, garr)])
                   else Some (JObject [("@context", ctx_val); (gkey, garr)]))))))
