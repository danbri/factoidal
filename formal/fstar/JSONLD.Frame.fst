module JSONLD.Frame

// ============================================================================
// JSON-LD 1.1 Framing Algorithm — FIRST CUT.
//
// https://www.w3.org/TR/json-ld11-framing/
//
// Framing lets a caller shape a JSON-LD document into a specific tree layout
// described by a "frame" document: which node types appear at the top level,
// which properties are embedded inline vs. left as references, and (in the
// full algorithm) defaults for missing values.
//
// This module implements the basic pipeline only:
//   expand input -> flatten to a node map -> match nodes against the frame ->
//   embed matched referenced nodes recursively -> wrap in @graph -> compact
//   against the frame's context.
//
// SUPPORTED (first cut):
//   - @type matching   (present / wildcard / IRI-set intersection)
//   - @id matching     (present / wildcard / id-set membership)
//   - property matching (must-be-present, must-be-absent [] , wildcard {})
//   - node embedding of node-references, with a visited set to break cycles
//     (approximates the default @embed=@once behaviour)
//
// NOT YET (refine later — see the framing spec):
//   - @explicit, @default, @omitDefault, @requireAll variations
//   - @embed=@always / @never / @link, @reverse, @included, named graphs
//   - value-object level matching inside a property frame
//
// All logic here is Tot and verifies with no --lax / no --admit_smt_queries.
// Recursion over the (untrusted, possibly cyclic) node graph is fuel-bounded.
// ============================================================================

open FStar.List.Tot
open Parser.JSON
open Parser.JSONLD
open JSONLD.Flatten
open JSONLD.Compact

// ================================================================
// Small total helpers over json_val
// ================================================================

// A JSON-LD keyword key starts with a commercial-at byte ('@' = 0x40).
let is_keyword (k:string) : bool =
  jbyte_at k 0 = 0x40

// The member list of a JSON object, or [] for any non-object.
let obj_fields (v:json_val) : list (string & json_val) =
  match v with
  | JObject fs -> fs
  | _ -> []

// Look a member up by key. String keys have decidable equality.
let obj_get (v:json_val) (k:string) : option json_val =
  List.Tot.assoc k (obj_fields v)

// Does an object carry this member at all?
let obj_has (v:json_val) (k:string) : bool =
  Some? (obj_get v k)

// Flatten a value that is expected to be an IRI or a list of IRIs to the
// plain list of the string payloads it carries (used for @type / @id).
let rec jstrings (v:json_val) : Tot (list string) (decreases v) =
  match v with
  | JString s -> [s]
  | JArray items -> jstrings_list items
  | _ -> []
and jstrings_list (items:list json_val) : Tot (list string) (decreases items) =
  match items with
  | [] -> []
  | hd :: tl -> jstrings hd @ jstrings_list tl

// The @type IRIs a node declares (expanded form: @type is an array of IRIs).
let node_types (node:json_val) : list string =
  match obj_get node "@type" with
  | Some tv -> jstrings tv
  | None -> []

// A node's @id string, if any.
let node_id (node:json_val) : option string =
  match obj_get node "@id" with
  | Some (JString s) -> Some s
  | _ -> None

// Is a value the empty object {} (the framing wildcard "match if present")?
let is_wildcard (v:json_val) : bool =
  match v with
  | JObject [] -> true
  | _ -> false

// Is a value the empty array [] (the framing "match if absent" marker)?
let is_empty_array (v:json_val) : bool =
  match v with
  | JArray [] -> true
  | _ -> false

// The values a node holds for property k (expanded form: an array).
let prop_values (node:json_val) (k:string) : list json_val =
  match obj_get node k with
  | Some (JArray xs) -> xs
  | Some other -> [other]
  | None -> []

// If v is a bare node-reference {"@id": X}, return X.
let ref_id (v:json_val) : option string =
  match v with
  | JObject fs ->
    (match List.Tot.assoc "@id" fs with
     | Some (JString x) -> Some x
     | _ -> None)
  | _ -> None

// The sub-frame governing a framed property's values. In expanded form the
// frame's property value is an array; take the first object as the frame
// (empty frame = match everything) — a bare object is accepted leniently.
let prop_subframe (fv:json_val) : json_val =
  match fv with
  | JArray (JObject o :: _) -> JObject o
  | JObject o -> JObject o
  | _ -> JObject []

// ================================================================
// Frame matching
// ================================================================

// Does a single frame constraint (k, fv) hold for node?
let match_one (k:string) (fv:json_val) (node:json_val) : bool =
  if k = "@type" then
    (let ft = jstrings fv in
     let nt = node_types node in
     if Nil? ft || is_wildcard fv then
       // present / wildcard: node must declare at least one @type
       Cons? nt
     else
       // node's @type IRIs must intersect the frame's @type IRIs
       List.Tot.existsb (fun t -> List.Tot.mem t ft) nt)
  else if k = "@id" then
    (let fid = jstrings fv in
     if is_wildcard fv || Nil? fid then true
     else (match node_id node with
           | Some nid -> List.Tot.mem nid fid
           | None -> false))
  else if is_keyword k then
    // any other JSON-LD keyword imposes no constraint in this first cut
    true
  else
    // a property IRI constraint
    if is_empty_array fv then not (obj_has node k)   // [] : must be absent
    else obj_has node k                              // present / wildcard {}

// Every frame constraint must hold (default @requireAll=false is satisfied
// by "all present constraints hold"; missing frame properties add nothing).
let rec matches_fields (frame_fields:list (string & json_val)) (node:json_val)
  : Tot bool (decreases frame_fields) =
  match frame_fields with
  | [] -> true
  | (k, fv) :: tl -> match_one k fv node && matches_fields tl node

let node_matches (frame node:json_val) : bool =
  matches_fields (obj_fields frame) node

// ================================================================
// Frame + embed core (fuel-bounded, cycle-guarded)
//
// Lexicographic termination measure %[fuel; phase; list-length]:
//   frame_node   at phase 2 -> calls frame_props at phase 1 (same fuel)
//   frame_props  at phase 1 -> calls frame_values at phase 0 (same fuel)
//   frame_values at phase 0 -> calls frame_node with fuel-1 (fuel drops)
// so every edge strictly decreases the measure.
// ================================================================

let rec frame_node (map:list (string & json_val)) (frame node:json_val)
                   (visited:list string) (fuel:nat)
  : Tot json_val (decreases %[fuel; 2; 0]) =
  if fuel = 0 then node
  else
    let id_entry =
      (match obj_get node "@id" with Some v -> [("@id", v)] | None -> []) in
    let type_entry =
      (match obj_get node "@type" with Some v -> [("@type", v)] | None -> []) in
    let prop_entries = frame_props map (obj_fields frame) node visited fuel in
    JObject (id_entry @ type_entry @ prop_entries)

// Walk the frame's members, building output property entries. @id / @type
// (and every other keyword) are skipped here — @id/@type were copied above.
and frame_props (map:list (string & json_val)) (frame_fields:list (string & json_val))
                (node:json_val) (visited:list string) (fuel:nat)
  : Tot (list (string & json_val)) (decreases %[fuel; 1; List.Tot.length frame_fields]) =
  match frame_fields with
  | [] -> []
  | (k, fv) :: tl ->
    let rest = frame_props map tl node visited fuel in
    if is_keyword k then rest
    else
      (match obj_get node k with
       | None -> rest
       | Some _ ->
         let vals = prop_values node k in
         let subframe = prop_subframe fv in
         let framed = frame_values map subframe vals visited fuel in
         (k, JArray framed) :: rest)

// Frame each value of a property. A node-reference into the map that is not
// on the visited path is embedded (recursively framed); everything else is
// copied verbatim.
and frame_values (map:list (string & json_val)) (subframe:json_val)
                 (vals:list json_val) (visited:list string) (fuel:nat)
  : Tot (list json_val) (decreases %[fuel; 0; List.Tot.length vals]) =
  match vals with
  | [] -> []
  | v :: tl ->
    let rest = frame_values map subframe tl visited fuel in
    let this =
      if fuel = 0 then v
      else
        (match ref_id v with
         | Some x ->
           (match List.Tot.assoc x map with
            | Some target ->
              if List.Tot.mem x visited then v            // cycle: keep the ref
              else frame_node map subframe target (x :: visited) (fuel - 1)
            | None -> v)                                   // unmatched: keep ref
         | None -> v) in
    this :: rest

// ================================================================
// Top level
// ================================================================

// Build the node map (id -> node) from a flattened node list, in order.
let rec build_node_map (nodes:list json_val)
  : Tot (list (string & json_val)) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: tl ->
    (match node_id n with
     | Some id -> (id, n) :: build_node_map tl
     | None -> build_node_map tl)

// The frame object out of an expanded frame (a JArray of one object).
let first_frame (frame_exp:json_val) : json_val =
  match frame_exp with
  | JArray (JObject o :: _) -> JObject o
  | JObject o -> JObject o
  | _ -> JObject []   // empty array / anything else -> empty frame (match all)

// Frame every matching node in document order.
let rec top_frame (map:list (string & json_val)) (frame:json_val)
                  (nodes:list json_val) (fuel:nat)
  : Tot (list json_val) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: tl ->
    let rest = top_frame map frame tl fuel in
    if node_matches frame n then
      (let seed = (match node_id n with Some id -> [id] | None -> []) in
       frame_node map frame n seed fuel :: rest)
    else rest

// ================================================================
// Public entry point
// ================================================================

// Frame `input_str` according to `frame_str`.
//   base:            document base IRI (seeds expansion + relative-IRI compaction)
//   processing_mode: "json-ld-1.0" selects 1.0 mode, anything else 1.1
// Returns the compacted framed result, or None on any processing error.
let frame_document (input_str frame_str:string) (base:option string)
                   (processing_mode:option string)
  : option json_val =
  match expand_document input_str base None processing_mode with
  | None -> None
  | Some expanded ->
    (match jld_flatten_expanded expanded with
     | None -> None
     | Some nodes ->
       let map = build_node_map nodes in
       (match expand_document frame_str base None processing_mode with
        | None -> None
        | Some frame_exp ->
          let frame = first_frame frame_exp in
          // Node-map order from jld_flatten_expanded is already deterministic
          // (it sorts by @id), so we consume it directly. A dedicated @id
          // sort here is a refine-later nicety, not a correctness need.
          let fuel = op_Multiply 16 (json_size expanded) + 128 in
          let trees = top_frame map frame nodes fuel in
          let framed = JObject [("@graph", JArray trees)] in
          let framed_str = jcanon_document framed in
          compact_document framed_str frame_str base None true true processing_mode))
