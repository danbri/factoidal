module RDF.Canonical

(* RDF Dataset Canonicalization 1.0 (RDFC-1.0) — Phase 1 (HFDQ).

   Spec: https://www.w3.org/TR/rdf-canon/

   This module implements the Hash First Degree Quads ("HFDQ") branch
   of the RDFC-1.0 algorithm plus a deterministic identifier issuer.
   Phase-1 scope:

     - Render quads in canonical N-Quads form (per spec §4.7.3).
     - For each blank node, compute its HFDQ — SHA-256 over its
       lexicographically-sorted, locally-rewritten incident quads
       (own bnode → "_:a", others → "_:z").
     - Assign canonical labels "_:c14n0", "_:c14n1", … in HFDQ-sort
       order. Ties (HFDQ collisions) are currently broken by the
       original blank-node label, which is wrong for symmetric
       graphs where Phase 2 (HNDQ) is required.
     - Produce a canonicalised dataset where every blank-node label
       is replaced by its canonical form.

   Phase 2 (Hash N-Degree Quads) handles HFDQ collisions properly via
   bounded permutation enumeration over neighbouring bnodes; deferred.

   Per CLAUDE.md rules #1, #4, #10 — semantic logic lives here in F*,
   not in OCaml glue. The runner just calls `canonicalize`.
*)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

(* ------------------------------------------------------------------ *)
(* Hash primitive — assumed external; wired to Fstar_pure_hashes.sha256
   by ocaml-patches.sh (issue #63 patch). *)
assume val hash_sha256 : string -> string

(* ------------------------------------------------------------------ *)
(* Section 1. Canonical N-Quads serialisation
   per RDFC-1.0 §4.7.3 / N-Triples §4. *)

(* N-Triples character escaping: backslash, quote, LF, CR, TAB. We do
   not perform full UTF-8 \uXXXX escaping here; the rdf-canon test
   inputs are ASCII-clean for the lexical forms we care about. *)
let escape_lit_char (c : FStar.Char.char) : string =
  let n = FStar.Char.int_of_char c in
  if n = 0x5C then "\\\\"        // backslash
  else if n = 0x22 then "\\\""   // double quote
  else if n = 0x0A then "\\n"
  else if n = 0x0D then "\\r"
  else if n = 0x09 then "\\t"
  else FStar.String.string_of_char c

let rec escape_lit_acc (s : string) (pos : nat) (fuel : nat) (acc : string)
  : Tot string (decreases fuel) =
  if fuel = 0 then acc
  else
    let len = String.length s in
    if pos >= len then acc
    else
      let c = String.index s pos in
      escape_lit_acc s (pos + 1) (fuel - 1) (acc ^ escape_lit_char c)

let escape_lit (s : string) : string =
  escape_lit_acc s 0 (String.length s + 1) ""

let canon_term (t : rdf_term) : string =
  match t with
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let lex = escape_lit l.lexical_form in
    (match l.lang_tag with
     | Some tag -> "\"" ^ lex ^ "\"@" ^ tag
     | None ->
       if l.datatype = xsd_string then "\"" ^ lex ^ "\""
       else "\"" ^ lex ^ "\"^^<" ^ l.datatype ^ ">")

let canon_subject (s : subject) : string =
  match s with
  | S_IRI i -> "<" ^ i ^ ">"
  | S_BNode b -> "_:" ^ b

(* Render a quad with its graph name. Default graph: graph slot omitted. *)
let canon_quad (graph_name : option iri) (t : triple) : string =
  let g = match graph_name with
    | Some gi -> " <" ^ gi ^ ">"
    | None -> ""
  in
  canon_subject t.s ^ " <" ^ t.p ^ "> " ^ canon_term t.o ^ g ^ " .\n"

(* ------------------------------------------------------------------ *)
(* Section 2. Quads with graph names (flattened dataset view).

   The algorithm reasons over (graph_name, triple) pairs; the
   default graph is `None`. *)

type qquad = (option iri * triple)

let rec attach_graph (g : option iri) (ts : list triple)
  : Tot (list qquad) (decreases ts) =
  match ts with
  | [] -> []
  | hd :: tl -> (g, hd) :: attach_graph g tl

let rec flatten_named (named : list named_graph)
  : Tot (list qquad) (decreases named) =
  match named with
  | [] -> []
  | ng :: rest ->
    attach_graph (Some ng.ng_name) ng.ng_graph @ flatten_named rest

let dataset_quads (ds : rdf_dataset) : list qquad =
  attach_graph None ds.ds_default @ flatten_named ds.ds_named

(* ------------------------------------------------------------------ *)
(* Section 3. Blank-node enumeration. *)

let bnodes_in_quad (qq : qquad) : list bnode_id =
  let (_, t) = qq in
  let l1 = match t.s with | S_BNode b -> [b] | _ -> [] in
  let l2 = match t.o with | T_BNode b -> [b] | _ -> [] in
  l1 @ l2

let rec mem_string (x : string) (xs : list string) : bool =
  match xs with
  | [] -> false
  | hd :: tl -> hd = x || mem_string x tl

let rec dedup_strings_acc (acc : list string) (xs : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if mem_string hd acc then dedup_strings_acc acc tl
    else dedup_strings_acc (hd :: acc) tl

let dedup_strings (xs : list string) : list string =
  dedup_strings_acc [] xs

let rec all_bnodes_acc (acc : list bnode_id) (qs : list qquad)
  : Tot (list bnode_id) (decreases qs) =
  match qs with
  | [] -> acc
  | q :: rest -> all_bnodes_acc (acc @ bnodes_in_quad q) rest

let dataset_bnodes (ds : rdf_dataset) : list bnode_id =
  dedup_strings (all_bnodes_acc [] (dataset_quads ds))

(* ------------------------------------------------------------------ *)
(* Section 4. Hash First Degree Quads (HFDQ).

   For a blank node `b`, render every quad in which `b` appears,
   replacing:
     - occurrences of `b` itself by `_:a`
     - occurrences of any other bnode by `_:z`
   Sort the rendered quads lexicographically, concatenate, SHA-256.
*)

let rewrite_subject_for_hfdq (target : bnode_id) (s : subject) : subject =
  match s with
  | S_BNode b -> if b = target then S_BNode "a" else S_BNode "z"
  | S_IRI _ -> s

let rewrite_term_for_hfdq (target : bnode_id) (t : rdf_term) : rdf_term =
  match t with
  | T_BNode b -> if b = target then T_BNode "a" else T_BNode "z"
  | _ -> t

let rewrite_triple_for_hfdq (target : bnode_id) (t : triple) : triple =
  {
    s = rewrite_subject_for_hfdq target t.s;
    p = t.p;
    o = rewrite_term_for_hfdq target t.o;
  }

let quad_mentions_bnode (target : bnode_id) (q : qquad) : bool =
  let (_, t) = q in
  (match t.s with | S_BNode b -> b = target | _ -> false) ||
  (match t.o with | T_BNode b -> b = target | _ -> false)

let rec quads_for_bnode_acc (target : bnode_id) (qs : list qquad)
                            (acc : list qquad)
  : Tot (list qquad) (decreases qs) =
  match qs with
  | [] -> List.Tot.rev acc
  | q :: rest ->
    if quad_mentions_bnode target q
    then quads_for_bnode_acc target rest (q :: acc)
    else quads_for_bnode_acc target rest acc

let quads_for_bnode (target : bnode_id) (qs : list qquad) : list qquad =
  quads_for_bnode_acc target qs []

let render_for_hfdq (target : bnode_id) (q : qquad) : string =
  let (g, t) = q in
  canon_quad g (rewrite_triple_for_hfdq target t)

let rec render_all_for_hfdq (target : bnode_id) (qs : list qquad)
  : Tot (list string) (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest -> render_for_hfdq target q :: render_all_for_hfdq target rest

(* Lexicographic comparison over strings — compare codepoint by
   codepoint, shorter prefix wins on tie. F* doesn't expose `<=`
   on string, so we do this by hand over `String.index`. *)
let rec str_le_from (a b : string) (pos : nat) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else
    let la = String.length a in
    let lb = String.length b in
    if pos >= la then true        // a exhausted (prefix or equal): a <= b
    else if pos >= lb then false  // b exhausted, a not: a > b
    else
      let ca = FStar.Char.int_of_char (String.index a pos) in
      let cb = FStar.Char.int_of_char (String.index b pos) in
      if ca < cb then true
      else if ca > cb then false
      else str_le_from a b (pos + 1) (fuel - 1)

let str_le (a b : string) : bool =
  let la = String.length a in
  let lb = String.length b in
  let m = if la < lb then lb else la in
  str_le_from a b 0 (m + 1)

let str_eq (a b : string) : bool = a = b

let rec insert_sorted (x : string) (xs : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> [x]
  | hd :: tl ->
    if str_le x hd then x :: xs
    else hd :: insert_sorted x tl

let rec insertion_sort (xs : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl -> insert_sorted hd (insertion_sort tl)

let rec concat_strings (xs : list string)
  : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | hd :: tl -> hd ^ concat_strings tl

let compute_hfdq (target : bnode_id) (qs : list qquad) : string =
  let mentioning = quads_for_bnode target qs in
  let rendered = render_all_for_hfdq target mentioning in
  let sorted = insertion_sort rendered in
  hash_sha256 (concat_strings sorted)

(* ------------------------------------------------------------------ *)
(* Section 5. Identifier issuer.

   A list of (original-bnode, canonical-label) pairs plus a counter.
   Issuance is sequential — calling `issue` with a fresh original
   produces "_:c14n<n>" and advances the counter. *)

(* Decimal rendering of a nat — F* doesn't ship a stdlib `string_of_nat`
   we can rely on extracting cleanly; provide a self-contained version. *)
let digit_char (d : nat) : string =
  if d = 0 then "0"
  else if d = 1 then "1"
  else if d = 2 then "2"
  else if d = 3 then "3"
  else if d = 4 then "4"
  else if d = 5 then "5"
  else if d = 6 then "6"
  else if d = 7 then "7"
  else if d = 8 then "8"
  else "9"

let rec nat_to_string_acc (n : nat) (acc : string) (fuel : nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then acc
  else if n < 10 then digit_char n ^ acc
  else
    let q : nat = n / 10 in
    let r : nat = n % 10 in
    (* F* requires nonneg modulus on int; n >= 10 above means n > 0 so
       both operations are total. *)
    nat_to_string_acc q (digit_char r ^ acc) (fuel - 1)

let nat_to_string (n : nat) : string =
  if n = 0 then "0" else nat_to_string_acc n "" (n + 1)

type issuer_state = {
  is_counter : nat;
  is_issued  : list (bnode_id * string); (* original → canonical *)
}

let empty_issuer : issuer_state = {
  is_counter = 0;
  is_issued = [];
}

let rec lookup_issued (b : bnode_id) (xs : list (bnode_id * string))
  : Tot (option string) (decreases xs) =
  match xs with
  | [] -> None
  | (k, v) :: rest -> if k = b then Some v else lookup_issued b rest

let issue_identifier (st : issuer_state) (b : bnode_id)
  : (issuer_state * string) =
  match lookup_issued b st.is_issued with
  | Some v -> (st, v)
  | None ->
    let label = "c14n" ^ nat_to_string st.is_counter in
    let st' : issuer_state = {
      is_counter = st.is_counter + 1;
      is_issued = st.is_issued @ [(b, label)];
    } in
    (st', label)

(* ------------------------------------------------------------------ *)
(* Section 6. Phase-1 assignment driver.

   1. Compute HFDQ for every blank node.
   2. Sort (hfdq, original-label) pairs lexicographically — primary
      key hfdq, tiebreak original label.
   3. Phase 2 (HNDQ — see Section 6b) refines the tiebreak using
      structural information from neighbour bnodes.
   4. In sorted order, issue canonical identifiers.
*)

type bn_hfdq_pair = (bnode_id * string)  (* (orig, hfdq) *)

let rec compute_all_hfdq (qs : list qquad) (bs : list bnode_id)
  : Tot (list bn_hfdq_pair) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest -> (b, compute_hfdq b qs) :: compute_all_hfdq qs rest

let rec lookup_hfdq (b : bnode_id) (xs : list bn_hfdq_pair)
  : Tot string (decreases xs) =
  match xs with
  | [] -> ""  // sentinel — every bnode in the dataset is in the table
  | (k, h) :: rest -> if k = b then h else lookup_hfdq b rest

(* ------------------------------------------------------------------ *)
(* Section 6b. Hash N-Degree Quads (HNDQ) — single-level neighbour hash.

   Per RDFC-1.0 §4.9. The full spec recursively enumerates permutations
   of related bnodes through a cloned issuer; that handles graphs where
   every collision class is itself only resolvable by structural
   recursion (the "poison clique" / true-automorphism cases).

   This implementation lands a *bounded* HNDQ:

     - For each bnode `n`, walk the quads it appears in.
     - For each occurrence, identify the *related* bnode (the bnode
       in the other position of the same quad), the position tag
       ("s" if `n` is subject and the related bnode is object,
       "o" if `n` is object and the related bnode is subject,
       "g" if the related bnode is in the graph-name slot — currently
       not produced, since graph-name bnodes are uncommon, but the
       tag space is reserved), and the predicate IRI.
     - Build a list of strings of the form "<position>|<predicate>|<related_key>".
       For the level-1 hash, `related_key` is the related bnode's HFDQ;
       for the level-2 hash, it is the related bnode's level-1
       neighbour-hash. If a quad mentions only `n` (e.g. `n` linked
       to a literal or IRI, or `n` to itself in a self-loop where
       both ends are `n`), the related_key is a sentinel "_".
     - Sort the list lexicographically, concat, SHA-256.

   Termination is structural: we only walk `qs` and the (finite)
   list of HFDQ pairs, no fuel needed.

   Two passes (level-1 then level-2 over the level-1 results) catch
   collisions one structural step deeper than HFDQ alone. Spec-correct
   resolution of n-step-symmetric graphs requires the full
   permutation algorithm — deferred (see plan doc, test074c). *)

(* Position-tag for a quad mentioning `target`. We do NOT distinguish
   "target as subject" vs "target as object" in the rendered quad
   (canonical N-Quads serialisation already handles that), but we DO
   want symmetry-breaking when the same predicate connects two bnodes
   in opposite directions (e.g. `_:a foo _:b` vs `_:b foo _:a`). *)
let nbr_position_tag (target : bnode_id) (q : qquad) : string =
  let (_, t) = q in
  let s_is_target = match t.s with | S_BNode b -> b = target | _ -> false in
  let o_is_target = match t.o with | T_BNode b -> b = target | _ -> false in
  if s_is_target && o_is_target then "ss"  // self-loop: target both ways
  else if s_is_target then "s"              // target is subject
  else if o_is_target then "o"              // target is object
  else "_"                                   // shouldn't happen — caller filtered

(* Extract the related bnode (the *other* bnode in this quad), if any.
   Returns None when the quad has no second bnode (e.g. `_:n p "lit"`)
   or when target appears in both slots of a self-loop (treated as
   "no related" — symmetry handled by the position tag "ss"). *)
let related_bnode (target : bnode_id) (q : qquad) : option bnode_id =
  let (_, t) = q in
  let s_bn = match t.s with | S_BNode b -> Some b | _ -> None in
  let o_bn = match t.o with | T_BNode b -> Some b | _ -> None in
  match s_bn, o_bn with
  | Some sb, Some ob ->
    if sb = target && ob = target then None       // self-loop
    else if sb = target then Some ob
    else if ob = target then Some sb
    else None                                      // shouldn't happen
  | Some sb, None -> if sb = target then None else Some sb
  | None, Some ob -> if ob = target then None else Some ob
  | None, None -> None

(* For a single quad mentioning `target`, build the contribution
   "<pos>|<pred>|<related_key>". `key_of` resolves the related-bnode
   key (HFDQ for level-1, neighbour-hash for level-2). *)
let nbr_contribution
    (target : bnode_id)
    (q : qquad)
    (key_of : bnode_id -> string)
  : string =
  let (_, t) = q in
  let pos = nbr_position_tag target q in
  let pred = t.p in
  let rk = match related_bnode target q with
    | None -> "_"
    | Some rb -> key_of rb
  in
  pos ^ "|" ^ pred ^ "|" ^ rk

let rec nbr_contributions
    (target : bnode_id)
    (qs : list qquad)
    (key_of : bnode_id -> string)
  : Tot (list string) (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest ->
    nbr_contribution target q key_of :: nbr_contributions target rest key_of

(* Compute a neighbour-hash for `target`, using `key_of` to look up the
   key associated with each neighbouring bnode. The set of incident
   quads is filtered first; then each contribution is computed,
   sorted, concatenated, and hashed. *)
let compute_nbr_hash
    (target : bnode_id)
    (qs : list qquad)
    (key_of : bnode_id -> string)
  : string =
  let mentioning = quads_for_bnode target qs in
  let contribs = nbr_contributions target mentioning key_of in
  let sorted = insertion_sort contribs in
  hash_sha256 (concat_strings sorted)

(* Level-1 neighbour hashes for every bnode, keyed by HFDQ of the
   related bnode. *)
let rec compute_all_nbr1
    (qs : list qquad)
    (bs : list bnode_id)
    (hfdq_table : list bn_hfdq_pair)
  : Tot (list bn_hfdq_pair) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest ->
    let key_of (rb : bnode_id) : string = lookup_hfdq rb hfdq_table in
    let h = compute_nbr_hash b qs key_of in
    (b, h) :: compute_all_nbr1 qs rest hfdq_table

(* Level-2 neighbour hashes — uses the level-1 table as the related-key
   source. This catches collisions one structural step deeper. *)
let rec compute_all_nbr2
    (qs : list qquad)
    (bs : list bnode_id)
    (nbr1_table : list bn_hfdq_pair)
  : Tot (list bn_hfdq_pair) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest ->
    let key_of (rb : bnode_id) : string = lookup_hfdq rb nbr1_table in
    let h = compute_nbr_hash b qs key_of in
    (b, h) :: compute_all_nbr2 qs rest nbr1_table

(* ------------------------------------------------------------------ *)
(* Section 6c. Sorting with the HNDQ-augmented key.

   Sort key: (hfdq, nbr1, nbr2, orig). Two bnodes that agree on
   hfdq + nbr1 + nbr2 are very likely true automorphisms in the
   graph; any deterministic tiebreak is acceptable for them
   (the W3C reference output for true automorphisms is itself
   one arbitrary choice from the orbit — but it matches the
   reference's enumeration order). For those, fall through to
   original label. *)

type bn_full_key = {
  bk_orig : bnode_id;
  bk_hfdq : string;
  bk_nbr1 : string;
  bk_nbr2 : string;
}

let rec lookup_pair (b : bnode_id) (xs : list bn_hfdq_pair)
  : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | (k, v) :: rest -> if k = b then v else lookup_pair b rest

let rec build_full_keys
    (bs : list bnode_id)
    (hfdq_t : list bn_hfdq_pair)
    (nbr1_t : list bn_hfdq_pair)
    (nbr2_t : list bn_hfdq_pair)
  : Tot (list bn_full_key) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest ->
    {
      bk_orig = b;
      bk_hfdq = lookup_pair b hfdq_t;
      bk_nbr1 = lookup_pair b nbr1_t;
      bk_nbr2 = lookup_pair b nbr2_t;
    } :: build_full_keys rest hfdq_t nbr1_t nbr2_t

let full_key_le (a b : bn_full_key) : bool =
  if a.bk_hfdq <> b.bk_hfdq then str_le a.bk_hfdq b.bk_hfdq
  else if a.bk_nbr1 <> b.bk_nbr1 then str_le a.bk_nbr1 b.bk_nbr1
  else if a.bk_nbr2 <> b.bk_nbr2 then str_le a.bk_nbr2 b.bk_nbr2
  else str_le a.bk_orig b.bk_orig

let rec insert_full_key (x : bn_full_key) (xs : list bn_full_key)
  : Tot (list bn_full_key) (decreases xs) =
  match xs with
  | [] -> [x]
  | hd :: tl ->
    if full_key_le x hd then x :: xs
    else hd :: insert_full_key x tl

let rec sort_full_keys (xs : list bn_full_key)
  : Tot (list bn_full_key) (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl -> insert_full_key hd (sort_full_keys tl)

(* Legacy pair-based ordering (kept for backwards-compat / tests). *)
let pair_le (a b : bn_hfdq_pair) : bool =
  let (oa, ha) = a in
  let (ob, hb) = b in
  if ha = hb then str_le oa ob
  else str_le ha hb

let rec insert_pair (x : bn_hfdq_pair) (xs : list bn_hfdq_pair)
  : Tot (list bn_hfdq_pair) (decreases xs) =
  match xs with
  | [] -> [x]
  | hd :: tl ->
    if pair_le x hd then x :: xs
    else hd :: insert_pair x tl

let rec sort_pairs (xs : list bn_hfdq_pair)
  : Tot (list bn_hfdq_pair) (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl -> insert_pair hd (sort_pairs tl)

let rec assign_in_order (st : issuer_state) (xs : list bn_hfdq_pair)
  : Tot issuer_state (decreases xs) =
  match xs with
  | [] -> st
  | (orig, _) :: rest ->
    let (st', _) = issue_identifier st orig in
    assign_in_order st' rest

let rec assign_full_in_order (st : issuer_state) (xs : list bn_full_key)
  : Tot issuer_state (decreases xs) =
  match xs with
  | [] -> st
  | k :: rest ->
    let (st', _) = issue_identifier st k.bk_orig in
    assign_full_in_order st' rest

(* ------------------------------------------------------------------ *)
(* Section 7. Apply the issuer map to the dataset. *)

let relabel_subject (mapping : list (bnode_id * string)) (s : subject) : subject =
  match s with
  | S_IRI _ -> s
  | S_BNode b ->
    (match lookup_issued b mapping with
     | Some lbl -> S_BNode lbl
     | None -> s)

let relabel_term (mapping : list (bnode_id * string)) (t : rdf_term) : rdf_term =
  match t with
  | T_BNode b ->
    (match lookup_issued b mapping with
     | Some lbl -> T_BNode lbl
     | None -> t)
  | _ -> t

let relabel_triple (mapping : list (bnode_id * string)) (t : triple) : triple =
  {
    s = relabel_subject mapping t.s;
    p = t.p;
    o = relabel_term mapping t.o;
  }

let relabel_graph (mapping : list (bnode_id * string)) (g : rdf_graph) : rdf_graph =
  List.Tot.map (relabel_triple mapping) g

let relabel_named_graph (mapping : list (bnode_id * string)) (ng : named_graph)
  : named_graph =
  {
    ng_name = ng.ng_name;
    ng_graph = relabel_graph mapping ng.ng_graph;
  }

let relabel_dataset (mapping : list (bnode_id * string)) (ds : rdf_dataset)
  : rdf_dataset =
  {
    ds_default = relabel_graph mapping ds.ds_default;
    ds_named = List.Tot.map (relabel_named_graph mapping) ds.ds_named;
  }

(* ------------------------------------------------------------------ *)
(* Section 8. Public entry points. *)

(* Build the full canonical-id mapping for a dataset.

   Phase 1: HFDQ. Phase 2 (this version): adds two levels of
   neighbour-hash refinement to break HFDQ ties using the structural
   neighbourhood of each blank node. This handles the majority of
   eval tests where collisions stem from local symmetry — including
   tests where two collision-class members have neighbours with
   distinct HFDQ. True n-step automorphisms (test074c-style poison
   cliques) are not handled by this layer; they would require full
   permutation enumeration with a cloned issuer (deferred). *)
let build_canonical_mapping (ds : rdf_dataset) : list (bnode_id * string) =
  let qs = dataset_quads ds in
  let bs = dataset_bnodes ds in
  let hfdq_table = compute_all_hfdq qs bs in
  let nbr1_table = compute_all_nbr1 qs bs hfdq_table in
  let nbr2_table = compute_all_nbr2 qs bs nbr1_table in
  let keys = build_full_keys bs hfdq_table nbr1_table nbr2_table in
  let sorted = sort_full_keys keys in
  let final_state = assign_full_in_order empty_issuer sorted in
  final_state.is_issued

(* Canonicalise a dataset: relabel every blank node deterministically. *)
let canonicalize (ds : rdf_dataset) : rdf_dataset =
  let mapping = build_canonical_mapping ds in
  relabel_dataset mapping ds

(* Render a dataset to canonical N-Quads: emit each quad, sort the
   resulting lines lexicographically, concatenate. The relabelling
   must already have happened (call after `canonicalize`). *)
let rec render_quads (qs : list qquad)
  : Tot (list string) (decreases qs) =
  match qs with
  | [] -> []
  | (g, t) :: rest -> canon_quad g t :: render_quads rest

let canonical_nquads (ds : rdf_dataset) : string =
  let qs = dataset_quads ds in
  let lines = render_quads qs in
  let sorted = insertion_sort lines in
  concat_strings sorted

(* Convenience: canonicalise then serialise. *)
let canonicalize_to_nquads (ds : rdf_dataset) : string =
  canonical_nquads (canonicalize ds)
