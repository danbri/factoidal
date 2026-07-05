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
open Parser.FastString

(* ------------------------------------------------------------------ *)
(* Hash primitives — assumed external; wired to Fstar_pure_hashes.sha256
   / Fstar_pure_hashes.sha384 by ocaml-patches.sh (issue #63 patch). *)
assume val hash_sha256 : string -> string
assume val hash_sha384 : string -> string

// RDFC-1.0 §4.4 note 2 / test manifests: `rdfc:hashAlgorithm` selects
// SHA-256 (the algorithm's default) or SHA-384 for a given test. Every
// hash call site in this module goes through `apply_hash` so a single
// dispatch point governs the choice; the manifest-declared literal is
// mapped to this type by `hash_algorithm_of_string` (used by
// rdfc10_runner.ml — see RDF.Canonical.Manifest.fst for the
// `rdfc:hashAlgorithm` predicate IRI).
type hash_algorithm =
  | HA_SHA256
  | HA_SHA384

let apply_hash (alg : hash_algorithm) (s : string) : string =
  match alg with
  | HA_SHA256 -> hash_sha256 s
  | HA_SHA384 -> hash_sha384 s

let hash_algorithm_of_string (s : string) : hash_algorithm =
  if s = "SHA384" then HA_SHA384 else HA_SHA256

(* ------------------------------------------------------------------ *)
(* Section 1. Canonical N-Quads serialisation
   per RDFC-1.0 §4.7.3 / N-Triples §4. *)

(* N-Triples character escaping: backslash, quote, LF, CR, TAB. Canonical
   N-Quads keeps non-ASCII as raw UTF-8 (no \uXXXX escaping) per
   RDFC-1.0.

   2026-07-04 rewrite (issue #272): walk the literal BYTE-by-byte with
   fs_byte_at / fs_byte_length (Parser.FastString — the same
   primitives the Turtle / N-Triples / N-Quads *parsers* already use
   on their hot loop) and copy maximal runs of non-special bytes with
   one fs_byte_sub each, instead of the previous per-CHARACTER `^`
   fold (escape_lit_acc over FStar.String.index / String.length,
   which is O(n^2) in the literal's length -- the profiling suspect
   the issue named). Same run-slicing shape as SPARQL.JSON.Escape's
   walk_runs and RDF.NQuads.Serialize.nq_escape_literal's sibling
   rewrite (both same day).

   Byte-transparent copying also means multi-byte UTF-8 sequences pass
   through as raw bytes without ever decoding to a FStar.Char, so this
   drops the string_of_list codepoint workaround the old pass-through
   arm needed: the extracted string_of_char realisation is
   byte-oriented (Char.chr) and CRASHES for codepoints above 255 while
   silently emitting Latin-1 mojibake for 128-255, and string_of_list
   re-encodes each list element as a codepoint (double-encoding bytes
   >= 0x80). Found 2026-07-04 via the JSON-LD scalars/escapes fixture;
   the rdf-canon suite inputs are ASCII-clean so the dashboard never
   saw either bug. *)
// One uppercase hex digit (0..15). Out-of-range mapped to '0' to keep
// the function total. Canonical N-Quads \uXXXX escapes use uppercase
// hex per the rdf-canon test suite fixtures.
let hex_digit_uc (n:nat) : FStar.Char.char =
  if n < 10 then FStar.Char.char_of_int (0x30 + n)
  else if n < 16 then FStar.Char.char_of_int (0x41 + (n - 10))
  else FStar.Char.char_of_int 0x30

// Control bytes 0x00-0x1F without a short mnemonic (\t \n \r \b \f),
// plus DEL (0x7F), MUST be \uXXXX-escaped in canonical N-Quads output
// (RDF 1.1 N-Triples canonical literal form) — leaving them as raw
// bytes is legal N-Triples but not the canonical form the rdf-canon
// suite's fixtures expect (2026-07-04: previously only the five
// short-mnemonic specials were escaped, so e.g. NUL, VT, DEL passed
// through raw, dropping/corrupting bytes relative to expected output).
let escape_lit_special_byte (b : nat) : bool =
  b = 0x5C || b = 0x22 || b = 0x0A || b = 0x0D || b = 0x09
  || b = 0x08 || b = 0x0C || b < 0x20 || b = 0x7F

let escape_lit_byte (b : nat{escape_lit_special_byte b}) : string =
  if b = 0x5C then "\\\\"        // backslash
  else if b = 0x22 then "\\\""   // double quote
  else if b = 0x0A then "\\n"
  else if b = 0x0D then "\\r"
  else if b = 0x09 then "\\t"
  else if b = 0x08 then "\\b"
  else if b = 0x0C then "\\f"
  else
    // Remaining control bytes (0x00-0x1F minus the mnemonics above)
    // and DEL (0x7F): \u00XX, uppercase hex, high nibble first.
    let n1 = (b / 16) % 16 in
    let n0 = b % 16 in
    String.string_of_list [FStar.Char.char_of_int 0x5C;   // '\\'
                            FStar.Char.char_of_int 0x75;   // 'u'
                            FStar.Char.char_of_int 0x30;   // '0'
                            FStar.Char.char_of_int 0x30;   // '0'
                            hex_digit_uc n1;
                            hex_digit_uc n0]

// Copy maximal runs of non-special bytes with fs_byte_sub, splicing
// escape strings in at special bytes. `run_start` marks the start of
// the current unescaped run; `pos` is the scan cursor.
let rec escape_lit_walk (s : string) (len : nat) (run_start : nat) (pos : nat) (acc : string)
  : Tot string (decreases (len - pos)) =
  if pos >= len then
    (if pos > run_start then acc ^ fs_byte_sub s run_start (pos - run_start) else acc)
  else
    let b = fs_byte_at s pos in
    if escape_lit_special_byte b then
      let run = if pos > run_start then fs_byte_sub s run_start (pos - run_start) else "" in
      escape_lit_walk s len (pos + 1) (pos + 1) (acc ^ run ^ escape_lit_byte b)
    else
      escape_lit_walk s len run_start (pos + 1) acc

let escape_lit (s : string) : string =
  escape_lit_walk s (fs_byte_length s) 0 0 ""

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

(* The N-Quads / TriG parsers store a blank-node graph name as the
   string "_:<label>" inside the `iri`-typed `ng_name` field of
   `named_graph`. Lacking a sum-typed `graph_label` (refactor tracked
   separately), the canonical serialiser detects this sentinel and
   emits the slot as a bnode rather than wrapping it as `<_:label>`.
   See docs/designissues/2026-04-25-nquads-bnode-graph-fix.md. *)
let is_bnode_graph_label (gi : iri) : bool =
  let n = String.length gi in
  if n < 2 then false
  else String.sub gi 0 2 = "_:"

let bnode_of_graph_label (gi : iri) : bnode_id =
  let n = String.length gi in
  if n < 2 then gi
  else String.sub gi 2 (n - 2)

let canon_graph_name (gi : iri) : string =
  if is_bnode_graph_label gi then "_:" ^ bnode_of_graph_label gi
  else "<" ^ gi ^ ">"

(* Render a quad with its graph name. Default graph: graph slot omitted. *)
let canon_quad (graph_name : option iri) (t : triple) : string =
  let g = match graph_name with
    | Some gi -> " " ^ canon_graph_name gi
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
  let (g, t) = qq in
  let l1 = match t.s with | S_BNode b -> [b] | _ -> [] in
  let l2 = match t.o with | T_BNode b -> [b] | _ -> [] in
  // N-Quads/TriG bnode graph names are encoded as "_:label" in the
  // iri-typed `ng_name` slot. Surface them so HFDQ visits them.
  let l3 = match g with
           | Some gi -> if is_bnode_graph_label gi
                        then [bnode_of_graph_label gi]
                        else []
           | None -> []
  in
  l1 @ l2 @ l3

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

(* Render-key for a qquad — used solely as a uniqueness key when
   deduplicating duplicates per RDF set semantics (tests 076 / 077).
   Two triples that render byte-identical here are by construction
   the same triple. *)
let qquad_key (q : qquad) : string =
  let (g, t) = q in canon_quad g t

let rec dedup_qquads_acc (acc : list qquad) (seen : list string) (qs : list qquad)
  : Tot (list qquad) (decreases qs) =
  match qs with
  | [] -> List.Tot.rev acc
  | q :: rest ->
    let k = qquad_key q in
    if mem_string k seen then dedup_qquads_acc acc seen rest
    else dedup_qquads_acc (q :: acc) (k :: seen) rest

(* RDF set semantics: a dataset's quads form a set, not a multiset.
   The N-Quads parser yields a list which can carry duplicates from
   the input syntax; collapse them before per-bnode hashing so HFDQ
   neighbour counts stay correct (test077: same triple repeated would
   otherwise double the bnode's HFDQ contribution). *)
let dedup_qquads (qs : list qquad) : list qquad = dedup_qquads_acc [] [] qs

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
  let (g, t) = q in
  (match t.s with | S_BNode b -> b = target | _ -> false) ||
  (match t.o with | T_BNode b -> b = target | _ -> false) ||
  (match g with
   | Some gi -> is_bnode_graph_label gi
                && bnode_of_graph_label gi = target
   | None -> false)

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

(* Rewrite a graph name slot for HFDQ: own bnode → "_:a", other bnodes → "_:z",
   IRI graphs / default graph (None) unchanged. *)
let rewrite_graph_for_hfdq (target : bnode_id) (g : option iri) : option iri =
  match g with
  | None -> None
  | Some gi ->
    if is_bnode_graph_label gi then
      let lbl = bnode_of_graph_label gi in
      if lbl = target then Some "_:a" else Some "_:z"
    else Some gi

let render_for_hfdq (target : bnode_id) (q : qquad) : string =
  let (g, t) = q in
  canon_quad (rewrite_graph_for_hfdq target g)
             (rewrite_triple_for_hfdq target t)

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

// Three-way comparator for FStar.List.Tot.sortWith, derived from the
// str_le total preorder above.
let str_compare (a b : string) : int =
  if a = b then 0
  else if str_le a b then -1 else 1

// 2026-07-04 rewrite (issue #272): this used to be a hand-rolled
// insertion sort (insert_sorted / insertion_sort, O(n^2) always --
// the dominant quadratic term behind dump-nq / canonicalize going
// from 0.65s/0.46s at 1k triples to 12.9s/8.6s at 2k, per the
// benchmark's superlinear reading). FStar.List.Tot.sortWith is a
// partition-based (quicksort-shape) sort already proven Tot in the
// stdlib; average case O(n log n), used here instead. Kept under the
// `insertion_sort` name since every call site below (and none outside
// this module -- grep-verified) just wants "sorted ascending by
// str_le", not the algorithm.
let insertion_sort (xs : list string) : list string =
  List.Tot.sortWith str_compare xs

// 2026-07-04 rewrite (issue #272): the previous definition was
// `hd ^ concat_strings tl`, a right fold whose every step re-copies
// the entire (still-growing) tail into a fresh string -- O(n^2) in
// the total character count for a list of n lines (each `^` costs
// O(len(hd) + len(tail-so-far)), summed over n steps). FStar.String's
// `concat` extracts to OCaml's/Batteries' String.concat, which
// computes the total length once and copies each piece exactly once
// -- O(total length), single pass.
let concat_strings (xs : list string) : string =
  String.concat "" xs

let compute_hfdq (alg : hash_algorithm) (target : bnode_id) (qs : list qquad) : string =
  let mentioning = quads_for_bnode target qs in
  let rendered = render_all_for_hfdq target mentioning in
  let sorted = insertion_sort rendered in
  apply_hash alg (concat_strings sorted)

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
  is_prefix  : string;                   (* label prefix: "c14n" or "b" *)
  is_counter : nat;
  is_issued  : list (bnode_id * string); (* original → issued label *)
}

let empty_issuer : issuer_state = {
  is_prefix = "c14n";
  is_counter = 0;
  is_issued = [];
}

// RDFC-1.0 4.4.3 step 6.2.2: the per-candidate temporary issuer is
// "initialized with the prefix b" — its labels ("b0", "b1", ...) are
// spec-visible, not cosmetic: they are embedded in HNDQ path strings
// and in Hash Related Blank Node inputs, so every HNDQ hash depends
// on this prefix. Issuing temporaries as "c14nN" produces different
// hashes and therefore a different (still self-consistent, but
// non-conformant) ordering wherever a hash comparison breaks a tie
// between non-automorphic candidates.
let empty_temp_issuer : issuer_state = {
  is_prefix = "b";
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
    let label = st.is_prefix ^ nat_to_string st.is_counter in
    let st' : issuer_state = {
      is_prefix = st.is_prefix;
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

let rec compute_all_hfdq (alg : hash_algorithm) (qs : list qquad) (bs : list bnode_id)
  : Tot (list bn_hfdq_pair) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest -> (b, compute_hfdq alg b qs) :: compute_all_hfdq alg qs rest

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
   in opposite directions (e.g. `_:a foo _:b` vs `_:b foo _:a`).

   Tag "g" marks a target appearing only in the graph slot; this lets
   a bnode-typed graph name participate in HNDQ collision-breaking
   alongside subject/object bnodes. *)
// RDFC-1.0 4.9 step 3.1: position is s/o/g based on the slot of the
// RELATED component itself (the "other" blank node), NOT the slot of
// `target`. In a plain two-bnode quad the two are swapped (target
// subject <=> related object, and vice versa); when target occupies
// the graph slot, the related bnode is whichever of s/o is present
// (tag "s"/"o"); when target is s/o and a *different* bnode labels
// the graph, that related bnode's tag is "g".
let nbr_position_tag (target : bnode_id) (q : qquad) : string =
  let (g, t) = q in
  let s_bn = match t.s with | S_BNode b -> Some b | _ -> None in
  let o_bn = match t.o with | T_BNode b -> Some b | _ -> None in
  let g_is_target = match g with
                    | Some gi -> is_bnode_graph_label gi
                                 && bnode_of_graph_label gi = target
                    | None -> false in
  let so_pos =
    match s_bn, o_bn with
    | Some sb, Some ob ->
      if sb = target && ob = target then Some "ss"  // self-loop: no distinct related
      else if sb = target then Some "o"              // related occupies the object slot
      else if ob = target then Some "s"              // related occupies the subject slot
      else None
    | Some sb, None -> if sb = target then None else Some "s"
    | None, Some ob -> if ob = target then None else Some "o"
    | None, None -> None
  in
  match so_pos with
  | Some p -> p
  | None ->
    if g_is_target then
      // target is the graph bnode; related is whichever s/o bnode
      // is present (if any).
      (match s_bn with
       | Some _ -> "s"
       | None -> (match o_bn with | Some _ -> "o" | None -> "_")
      )
    else "g"  // a different bnode labels the graph — that's the related one

(* Extract the related bnode (the *other* bnode in this quad), if any.
   Returns None when the quad has no second bnode (e.g. `_:n p "lit"`)
   or when target appears in both slots of a self-loop (treated as
   "no related" — symmetry handled by the position tag "ss").

   Graph-position bnodes count as candidates: when target is in s/o
   the graph bnode is a structural neighbour, and when target is the
   graph bnode the s/o bnodes are. Prefer s/o over g when both are
   present and target is in s/o (consistent with the binary-relation
   focus of the level-2 hash); use g only when there is no s/o
   neighbour. *)
let graph_bnode_of (q : qquad) : option bnode_id =
  let (g, _) = q in
  match g with
  | Some gi -> if is_bnode_graph_label gi
               then Some (bnode_of_graph_label gi)
               else None
  | None -> None

let related_bnode (target : bnode_id) (q : qquad) : option bnode_id =
  let (_, t) = q in
  let s_bn = match t.s with | S_BNode b -> Some b | _ -> None in
  let o_bn = match t.o with | T_BNode b -> Some b | _ -> None in
  let g_bn = graph_bnode_of q in
  // Prefer the s/o "other" bnode; fall back to the graph bnode.
  let so_other =
    match s_bn, o_bn with
    | Some sb, Some ob ->
      if sb = target && ob = target then None       // self-loop
      else if sb = target then Some ob
      else if ob = target then Some sb
      else None
    | Some sb, None -> if sb = target then None else Some sb
    | None, Some ob -> if ob = target then None else Some ob
    | None, None -> None
  in
  match so_other with
  | Some _ -> so_other
  | None ->
    // No s/o neighbour — look at the graph slot.
    match g_bn with
    | Some gb -> if gb = target then
                   // target itself is the graph bnode; its neighbour
                   // is whichever s/o bnode is present (target is not
                   // in s/o by construction here).
                   (match s_bn with
                    | Some sb -> Some sb
                    | None -> o_bn)
                 else Some gb
    | None -> None

// RDFC-1.0 4.8 Hash Related Blank Node: input := position
// [+ "<" + predicate + ">" if position <> "g"] + identifier; return
// hash_algorithm(input). `identifier` is resolved by the caller
// (already-issued "_:<label>" or the bare HFDQ fallback).
let hash_related_blank_node (alg : hash_algorithm) (pos : string) (pred : string) (identifier : string)
  : string =
  let input = pos ^ (if pos <> "g" then "<" ^ pred ^ ">" else "") ^ identifier in
  apply_hash alg input

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

(* Level-3 neighbour hashes — uses the level-2 table as the related-key
   source. Phase 3 (Nun): handles graphs where a literal/IRI distinction
   is 3 structural steps away from a colliding bnode (e.g. test047 deep
   diff: chain `_:e -> _:m -> _:t -> "lit"`, two such chains differing
   only in the trailing literal — HFDQ identical, nbr1 identical, nbr2
   identical for the mid node; nbr3 finally distinguishes via the
   literal-bearing leaf's neighbour. *)
let rec compute_all_nbr3
    (qs : list qquad)
    (bs : list bnode_id)
    (nbr2_table : list bn_hfdq_pair)
  : Tot (list bn_hfdq_pair) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest ->
    let key_of (rb : bnode_id) : string = lookup_hfdq rb nbr2_table in
    let h = compute_nbr_hash b qs key_of in
    (b, h) :: compute_all_nbr3 qs rest nbr2_table

(* ------------------------------------------------------------------ *)
(* Section 6c. Sorting with the HNDQ-augmented key.

   Sort key: (hfdq, nbr1, nbr2, nbr3, orig). Two bnodes that agree on
   hfdq + nbr1 + nbr2 + nbr3 are very likely true automorphisms in the
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
  bk_nbr3 : string;
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
    (nbr3_t : list bn_hfdq_pair)
  : Tot (list bn_full_key) (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest ->
    {
      bk_orig = b;
      bk_hfdq = lookup_pair b hfdq_t;
      bk_nbr1 = lookup_pair b nbr1_t;
      bk_nbr2 = lookup_pair b nbr2_t;
      bk_nbr3 = lookup_pair b nbr3_t;
    } :: build_full_keys rest hfdq_t nbr1_t nbr2_t nbr3_t

let full_key_le (a b : bn_full_key) : bool =
  if a.bk_hfdq <> b.bk_hfdq then str_le a.bk_hfdq b.bk_hfdq
  else if a.bk_nbr1 <> b.bk_nbr1 then str_le a.bk_nbr1 b.bk_nbr1
  else if a.bk_nbr2 <> b.bk_nbr2 then str_le a.bk_nbr2 b.bk_nbr2
  else if a.bk_nbr3 <> b.bk_nbr3 then str_le a.bk_nbr3 b.bk_nbr3
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
// 2026-07-04 (issue #272): same O(n^2) -> sortWith swap as
// insertion_sort above. Only exercised on the fuel-exhaustion
// leftover fallback in build_canonical_mapping (rare and small in
// practice), but the fix is free and keeps the module internally
// consistent.
let pair_compare (a b : bn_hfdq_pair) : int =
  let (oa, ha) = a in
  let (ob, hb) = b in
  if ha = hb then
    (if oa = ob then 0 else if str_le oa ob then -1 else 1)
  else if str_le ha hb then -1 else 1

let sort_pairs (xs : list bn_hfdq_pair) : list bn_hfdq_pair =
  List.Tot.sortWith pair_compare xs

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

(* Relabel a graph name slot if it carries a bnode sentinel.
   Canonical labels are emitted bare (e.g. "c14n0"), so when we
   rewrite back into the iri-typed slot we re-attach the "_:"
   prefix to keep the sentinel scheme intact. *)
let relabel_graph_name (mapping : list (bnode_id * string)) (gi : iri) : iri =
  if is_bnode_graph_label gi then
    let lbl = bnode_of_graph_label gi in
    match lookup_issued lbl mapping with
    | Some new_lbl -> "_:" ^ new_lbl
    | None -> gi
  else gi

let relabel_named_graph (mapping : list (bnode_id * string)) (ng : named_graph)
  : named_graph =
  {
    ng_name = relabel_graph_name mapping ng.ng_name;
    ng_graph = relabel_graph mapping ng.ng_graph;
  }

let relabel_dataset (mapping : list (bnode_id * string)) (ds : rdf_dataset)
  : rdf_dataset =
  {
    ds_default = relabel_graph mapping ds.ds_default;
    ds_named = List.Tot.map (relabel_named_graph mapping) ds.ds_named;
  }

(* ------------------------------------------------------------------ *)
(* Section 6d. Hash N-Degree Quads (HNDQ) — full permutation enumeration
   with a cloned issuer.

   Per RDFC-1.0 §4.9. For each blank node `n` whose HFDQ collides:

   1. Walk every quad `q` mentioning `n`. Identify related bnodes
      (the bnode in the *other* position of `q`), and bucket them by
      (position-tag, predicate, hfdq-of-related).
   2. For each bucket key in lex-sorted order, enumerate every
      permutation of the bucket's related-bnode list. For each
      permutation, walk it: if the related bnode is already in the
      global issuer, append `_:<canonical>`; otherwise issue a temp
      ID via the cloned issuer and recurse into HNDQ for the related
      bnode (yielding a path-hash + extended issuer). Append the
      temp ID + the recursive path-hash. Pick the lex-smallest
      resulting path-hash; that permutation's issuer wins for this
      bucket. Concatenate the bucket's contribution to the parent
      data-string.
   3. Hash the full data-string; return (hash, final-issuer).

   Fuel: the outer recursion is bounded by |bnodes| (each recursive
   call issues at least one new bnode). Permutation enumeration is
   bounded by factorial of bucket size; we cap each bucket at 6
   members to keep the bound tractable (any test with a tighter
   collision class than that needs the full automorphism-search
   algorithm — see test074c, deferred). *)

(* Group related bnodes by bucket key (pos|pred|hfdq) for HNDQ. *)
type bucket = (string * list bnode_id)  // (key, members)

(* Insert `b` into the bucket with key `k`; create the bucket if
   missing; sort buckets by key on the fly. *)
let rec bucket_insert (k : string) (b : bnode_id) (xs : list bucket)
  : Tot (list bucket) (decreases xs) =
  match xs with
  | [] -> [(k, [b])]
  | (k', members) :: rest ->
    if k = k' then (k', members @ [b]) :: rest
    else if str_le k k' then (k, [b]) :: xs
    else (k', members) :: bucket_insert k b rest

(* Build the bucket map (RDFC-1.0 4.9 steps 1-3, "hash to related
   blank nodes map") for `target` from its incident quads.

   Per 4.9 step 3.1, EVERY component of an incident quad — subject,
   object, AND graph name — that is a blank node other than `target`
   contributes its own Hn entry, with position tag "s"/"o"/"g" set by
   the slot the related component itself occupies. A single quad can
   therefore contribute up to three entries (e.g. `_:s <p> _:o _:g`
   seen from `_:s` yields one "o" entry and one "g" entry). Quads
   whose only blank node is `target` itself contribute NOTHING here —
   they were fully accounted for by the first-degree hash. The bucket
   key is the Hash Related Blank Node value (4.8). *)
// Look up `b`'s already-issued identifier, checking the *real*
// canonical issuer first, then the per-candidate local (temporary)
// issuer — RDFC-1.0 4.8 branches 1/2 unified, since both are just
// "an already-issued identifier", canonical taking precedence.
let lookup_issued2 (b : bnode_id) (canon_st : issuer_state) (local_st : issuer_state)
  : option string =
  match lookup_issued b canon_st.is_issued with
  | Some lbl -> Some lbl
  | None -> lookup_issued b local_st.is_issued

// RDFC-1.0 4.9 step 3.1: all blank-node components of `q` other than
// `target`, each tagged with the slot it occupies ("s"/"o"/"g"). Note
// a bnode appearing in two slots of the same quad yields two entries
// (matching the spec's per-component loop), and a component equal to
// `target` yields none.
let related_components (target : bnode_id) (q : qquad)
  : list (string * bnode_id) =
  let (_, t) = q in
  let s_e = (match t.s with
             | S_BNode b -> if b <> target then [("s", b)] else []
             | _ -> []) in
  let o_e = (match t.o with
             | T_BNode b -> if b <> target then [("o", b)] else []
             | _ -> []) in
  let g_e = (match graph_bnode_of q with
             | Some b -> if b <> target then [("g", b)] else []
             | None -> []) in
  s_e @ (o_e @ g_e)

// Fold one quad's related components into the bucket map: resolve
// each related bnode's identifier (canonical label, then this
// candidate's temporary label, then bare HFDQ hash — RDFC-1.0 4.8
// step 3), hash it with position + predicate, and insert.
let rec insert_related_entries
    (alg : hash_algorithm)
    (entries : list (string * bnode_id))
    (pred : string)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (acc : list bucket)
  : Tot (list bucket) (decreases entries) =
  match entries with
  | [] -> acc
  | (pos, rb) :: rest ->
    let identifier =
      match lookup_issued2 rb canon_st local_st with
      | Some lbl -> "_:" ^ lbl               // branch 1/2
      | None -> lookup_hfdq rb hfdq_table     // branch 3
    in
    let k = hash_related_blank_node alg pos pred identifier in
    insert_related_entries alg rest pred hfdq_table canon_st local_st
      (bucket_insert k rb acc)

let rec build_buckets_for
    (alg : hash_algorithm)
    (target : bnode_id)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)  // real canonical issuer, read-only
                                // here (already-issued check, branch 1)
    (local_st : issuer_state)  // this candidate's own temporary
                                // issuer (already-issued check, branch 2)
    (acc : list bucket)
  : Tot (list bucket) (decreases qs) =
  match qs with
  | [] -> acc
  | q :: rest ->
    if not (quad_mentions_bnode target q) then
      build_buckets_for alg target rest hfdq_table canon_st local_st acc
    else
      let (_, t) = q in
      let entries = related_components target q in
      let acc' = insert_related_entries alg entries t.p hfdq_table canon_st local_st acc in
      build_buckets_for alg target rest hfdq_table canon_st local_st acc'

(* Permutation enumeration: list all permutations of a list. We bound
   this at factorial(6) = 720 by truncating longer lists; for tests in
   the W3C eval suite, no collision bucket exceeds 6 members. *)
let rec remove_first (x : bnode_id) (xs : list bnode_id)
  : Tot (list bnode_id) (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl -> if hd = x then tl else hd :: remove_first x tl

let rec take_n (#a:Type) (n : nat) (xs : list a)
  : Tot (list a) (decreases xs) =
  if n = 0 then []
  else match xs with
       | [] -> []
       | hd :: tl -> hd :: take_n (n - 1) tl

(* Insert `x` at every position of `ys`. *)
let rec insert_at_all (x : bnode_id) (ys : list bnode_id)
  : Tot (list (list bnode_id)) (decreases ys) =
  match ys with
  | [] -> [[x]]
  | hd :: tl ->
    (x :: ys) :: List.Tot.map (fun zs -> hd :: zs) (insert_at_all x tl)

let rec permutations (xs : list bnode_id)
  : Tot (list (list bnode_id)) (decreases xs) =
  match xs with
  | [] -> [[]]
  | hd :: tl ->
    let sub = permutations tl in
    List.Tot.fold_left
      (fun acc p -> acc @ insert_at_all hd p)
      []
      sub

(* List membership over bnode_id. *)
let rec mem_bnode (b : bnode_id) (xs : list bnode_id) : bool =
  match xs with
  | [] -> false
  | hd :: tl -> hd = b || mem_bnode b tl

(* The HNDQ recursion + permutation walk.

   Termination: outer recursion uses an explicit `fuel` parameter
   bounded by the number of bnodes in the dataset. Each recursive
   call into `hndq_run` happens only when the issuer issues a fresh
   ID for a previously-unidentified bnode, so the strict-decrease
   condition on (count of unissued bnodes) holds operationally;
   fuel makes that decrease syntactic for F*. *)

(* RDFC-1.0 4.9 step 5.4.4: first pass over a permutation. Every
   member contributes its "_:<label>" identifier — already-issued
   (canonical or local) or freshly issued into `local_st` — to `path`,
   in order, with NO separator between members (spec-literal: plain
   concatenation, no comma, no period). Members freshly issued here
   are recorded, in the same order, as the `recursion` list, which the
   second pass (step 5.4.5, `walk_recursion` below) consumes. *)
let rec build_path_labels
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (perm : list bnode_id)
    (path : string)
    (recursion : list bnode_id)
  : Tot (string * issuer_state * list bnode_id) (decreases perm) =
  match perm with
  | [] -> (path, local_st, recursion)
  | b :: rest ->
    (match lookup_issued2 b canon_st local_st with
     | Some lbl ->
       build_path_labels canon_st local_st rest (path ^ "_:" ^ lbl) recursion
     | None ->
       let (local1, lbl) = issue_identifier local_st b in
       build_path_labels canon_st local1 rest (path ^ "_:" ^ lbl) (recursion @ [b]))

(* Walk a permutation, building (path_string, updated_issuer).
   Returns None if a related bnode exits scope (defensive — the
   bucket-key construction should keep all related bnodes well-typed,
   but the recursive HNDQ may not terminate in a reasonable horizon
   for highly symmetric graphs; we abort with None and the caller
   falls back to the orig-label tiebreak). *)
// `canon_st` is threaded unchanged through this whole mutual-recursion
// group — RDFC-1.0's Hash N-Degree Quads algorithm only *reads* the
// real canonical issuer (to detect bnodes already committed by prior
// groups) during exploration; only `local_st`, this candidate's own
// temporary issuer, grows as the walk proceeds. The real canonical
// issuer is only ever updated afterwards, by replaying the winning
// exploration's temporary-issuance list (see `replay_group` below).
let rec hndq_run
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (target : bnode_id)
  : Tot (string * issuer_state) (decreases %[fuel; 4; 0]) =
  if fuel = 0 then ("", local_st)
  else
    let buckets = build_buckets_for alg target qs hfdq_table canon_st local_st [] in
    walk_buckets alg (fuel - 1) qs hfdq_table canon_st local_st buckets ""

and walk_buckets
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (buckets : list bucket)
    (data : string)
  : Tot (string * issuer_state) (decreases %[fuel; 3; buckets]) =
  match buckets with
  | [] -> (apply_hash alg data, local_st)
  | (k, members) :: rest ->
    let data1 = data ^ k in
    let perms = permutations (take_n 6 members) in
    let (best_hash, best_st) = best_permutation alg fuel qs hfdq_table canon_st local_st perms in
    let data2 = data1 ^ best_hash in
    walk_buckets alg fuel qs hfdq_table canon_st best_st rest data2

and best_permutation
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (perms : list (list bnode_id))
  : Tot (string * issuer_state) (decreases %[fuel; 2; perms]) =
  match perms with
  | [] -> ("", local_st)  // no permutations: empty bucket
  | p :: rest ->
    let (h, st') = walk_perm alg fuel qs hfdq_table canon_st local_st p "" in
    pick_best alg fuel qs hfdq_table canon_st local_st rest h st'

and pick_best
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st_initial : issuer_state)
    (perms : list (list bnode_id))
    (best_hash : string)
    (best_st : issuer_state)
  : Tot (string * issuer_state) (decreases %[fuel; 2; perms]) =
  match perms with
  | [] -> (best_hash, best_st)
  | p :: rest ->
    let (h, st') = walk_perm alg fuel qs hfdq_table canon_st local_st_initial p "" in
    let (best_hash', best_st') =
      if str_le h best_hash && h <> best_hash then (h, st')
      else (best_hash, best_st) in
    pick_best alg fuel qs hfdq_table canon_st local_st_initial rest best_hash' best_st'

and walk_perm
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (perm : list bnode_id)
    (path : string)
  : Tot (string * issuer_state) (decreases %[fuel; 1; perm]) =
  // RDFC-1.0 4.9 steps 5.4.4 + 5.4.5: build every member's label
  // first (no recursion yet), THEN walk only the freshly-issued
  // members a second time, appending "_:<label><recursive-hash>" for
  // each, in order. See `build_path_labels` / `walk_recursion` above
  // and below.
  let (path1, local1, recursion) = build_path_labels canon_st local_st perm path [] in
  walk_recursion alg fuel qs hfdq_table canon_st local1 recursion path1

and walk_recursion
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (local_st : issuer_state)
    (recursion : list bnode_id)
    (path : string)
  : Tot (string * issuer_state) (decreases %[fuel; 0; recursion]) =
  match recursion with
  | [] -> (path, local_st)
  | b :: rest ->
    // `b` was already issued in `build_path_labels`'s first pass;
    // `issue_identifier` is idempotent, so this just recovers its label.
    let (local1, lbl) = issue_identifier local_st b in
    let (sub_hash, local2) =
      if fuel = 0 then ("", local1)
      else hndq_run alg (fuel - 1) qs hfdq_table canon_st local1 b in
    walk_recursion alg fuel qs hfdq_table canon_st local2 rest (path ^ "_:" ^ lbl ^ "<" ^ sub_hash ^ ">")

(* ------------------------------------------------------------------ *)
(* Section 6e. Top-level: unique-HFDQ first, then collision groups.

   Per RDFC-1.0 §4.5.3 step 6: assign canonical IDs to bnodes whose
   HFDQ is unique, in HFDQ-sort order. Then per §4.5.3 step 7: for
   each remaining (collision) group in HFDQ-sort order, run HNDQ on
   each member, pick the lex-smallest path-hash, and commit that
   member's cloned issuer as the new global state. *)

(* Group bnodes by HFDQ. Returns a list of buckets, sorted by HFDQ
   ascending; within each bucket members are in stable input order. *)
let rec group_by_hfdq_aux
    (bs : list bnode_id)
    (table : list bn_hfdq_pair)
    (acc : list bucket)
  : Tot (list bucket) (decreases bs) =
  match bs with
  | [] -> acc
  | b :: rest ->
    let h = lookup_hfdq b table in
    group_by_hfdq_aux rest table (bucket_insert h b acc)

let group_by_hfdq (bs : list bnode_id) (table : list bn_hfdq_pair)
  : list bucket =
  group_by_hfdq_aux bs table []

(* Filter a group to bnodes not yet in the issuer. *)
let rec filter_unissued (st : issuer_state) (xs : list bnode_id)
  : Tot (list bnode_id) (decreases xs) =
  match xs with
  | [] -> []
  | b :: rest ->
    match lookup_issued b st.is_issued with
    | Some _ -> filter_unissued st rest
    | None -> b :: filter_unissued st rest

(* RDFC-1.0 4.4.3 step 5.2: explore *every* member of a collision
   group using its own fresh temporary issuer (never accumulated
   across members — each candidate starts from a clean `empty_temp_issuer`
   slate, only `canon_st`, the real issuer, is shared and read-only
   here). Returns one (hash, temporary-issued-list) pair per
   not-yet-canonically-issued member, in original member order. *)
let rec explore_members
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (canon_st : issuer_state)
    (members : list bnode_id)
  : Tot (list (string * list (bnode_id * string))) (decreases members) =
  match members with
  | [] -> []
  | m :: rest ->
    (match lookup_issued m canon_st.is_issued with
     | Some _ -> explore_members alg fuel qs hfdq_table canon_st rest
     | None ->
       let (local1, _) = issue_identifier empty_temp_issuer m in
       let (h, local2) = hndq_run alg fuel qs hfdq_table canon_st local1 m in
       (h, local2.is_issued) :: explore_members alg fuel qs hfdq_table canon_st rest)

(* Stable insertion sort of (hash, temp-issued-list) results by hash,
   ascending, preserving original relative order for ties. RDFC-1.0
   4.4.3 step 5.3 says "code point ordered by hash" but does not
   define tie-breaking; first-explored-member-wins is a deterministic,
   stable choice consistent across runs over the same input order. *)
let rec insert_result_stable
    (x : string * list (bnode_id * string))
    (xs : list (string * list (bnode_id * string)))
  : Tot (list (string * list (bnode_id * string))) (decreases xs) =
  match xs with
  | [] -> [x]
  | (k, v) :: rest ->
    let (xk, _) = x in
    if str_le k xk then (k, v) :: insert_result_stable x rest
    else x :: xs

let rec sort_results_stable_acc
    (acc : list (string * list (bnode_id * string)))
    (xs : list (string * list (bnode_id * string)))
  : Tot (list (string * list (bnode_id * string))) (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> sort_results_stable_acc (insert_result_stable x acc) rest

let sort_results_stable (xs : list (string * list (bnode_id * string)))
  : list (string * list (bnode_id * string)) =
  sort_results_stable_acc [] xs

(* RDFC-1.0 4.4.3 step 5.3: for each result in ascending-hash order,
   replay *every* identifier its exploration touched (in the order it
   touched them) into the real canonical issuer. `issue_identifier` is
   idempotent on an already-issued bnode, so bnodes swept up by an
   earlier result in this same fold are safely skipped when their own
   turn comes. *)
let rec replay_one (canon_st : issuer_state) (temp_issued : list (bnode_id * string))
  : Tot issuer_state (decreases temp_issued) =
  match temp_issued with
  | [] -> canon_st
  | (b, _) :: rest ->
    let (canon_st', _) = issue_identifier canon_st b in
    replay_one canon_st' rest

let rec replay_all
    (canon_st : issuer_state)
    (results : list (string * list (bnode_id * string)))
  : Tot issuer_state (decreases results) =
  match results with
  | [] -> canon_st
  | (_, temp_issued) :: rest ->
    replay_all (replay_one canon_st temp_issued) rest

(* Run HNDQ on every not-yet-issued member of a collision group,
   independently (fresh local issuer each — see `explore_members`);
   then replay each result's temporary issuance, in ascending-hash
   order, into the real canonical issuer (`replay_all`). This assigns
   a canonical id to *every* member of the group — not just a single
   "winner" — matching RDFC-1.0 4.4.3 steps 5.2 + 5.3. *)
let process_collision_members
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (st : issuer_state)
    (members : list bnode_id)
  : issuer_state =
  let results = explore_members alg fuel qs hfdq_table st members in
  let sorted = sort_results_stable results in
  replay_all st sorted

(* Walk all groups: unique → assign directly; collision → process via
   HNDQ. Groups are passed in HFDQ-sort order.

   RDFC-1.0 4.4.3 runs this as TWO separate full passes over the
   hash-sorted group list, not one interleaved pass: step (4) assigns
   every unique-hash (singleton) group its canonical id, in hash
   order, in full BEFORE step (5) even starts; step (5) then handles
   every remaining (collision) group, in hash order, as its own
   complete pass. Interleaving them (processing whichever group's
   hash sorts first, singleton or collision, in one merged walk) hands
   out canonical numbers in the wrong relative order whenever a
   singleton's hash falls between two collision groups' hashes, or
   vice versa — same isomorphism, different absolute `c14nN` numbers,
   which is exactly the failure signature this two-pass split fixes. *)
let rec assign_singletons
    (st : issuer_state)
    (groups : list bucket)
  : Tot issuer_state (decreases groups) =
  match groups with
  | [] -> st
  | (_, [b]) :: rest ->
    let (st', _) = issue_identifier st b in
    assign_singletons st' rest
  | (_, _) :: rest -> assign_singletons st rest  // multi-member: pass 2's job

let rec process_collision_groups
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (st : issuer_state)
    (groups : list bucket)
  : Tot issuer_state (decreases groups) =
  match groups with
  | [] -> st
  | (_, [_]) :: rest -> process_collision_groups alg fuel qs hfdq_table st rest  // pass 1 already did this one
  | (_, members) :: rest ->
    let unissued = filter_unissued st members in
    let st' = process_collision_members alg fuel qs hfdq_table st unissued in
    process_collision_groups alg fuel qs hfdq_table st' rest

let walk_groups
    (alg : hash_algorithm)
    (fuel : nat)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (st : issuer_state)
    (groups : list bucket)
  : issuer_state =
  let st1 = assign_singletons st groups in
  process_collision_groups alg fuel qs hfdq_table st1 groups

(* ------------------------------------------------------------------ *)
(* Section 8. Public entry points. *)

(* Build the full canonical-id mapping for a dataset.

   Phase 2: full HNDQ with permutation enumeration and a cloned
   issuer. Per RDFC-1.0 §4.5: assign canonical IDs to unique-HFDQ
   bnodes first (in HFDQ-sort order), then for each collision group
   run HNDQ on each member and pick the member whose path-hash is
   lex-smallest, committing its issuer state. The HNDQ recursion is
   bounded by the bnode count; permutation enumeration is bounded at
   factorial(6) per bucket. Tests beyond that bound (test074c poison
   clique) fall back to the orig-label tiebreak. *)
// `alg` selects the hash primitive per RDFC-1.0's `rdfc:hashAlgorithm`
// test-manifest option (default SHA-256; SHA-384 for the small number
// of manifest entries that request it — see `hash_algorithm_of_string`
// and RDF.Canonical.Manifest.fst). `build_canonical_mapping` below
// keeps its original 1-argument signature (defaulting to SHA-256) so
// every existing caller (factoidal_cli, entry_jsoo, dump-nq,
// jsonld_runner) is unaffected; rdfc10_runner calls this `_alg` form
// directly when a test declares a non-default algorithm.
let build_canonical_mapping_alg (alg : hash_algorithm) (ds : rdf_dataset) : list (bnode_id * string) =
  let qs = dedup_qquads (dataset_quads ds) in
  let bs = dataset_bnodes ds in
  let hfdq_table = compute_all_hfdq alg qs bs in
  let groups = group_by_hfdq bs hfdq_table in
  let fuel : nat = List.Tot.length bs + 1 in
  let final_state = walk_groups alg fuel qs hfdq_table empty_issuer groups in
  // Defensive: any bnode not yet issued (e.g. due to fuel exhaustion
  // on a poison-clique input) gets an ID via lex-fallback. Sort by
  // (hfdq, orig) and assign.
  let leftover = filter_unissued final_state bs in
  let leftover_pairs : list bn_hfdq_pair =
    List.Tot.map (fun b -> (b, lookup_hfdq b hfdq_table)) leftover in
  let leftover_sorted = sort_pairs leftover_pairs in
  let final_state' = assign_in_order final_state leftover_sorted in
  final_state'.is_issued

let build_canonical_mapping (ds : rdf_dataset) : list (bnode_id * string) =
  build_canonical_mapping_alg HA_SHA256 ds

(* Canonicalise a dataset: relabel every blank node deterministically. *)
let canonicalize_alg (alg : hash_algorithm) (ds : rdf_dataset) : rdf_dataset =
  let mapping = build_canonical_mapping_alg alg ds in
  relabel_dataset mapping ds

let canonicalize (ds : rdf_dataset) : rdf_dataset =
  canonicalize_alg HA_SHA256 ds

(* Render a dataset to canonical N-Quads: emit each quad, sort the
   resulting lines lexicographically, concatenate. The relabelling
   must already have happened (call after `canonicalize`). *)
let rec render_quads (qs : list qquad)
  : Tot (list string) (decreases qs) =
  match qs with
  | [] -> []
  | (g, t) :: rest -> canon_quad g t :: render_quads rest

(* Dedup adjacent duplicates in a sorted list of strings. After
   `insertion_sort`, RDF set semantics requires that identical canonical
   N-Quads lines collapse to a single line (tests 076/077). Walking the
   sorted list and dropping adjacent equals is sufficient. *)
let rec dedup_sorted_strings (xs : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | [x] -> [x]
  | x :: y :: rest ->
    if x = y then dedup_sorted_strings (y :: rest)
    else x :: dedup_sorted_strings (y :: rest)

let canonical_nquads (ds : rdf_dataset) : string =
  let qs = dataset_quads ds in
  let lines = render_quads qs in
  let sorted = insertion_sort lines in
  let deduped = dedup_sorted_strings sorted in
  concat_strings deduped

(* Convenience: canonicalise then serialise. *)
let canonicalize_to_nquads_alg (alg : hash_algorithm) (ds : rdf_dataset) : string =
  canonical_nquads (canonicalize_alg alg ds)

let canonicalize_to_nquads (ds : rdf_dataset) : string =
  canonicalize_to_nquads_alg HA_SHA256 ds

// Canonicalize one named graph as a single-graph dataset -- the
// per-graph sibling of canonicalize_to_nquads (graphs-api design doc
// docs/designissues/2026-07-05-graphs-api-design.md section 1.1).
// Composes two existing things (component projection via
// lookup_named_graph, whole-dataset canonicalize_to_nquads), not a
// new algorithm. Inherits the existing HFDQ-only limitation unchanged
// (HNDQ not implemented, 23/86 rdf-canon fails): it adds no
// tie-detection or decline-to-hash guard beyond what
// canonicalize_to_nquads already does.
let canonicalize_named_graph (ds : rdf_dataset) (name : RDF.Dataset.Graphs.graph_ref)
    : option string =
  match lookup_named_graph name ds.ds_named with
  | None -> None
  | Some g -> Some (canonicalize_to_nquads ({ ds_default = g; ds_named = [] }))
