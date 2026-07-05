module RDF.Indexed

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.3/§3.3 step 3. The design doc's §2.3 describes this module as
// "the indexed_graph/bucket_map machinery ... lines 286-514" moved
// verbatim out of RDF.Graph.Executable.fst. Executing that literally
// is impossible without introducing a cyclic module dependency: the
// RDF-specific pieces of that block (`indexed_graph`'s record fields,
// `subject_to_key`, `term_to_key_opt`, `find_objects_indexed`,
// `find_subjects_indexed`, `add_triple_to_indexes`, `build_indexed`)
// all pattern-match on `triple`/`subject`/`rdf_term` — types that live
// in RDF.Graph.Executable.fst and are not extracted out until step 5
// (`RDF.Term`/`RDF.Triple`/`RDF.Graph`). If this module opened
// RDF.Graph.Executable for those types, and RDF.Graph.Executable kept
// its ~140 RDFS/OWL-RL closure-rule call sites of `indexed_graph`
// (step 6 territory, not moving yet) by opening this module back,
// F*'s acyclic-module-DAG requirement would reject the pair outright.
//
// The fix, discovered during this step's execution: only the truly
// generic association-list "bucket map" plumbing is RDF-independent
// — it never inspects `triple`/`subject`/`rdf_term` internals, only
// `key_of`-supplied `string`/`option string` keys and an opaque
// element type. That subset (`bucket_map`, `bucket_lookup`,
// `bucket_replace`, `bucket_push`, `build_bucket`) is genericised over
// a type parameter here, giving RDF.Indexed.fst a real dependency of
// zero on RDF.Graph.Executable — a one-directional edge in the other
// direction, safe to `open` from RDF.Graph.Executable.fst without a
// cycle. The RDF-specific glue that instantiates this at `triple`
// (`indexed_graph`, `subject_to_key`, `term_to_key_opt`, the `*_key`
// builders, `find_objects_indexed`/`find_subjects_indexed`,
// `add_triple_to_indexes`, `build_indexed`/`empty_indexed`) stays in
// RDF.Graph.Executable.fst — moving it is blocked on step 5 landing
// first. See the plan doc's step-3 row for the follow-up this leaves.
//
// Every value below is a *transparent* `let` (not an abstract `val`),
// matching the RDF.Vocabulary.fsti precedent (§2.9): this module's
// whole content lives here; RDF.Indexed.fst is an (almost) empty
// companion, same shape as RDF.Vocabulary.fst/.fsti.

open FStar.String
open FStar.List.Tot

/// A generic "bucket map": an association list from string keys to
/// lists of elements of type `a`. Used as the storage layer for
/// `RDF.Graph.Executable`'s `indexed_graph` acceleration structure
/// (predicate/subject/object/sp/po/so buckets over `triple`), but has
/// no RDF-specific content itself.
let bucket_map (a:Type) = list (string * list a)

/// First-match lookup; absent key returns the empty list. Total,
/// structural recursion on the map.
let rec bucket_lookup (#a:Type) (m : bucket_map a) (k : string)
  : Tot (list a) (decreases m) =
  match m with
  | [] -> []
  | (k', v) :: rest -> if k = k' then v else bucket_lookup rest k

/// Tail-recursive accumulator form (mirrors the pre-move code's
/// issue-#119 stack-safety fix: a straight-recursive shape blew JS's
/// ~10K stack at lifesci-scale ingest because each frame wraps the
/// recursive result in a fresh cons).
let rec bucket_replace_acc (#a:Type)
  (acc : bucket_map a) (m : bucket_map a) (k : string) (v : list a)
  : Tot (bucket_map a) (decreases m) =
  match m with
  | [] -> List.Tot.rev_acc acc [(k, v)]
  | (k', v') :: rest ->
    if k = k' then List.Tot.rev_acc acc ((k, v) :: rest)
    else bucket_replace_acc ((k', v') :: acc) rest k v

/// Replace-or-add for a key: keeps a single binding per key (mirrors
/// OCaml's `Hashtbl.replace`).
let bucket_replace (#a:Type) (m : bucket_map a) (k : string) (v : list a)
  : Tot (bucket_map a) =
  bucket_replace_acc [] m k v

/// Push a single element onto the bucket for `k` (cons-to-front).
let bucket_push (#a:Type) (m : bucket_map a) (k : string) (t : a)
  : Tot (bucket_map a) =
  bucket_replace m k (t :: bucket_lookup m k)

/// Comparator for `List.Tot.sortWith`, generic over `key_of`.
/// Elements with no key for this bucket (`None`) sort first; the
/// grouping pass below filters them out.
let cmp_by_key (#a:Type) (key_of : a -> option string) (t1 t2 : a) : int =
  match key_of t1, key_of t2 with
  | None, None       -> 0
  | None, Some _     -> -1
  | Some _, None     -> 1
  | Some k1, Some k2 -> String.compare k1 k2

/// Walk a key-sorted list, collapsing each run of same-key elements
/// into one `(key, elements)` binding. Tail-rec via reversed
/// accumulator; `bucket_map` lookup doesn't depend on bucket order so
/// this doesn't bother to reverse at the end.
let rec group_sorted_aux (#a:Type)
    (key_of : a -> option string)
    (ts : list a)
    (cur_key : option string) (cur_bucket : list a)
    (acc : bucket_map a)
  : Tot (bucket_map a) (decreases ts) =
  match ts with
  | [] ->
    (match cur_key with
     | Some k -> (k, cur_bucket) :: acc
     | None   -> acc)
  | t :: rest ->
    (match key_of t with
     | None -> group_sorted_aux key_of rest cur_key cur_bucket acc
     | Some k ->
       (match cur_key with
        | Some k0 ->
          if k = k0 then
            group_sorted_aux key_of rest cur_key (t :: cur_bucket) acc
          else
            group_sorted_aux key_of rest (Some k) [t] ((k0, cur_bucket) :: acc)
        | None ->
          group_sorted_aux key_of rest (Some k) [t] acc))

/// Build a bucket map from a flat list in one pass: sort by key
/// (elements with no key for this bucket sort first and are dropped),
/// then collapse each run of same-key elements into one binding.
/// O(N log N) — see `RDF.Graph.Executable.fst`'s `build_indexed`
/// banner (issue #259) for why this replaced an O(N*K) per-insert
/// build.
let build_bucket (#a:Type) (key_of : a -> option string) (ts : list a)
  : Tot (bucket_map a) =
  let sorted = List.Tot.sortWith (cmp_by_key key_of) ts in
  group_sorted_aux key_of sorted None [] []
