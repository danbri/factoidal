#!/bin/bash
# Issue #97: predicate-indexed graph store for triple-pattern lookup.
# https://github.com/danbri/factoidal/issues/97
#
# The F*-extracted `store_search` today does `triple_matches_bound b
# g.gs_graph` — a linear scan of the entire graph triple list for
# every bound lookup. On ~1M-triple graphs that is prohibitive for any
# BGP with a join.
#
# This patch adds a predicate-keyed in-memory index, cached per
# `rdf_graph` identity (physical equality), and routes `store_search`
# through it when the triple pattern has a bound predicate (the common
# case). Semantics are identical — same set of matching triples, just
# scanned from a smaller candidate list. Order may differ, which is
# fine for RDF set semantics.
#
# Next steps (not in this patch): add a by-subject and by-object index
# so patterns with only a bound subject or only a bound object also
# skip the full scan, and hash-join primitive so cross-graph joins
# don't pay O(outer × inner_graph_size) when both sides are indexed.
#
# Like #95 this is purely a physical-layer fix: no SPARQL or RDF
# semantics change. The verified F* algebra still treats the graph as
# a `list triple`; only the OCaml runtime sees the Hashtbl-backed
# index. Correct per the store_search boundary described in
# docs/designissues/sparql-store-backend.md.

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  SPARQL11_Algebra.ml not found in $OUTDIR; skipping 97_indexed_graph_store.sh"
  exit 0
fi

# Idempotency: marker string left by a successful apply.
if grep -q '_sse_indexes_cache' "$FILE"; then
  echo "  97_indexed_graph_store.sh already applied to $FILE"
  exit 0
fi

# Dependency: patch #95 must have already created sse_* helpers + the
# tail-rec triple_matches_bound. If `triple_matches_bound` still looks
# like the pristine cons-after-recurse form, bail — order of the
# `ocaml-patches.sh` invocation list must put #95 before #97.
if ! grep -q 'sse_concat_map' "$FILE"; then
  echo "  97_indexed_graph_store.sh: #95 has not yet applied; refusing"
  exit 1
fi

echo "  Applying 97_indexed_graph_store.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    s = f.read()

# ------------------------------------------------------------------
# Step 1: insert the index data structure + cache + builder right
# before `let store_search` so the new store_search body can call
# them. We anchor on the `let store_search` definition and prepend.
# ------------------------------------------------------------------

store_search_marker = 'let store_search (g : graph_store) (b : triple_pattern_bound) :'
idx = s.find(store_search_marker)
if idx < 0:
    raise SystemExit("SPARQL11_Algebra.ml: store_search anchor not found")

index_block = '''(* Indexed graph store — post-extraction patch (issue #97).

   Three Hashtbls per graph (predicate / subject / object), each
   built lazily on first use, cached by physical equality on the
   rdf_graph. OCaml list cells have stable identity, so the same
   loaded graph reuses its indexes across every store_search call
   in a BGP.

   Key insight: real SPARQL triple patterns bind somewhere between
   one and three components. With all three indexes in place,
   store_search picks whichever bucket is smallest (among those
   whose component is bound) as the candidate list and lets the
   normal triple_matches_bound filter nail down the rest.

   Selectivity on gene.ttl: predicate `a` → 92k, `wdt:P684` → 99k,
   `wdt:P1057` → 11k, `wdt:P688` → 1.6k. Object `bio:Gene` → 92k.
   Any unique subject → usually 1..10 matches. So for a two-TP BGP
   where one TP has a highly-selective bound component, the nested
   search through the other graph shrinks proportionally.

   The cache is not weak; it lives for process lifetime. Factoidal
   is a single-shot CLI / single-page browser demo so this is fine.
   A long-running server would want Ephemeron.K1. *)

module SseGraphHashtbl = Hashtbl.Make(struct
  type t = RDF_Graph_Executable.rdf_graph
  let equal = (==)
  let hash g = Hashtbl.seeded_hash_param 10 100 5 g
end)

(* Three indexes per graph, bundled into one record for caching. *)
type _sse_graph_indexes = {
  pred_idx : (string, RDF_Graph_Executable.triple) Hashtbl.t;
  subj_idx : (string, RDF_Graph_Executable.triple) Hashtbl.t;
  obj_idx  : (string, RDF_Graph_Executable.triple) Hashtbl.t;
}

let _sse_indexes_cache : _sse_graph_indexes SseGraphHashtbl.t =
  SseGraphHashtbl.create 16

(* Canonical string keys for subject / object indexing. We do NOT
   try to index on literal values — they would require normalising
   datatype and lang tag, and they rarely appear as the join axis.
   Literal objects fall through to the predicate index. *)
let _sse_subject_key (s : RDF_Graph_Executable.subject) : string option =
  match s with
  | RDF_Graph_Executable.S_IRI i   -> Some (Stdlib.String.concat "" ["i:"; i])
  | RDF_Graph_Executable.S_BNode b -> Some (Stdlib.String.concat "" ["b:"; b])

let _sse_object_key (o : RDF_Graph_Executable.rdf_term) : string option =
  match o with
  | RDF_Graph_Executable.T_IRI i   -> Some (Stdlib.String.concat "" ["i:"; i])
  | RDF_Graph_Executable.T_BNode b -> Some (Stdlib.String.concat "" ["b:"; b])
  | RDF_Graph_Executable.T_Literal _ -> None  (* not indexed; see above *)

let _sse_build_indexes (g : RDF_Graph_Executable.rdf_graph) :
  _sse_graph_indexes =
  let pred_t = Hashtbl.create 256 in
  let subj_t = Hashtbl.create 256 in
  let obj_t  = Hashtbl.create 256 in
  Stdlib.List.iter (fun tr ->
    Hashtbl.add pred_t tr.RDF_Graph_Executable.p tr;
    (match _sse_subject_key tr.RDF_Graph_Executable.s with
     | Some k -> Hashtbl.add subj_t k tr
     | None -> ());
    (match _sse_object_key tr.RDF_Graph_Executable.o with
     | Some k -> Hashtbl.add obj_t k tr
     | None -> ())
  ) g;
  { pred_idx = pred_t; subj_idx = subj_t; obj_idx = obj_t }

let _sse_get_indexes (g : RDF_Graph_Executable.rdf_graph) : _sse_graph_indexes =
  match SseGraphHashtbl.find_opt _sse_indexes_cache g with
  | Some i -> i
  | None ->
    let i = _sse_build_indexes g in
    SseGraphHashtbl.add _sse_indexes_cache g i;
    i

(* Pick whichever bound component has the smallest bucket. Returns
   the candidate triple list plus a tag for debugging/stats (unused
   now but handy for future explain hooks). Hashtbl.find_all returns
   the whole bucket as a list; buckets have stable length under
   physical-equality caching. *)
let _sse_smallest_candidate_bucket
    (b : triple_pattern_bound)
    (ixs : _sse_graph_indexes)
    (fallback : RDF_Graph_Executable.rdf_graph) :
    RDF_Graph_Executable.triple Prims.list =
  let len (l : RDF_Graph_Executable.triple list) : int = Stdlib.List.length l in
  let pred_bucket = match b.bp with
    | FStar_Pervasives_Native.Some p -> Some (Hashtbl.find_all ixs.pred_idx p)
    | FStar_Pervasives_Native.None -> None in
  let subj_bucket = match b.bs with
    | FStar_Pervasives_Native.Some s ->
      (match _sse_subject_key s with
       | Some k -> Some (Hashtbl.find_all ixs.subj_idx k)
       | None -> None)
    | FStar_Pervasives_Native.None -> None in
  let obj_bucket = match b.bo with
    | FStar_Pervasives_Native.Some o ->
      (match _sse_object_key o with
       | Some k -> Some (Hashtbl.find_all ixs.obj_idx k)
       | None -> None)
    | FStar_Pervasives_Native.None -> None in
  let pick a b = match a, b with
    | None, None -> None
    | Some _, None -> a
    | None, Some _ -> b
    | Some la, Some lb -> if Stdlib.(<=) (len la) (len lb) then Some la else Some lb in
  match pick (pick pred_bucket subj_bucket) obj_bucket with
  | Some bucket -> bucket
  | None -> fallback

'''

s = s[:idx] + index_block + s[idx:]

# ------------------------------------------------------------------
# Step 2: rewrite `store_search` to consult the pred index when the
# triple pattern has a bound predicate. Fall back to the original
# full-list scan otherwise.
#
# Original (as patched by #95):
#   let store_search (g : graph_store) (b : triple_pattern_bound) :
#     RDF_Graph_Executable.triple Prims.list = triple_matches_bound b g.gs_graph
# ------------------------------------------------------------------

old_ss = ('let store_search (g : graph_store) (b : triple_pattern_bound) :\n'
          '  RDF_Graph_Executable.triple Prims.list= triple_matches_bound b g.gs_graph')

new_ss = ('let store_search (g : graph_store) (b : triple_pattern_bound) :\n'
          '  RDF_Graph_Executable.triple Prims.list=\n'
          '  let has_any_bound =\n'
          '    (match b.bp with FStar_Pervasives_Native.Some _ -> true | _ -> false)\n'
          '    || (match b.bs with FStar_Pervasives_Native.Some _ -> true | _ -> false)\n'
          '    || (match b.bo with FStar_Pervasives_Native.Some _ -> true | _ -> false)\n'
          '  in\n'
          '  if has_any_bound then\n'
          '    let ixs = _sse_get_indexes g.gs_graph in\n'
          '    let candidates = _sse_smallest_candidate_bucket b ixs g.gs_graph in\n'
          '    triple_matches_bound b candidates\n'
          '  else\n'
          '    triple_matches_bound b g.gs_graph')

if old_ss not in s:
    raise SystemExit("SPARQL11_Algebra.ml: expected store_search shape not found (has #95 applied?)")
s = s.replace(old_ss, new_ss)

with open(path, 'w') as f:
    f.write(s)

print('  pred-index installed; store_search now uses it for bound-predicate patterns')
PYEOF

echo "  SPARQL11_Algebra.ml patched (#97)."
