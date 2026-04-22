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
if grep -q 'sse_pred_index_cache' "$FILE"; then
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

index_block = '''(* Predicate-indexed graph store — post-extraction patch (issue #97).

   Key insight: most SPARQL triple patterns have a bound predicate.
   Keeping a `(predicate -> triple list)` Hashtbl per graph turns an
   O(|graph|) scan into an O(|triples with that predicate|) scan.
   On gene.ttl the predicate `a` has ~92k matches out of 889k triples;
   `wdt:P1057` has ~11k; `wdt:P688` has ~1.6k. The speedup scales
   directly with predicate selectivity.

   Cache is keyed by physical equality on the rdf_graph (which is just
   a triple list). OCaml list cells have stable identity, so the same
   loaded graph reuses its index across repeated store_search calls
   within a BGP. A different graph (new parse, different object) gets
   its own cache entry.

   The cache leaks memory weakly (Hashtbl.Make is not weak), but
   Factoidal is a single-shot CLI / single-page browser demo — process
   lifetime is short enough that this is fine. A long-running server
   would want Ephemeron.K1 or explicit invalidation. *)

module SseGraphHashtbl = Hashtbl.Make(struct
  type t = RDF_Graph_Executable.rdf_graph
  let equal = (==)
  (* hash_param limits traversal depth + visited count; for a list of
     millions this is essentially pointer-tag-level, constant time. *)
  let hash g = Hashtbl.seeded_hash_param 10 100 5 g
end)

(* The global cache. One entry per rdf_graph seen by store_search. *)
let _sse_pred_index_cache :
  (string, RDF_Graph_Executable.triple) Hashtbl.t SseGraphHashtbl.t =
  SseGraphHashtbl.create 16

let _sse_build_pred_index (g : RDF_Graph_Executable.rdf_graph) :
  (string, RDF_Graph_Executable.triple) Hashtbl.t =
  (* Start at 256 and let Hashtbl grow; counting the list would force
     an O(n) walk before we start populating, wasting time. *)
  let t = Hashtbl.create 256 in
  Stdlib.List.iter (fun tr ->
    Hashtbl.add t tr.RDF_Graph_Executable.p tr
  ) g;
  t

let _sse_get_pred_index (g : RDF_Graph_Executable.rdf_graph) :
  (string, RDF_Graph_Executable.triple) Hashtbl.t =
  match SseGraphHashtbl.find_opt _sse_pred_index_cache g with
  | Some t -> t
  | None ->
    let t = _sse_build_pred_index g in
    SseGraphHashtbl.add _sse_pred_index_cache g t;
    t

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
          '  match b.bp with\n'
          '  | FStar_Pervasives_Native.Some p ->\n'
          '    let idx = _sse_get_pred_index g.gs_graph in\n'
          '    let candidates = Hashtbl.find_all idx p in\n'
          '    triple_matches_bound b candidates\n'
          '  | FStar_Pervasives_Native.None ->\n'
          '    triple_matches_bound b g.gs_graph')

if old_ss not in s:
    raise SystemExit("SPARQL11_Algebra.ml: expected store_search shape not found (has #95 applied?)")
s = s.replace(old_ss, new_ss)

with open(path, 'w') as f:
    f.write(s)

print('  pred-index installed; store_search now uses it for bound-predicate patterns')
PYEOF

echo "  SPARQL11_Algebra.ml patched (#97)."
