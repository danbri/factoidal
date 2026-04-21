#!/bin/bash
# Issue #95: Stack-safe list operations in SPARQL11_Algebra.ml.
# https://github.com/danbri/factoidal/issues/95
#
# The F* extraction emits three hot-path list operations in
# SPARQL11_Algebra.ml that are structurally non-tail-recursive:
#
#   1. triple_matches_bound      — cons-after-recurse over the full
#                                  graph triple list; blows the native
#                                  stack on graphs >~200k triples.
#   2. list_filter_map           — cons-after-recurse over an arbitrary
#                                  solution_sequence.
#   3. FStar_List_Tot_Base.concatMap call sites — the underlying
#                                  runtime function is `flatten (map f l)`
#                                  where `flatten` uses non-tail-rec
#                                  append, so stack-unsafe on long lists.
#
# All three come from straightforward F* definitions that are provably
# correct but do not extract to tail-recursive OCaml. The fix is
# purely mechanical and preserves observational equivalence:
#
#   * triple_matches_bound becomes List.rev (List.fold_left ... [] ts)
#   * list_filter_map becomes the tail-rec `sse_filter_map` defined
#     at module top
#   * concatMap call sites are rewritten to `sse_concat_map`
#
# No semantic change. Same outputs; only stack behaviour changes.
# Every edit is protected by an idempotency marker so re-running the
# patch on an already-patched file is a no-op.
#
# This is the smallest patch that unblocks basic SPARQL evaluation on
# ~1M-triple graphs. Joins with naive O(n*m) cardinality still run
# slow without indexed stores — that is a separate perf issue and
# out of scope here.

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
  echo "  SPARQL11_Algebra.ml not found in $OUTDIR; skipping 95_stack_safe_list_ops.sh"
  exit 0
fi

# Idempotency: all three pieces leave the marker string "sse_concat_map"
# in the file. If present, this patch has already been applied.
if grep -q 'sse_concat_map' "$FILE"; then
  echo "  95_stack_safe_list_ops.sh already applied to $FILE"
  exit 0
fi

echo "  Applying 95_stack_safe_list_ops.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    s = f.read()

# ------------------------------------------------------------------
# Step 1: insert stack-safe helpers right after `open Prims`.
# ------------------------------------------------------------------
helpers = '''
(* Stack-safe list helpers — post-extraction patch (issue #95).
   FStar_List_Tot_Base.concatMap is `flatten (map f l)`, which on
   ~889k-element solution_sequences overflows the native stack via
   non-tail-rec append inside flatten. These helpers use
   List.rev_append + List.rev (both tail-rec) so the same pure
   operation runs in constant stack. Observationally identical to
   the originals. *)
let sse_concat_map f l =
  Stdlib.List.rev
    (Stdlib.List.fold_left
       (fun acc x -> Stdlib.List.rev_append (f x) acc)
       [] l)
let sse_filter_map f l =
  Stdlib.List.rev
    (Stdlib.List.fold_left
       (fun acc x ->
          match f x with
          | FStar_Pervasives_Native.Some y -> y :: acc
          | FStar_Pervasives_Native.None -> acc)
       [] l)
let sse_append xs ys =
  Stdlib.List.rev_append (Stdlib.List.rev xs) ys
'''

marker = 'open Prims\n'
idx = s.find(marker)
if idx < 0:
    raise SystemExit("SPARQL11_Algebra.ml: missing 'open Prims' preamble")
insert_at = idx + len(marker)
s = s[:insert_at] + helpers + s[insert_at:]

# ------------------------------------------------------------------
# Step 2: rewrite triple_matches_bound to tail-rec form.
# The extracted definition looks like:
#   let rec triple_matches_bound (b : triple_pattern_bound)
#     (ts : RDF_Graph_Executable.triple Prims.list) :
#     RDF_Graph_Executable.triple Prims.list=
#     match ts with
#     | [] -> []
#     | t::rest ->
#         let subj_ok = ... in
#         let pred_ok = ... in
#         let obj_ok  = ... in
#         let rest' = triple_matches_bound b rest in
#         if (subj_ok && pred_ok) && obj_ok then t :: rest' else rest'
# ------------------------------------------------------------------

old_tmb = '''let rec triple_matches_bound (b : triple_pattern_bound)
  (ts : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match ts with
  | [] -> []
  | t::rest ->
      let subj_ok =
        match b.bs with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some s ->
            RDF_Graph_Executable.subject_eq s t.RDF_Graph_Executable.s in
      let pred_ok =
        match b.bp with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some p -> p = t.RDF_Graph_Executable.p in
      let obj_ok =
        match b.bo with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some o ->
            RDF_Graph_Executable.rdf_term_eq o t.RDF_Graph_Executable.o in
      let rest' = triple_matches_bound b rest in
      if (subj_ok && pred_ok) && obj_ok then t :: rest' else rest\''''

new_tmb = '''(* Stack-safe rewrite — issue #95. Original was cons-after-recurse,
   which overflows on graphs larger than ~200k triples (gene.ttl has
   889k). This version is tail-rec via fold_left accumulator. *)
let triple_matches_bound (b : triple_pattern_bound)
  (ts : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  Stdlib.List.rev
    (Stdlib.List.fold_left
       (fun acc t ->
          let subj_ok =
            match b.bs with
            | FStar_Pervasives_Native.None -> true
            | FStar_Pervasives_Native.Some s ->
                RDF_Graph_Executable.subject_eq s t.RDF_Graph_Executable.s in
          let pred_ok =
            match b.bp with
            | FStar_Pervasives_Native.None -> true
            | FStar_Pervasives_Native.Some p -> p = t.RDF_Graph_Executable.p in
          let obj_ok =
            match b.bo with
            | FStar_Pervasives_Native.None -> true
            | FStar_Pervasives_Native.Some o ->
                RDF_Graph_Executable.rdf_term_eq o t.RDF_Graph_Executable.o in
          if (subj_ok && pred_ok) && obj_ok then t :: acc else acc)
       [] ts)'''

if old_tmb not in s:
    raise SystemExit("SPARQL11_Algebra.ml: expected triple_matches_bound shape not found")
s = s.replace(old_tmb, new_tmb)

# ------------------------------------------------------------------
# Step 3: rewrite list_filter_map to delegate to sse_filter_map.
# The extracted definition is cons-after-recurse and overflows on
# solution_sequence lengths > ~200k.
# ------------------------------------------------------------------

old_lfm = '''let rec list_filter_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f l ->
    match l with
    | [] -> []
    | x::xs ->
        (match f x with
         | FStar_Pervasives_Native.Some y -> y :: (list_filter_map f xs)
         | FStar_Pervasives_Native.None -> list_filter_map f xs)'''

new_lfm = '''(* Stack-safe rewrite — issue #95. Original was cons-after-recurse. *)
let list_filter_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  = sse_filter_map'''

if old_lfm not in s:
    raise SystemExit("SPARQL11_Algebra.ml: expected list_filter_map shape not found")
s = s.replace(old_lfm, new_lfm)

# ------------------------------------------------------------------
# Step 4: swap FStar_List_Tot_Base.concatMap call sites to sse_concat_map.
# We don't touch the import — FStar_List_Tot_Base.concatMap just stops
# being referenced. Sixteen call sites in SPARQL11_Algebra.ml as of
# 2026-04-21.
# ------------------------------------------------------------------

n = s.count('FStar_List_Tot_Base.concatMap')
if n == 0:
    raise SystemExit("SPARQL11_Algebra.ml: no FStar_List_Tot_Base.concatMap call sites found")
s = s.replace('FStar_List_Tot_Base.concatMap', 'sse_concat_map')

with open(path, 'w') as f:
    f.write(s)

print(f'  rewrote {n} concatMap call sites + triple_matches_bound + list_filter_map')
PYEOF

echo "  SPARQL11_Algebra.ml patched."
