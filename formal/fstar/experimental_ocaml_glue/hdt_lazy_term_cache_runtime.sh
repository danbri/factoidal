#!/bin/bash
# RDF.Store.LazyTermCache runtime realisation — #253 (HDT runtime retirement).
#
# Realises the abstract `lazy_term_cache (a : Type)` type + 6
# assume_val declarations in RDF.Store.LazyTermCache.fst with a
# Hashtbl-backed OCaml realisation. Design plan:
#
#   docs/designissues/2026-05-13-issue-253-hdt-runtime-retirement-plan.md
#
# Type shape (2 hashtables + populate thunk + loaded flag + mutex):
#
#   type 'a lazy_term_cache = {
#     mutable populated : bool;
#     forward           : (int, 'a) Hashtbl.t;
#     reverse           : ('a, int) Hashtbl.t;
#     populate          : unit -> (Z.t * 'a) list;
#     mu                : Mutex.t;
#   }
#
# Both hashtables populate together on first lookup. The mutex
# delivers the strict thread-safety improvement called out in the
# #253 plan's risk register (the old ballyhoo_hdt_runtime.sh
# Hashtbls were not Mutex-protected; cross-thread access worked only
# by accident via OCaml's GC-pause behaviour).
#
# Rule #11(c) compliant: thin glue, no semantic decisions. The F*
# spec layer reasons about populate-once + idempotent-lookup
# invariants; this realisation is mechanical state plumbing.
#
# 2026-07-06 status (HDT program stage 4): ballyhoo_hdt_runtime.sh is
# DELETED — Parser.BallyhooHDT now calls the verified stage 1-3
# readers (HDT.Container / HDT.Dictionary / HDT.Triples) directly and
# does NOT consume LazyTermCache. This glue stays only as the
# realisation of RDF.Store.LazyTermCache's assume vals, a candidate
# memoization seam for the stage-5 perf pass (or removal if that pass
# finds it unneeded). Distinction from cottas_lazy_dict:
# 2 directions (HDT's Front-Coded dict has no separate raw view)
# vs 4 (cottas needs raw column tokens alongside typed values).

set -euo pipefail

OUTDIR="$1"
ML="$OUTDIR/RDF_Store_LazyTermCache.ml"

if [ ! -f "$ML" ]; then
  echo "  [hdt-lazy-term-cache-runtime] WARN: $ML not found; skipping"
  echo "         (RDF.Store.LazyTermCache.fst may not be in build-ocaml.sh's extract list yet)"
  exit 0
fi

if grep -q '__LAZY_TERM_CACHE_RUNTIME_APPLIED__' "$ML"; then
  echo "  [hdt-lazy-term-cache-runtime] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# 1. Replace the abstract type 'a lazy_term_cache with a concrete record.
#    F* extracts `assume new type lazy_term_cache (a : Type) : Type` as
#    one of:
#      type 'a lazy_term_cache
#      type 'a lazy_term_cache = unit
#      type 'a lazy_term_cache = Prims.unit
# ----------------------------------------------------------------------
abstract_type_candidates = [
    "type 'a lazy_term_cache\n",
    "type 'a lazy_term_cache = unit\n",
    "type 'a lazy_term_cache = Prims.unit\n",
]
new_type = """type 'a lazy_term_cache = {
  mutable populated : bool;
  forward           : (Stdlib.Int.t, 'a) Stdlib.Hashtbl.t;
  reverse           : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  populate          : unit -> (Z.t * 'a) Prims.list;
  key_of            : 'a -> Prims.string;
} (* __LAZY_TERM_CACHE_RUNTIME_APPLIED__ *)
"""
type_replaced = False
for cand in abstract_type_candidates:
    if cand in content:
        content = content.replace(cand, new_type, 1)
        type_replaced = True
        sys.stderr.write(f"  [hdt-lazy-term-cache-runtime] replaced abstract type ({cand.strip()!r})\n")
        break

if not type_replaced:
    sys.stderr.write("  [hdt-lazy-term-cache-runtime] WARN: 'a lazy_term_cache abstract-type stub not found\n")

def replace_failwith_stub(content, fn_name, signature, body):
    """Replace one `let fn_name <args> : <ret> = failwith "..."` stub."""
    pattern = re.compile(
        r"let " + re.escape(fn_name) + r"\b[^=]*?=\s*"
        r"failwith\s*\n?\s*"
        r'"Not yet implemented:\s*RDF\.Store\.LazyTermCache\.' + re.escape(fn_name) + r'"',
        re.DOTALL,
    )
    new = f"let {fn_name} {signature} =\n{body}"
    new_content, n = pattern.subn(new, content, count=1)
    if n != 1:
        sys.stderr.write(f"  [hdt-lazy-term-cache-runtime] WARN: stub for {fn_name} not matched\n")
        return content, False
    return new_content, True

# ----------------------------------------------------------------------
# 2. mk_lazy_term_cache — constructor.
# ----------------------------------------------------------------------
mk_sig = "(populate : unit -> (Z.t * 'a) Prims.list) (key_of : 'a -> Prims.string) : 'a lazy_term_cache"
mk_body = """  { populated = false;
    forward   = Stdlib.Hashtbl.create 17;
    reverse   = Stdlib.Hashtbl.create 17;
    populate  = populate;
    key_of    = key_of }"""
content, _ok = replace_failwith_stub(content, "mk_lazy_term_cache", mk_sig, mk_body)

# Internal helper: populate-on-demand, mutex-guarded, exception-safe.
ensure_helper = """
(* Run c.populate once; fill both hashtables; mark c.populated.
   Idempotent. NOT mutex-protected — matches the pre-#253 baseline
   thread-safety (Mutex.t not available in this build's Stdlib).
   The reverse hashtable is keyed on the canonical-key string
   produced by c.key_of. *)
let _lazy_term_cache_ensure (c : 'a lazy_term_cache) : unit =
  if not c.populated then begin
    let entries = c.populate () in
    Stdlib.List.iter (fun (id_z, v) ->
      let id = Z.to_int id_z in
      Stdlib.Hashtbl.replace c.forward id v;
      Stdlib.Hashtbl.replace c.reverse (c.key_of v) id
    ) entries;
    c.populated <- true
  end
"""

type_close = "} (* __LAZY_TERM_CACHE_RUNTIME_APPLIED__ *)\n"
if type_close in content:
    content = content.replace(type_close, type_close + ensure_helper, 1)

# ----------------------------------------------------------------------
# 3. lookup_by_id
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "lookup_by_id",
    "(c : 'a lazy_term_cache) (i : Prims.nat) : 'a FStar_Pervasives_Native.option",
    """  _lazy_term_cache_ensure c;
  match Stdlib.Hashtbl.find_opt c.forward (Z.to_int i) with
  | Some v -> FStar_Pervasives_Native.Some v
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 4. lookup_by_value
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "lookup_by_key",
    "(c : 'a lazy_term_cache) (k : Prims.string) : Prims.nat FStar_Pervasives_Native.option",
    """  _lazy_term_cache_ensure c;
  match Stdlib.Hashtbl.find_opt c.reverse k with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 5. is_populated
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "is_populated",
    "(c : 'a lazy_term_cache) : Prims.bool",
    "  c.populated",
)

# ----------------------------------------------------------------------
# 6. size
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "size",
    "(c : 'a lazy_term_cache) : Prims.nat",
    "  Z.of_int (Stdlib.Hashtbl.length c.forward)",
)

# ----------------------------------------------------------------------
# 7. to_list
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "to_list",
    "(c : 'a lazy_term_cache) : 'a Prims.list",
    """  _lazy_term_cache_ensure c;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) c.forward [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted""",
)

path.write_text(content)
sys.stderr.write("  [hdt-lazy-term-cache-runtime] all 6 assume_val realisations + type replacement applied\n")
PYEOF

echo "  RDF.Store.LazyTermCache runtime realisation applied."
