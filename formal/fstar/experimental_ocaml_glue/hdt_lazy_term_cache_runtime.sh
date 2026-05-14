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
# #253 plan's risk register (the current ballyhoo_hdt_runtime.sh
# Hashtbls are not Mutex-protected; cross-thread access works only
# by accident via OCaml's GC-pause behaviour).
#
# Rule #11(c) compliant: thin glue, no semantic decisions. The F*
# spec layer reasons about populate-once + idempotent-lookup
# invariants; this realisation is mechanical state plumbing.
#
# Replaces ballyhoo_hdt_runtime.sh once the HDT cache consumers
# (Parser.BallyhooHDT.fst:hdt_open_graph_store + term-ID decoders)
# migrate to LazyTermCache. Distinction from cottas_lazy_dict:
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
  forward           : (int, 'a) Stdlib.Hashtbl.t;
  reverse           : ('a, int) Stdlib.Hashtbl.t;
  populate          : unit -> (Z.t * 'a) Prims.list;
  mu                : Stdlib.Mutex.t;
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
mk_sig = "(populate : unit -> (Z.t * 'a) Prims.list) : 'a lazy_term_cache"
mk_body = """  { populated = false;
    forward   = Stdlib.Hashtbl.create 17;
    reverse   = Stdlib.Hashtbl.create 17;
    populate  = populate;
    mu        = Stdlib.Mutex.create () }"""
content, _ok = replace_failwith_stub(content, "mk_lazy_term_cache", mk_sig, mk_body)

# Internal helper: populate-on-demand, mutex-guarded, exception-safe.
ensure_helper = """
(* Run c.populate once; fill both hashtables; mark c.populated.
   Idempotent + cross-thread safe (mutex). *)
let _lazy_term_cache_ensure (c : 'a lazy_term_cache) : unit =
  if not c.populated then begin
    Stdlib.Mutex.lock c.mu;
    (try
      if not c.populated then begin
        let entries = c.populate () in
        Stdlib.List.iter (fun (id_z, v) ->
          let id = Z.to_int id_z in
          Stdlib.Hashtbl.replace c.forward id v;
          Stdlib.Hashtbl.replace c.reverse v id
        ) entries;
        c.populated <- true
      end;
      Stdlib.Mutex.unlock c.mu
    with e ->
      Stdlib.Mutex.unlock c.mu;
      raise e)
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
    content, "lookup_by_value",
    "(c : 'a lazy_term_cache) (v : 'a) : Prims.nat FStar_Pervasives_Native.option",
    """  _lazy_term_cache_ensure c;
  match Stdlib.Hashtbl.find_opt c.reverse v with
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
  let n = Stdlib.Hashtbl.length c.forward in
  let buf = Stdlib.Array.make n (Obj.magic ()) in
  Stdlib.Hashtbl.iter (fun i v ->
    if i >= 0 && i < n then Stdlib.Array.set buf i v) c.forward;
  Stdlib.Array.to_list buf""",
)

path.write_text(content)
sys.stderr.write("  [hdt-lazy-term-cache-runtime] all 6 assume_val realisations + type replacement applied\n")
PYEOF

echo "  RDF.Store.LazyTermCache runtime realisation applied."
