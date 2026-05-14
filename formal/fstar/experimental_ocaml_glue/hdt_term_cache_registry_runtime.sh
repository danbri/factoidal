#!/bin/bash
# RDF.Store.HDTTermCacheRegistry realisation — #253 Phase 2.5b.
#
# Mirrors cottas_lazy_dict_registry_runtime.sh's pattern but for
# HDT's 2-direction `lazy_term_cache` (vs cottas's 4-direction
# `lazy_dict`).
#
# Realises 4 assume_val declarations:
#   get_subjects_cache / get_predicates_cache / get_objects_cache
#   is_registered

set -euo pipefail

OUTDIR="$1"
ML="$OUTDIR/RDF_Store_HDTTermCacheRegistry.ml"

if [ ! -f "$ML" ]; then
  echo "  [hdt-term-cache-registry-runtime] WARN: $ML not found; skipping"
  exit 0
fi

if grep -q '__HDT_TERM_CACHE_REGISTRY_RUNTIME_APPLIED__' "$ML"; then
  echo "  [hdt-term-cache-registry-runtime] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

storage = """(* __HDT_TERM_CACHE_REGISTRY_RUNTIME_APPLIED__ *)
type registry_entry = {
  re_subjects   : RDF_Graph_Executable.subject RDF_Store_LazyTermCache.lazy_term_cache;
  re_predicates : RDF_Graph_Executable.wf_iri  RDF_Store_LazyTermCache.lazy_term_cache;
  re_objects    : RDF_Graph_Executable.rdf_term RDF_Store_LazyTermCache.lazy_term_cache;
}

let registry : (Prims.string, registry_entry) Stdlib.Hashtbl.t =
  Stdlib.Hashtbl.create 17

(* Called by the HDT runtime realisation when a fresh handle is
   opened. Populate thunks wrap the already-built dicts. *)
let register_for_path
  (p : Prims.string)
  (subj_pop : unit -> (Z.t * RDF_Graph_Executable.subject) Prims.list)
  (pred_pop : unit -> (Z.t * RDF_Graph_Executable.wf_iri) Prims.list)
  (obj_pop  : unit -> (Z.t * RDF_Graph_Executable.rdf_term) Prims.list)
  (subj_key : RDF_Graph_Executable.subject -> Prims.string)
  (pred_key : RDF_Graph_Executable.wf_iri -> Prims.string)
  (obj_key  : RDF_Graph_Executable.rdf_term -> Prims.string)
  : unit =
  let entry = {
    re_subjects   = RDF_Store_LazyTermCache.mk_lazy_term_cache subj_pop subj_key;
    re_predicates = RDF_Store_LazyTermCache.mk_lazy_term_cache pred_pop pred_key;
    re_objects    = RDF_Store_LazyTermCache.mk_lazy_term_cache obj_pop  obj_key;
  } in
  Stdlib.Hashtbl.replace registry p entry
"""
if "__HDT_TERM_CACHE_REGISTRY_RUNTIME_APPLIED__" not in content:
    content = content.replace("open Prims\n", "open Prims\n" + storage, 1)

def replace_failwith_stub(content, fn_name, signature, body):
    pattern = re.compile(
        r"let " + re.escape(fn_name) + r"\b[^=]*?=\s*"
        r"failwith\s*\n?\s*"
        r'"Not yet implemented:\s*RDF\.Store\.HDTTermCacheRegistry\.' + re.escape(fn_name) + r'"',
        re.DOTALL,
    )
    new = f"let {fn_name} {signature} =\n{body}"
    new_content, n = pattern.subn(new, content, count=1)
    if n != 1:
        sys.stderr.write(f"  [hdt-term-cache-registry-runtime] WARN: stub for {fn_name} not matched\n")
        return content, False
    return new_content, True

for (fn, field_ml, ret_ml) in [
    ("get_subjects_cache",   "re_subjects",   "RDF_Graph_Executable.subject"),
    ("get_predicates_cache", "re_predicates", "RDF_Graph_Executable.wf_iri"),
    ("get_objects_cache",    "re_objects",    "RDF_Graph_Executable.rdf_term"),
]:
    content, _ok = replace_failwith_stub(
        content, fn,
        f"(p : Prims.string) : {ret_ml} RDF_Store_LazyTermCache.lazy_term_cache FStar_Pervasives_Native.option",
        f"""  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.{field_ml}
  | None       -> FStar_Pervasives_Native.None""",
    )

content, _ok = replace_failwith_stub(
    content, "is_registered",
    "(p : Prims.string) : Prims.bool",
    "  Stdlib.Hashtbl.mem registry p",
)

path.write_text(content)
sys.stderr.write("  [hdt-term-cache-registry-runtime] 4 assume_vals + storage applied\n")
PYEOF

echo "  RDF.Store.HDTTermCacheRegistry runtime realisation applied."
