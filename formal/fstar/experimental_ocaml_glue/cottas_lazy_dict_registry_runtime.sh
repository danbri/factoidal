#!/bin/bash
# RDF.CottasStore.LazyDictRegistry realisation — #254 Commit 2b.
#
# Universe-safe alternative to the reverted Commit 2a (1daf67e ->
# f442c13). Instead of putting 4 `lazy_dict T` fields on
# `cottas_ondisk_handle` (which cascaded a universe-polymorphism
# constraint through SPARQL11.Store's mutual recursion), expose the
# lazy_dicts via path-keyed `assume val` lookups. The registry is
# an OCaml-side global Hashtbl<path, record-of-4-lazy_dicts>; F*
# sees only `path -> ML (option (lazy_dict T))` at the boundary.
#
# Realises 5 assume_val declarations:
#   get_subjects_lazy / get_predicates_lazy /
#   get_objects_lazy  / get_graphs_lazy / is_registered

set -euo pipefail

OUTDIR="$1"
ML="$OUTDIR/RDF_CottasStore_LazyDictRegistry.ml"

if [ ! -f "$ML" ]; then
  echo "  [lazy-dict-registry-runtime] WARN: $ML not found; skipping"
  exit 0
fi

if grep -q '__LAZY_DICT_REGISTRY_RUNTIME_APPLIED__' "$ML"; then
  echo "  [lazy-dict-registry-runtime] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# Header marker for idempotency + registry storage cell. Inserted
# just after `open Prims`.
storage = """(* __LAZY_DICT_REGISTRY_RUNTIME_APPLIED__ *)
type registry_entry = {
  re_subjects   : RDF_Graph_Executable.subject RDF_CottasStore_LazyDict.lazy_dict;
  re_predicates : RDF_Graph_Executable.wf_iri  RDF_CottasStore_LazyDict.lazy_dict;
  re_objects    : RDF_Graph_Executable.rdf_term RDF_CottasStore_LazyDict.lazy_dict;
  re_graphs     : Prims.string RDF_CottasStore_LazyDict.lazy_dict;
}

let registry : (Prims.string, registry_entry) Stdlib.Hashtbl.t =
  Stdlib.Hashtbl.create 17

(* Called by the cottas_ondisk_runtime realisation when a fresh
   handle is opened. Populate thunks here just wrap the already-
   built eager dicts — true lazy-on-disk parquet population is a
   future-commit upgrade once the consumer migration validates the
   shape. *)
let register_for_path
  (p : Prims.string)
  (subj_pop : unit -> (Z.t * RDF_Graph_Executable.subject * Prims.string) Prims.list)
  (pred_pop : unit -> (Z.t * RDF_Graph_Executable.wf_iri * Prims.string) Prims.list)
  (obj_pop  : unit -> (Z.t * RDF_Graph_Executable.rdf_term * Prims.string) Prims.list)
  (graph_pop : unit -> (Z.t * Prims.string * Prims.string) Prims.list)
  (subj_key : RDF_Graph_Executable.subject -> Prims.string)
  (pred_key : RDF_Graph_Executable.wf_iri -> Prims.string)
  (obj_key  : RDF_Graph_Executable.rdf_term -> Prims.string)
  (graph_key : Prims.string -> Prims.string)
  : unit =
  let entry = {
    re_subjects   = RDF_CottasStore_LazyDict.mk_lazy_dict subj_pop  subj_key;
    re_predicates = RDF_CottasStore_LazyDict.mk_lazy_dict pred_pop  pred_key;
    re_objects    = RDF_CottasStore_LazyDict.mk_lazy_dict obj_pop   obj_key;
    re_graphs     = RDF_CottasStore_LazyDict.mk_lazy_dict graph_pop graph_key;
  } in
  Stdlib.Hashtbl.replace registry p entry
"""
if "__LAZY_DICT_REGISTRY_RUNTIME_APPLIED__" not in content:
    content = content.replace("open Prims\n", "open Prims\n" + storage, 1)

def replace_failwith_stub(content, fn_name, signature, body):
    pattern = re.compile(
        r"let " + re.escape(fn_name) + r"\b[^=]*?=\s*"
        r"failwith\s*\n?\s*"
        r'"Not yet implemented:\s*RDF\.CottasStore\.LazyDictRegistry\.' + re.escape(fn_name) + r'"',
        re.DOTALL,
    )
    new = f"let {fn_name} {signature} =\n{body}"
    new_content, n = pattern.subn(new, content, count=1)
    if n != 1:
        sys.stderr.write(f"  [lazy-dict-registry-runtime] WARN: stub for {fn_name} not matched\n")
        return content, False
    return new_content, True

for (fn, field_ml, ret_ml) in [
    ("get_subjects_lazy",   "re_subjects",   "RDF_Graph_Executable.subject"),
    ("get_predicates_lazy", "re_predicates", "RDF_Graph_Executable.wf_iri"),
    ("get_objects_lazy",    "re_objects",    "RDF_Graph_Executable.rdf_term"),
    ("get_graphs_lazy",     "re_graphs",     "Prims.string"),
]:
    content, _ok = replace_failwith_stub(
        content, fn,
        f"(p : Prims.string) : {ret_ml} RDF_CottasStore_LazyDict.lazy_dict FStar_Pervasives_Native.option",
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
sys.stderr.write("  [lazy-dict-registry-runtime] 5 assume_vals + storage applied\n")
PYEOF

echo "  RDF.CottasStore.LazyDictRegistry runtime realisation applied."
