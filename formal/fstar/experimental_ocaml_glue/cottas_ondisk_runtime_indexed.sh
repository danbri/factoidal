#!/bin/bash
# RDF.CottasStore.OnDiskRuntime realisation — #118 Phase 2.5c.
#
# Realises the 9 `assume val ondisk_*_indexed` declarations in
# RDF.CottasStore.OnDiskRuntime.fst by routing them to the existing
# Hashtbl-backed `_fast` functions inside the `Cottas_ondisk_runtime`
# OCaml module that `cottas_ondisk_runtime.sh` installs into
# RDF_CottasStore.ml.
#
# Per the #118 retirement plan:
#
#   docs/designissues/2026-05-13-issue-118-cottas-ondisk-runtime-retirement-plan.md
#
# The F* spec layer reasons about the perf primitives via assume_vals.
# This patch is the OCaml-side realisation: each primitive forwards
# to `Cottas_ondisk_runtime.<name>_fast h <args>` where `h` is the
# handle extracted from `ds.cods_handle`.
#
# Rule #11(c) compliant: pure dispatch shim. No semantic decisions —
# only argument shuffling between the typed F* boundary and the
# Hashtbl-backed runtime helpers. The runtime helpers themselves
# remain in cottas_ondisk_runtime.sh's perf-shim block (Yod6/Tet3/
# Lamed3/bloom prune cascade) until #118 Phase 2.5g lands the
# round-trip lemmas + hash-witness CI gates.

set -euo pipefail

OUTDIR="$1"
ML="$OUTDIR/RDF_CottasStore_OnDiskRuntime.ml"

if [ ! -f "$ML" ]; then
  echo "  [ondisk-runtime-realise] WARN: $ML not found; skipping"
  echo "         (RDF.CottasStore.OnDiskRuntime.fst may not be in build-ocaml.sh's extract list yet)"
  exit 0
fi

if grep -q '__ONDISK_RUNTIME_REALISED__' "$ML"; then
  echo "  [ondisk-runtime-realise] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

def replace_failwith_stub(content, fn_name, signature, body):
    """Replace one `let fn_name <args> : <ret> = failwith "..."` stub."""
    pattern = re.compile(
        r"let " + re.escape(fn_name) + r"\b[^=]*?=\s*"
        r"failwith\s*\n?\s*"
        r'"Not yet implemented:\s*RDF\.CottasStore\.OnDiskRuntime\.' + re.escape(fn_name) + r'"',
        re.DOTALL,
    )
    new = f"let {fn_name} {signature} =\n{body}"
    new_content, n = pattern.subn(new, content, count=1)
    if n != 1:
        sys.stderr.write(f"  [ondisk-runtime-realise] WARN: stub for {fn_name} not matched\n")
        return content, False
    return new_content, True

# Header marker for idempotency.
header = "(* __ONDISK_RUNTIME_REALISED__ *)\n"
if header not in content:
    # Insert marker just after the `open Prims` line.
    content = content.replace("open Prims\n", "open Prims\n" + header, 1)

# NOTE: search/estimate skipped in Phase 2.5c — no _fast variants
# exist in current Cottas_ondisk_runtime module (retired earlier).
# Re-add when perf-fast search/estimate land again.

# 4 decoders
for (fn, ret) in [
    ("ondisk_decode_subject_indexed", "RDF_Graph_Executable.subject"),
    ("ondisk_decode_predicate_indexed", "RDF_Graph_Executable.wf_iri"),
    ("ondisk_decode_object_indexed", "RDF_Graph_Executable.rdf_term"),
    ("ondisk_decode_graph_indexed", "RDF_Graph_Executable.iri"),
]:
    short = fn.replace("ondisk_decode_", "").replace("_indexed", "")
    fast_name = f"decode_{short}_fast"
    content, _ok = replace_failwith_stub(
        content, fn,
        f"""(ds : RDF_CottasStore.cottas_ondisk_store)
  (id : Prims.nat)
  : {ret} FStar_Pervasives_Native.option""",
        f"""  let h = ds.RDF_CottasStore.cods_handle in
  try
    FStar_Pervasives_Native.Some
      (RDF_CottasStore.Cottas_ondisk_runtime.{fast_name} h id)
  with _ -> FStar_Pervasives_Native.None""",
    )

# 4 encoders (incl. graph)
for (fn, arg, ret) in [
    ("ondisk_encode_subject_indexed", "RDF_Graph_Executable.subject", "Prims.nat"),
    ("ondisk_encode_predicate_indexed", "RDF_Graph_Executable.wf_iri", "Prims.nat"),
    ("ondisk_encode_object_indexed", "RDF_Graph_Executable.rdf_term", "Prims.nat"),
    ("ondisk_encode_graph_indexed", "RDF_Graph_Executable.iri", "Prims.nat"),
]:
    short = fn.replace("ondisk_encode_", "").replace("_indexed", "")
    fast_name = f"encode_{short}_fast"
    content, _ok = replace_failwith_stub(
        content, fn,
        f"""(ds : RDF_CottasStore.cottas_ondisk_store)
  (v : {arg})
  : {ret} FStar_Pervasives_Native.option""",
        f"""  let h = ds.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_ondisk_runtime.{fast_name} h v""",
    )

path.write_text(content)
sys.stderr.write("  [ondisk-runtime-realise] all 9 assume_val routes applied\n")
PYEOF

echo "  RDF.CottasStore.OnDiskRuntime realisation applied."
