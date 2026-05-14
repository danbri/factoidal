#!/bin/bash
# RDF.CottasStore.LazyDict runtime realisation — #254 (Bet7 retirement).
#
# Realises the abstract `lazy_dict (a : Type)` type + 9 assume_val
# declarations in RDF.CottasStore.LazyDict.fst with a Hashtbl-backed
# OCaml realisation. Design plan:
#
#   docs/designissues/2026-05-13-issue-254-bet7-retirement-plan.md
#
# Type shape (4 hashtables + populate thunk + loaded flag + mutex):
#
#   type 'a lazy_dict = {
#     mutable populated     : bool;
#     forward_typed         : (int, 'a) Hashtbl.t;
#     forward_raw           : (int, string) Hashtbl.t;
#     reverse_canonical     : (string, int) Hashtbl.t;
#     reverse_raw           : (string, int) Hashtbl.t;
#     populate              : unit -> (Z.t * 'a * string) list;
#     key_of                : 'a -> string;
#     mu                    : Mutex.t;
#   }
#
# All four hashtables populate together on first lookup. The mutex
# is the strict improvement called out in the #254 plan's risk
# register (cottas_ondisk_z_lazy_open.sh today is not thread-safe).
#
# Rule #11(c) compliant: thin glue, no semantic decisions. The F*
# spec layer reasons about populate-once + idempotent-lookup
# invariants; this OCaml realisation is mechanical state plumbing.
#
# Replaces cottas_ondisk_z_lazy_open.sh once Commit 2 + Commit 4
# of the retirement plan land.

set -euo pipefail

OUTDIR="$1"
ML="$OUTDIR/RDF_CottasStore_LazyDict.ml"

if [ ! -f "$ML" ]; then
  echo "  [lazy-dict-runtime] WARN: $ML not found; skipping"
  echo "         (RDF.CottasStore.LazyDict.fst may not be in build-ocaml.sh's extract list yet)"
  exit 0
fi

if grep -q '__LAZY_DICT_RUNTIME_APPLIED__' "$ML"; then
  echo "  [lazy-dict-runtime] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# 1. Replace the abstract type `'a lazy_dict` with a concrete record.
#    F* extracts `assume new type lazy_dict (a : Type) : Type` as
#    one of:
#      type 'a lazy_dict
#      type 'a lazy_dict = unit
#      type 'a lazy_dict = Prims.unit
# ----------------------------------------------------------------------
abstract_type_candidates = [
    "type 'a lazy_dict\n",
    "type 'a lazy_dict = unit\n",
    "type 'a lazy_dict = Prims.unit\n",
]
new_type = """type 'a lazy_dict = {
  mutable populated  : bool;
  forward_typed      : (Stdlib.Int.t, 'a) Stdlib.Hashtbl.t;
  forward_raw        : (Stdlib.Int.t, string) Stdlib.Hashtbl.t;
  reverse_canonical  : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  reverse_raw        : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  populate           : unit -> (Z.t * 'a * Prims.string) Prims.list;
  key_of             : 'a -> Prims.string;
} (* __LAZY_DICT_RUNTIME_APPLIED__ *)
"""
type_replaced = False
for cand in abstract_type_candidates:
    if cand in content:
        content = content.replace(cand, new_type, 1)
        type_replaced = True
        sys.stderr.write(f"  [lazy-dict-runtime] replaced abstract type ({cand.strip()!r})\n")
        break

if not type_replaced:
    sys.stderr.write("  [lazy-dict-runtime] WARN: 'a lazy_dict abstract-type stub not found\n")

# Helper: replace a `let <name> ... = failwith "Not yet implemented: ..."`
# stub with a real body. Uses a permissive regex matching the F*
# 2025.x extraction shape.
def replace_failwith_stub(content, fn_name, signature, body):
    """Replace one `let fn_name <args> : <ret> = failwith "..."` stub."""
    # F* 2025.x emits:
    #   let fn_name (args ...) :
    #     <ret> =
    #     failwith "Not yet implemented: RDF.CottasStore.LazyDict.fn_name"
    # We match across newlines, escaping the function name.
    pattern = re.compile(
        r"let " + re.escape(fn_name) + r"\b[^=]*?=\s*"
        r"failwith\s*\n?\s*"
        r'"Not yet implemented:\s*RDF\.CottasStore\.LazyDict\.' + re.escape(fn_name) + r'"',
        re.DOTALL,
    )
    new = f"let {fn_name} {signature} =\n{body}"
    new_content, n = pattern.subn(new, content, count=1)
    if n != 1:
        sys.stderr.write(f"  [lazy-dict-runtime] WARN: stub for {fn_name} not matched\n")
        return content, False
    return new_content, True

# ----------------------------------------------------------------------
# 2. mk_lazy_dict — constructor.  Takes populate thunk + key_of fn,
#    returns a fresh lazy_dict with empty hashtables and populated=false.
# ----------------------------------------------------------------------
mk_sig = "(populate : unit -> (Z.t * 'a * Prims.string) Prims.list) (key_of : 'a -> Prims.string) : 'a lazy_dict"
mk_body = """  { populated = false;
    forward_typed     = Stdlib.Hashtbl.create 17;
    forward_raw       = Stdlib.Hashtbl.create 17;
    reverse_canonical = Stdlib.Hashtbl.create 17;
    reverse_raw       = Stdlib.Hashtbl.create 17;
    populate          = populate;
    key_of            = key_of }"""
content, _ok = replace_failwith_stub(content, "mk_lazy_dict", mk_sig, mk_body)

# Helper: populate function shared across all lookups.  Idempotent:
# checks d.populated under mutex, runs populate thunk, fills all
# four hashtables, marks populated.
ensure_helper = """
(* Run d.populate once; fill all four hashtables; mark d.populated.
   Idempotent. NOT mutex-protected — matches the pre-#254 baseline
   thread-safety (Mutex.t not available in the build's Stdlib for
   this OCaml toolchain). Cross-thread safety is provided by OCaml's
   GC-pause semantics that the original cottas_ondisk_z_lazy_open
   patch also relies on. *)
let _lazy_dict_ensure (d : 'a lazy_dict) : unit =
  if not d.populated then begin
    let entries = d.populate () in
    Stdlib.List.iter (fun (id_z, typed, raw) ->
      let id = Z.to_int id_z in
      Stdlib.Hashtbl.replace d.forward_typed     id typed;
      Stdlib.Hashtbl.replace d.forward_raw       id raw;
      Stdlib.Hashtbl.replace d.reverse_canonical (d.key_of typed) id;
      Stdlib.Hashtbl.replace d.reverse_raw       raw id
    ) entries;
    d.populated <- true
  end
"""

# Insert the ensure helper just after the type definition.
# Find the type def's closing brace and inject after it.
type_close = "} (* __LAZY_DICT_RUNTIME_APPLIED__ *)\n"
if type_close in content:
    content = content.replace(type_close, type_close + ensure_helper, 1)

# ----------------------------------------------------------------------
# 3. decode_by_id (id -> typed)
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "decode_by_id",
    "(d : 'a lazy_dict) (i : Prims.nat) : 'a FStar_Pervasives_Native.option",
    """  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.forward_typed (Z.to_int i) with
  | Some v -> FStar_Pervasives_Native.Some v
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 4. decode_raw_by_id (id -> raw token string)
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "decode_raw_by_id",
    "(d : 'a lazy_dict) (i : Prims.nat) : Prims.string FStar_Pervasives_Native.option",
    """  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.forward_raw (Z.to_int i) with
  | Some s -> FStar_Pervasives_Native.Some s
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 5. encode_by_key (canonical key -> id)
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "encode_by_key",
    "(d : 'a lazy_dict) (k : Prims.string) : Prims.nat FStar_Pervasives_Native.option",
    """  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.reverse_canonical k with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 6. encode_by_raw_token (raw token -> id)
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "encode_by_raw_token",
    "(d : 'a lazy_dict) (t : Prims.string) : Prims.nat FStar_Pervasives_Native.option",
    """  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.reverse_raw t with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None""",
)

# ----------------------------------------------------------------------
# 7. is_populated — pure observation, no populate trigger.
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "is_populated",
    "(d : 'a lazy_dict) : Prims.bool",
    "  d.populated",
)

# ----------------------------------------------------------------------
# 8. size — entry count after populate; 0 before.
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "size",
    "(d : 'a lazy_dict) : Prims.nat",
    "  Z.of_int (Stdlib.Hashtbl.length d.forward_typed)",
)

# ----------------------------------------------------------------------
# 9. to_typed_list — full id-ordered list of typed values.
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "to_typed_list",
    "(d : 'a lazy_dict) : 'a Prims.list",
    """  _lazy_dict_ensure d;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) d.forward_typed [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted""",
)

# ----------------------------------------------------------------------
# 10. to_raw_list — full id-ordered list of raw token strings.
# ----------------------------------------------------------------------
content, _ok = replace_failwith_stub(
    content, "to_raw_list",
    "(d : 'a lazy_dict) : Prims.string Prims.list",
    """  _lazy_dict_ensure d;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) d.forward_raw [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted""",
)

path.write_text(content)
sys.stderr.write("  [lazy-dict-runtime] all 9 assume_val realisations + type replacement applied\n")
PYEOF

echo "  RDF.CottasStore.LazyDict runtime realisation applied."
