#!/bin/bash
# Issue #63: hash and UUID assume val stubs for SPARQL11_Algebra.ml
# https://github.com/danbri/factoidal/issues/63
#
# Replaces F*-extracted failwith stubs for:
#   - hash_md5, hash_sha1, hash_sha256, hash_sha384, hash_sha512
#   - UUID/STRUUID generation (random UUID v4 instead of all-zeros placeholder)
#
# REGEX STATUS (rule #3): this patch NO LONGER realises any regex assume val.
# Both regex seams are now VERIFIED F* over the Regex.Syntax/Exec/XSDPattern
# codepoint engine (SPARQL11.Algebra.fst):
#   - regex_match  (SPARQL REGEX / XPath fn:matches) — retired #304 phase 4.
#   - regex_replace (SPARQL REPLACE / XPath fn:replace) — retired #304 phase 5
#     (leftmost-longest spans on the verified derivative engine + a total,
#     fuel-bounded capturing matcher for `$N` templates). The former OCaml
#     `Str` realisation + the `xpath_to_str_regex` byte-level translator are
#     GONE (anti-pattern #10 eliminated). This script therefore no longer
#     touches SPARQL11_Algebra.ml's regex functions at all.
# The only assume vals this script still realises are the pure-OCaml hash
# primitives (Fstar_pure_hashes, same bytecode under native/js_of_ocaml/
# wasm_of_ocaml) and random UUID v4 generation — both acknowledged #63 gaps.

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
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (hash/UUID stubs)..."

# All patches are applied in a single python3 pass for atomicity.
# Guard on the md5 marker: once the hash stubs are realised, re-running is a
# no-op (the failwith source strings no longer match).
if ! grep -q 'Fstar_pure_hashes.md5' "$FILE"; then
  python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# 1. Replace hash function stubs with pure-OCaml implementations.
# Pure OCaml (no C primitives) so the same bytecode runs under native +
# js_of_ocaml + wasm_of_ocaml. See ocaml-output/fstar_pure_hashes.ml.
content = content.replace(
    '''let hash_md5 (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: SPARQL11.Algebra.hash_md5"''',
    '''let hash_md5 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.md5 s'''
)
content = content.replace(
    '''let hash_sha1 (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: SPARQL11.Algebra.hash_sha1"''',
    '''let hash_sha1 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha1 s'''
)
content = content.replace(
    '''let hash_sha256 (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: SPARQL11.Algebra.hash_sha256"''',
    '''let hash_sha256 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha256 s'''
)
content = content.replace(
    '''let hash_sha384 (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: SPARQL11.Algebra.hash_sha384"''',
    '''let hash_sha384 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha384 s'''
)
content = content.replace(
    '''let hash_sha512 (uu___ : Prims.string) : Prims.string=
  failwith "Not yet implemented: SPARQL11.Algebra.hash_sha512"''',
    '''let hash_sha512 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha512 s'''
)

# 2. Replace UUID/STRUUID hardcoded stubs with random UUID v4 generation
content = content.replace(
    '''          if iri_s = "http://www.w3.org/2005/xpath-functions#uuid"
          then
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 "urn:uuid:00000000-0000-0000-0000-000000000000")
          else
            if iri_s = "http://www.w3.org/2005/xpath-functions#struuid"
            then er_string "00000000-0000-0000-0000-000000000000"''',
    '''          if iri_s = "http://www.w3.org/2005/xpath-functions#uuid"
          then
            let () = Random.self_init () in
            let hex () = Printf.sprintf "%04x" (Random.int 0x10000) in
            let s = Printf.sprintf "%s%s-%s-%s-%s-%s%s%s"
              (hex ()) (hex ()) (hex ())
              (Printf.sprintf "4%03x" (Random.int 0x1000))
              (Printf.sprintf "%04x" (0x8000 lor (Random.int 0x4000)))
              (hex ()) (hex ()) (hex ()) in
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 (Prims.strcat "urn:uuid:" s))
          else
            if iri_s = "http://www.w3.org/2005/xpath-functions#struuid"
            then
              let () = Random.self_init () in
              let hex () = Printf.sprintf "%04x" (Random.int 0x10000) in
              let s = Printf.sprintf "%s%s-%s-%s-%s-%s%s%s"
                (hex ()) (hex ()) (hex ())
                (Printf.sprintf "4%03x" (Random.int 0x1000))
                (Printf.sprintf "%04x" (0x8000 lor (Random.int 0x4000)))
                (hex ()) (hex ()) (hex ()) in
              er_string s'''
)

with open(path, 'w') as f:
    f.write(content)
PYEOF
fi

echo "  Hash/UUID stubs patched."

# RDF_Canonical.ml — wire its hash_sha256 assume_val to Fstar_pure_hashes.sha256.
# RDF.Canonical.fst declares its own assume val for self-containment (avoids a
# back-edge from RDF.Canonical to SPARQL11.Algebra). Same shape as the
# SPARQL11_Algebra patches above.
#
# F* 2025.12.15 emits two distinct surface forms for `assume val`:
#   form A:  let hash_sha256 (uu___ : Prims.string) : Prims.string=
#              failwith "Not yet implemented: ..."
#   form B:  let (hash_sha256 : Prims.string -> Prims.string) =
#              fun uu___ -> failwith "Not yet implemented: ..."
# SPARQL11_Algebra.ml extracts as form A; RDF_Canonical.ml as form B (the
# determining factor appears to be module-level details, not the assume-val
# itself). Patch both forms — the unmatched one is a no-op replace.
CANON_FILE="$OUTDIR/RDF_Canonical.ml"
if [[ -f "$CANON_FILE" ]]; then
  echo "  Patching $CANON_FILE (hash_sha256 stub)..."
  python3 -c "
import sys
with open('$CANON_FILE', 'r') as f:
    content = f.read()
form_a_old = '''let hash_sha256 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: RDF.Canonical.hash_sha256\"'''
form_a_new = '''let hash_sha256 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha256 s'''
form_b_old = '''let (hash_sha256 : Prims.string -> Prims.string) =
  fun uu___ -> failwith \"Not yet implemented: RDF.Canonical.hash_sha256\"'''
form_b_new = '''let (hash_sha256 : Prims.string -> Prims.string) =
  fun s -> Fstar_pure_hashes.sha256 s'''
matched = (form_a_old in content) or (form_b_old in content)
already_patched = ('Fstar_pure_hashes.sha256 s' in content)
content = content.replace(form_a_old, form_a_new)
content = content.replace(form_b_old, form_b_new)
if not matched and not already_patched:
    sys.stderr.write('  ERROR: RDF_Canonical.ml hash_sha256 stub matched neither form A nor form B.\n')
    sys.stderr.write('  RDFC-1.0 will fail every blank-node test (canonicalize raises failwith).\n')
    sys.stderr.write('  Inspect $CANON_FILE around line 1-3 and update 63_regex_hash_uuid_stubs.sh.\n')
    sys.exit(2)
with open('$CANON_FILE', 'w') as f:
    f.write(content)
"
  echo "  RDF_Canonical hash_sha256 wired to Fstar_pure_hashes.sha256."

  # 2026-07-05: RDFC-1.0 rdfc:hashAlgorithm "SHA384" manifest variant
  # (test075c/test075m) needs a second hash primitive alongside
  # hash_sha256 above. Same assume-val shape, same two extraction
  # forms, same glue patch (issue #63) rather than a new hole per
  # CLAUDE.md rule #3.
  echo "  Patching $CANON_FILE (hash_sha384 stub)..."
  python3 -c "
import sys
with open('$CANON_FILE', 'r') as f:
    content = f.read()
form_a_old = '''let hash_sha384 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: RDF.Canonical.hash_sha384\"'''
form_a_new = '''let hash_sha384 (s : Prims.string) : Prims.string=
  Fstar_pure_hashes.sha384 s'''
form_b_old = '''let (hash_sha384 : Prims.string -> Prims.string) =
  fun uu___ -> failwith \"Not yet implemented: RDF.Canonical.hash_sha384\"'''
form_b_new = '''let (hash_sha384 : Prims.string -> Prims.string) =
  fun s -> Fstar_pure_hashes.sha384 s'''
matched = (form_a_old in content) or (form_b_old in content)
already_patched = ('Fstar_pure_hashes.sha384 s' in content)
content = content.replace(form_a_old, form_a_new)
content = content.replace(form_b_old, form_b_new)
if not matched and not already_patched:
    sys.stderr.write('  ERROR: RDF_Canonical.ml hash_sha384 stub matched neither form A nor form B.\n')
    sys.stderr.write('  RDFC-1.0 SHA-384 manifest tests (test075c/075m) will fail (failwith).\n')
    sys.stderr.write('  Inspect $CANON_FILE and update 63_regex_hash_uuid_stubs.sh.\n')
    sys.exit(2)
with open('$CANON_FILE', 'w') as f:
    f.write(content)
"
  echo "  RDF_Canonical hash_sha384 wired to Fstar_pure_hashes.sha384."
fi
