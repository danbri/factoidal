#!/bin/bash
# Issue #NNN (TBD -- open-issue number not yet filed; see this patch's
# landing PR/report): realise the five durable-UPDATE delta-log I/O
# assume vals (rule-#11(a) pure-I/O realisations) in
# RDF.Store.Columnar.DeltaLog.fst §3.3 / stage 2 of
# docs/designissues/2026-07-06-durable-update-design.md.
#
#   delta_log_append   : path -> bytes -> ML unit    (O_APPEND write)
#   delta_log_fsync    : path -> ML unit             (Unix.fsync)
#   delta_log_read_all : path -> ML bytes            (whole-file read)
#   atomic_rename      : from_path -> to_path -> ML unit  (Unix.rename)
#   fsync_dir          : path -> ML unit             (fsync the dir fd,
#                                                      durability of a
#                                                      rename per §3.3
#                                                      step 5)
#
# No branching on delta_batch/delta_entry CONTENTS anywhere below --
# every function is "write these bytes" / "sync this fd" / "rename
# this path" / "read this whole file". The *decision* of what bytes
# to write (serialize_log / serialize_delta_batch / serialize_log_header)
# is F*, Tot, in RDF.Store.Columnar.DeltaLog.fst itself; this patch is
# the OCaml side of rule #11(a)'s I/O boundary only.
#
# Byte marshalling: RDF_Bytes.bytes (a `char list`) <-> OCaml `string`
# via the ALREADY-extracted RDF_Bytes.bytes_to_string / bytes_of_string
# -- no new byte-layout logic here, per rule #11's "companion-file
# byte assembly belongs in F*" line.

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

FILE="$OUTDIR/RDF_Store_Columnar_DeltaLog.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 282_delta_log_io patch." >&2
  echo "         (F* extract may not have produced RDF.Store.Columnar.DeltaLog yet.)" >&2
  exit 0
fi

# Idempotency: marker is the Unix.openfile call that distinguishes the
# realised version from the failwith stubs.
if grep -q '__delta_log_io_realised' "$FILE"; then
  echo "  [282_delta_log_io] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (delta_log_append/_fsync/_read_all, atomic_rename, fsync_dir)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

marker = "(* __delta_log_io_realised (issue #NNN) *)\n"

old_append = (
    'let delta_log_append (path : Prims.string) (bytes : RDF_Bytes.bytes) : \n'
    '  unit=\n'
    '  failwith\n'
    '    "Not yet implemented: RDF.Store.Columnar.DeltaLog.delta_log_append"'
)
new_append = (
    marker +
    '(* rule #11(a) pure-I/O realisation. O_APPEND writes below the\n'
    '   filesystem block size are atomic per POSIX -- a crash mid-append\n'
    '   leaves a torn TAIL entry, never corrupts already-committed bytes\n'
    '   earlier in the file (design doc §3.3 step 2). The caller (the\n'
    '   commit sequence, or the crash-harness driver deliberately\n'
    '   slicing one batch into several small appends to widen a kill\n'
    '   window) decides how many times to call this per batch; each\n'
    '   call is independently a plain append. *)\n'
    'let delta_log_append (path : Prims.string) (bytes : RDF_Bytes.bytes) :\n'
    '  unit=\n'
    '  let s = RDF_Bytes.bytes_to_string bytes in\n'
    '  let fd =\n'
    '    Unix.openfile path [Unix.O_APPEND; Unix.O_CREAT; Unix.O_WRONLY] 0o644 in\n'
    '  Fun.protect ~finally:(fun () -> Unix.close fd)\n'
    '    (fun () ->\n'
    '       (* this file has a top-level `open Prims` (F* extraction\n'
    '          convention) that shadows `(<)`/`(+)`/`(-)` to operate over\n'
    '          Prims.int = Z.t; qualify with plain OCaml Stdlib for the\n'
    '          native-int write-loop bookkeeping, same pattern as\n'
    '          experimental_ocaml_glue/parquet_footer_runtime.sh. *)\n'
    '       let module S = Stdlib in\n'
    '       let n = String.length s in\n'
    '       let written = ref 0 in\n'
    '       while S.(!written < n) do\n'
    '         let k = Unix.write_substring fd s !written S.(n - !written) in\n'
    '         written := S.(!written + k)\n'
    '       done)'
)

old_fsync = (
    'let delta_log_fsync (path : Prims.string) : unit=\n'
    '  failwith "Not yet implemented: RDF.Store.Columnar.DeltaLog.delta_log_fsync"'
)
new_fsync = (
    '(* rule #11(a): the commit point (design doc §3.3 step 3) -- before\n'
    '   this returns, nothing appended since the last fsync is durable.\n'
    '   Reopen read-write (not O_APPEND -- fsync just needs a valid fd on\n'
    '   the path, it does not write) since delta_log_append already\n'
    '   closed its own fd. *)\n'
    'let delta_log_fsync (path : Prims.string) : unit=\n'
    '  let fd = Unix.openfile path [Unix.O_WRONLY] 0o644 in\n'
    '  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> Unix.fsync fd)'
)

old_read = (
    'let delta_log_read_all (path : Prims.string) : RDF_Bytes.bytes=\n'
    '  failwith\n'
    '    "Not yet implemented: RDF.Store.Columnar.DeltaLog.delta_log_read_all"'
)
new_read = (
    '(* rule #11(a): whole-file read, no interpretation -- parse_log\n'
    '   (F*, Tot) decides what the bytes mean, including tolerating a\n'
    '   torn tail batch (design doc §3.3\'s crash-recovery replay). *)\n'
    'let delta_log_read_all (path : Prims.string) : RDF_Bytes.bytes=\n'
    '  let fd = Unix.openfile path [Unix.O_RDONLY] 0o644 in\n'
    '  Fun.protect ~finally:(fun () -> Unix.close fd)\n'
    '    (fun () ->\n'
    '       (* see delta_log_append -- same open-Prims arithmetic-shadow\n'
    '          trap, same Stdlib qualification fix. *)\n'
    '       let module S = Stdlib in\n'
    '       let len = (Unix.fstat fd).Unix.st_size in\n'
    '       let buf = Bytes.create len in\n'
    '       let read_total = ref 0 in\n'
    '       while S.(!read_total < len) do\n'
    '         let k = Unix.read fd buf !read_total S.(len - !read_total) in\n'
    '         if k = 0 then read_total := len (* EOF: file shrank under us *)\n'
    '         else read_total := S.(!read_total + k)\n'
    '       done;\n'
    '       RDF_Bytes.bytes_of_string (Bytes.sub_string buf 0 !read_total))'
)

old_rename = (
    'let atomic_rename (from_path : Prims.string) (to_path : Prims.string) : \n'
    '  unit=\n'
    '  failwith "Not yet implemented: RDF.Store.Columnar.DeltaLog.atomic_rename"'
)
new_rename = (
    '(* rule #11(a): POSIX rename(2) within one directory is atomic --\n'
    '   design doc §3.3 step 5\'s base-file swap relies on exactly this\n'
    '   property. Callers still owe a subsequent fsync_dir for the\n'
    '   rename itself to be durable across a crash. *)\n'
    'let atomic_rename (from_path : Prims.string) (to_path : Prims.string) :\n'
    '  unit=\n'
    '  Unix.rename from_path to_path'
)

old_fsyncdir = (
    'let fsync_dir (path : Prims.string) : unit=\n'
    '  failwith "Not yet implemented: RDF.Store.Columnar.DeltaLog.fsync_dir"'
)
new_fsyncdir = (
    '(* rule #11(a): a directory can be opened read-only and fsynced on\n'
    '   POSIX (Linux, most *BSDs) to force its entry-table changes\n'
    '   (a rename\'s new/removed name) to durable storage -- design doc\n'
    '   §3.3 step 5\'s "every WAL implementation gets bitten by if\n'
    '   skipped" detail. *)\n'
    'let fsync_dir (path : Prims.string) : unit=\n'
    '  let fd = Unix.openfile path [Unix.O_RDONLY] 0o644 in\n'
    '  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> Unix.fsync fd)'
)

replacements = [
    ("delta_log_append", old_append, new_append),
    ("delta_log_fsync", old_fsync, new_fsync),
    ("delta_log_read_all", old_read, new_read),
    ("atomic_rename", old_rename, new_rename),
    ("fsync_dir", old_fsyncdir, new_fsyncdir),
]

missing = []
for name, old, new in replacements:
    if old in content:
        content = content.replace(old, new, 1)
    elif new in content or f"__delta_log_io_realised" in content:
        pass  # already patched, e.g. re-run without a full re-extract
    else:
        missing.append(name)

if missing:
    sys.stderr.write(
        "  ERROR: 282_delta_log_io could not find the failwith stub(s) for: "
        + ", ".join(missing)
        + f"\n         in {path}\n         Has the extraction shape changed?\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [282_delta_log_io] applied: delta_log_append/_fsync/_read_all -> Unix I/O, atomic_rename -> Unix.rename, fsync_dir -> Unix.fsync"
