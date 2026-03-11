#!/bin/bash
# Issue #64: SPARQL parser escape processing stubs for SPARQL11_Parser.ml
# https://github.com/danbri/factoidal/issues/64
#
# Replaces F*-extracted failwith stubs for:
#   - utf8_of_codepoint: converts Unicode codepoint to UTF-8 string
#   - process_iri_escapes: processes \u and \U escapes in IRI strings
#   - process_string_escapes: processes string escape sequences (\t, \n, \r, etc.)
#     with surrogate codepoint validation

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

FILE="$OUTDIR/SPARQL11_Parser.ml"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (escape processing stubs)..."

if ! grep -q 'let utf8_of_codepoint (cp_z : Prims.nat)' "$FILE"; then
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Replace utf8_of_codepoint stub
content = content.replace(
    'let utf8_of_codepoint (uu___ : Prims.nat) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.utf8_of_codepoint"',
    '''let utf8_of_codepoint (cp_z : Prims.nat) : Prims.string =
  let cp = Z.to_int cp_z in
  let open Stdlib in
  if cp < 0x80 then String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 2 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.to_string s
  else if cp < 0x10000 then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 3 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1); Bytes.set s 2 (Char.chr b2);
    Bytes.to_string s
  else
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 4 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.set s 2 (Char.chr b2); Bytes.set s 3 (Char.chr b3);
    Bytes.to_string s'''
)

# 2. Replace process_iri_escapes stub
content = content.replace(
    'let process_iri_escapes (uu___ : Prims.string) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.process_iri_escapes"',
    '''let process_iri_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process backslash-u and backslash-U escapes in IRI strings *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\\\' then begin
      let next = s.[!i + 1] in
      if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf'''
)

# 3. Replace process_string_escapes stub
content = content.replace(
    'let process_string_escapes (uu___ : Prims.string) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.process_string_escapes"',
    '''let process_string_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process string escape sequences: backslash-t, -n, -r, etc. *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\\\' then begin
      let next = s.[!i + 1] in
      if next = 't' then (Buffer.add_char buf '\\t'; i := !i + 2)
      else if next = 'n' then (Buffer.add_char buf '\\n'; i := !i + 2)
      else if next = 'r' then (Buffer.add_char buf '\\r'; i := !i + 2)
      else if next = '\\\\' then (Buffer.add_char buf '\\\\'; i := !i + 2)
      else if next = '"' then (Buffer.add_char buf '"'; i := !i + 2)
      else if next = '\\'' then (Buffer.add_char buf '\\''; i := !i + 2)
      else if next = 'b' then (Buffer.add_char buf '\\008'; i := !i + 2)
      else if next = 'f' then (Buffer.add_char buf '\\012'; i := !i + 2)
      else if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
fi

echo "  SPARQL parser escape stubs patched."
