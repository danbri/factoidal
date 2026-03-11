#!/bin/bash
# Issue #63: Regex, hash, and UUID assume val stubs for SPARQL11_Algebra.ml
# https://github.com/danbri/factoidal/issues/63
#
# Replaces F*-extracted failwith stubs for:
#   - regex_match (SPARQL REGEX) with OCaml Str implementation + XPath regex conversion
#   - regex_replace (SPARQL REPLACE) with forward ref + OCaml Str implementation
#   - hash_md5, hash_sha1, hash_sha256, hash_sha384, hash_sha512
#   - UUID/STRUUID generation (random UUID v4 instead of all-zeros placeholder)
#
# Also wires regex_replace_ref after xpath_to_str_regex is defined.

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

echo "  Patching $FILE (regex/hash/UUID stubs)..."

# All patches are applied in a single python3 pass for atomicity
if ! grep -q 'xpath_to_str_regex' "$FILE"; then
  python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# 1. Replace regex_match stub with OCaml Str implementation
# Includes XPath/Perl regex -> OCaml Str regex conversion (handles {n}, (), |, etc.)
content = content.replace(
    '''let regex_match (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  failwith \"Not yet implemented: SPARQL11.Algebra.regex_match\"''',
    '''let xpath_to_str_regex (p : string) : string =
  let open Stdlib in
  let len = String.length p in
  let buf = Buffer.create (len * 2) in
  let i = ref 0 in
  let last_atom = ref \"\" in
  let set_atom s = last_atom := s; Buffer.add_string buf s in
  while !i < len do
    let c = p.[!i] in
    if c = '\\\\\\\\' && !i + 1 < len then begin
      let next = p.[!i + 1] in
      if next = '(' || next = ')' || next = '|' || next = '?' ||
         next = '{' || next = '}' || next = '+' || next = '*' then
        (set_atom (String.make 1 next); i := !i + 2)
      else if next = 'd' then (set_atom \"[0-9]\"; i := !i + 2)
      else if next = 'D' then (set_atom \"[^0-9]\"; i := !i + 2)
      else if next = 'w' then (set_atom \"[a-zA-Z0-9_]\"; i := !i + 2)
      else if next = 'W' then (set_atom \"[^a-zA-Z0-9_]\"; i := !i + 2)
      else if next = 's' then (set_atom \"[ \\\\t\\\\n\\\\r]\"; i := !i + 2)
      else if next = 'S' then (set_atom \"[^ \\\\t\\\\n\\\\r]\"; i := !i + 2)
      else (let s = String.sub p !i 2 in set_atom s; i := !i + 2)
    end else if c = '(' then
      (Buffer.add_string buf \"\\\\(\"; last_atom := \"\"; i := !i + 1)
    else if c = ')' then
      (Buffer.add_string buf \"\\\\)\"; last_atom := \"\\\\)\"; i := !i + 1)
    else if c = '|' then
      (Buffer.add_string buf \"\\\\|\"; last_atom := \"\"; i := !i + 1)
    else if c = '?' then
      (Buffer.add_string buf \"\\\\?\"; i := !i + 1)
    else if c = '{' then begin
      i := !i + 1;
      let nb = Buffer.create 8 in
      while !i < len && p.[!i] <> '}' && p.[!i] <> ',' do
        Buffer.add_char nb p.[!i]; i := !i + 1 done;
      let n = try int_of_string (Buffer.contents nb) with _ -> 1 in
      if !i < len && p.[!i] = ',' then begin
        i := !i + 1;
        let mb = Buffer.create 8 in
        while !i < len && p.[!i] <> '}' do
          Buffer.add_char mb p.[!i]; i := !i + 1 done;
        if !i < len then i := !i + 1;
        let ms = Buffer.contents mb in
        if ms = \"\" then begin
          for _ = 2 to n do Buffer.add_string buf !last_atom done;
          Buffer.add_string buf !last_atom; Buffer.add_char buf '*'
        end else begin
          let m = try int_of_string ms with _ -> n in
          for _ = 2 to n do Buffer.add_string buf !last_atom done;
          for _ = n + 1 to m do
            Buffer.add_string buf !last_atom;
            Buffer.add_string buf \"\\\\?\" done
        end
      end else begin
        if !i < len then i := !i + 1;
        for _ = 2 to n do Buffer.add_string buf !last_atom done
      end
    end else if c = '[' then begin
      let start = !i in
      i := !i + 1;
      if !i < len && p.[!i] = '^' then i := !i + 1;
      if !i < len && p.[!i] = ']' then i := !i + 1;
      while !i < len && p.[!i] <> ']' do i := !i + 1 done;
      if !i < len then i := !i + 1;
      let cls = String.sub p start (!i - start) in
      set_atom cls
    end else (set_atom (String.make 1 c); i := !i + 1)
  done;
  Buffer.contents buf
let regex_match (text : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let converted = xpath_to_str_regex pattern in
    let re = if case_insensitive
      then Str.regexp_case_fold converted
      else Str.regexp converted in
    (try let _ = Str.search_forward re text 0 in true
     with Not_found -> false)
  with _ -> false'''
)

# 2. Replace regex_replace stub with forward ref
content = content.replace(
    '''let regex_replace (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string)
  (uu___3 : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.regex_replace\"''',
    '''let regex_replace_ref : (Prims.string -> Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option -> Prims.string) ref =
  ref (fun t _ _ _ -> t)
let regex_replace (text : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  !regex_replace_ref text pattern replacement flags'''
)

# 3. Replace hash function stubs with OCaml Digest implementations
content = content.replace(
    '''let hash_md5 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_md5\"''',
    '''let hash_md5 (s : Prims.string) : Prims.string=
  Digest.to_hex (Digest.string s)'''
)
content = content.replace(
    '''let hash_sha1 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha1\"''',
    '''let hash_sha1 (s : Prims.string) : Prims.string=
  Sha1.to_hex (Sha1.string s)'''
)
content = content.replace(
    '''let hash_sha256 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha256\"''',
    '''let hash_sha256 (s : Prims.string) : Prims.string=
  Sha256.to_hex (Sha256.string s)'''
)
content = content.replace(
    '''let hash_sha384 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha384\"''',
    '''let hash_sha384 (s : Prims.string) : Prims.string=
  Digestif.SHA384.(to_hex (digest_string s))'''
)
content = content.replace(
    '''let hash_sha512 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha512\"''',
    '''let hash_sha512 (s : Prims.string) : Prims.string=
  Sha512.to_hex (Sha512.string s)'''
)

# 4. Replace UUID/STRUUID hardcoded stubs with random UUID v4 generation
content = content.replace(
    '''          if iri_s = \"http://www.w3.org/2005/xpath-functions#uuid\"
          then
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 \"urn:uuid:00000000-0000-0000-0000-000000000000\")
          else
            if iri_s = \"http://www.w3.org/2005/xpath-functions#struuid\"
            then er_string \"00000000-0000-0000-0000-000000000000\"''',
    '''          if iri_s = \"http://www.w3.org/2005/xpath-functions#uuid\"
          then
            let () = Random.self_init () in
            let hex () = Printf.sprintf \"%04x\" (Random.int 0x10000) in
            let s = Printf.sprintf \"%s%s-%s-%s-%s-%s%s%s\"
              (hex ()) (hex ()) (hex ())
              (Printf.sprintf \"4%03x\" (Random.int 0x1000))
              (Printf.sprintf \"%04x\" (0x8000 lor (Random.int 0x4000)))
              (hex ()) (hex ()) (hex ()) in
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 (Prims.strcat \"urn:uuid:\" s))
          else
            if iri_s = \"http://www.w3.org/2005/xpath-functions#struuid\"
            then
              let () = Random.self_init () in
              let hex () = Printf.sprintf \"%04x\" (Random.int 0x10000) in
              let s = Printf.sprintf \"%s%s-%s-%s-%s-%s%s%s\"
                (hex ()) (hex ()) (hex ())
                (Printf.sprintf \"4%03x\" (Random.int 0x1000))
                (Printf.sprintf \"%04x\" (0x8000 lor (Random.int 0x4000)))
                (hex ()) (hex ()) (hex ()) in
              er_string s'''
)

# 5. Wire regex_replace_ref after xpath_to_str_regex is defined
# (xpath_to_str_regex is defined inside the regex_match patch)
# This replaces the wiring block that issue #62 inserts for eval_expr refs
# by appending regex_replace_ref wiring after those lines.
content = content.replace(
    '''let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)''',
    '''let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)
let () = regex_replace_ref := (fun text pattern replacement flags ->
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let converted = xpath_to_str_regex pattern in
    let re = if case_insensitive
      then Str.regexp_case_fold converted
      else Str.regexp converted in
    (* Manual global replace that handles unmatched groups gracefully.
       OCaml Str.matched_group raises Not_found for unmatched groups;
       we replace them with empty string per XPath/SPARQL semantics. *)
    let open Stdlib in
    let build_replacement matched_text =
      let len = String.length replacement in
      let buf = Buffer.create len in
      let i = ref 0 in
      while !i < len do
        if replacement.[!i] = '$' && !i + 1 < len &&
           replacement.[!i + 1] >= '0' && replacement.[!i + 1] <= '9' then begin
          let group_n = Char.code replacement.[!i + 1] - Char.code '0' in
          (try Buffer.add_string buf (Str.matched_group group_n matched_text)
           with Not_found -> ());
          i := !i + 2
        end else begin
          Buffer.add_char buf replacement.[!i];
          i := !i + 1
        end
      done;
      Buffer.contents buf
    in
    let result = Buffer.create (String.length text) in
    let pos = ref 0 in
    (try
      while true do
        ignore (Str.search_forward re text !pos);
        let m_start = Str.match_beginning () in
        let m_end = Str.match_end () in
        Buffer.add_string result (String.sub text !pos (m_start - !pos));
        Buffer.add_string result (build_replacement text);
        pos := m_end;
        if m_start = m_end then begin
          if !pos < String.length text then begin
            Buffer.add_char result text.[!pos];
            pos := !pos + 1
          end else raise Not_found
        end
      done
    with Not_found -> ());
    Buffer.add_string result (String.sub text !pos (String.length text - !pos));
    Buffer.contents result
  with _ -> text)'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"
fi

echo "  Regex/hash/UUID stubs patched."
