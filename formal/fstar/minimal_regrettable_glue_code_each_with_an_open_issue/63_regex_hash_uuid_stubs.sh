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
  python3 - "$FILE" <<'PYEOF'
import re
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# 1. Replace regex_match stub with OCaml Str implementation
# Includes XPath/Perl regex -> OCaml Str regex conversion (handles {n}, (), |, etc.)
content = content.replace(
    '''let regex_match (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  failwith "Not yet implemented: SPARQL11.Algebra.regex_match"''',
    '''let xpath_to_str_regex (p : string) : string =
  let open Stdlib in
  let len = String.length p in
  let buf = Buffer.create (len * 2) in
  let i = ref 0 in
  let last_atom = ref "" in
  let last_atom_start = ref 0 in
  (* NOT annotated `: int list` — this .ml file has a top-level
     `open Prims` (F* extraction convention) that shadows the bare
     `int` type name to `Prims.int = Z.t` (zarith bignum) for the
     rest of the file, so an explicit `int` annotation here would
     silently pin this ref to a bignum list instead of Stdlib's
     native int, conflicting with `Buffer.length buf` (genuinely
     native int) at every push/pop. Leave it unannotated; the first
     push below (`(Buffer.length buf) :: !group_starts`) fixes the
     concrete native-int type from Buffer.length's real signature. *)
  let group_starts = ref [] in
  let set_atom s = last_atom_start := Buffer.length buf; last_atom := s; Buffer.add_string buf s in
  while !i < len do
    let c = p.[!i] in
    if c = '\\\\' && !i + 1 < len then begin
      let next = p.[!i + 1] in
      if next = '(' || next = ')' || next = '|' || next = '{' || next = '}' then
        (set_atom (String.make 1 next); i := !i + 2)
      else if next = '?' then (set_atom "\\?"; i := !i + 2)
      else if next = '+' then (set_atom "\\+"; i := !i + 2)
      else if next = '*' then (set_atom "\\*"; i := !i + 2)
      else if next = 'd' then (set_atom "[0-9]"; i := !i + 2)
      else if next = 'D' then (set_atom "[^0-9]"; i := !i + 2)
      else if next = 'w' then (set_atom "[a-zA-Z0-9_]"; i := !i + 2)
      else if next = 'W' then (set_atom "[^a-zA-Z0-9_]"; i := !i + 2)
      else if next = 's' then (set_atom "[ \\t\\n\\r]"; i := !i + 2)
      else if next = 'S' then (set_atom "[^ \\t\\n\\r]"; i := !i + 2)
      (* Outside-BMP ShEx characterization (#277 comment / follow-up
         issue): literal outside-BMP UTF-8 byte sequences embedded
         directly in a pattern already match correctly (no lead/cont.
         byte collides with an ASCII regex metachar), so no BMP-range
         translation belongs here. The XSD/XPath regex SingleCharEsc
         control escapes \n \r \t DO need translating though: OCaml
         Str has no notion of them (Str.regexp "\\t" matches the
         literal letter 't', not a tab byte), so without this the
         ShExJ "REGEXP_escapes" fixtures (which combine these with an
         astral character, hence their OutsideBMP trait tag) fail on
         the control-char escape, not on the astral byte matching. *)
      else if next = 'n' then (set_atom "\\n"; i := !i + 2)
      else if next = 'r' then (set_atom "\\r"; i := !i + 2)
      else if next = 't' then (set_atom "\\t"; i := !i + 2)
      else (let s = String.sub p !i 2 in set_atom s; i := !i + 2)
    end else if c = '(' then
      (group_starts := (Buffer.length buf) :: !group_starts;
       Buffer.add_string buf "\\("; last_atom := ""; i := !i + 1)
    else if c = ')' then begin
      Buffer.add_string buf "\\)";
      (* #277: capture the FULL group text (not just the closing
         delimiter) so {n,m} repetition of a group re-emits the whole
         group instead of stray close-parens. group_starts is a stack
         (not last_atom_start) because atoms *inside* the group (e.g.
         the 'b' in "(ab)") run through set_atom too and would
         otherwise clobber the group's own start position before we
         get here — nesting-safe via push on '(' / pop on ')'. *)
      (match !group_starts with
       | start :: rest ->
         group_starts := rest;
         last_atom_start := start;
         last_atom := Buffer.sub buf start (Buffer.length buf - start)
       | [] ->
         (* Unmatched ')' in a malformed pattern: no group to close
            over, fall back to the pre-#277 behaviour rather than
            crash on Buffer.sub with a bogus start. *)
         last_atom := "\\)");
      i := !i + 1
    end
    else if c = '|' then
      (Buffer.add_string buf "\\|"; last_atom := ""; i := !i + 1)
    else if c = '?' || c = '+' || c = '*' then
      (Buffer.add_char buf c; i := !i + 1)
    else if c = '{' then begin
      i := !i + 1;
      let nb = Buffer.create 8 in
      while !i < len && p.[!i] <> '}' && p.[!i] <> ',' do
        Buffer.add_char nb p.[!i]; i := !i + 1 done;
      let n = try int_of_string (Buffer.contents nb) with _ -> 1 in
      (* #277: the quantified atom's first occurrence was already
         written to buf unconditionally by the main loop (set_atom /
         the group-close branch) before this {n,m} was even parsed.
         Roll that copy back and rebuild the whole expansion from n
         and m directly, so a parsed minimum of 0 makes every copy
         optional instead of leaving one mandatory copy stuck at the
         front. Behaviourally identical to the old emission for
         n >= 1 (same text produced), and now also correct for n = 0
         and the exact-count {0} case. *)
      Buffer.truncate buf !last_atom_start;
      if !i < len && p.[!i] = ',' then begin
        i := !i + 1;
        let mb = Buffer.create 8 in
        while !i < len && p.[!i] <> '}' do
          Buffer.add_char mb p.[!i]; i := !i + 1 done;
        if !i < len then i := !i + 1;
        let ms = Buffer.contents mb in
        if ms = "" then begin
          (* {n,} unbounded: n mandatory copies + 0-or-more extra *)
          for _ = 1 to n do Buffer.add_string buf !last_atom done;
          Buffer.add_string buf !last_atom; Buffer.add_char buf '*'
        end else begin
          let m = try int_of_string ms with _ -> n in
          (* {n,m} bounded: n mandatory + (m - n) individually optional *)
          for _ = 1 to n do Buffer.add_string buf !last_atom done;
          for _ = n + 1 to m do
            Buffer.add_string buf !last_atom;
            Buffer.add_string buf "?" done
        end
      end else begin
        (* {n} exact: n mandatory copies, none at all when n = 0 *)
        if !i < len then i := !i + 1;
        for _ = 1 to n do Buffer.add_string buf !last_atom done
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
  failwith "Not yet implemented: SPARQL11.Algebra.regex_replace"''',
    '''let regex_replace_ref : (Prims.string -> Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option -> Prims.string) ref =
  ref (fun t _ _ _ -> t)
let regex_replace (text : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  !regex_replace_ref text pattern replacement flags'''
)

# 3. Replace hash function stubs with pure-OCaml implementations.
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

# 4. Replace UUID/STRUUID hardcoded stubs with random UUID v4 generation
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

# 5. Wire regex_replace_ref after xpath_to_str_regex is defined
# (xpath_to_str_regex is defined inside the regex_match patch)
# This replaces the wiring block that issue #62 inserts for eval_expr refs
# by appending regex_replace_ref wiring after those lines.
# #65 Step 2c (2026-05-10): the eval_expr_ebv_ref / eval_expr_fwd_ref
# wiring lines now thread `base` through to eval_expr_with_base. Anchor
# updated; the regex_replace_ref body itself is BASE-independent.
content = content.replace(
    '''let () = eval_expr_ebv_ref := (fun base e mu -> ebv (eval_expr_with_base base e mu))
let () = eval_expr_fwd_ref := (fun base e mu -> eval_expr_with_base base e mu)''',
    '''let () = eval_expr_ebv_ref := (fun base e mu -> ebv (eval_expr_with_base base e mu))
let () = eval_expr_fwd_ref := (fun base e mu -> eval_expr_with_base base e mu)
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
    (* UTF-8 correction: OCaml Str treats the input as bytes. A character
       class like `[^a-z0-9]` will match each byte of a multi-byte codepoint
       separately — e.g. "日" (E6 97 A5) produces three matches instead of one.
       We post-process Str matches so that:
         * a match starting at a UTF-8 continuation byte is skipped
           (it's inside a codepoint the regex couldn't actually match),
         * a single-byte match whose byte is a UTF-8 lead byte is extended
           to cover the whole codepoint.
       SPARQL REPLACE is defined over codepoint strings (XPath regex). *)
    let utf8_cp_len_at s pos =
      if pos >= String.length s then 1
      else
        let c = Char.code s.[pos] in
        if c < 0x80 then 1
        else if c < 0xC0 then 1
        else if c < 0xE0 then 2
        else if c < 0xF0 then 3
        else 4
    in
    let is_utf8_cont s pos =
      pos < String.length s && (Char.code s.[pos] land 0xC0) = 0x80
    in
    let result = Buffer.create (String.length text) in
    let pos = ref 0 in
    (try
      while true do
        ignore (Str.search_forward re text !pos);
        let m_start = Str.match_beginning () in
        let m_end = Str.match_end () in
        if is_utf8_cont text m_start then begin
          Buffer.add_string result (String.sub text !pos (m_start - !pos));
          Buffer.add_char result text.[m_start];
          pos := m_start + 1
        end else begin
          let m_end' =
            if m_end = m_start + 1 then
              let cp_len = utf8_cp_len_at text m_start in
              if cp_len > 1 then m_start + cp_len else m_end
            else m_end
          in
          Buffer.add_string result (String.sub text !pos (m_start - !pos));
          Buffer.add_string result (build_replacement text);
          pos := m_end';
          if m_start = m_end' then begin
            if !pos < String.length text then begin
              let step = utf8_cp_len_at text !pos in
              Buffer.add_string result (String.sub text !pos step);
              pos := !pos + step
            end else raise Not_found
          end
        end
      done
    with Not_found -> ());
    Buffer.add_string result (String.sub text !pos (String.length text - !pos));
    Buffer.contents result
  with _ -> text)'''
)

with open(path, 'w') as f:
    f.write(content)
PYEOF
fi

echo "  Regex/hash/UUID stubs patched."

# Belt-and-suspenders: ensure regex_replace_ref is wired even if the
# guarded python block above was skipped (xpath_to_str_regex already
# present from a prior run, etc.). The wiring depends on 62 having
# added the eval_expr_ebv_ref / eval_expr_fwd_ref lines above; this
# block targets the freshly-emitted shape after #65 Step 2c.
if ! grep -q 'regex_replace_ref :=' "$FILE"; then
  python3 - "$FILE" << 'PYEOF'
import sys
path = sys.argv[1]
with open(path) as f:
    content = f.read()
old = '''let () = eval_expr_ebv_ref := (fun base e mu -> ebv (eval_expr_with_base base e mu))
let () = eval_expr_fwd_ref := (fun base e mu -> eval_expr_with_base base e mu)'''
if old in content:
    new = old + '''
let () = regex_replace_ref := (fun text pattern replacement flags ->
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let converted = xpath_to_str_regex pattern in
    let re = if case_insensitive
      then Str.regexp_case_fold converted
      else Str.regexp converted in
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
    let utf8_cp_len_at s pos =
      if pos >= String.length s then 1
      else
        let c = Char.code s.[pos] in
        if c < 0x80 then 1
        else if c < 0xC0 then 1
        else if c < 0xE0 then 2
        else if c < 0xF0 then 3
        else 4
    in
    let is_utf8_cont s pos =
      pos < String.length s && (Char.code s.[pos] land 0xC0) = 0x80
    in
    let result = Buffer.create (String.length text) in
    let pos = ref 0 in
    (try
      while true do
        ignore (Str.search_forward re text !pos);
        let m_start = Str.match_beginning () in
        let m_end = Str.match_end () in
        if is_utf8_cont text m_start then begin
          Buffer.add_string result (String.sub text !pos (m_start - !pos));
          Buffer.add_char result text.[m_start];
          pos := m_start + 1
        end else begin
          let m_end' =
            if m_end = m_start + 1 then
              let cp_len = utf8_cp_len_at text m_start in
              if cp_len > 1 then m_start + cp_len else m_end
            else m_end
          in
          Buffer.add_string result (String.sub text !pos (m_start - !pos));
          Buffer.add_string result (build_replacement text);
          pos := m_end';
          if m_start = m_end' then begin
            if !pos < String.length text then begin
              let step = utf8_cp_len_at text !pos in
              Buffer.add_string result (String.sub text !pos step);
              pos := !pos + step
            end else raise Not_found
          end
        end
      done
    with Not_found -> ());
    Buffer.add_string result (String.sub text !pos (String.length text - !pos));
    Buffer.contents result
  with _ -> text)'''
    content = content.replace(old, new, 1)
    with open(path, 'w') as f:
        f.write(content)
    print("  regex_replace_ref wiring applied (belt-and-suspenders).")
PYEOF
fi

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
