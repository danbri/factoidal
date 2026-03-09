(* Stubs for SPARQL11_Parser.ml assume vals.
   These provide OCaml implementations for F*-extracted code that uses assume val
   for low-level string operations and escape processing.

   This file is included at compile time via -open or linked directly. *)

(* UTF-8 encode a Unicode codepoint *)
let utf8_of_codepoint_impl (cp : int) : string =
  if cp < 0x80 then String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let s = Bytes.create 2 in
    Bytes.set s 0 (Char.chr (0xC0 lor (cp lsr 6)));
    Bytes.set s 1 (Char.chr (0x80 lor (cp land 0x3F)));
    Bytes.to_string s
  else if cp < 0x10000 then
    let s = Bytes.create 3 in
    Bytes.set s 0 (Char.chr (0xE0 lor (cp lsr 12)));
    Bytes.set s 1 (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Bytes.set s 2 (Char.chr (0x80 lor (cp land 0x3F)));
    Bytes.to_string s
  else
    let s = Bytes.create 4 in
    Bytes.set s 0 (Char.chr (0xF0 lor (cp lsr 18)));
    Bytes.set s 1 (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Bytes.set s 2 (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Bytes.set s 3 (Char.chr (0x80 lor (cp land 0x3F)));
    Bytes.to_string s

(* Process escape sequences in an IRI string *)
let process_iri_escapes_impl (s : string) : string =
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if s.[!i] = '\\' && !i + 1 < len then begin
      let e = s.[!i + 1] in
      if e = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (utf8_of_codepoint_impl cp);
        i := !i + 6
      end else if e = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        let cp = int_of_string ("0x" ^ hex) in
        Buffer.add_string buf (utf8_of_codepoint_impl cp);
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
  Buffer.contents buf

(* Process escape sequences in a string literal *)
let process_string_escapes_impl (s : string) : string =
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if s.[!i] = '\\' && !i + 1 < len then begin
      let e = s.[!i + 1] in
      (match e with
       | 't' -> Buffer.add_char buf '\t'; i := !i + 2
       | 'n' -> Buffer.add_char buf '\n'; i := !i + 2
       | 'r' -> Buffer.add_char buf '\r'; i := !i + 2
       | 'b' -> Buffer.add_char buf '\b'; i := !i + 2
       | 'f' -> Buffer.add_char buf (Char.chr 0x0C); i := !i + 2
       | '"' -> Buffer.add_char buf '"'; i := !i + 2
       | '\'' -> Buffer.add_char buf '\''; i := !i + 2
       | '\\' -> Buffer.add_char buf '\\'; i := !i + 2
       | 'u' when !i + 5 < len ->
         let hex = String.sub s (!i + 2) 4 in
         let cp = int_of_string ("0x" ^ hex) in
         Buffer.add_string buf (utf8_of_codepoint_impl cp);
         i := !i + 6
       | 'U' when !i + 9 < len ->
         let hex = String.sub s (!i + 2) 8 in
         let cp = int_of_string ("0x" ^ hex) in
         Buffer.add_string buf (utf8_of_codepoint_impl cp);
         i := !i + 10
       | _ -> Buffer.add_char buf '\\'; Buffer.add_char buf e; i := !i + 2)
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf
