module Parser.Combinators

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString

// Issue #70: on the hot path, FStar.String.length / index / sub route
// through BatUTF8 and cost O(n) per call. We swap to the byte-indexed
// fs_byte_length / fs_byte_index / fs_byte_sub primitives here, which
// are O(1) / O(1) / O(len). See Parser.FastString.fst for the safety
// argument (byte semantics are correct for N-Triples, Turtle, N-Quads,
// TriG; any parser that needs codepoint semantics should not use these
// combinators on that code path).

(** Parse result: either success with value and new position, or failure *)
type parse_result (a:Type) =
  | ParseOk : value:a -> pos:nat -> parse_result a
  | ParseFail : msg:string -> pos:nat -> parse_result a

(** A parser takes an input string and a position, returns a parse_result *)
type parser (a:Type) = string -> nat -> parse_result a


(* ================================================================ *)
(* Basic parsers                                                     *)
(* ================================================================ *)

(** Always succeed with a value, consuming no input *)
let preturn (#a:Type) (v:a) : parser a =
  fun _input pos -> ParseOk v pos

(** Always fail with a message *)
let pfail (#a:Type) (msg:string) : parser a =
  fun _input pos -> ParseFail msg pos

(** Match a single specific character *)
let pchar (c:char) : parser char =
  fun input pos ->
    let len = fs_byte_length input in
    if pos < len then
      let ch = fs_byte_index input pos in
      if ch = c then ParseOk ch (pos + 1)
      else ParseFail (String.concat "" ["expected '"; String.string_of_char c; "'"]) pos
    else ParseFail "unexpected end of input" pos

(** Match a character satisfying a predicate *)
let psat (pred: char -> bool) : parser char =
  fun input pos ->
    let len = fs_byte_length input in
    if pos < len then
      let ch = fs_byte_index input pos in
      if pred ch then ParseOk ch (pos + 1)
      else ParseFail "character did not satisfy predicate" pos
    else ParseFail "unexpected end of input" pos

(** Match any single character *)
let pany : parser char =
  fun input pos ->
    let len = fs_byte_length input in
    if pos < len then
      let ch = fs_byte_index input pos in
      ParseOk ch (pos + 1)
    else ParseFail "unexpected end of input" pos

(** Match end of input *)
let peof : parser unit =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseOk () pos
    else ParseFail "expected end of input" pos

(** Match an exact string *)
let pstring (s:string) : parser string =
  fun input pos ->
    let slen = fs_byte_length s in
    let ilen = fs_byte_length input in
    if pos + slen <= ilen then
      let sub_str = fs_byte_sub input pos slen in
      if sub_str = s then ParseOk s (pos + slen)
      else ParseFail (String.concat "" ["expected \""; s; "\""]) pos
    else ParseFail (String.concat "" ["expected \""; s; "\""]) pos


(* ================================================================ *)
(* Combinators                                                       *)
(* ================================================================ *)

(** Monadic bind: run first parser, feed result to second *)
let pbind (#a #b:Type) (p: parser a) (f: a -> parser b) : parser b =
  fun input pos ->
    match p input pos with
    | ParseOk v pos' -> f v input pos'
    | ParseFail msg pos' -> ParseFail msg pos'

(** Functor map: transform the result of a parser *)
let pmap (#a #b:Type) (f: a -> b) (p: parser a) : parser b =
  fun input pos ->
    match p input pos with
    | ParseOk v pos' -> ParseOk (f v) pos'
    | ParseFail msg pos' -> ParseFail msg pos'

(** Alternative: try first parser, on failure try second (at original position) *)
let palt (#a:Type) (p1: parser a) (p2: parser a) : parser a =
  fun input pos ->
    match p1 input pos with
    | ParseOk v pos' -> ParseOk v pos'
    | ParseFail _ _ -> p2 input pos

(** Optional: try parser, return None on failure *)
let popt (#a:Type) (p: parser a) : parser (option a) =
  fun input pos ->
    match p input pos with
    | ParseOk v pos' -> ParseOk (Some v) pos'
    | ParseFail _ _ -> ParseOk None pos


(* ================================================================ *)
(* Recursive combinators (fuel-based for termination)                *)
(* ================================================================ *)

(** Internal: zero or more with explicit fuel for termination *)
let rec pmany_fuel (#a:Type) (p: parser a) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list a)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    match p input pos with
    | ParseOk v pos' ->
      if pos' = pos then
        (* Parser succeeded but didn't advance -- stop to avoid infinite loop *)
        ParseOk [v] pos'
      else
        begin match pmany_fuel p input pos' (fuel - 1) with
        | ParseOk vs pos'' -> ParseOk (v :: vs) pos''
        | ParseFail msg fpos -> ParseFail msg fpos
        end
    | ParseFail _ _ -> ParseOk [] pos

(** Zero or more: parse repeatedly until failure *)
let pmany (#a:Type) (p: parser a) (input:string) (pos:nat)
  : parse_result (list a) =
  let fuel = fs_byte_length input - pos + 1 in
  if fuel >= 0 then pmany_fuel p input pos fuel
  else ParseOk [] pos

(** One or more: parse at least one, then zero or more *)
let pmany1_from (#a:Type) (p: parser a) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list a)) (decreases fuel) =
  match p input pos with
  | ParseOk v pos' ->
    if pos' = pos then ParseOk [v] pos'
    else
      begin match pmany_fuel p input pos' fuel with
      | ParseOk vs pos'' -> ParseOk (v :: vs) pos''
      | ParseFail msg fpos -> ParseFail msg fpos
      end
  | ParseFail msg fpos -> ParseFail msg fpos

let pmany1 (#a:Type) (p: parser a) (input:string) (pos:nat)
  : parse_result (list a) =
  let fuel = fs_byte_length input - pos + 1 in
  if fuel >= 0 then pmany1_from p input pos fuel
  else ParseFail "unexpected end of input" pos

(** Skip zero or more: like pmany but discards results *)
let rec pskip_many_from (#a:Type) (p: parser a) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseOk () pos
  else
    match p input pos with
    | ParseOk _ pos' ->
      if pos' = pos then ParseOk () pos'
      else pskip_many_from p input pos' (fuel - 1)
    | ParseFail _ _ -> ParseOk () pos

let pskip_many (#a:Type) (p: parser a) (input:string) (pos:nat)
  : parse_result unit =
  let fuel = fs_byte_length input - pos + 1 in
  if fuel >= 0 then pskip_many_from p input pos fuel
  else ParseOk () pos

(** Separated list: parse items separated by a delimiter *)
let rec psep_by_rest (#a #b:Type) (p: parser a) (sep: parser b) (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list a)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    match sep input pos with
    | ParseOk _ pos' ->
      begin match p input pos' with
      | ParseOk v pos'' ->
        if pos'' = pos then ParseOk [v] pos''
        else
          begin match psep_by_rest p sep input pos'' (fuel - 1) with
          | ParseOk vs pos''' -> ParseOk (v :: vs) pos'''
          | ParseFail msg fpos -> ParseFail msg fpos
          end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail _ _ -> ParseOk [] pos

let psep_by (#a #b:Type) (p: parser a) (sep: parser b) (input:string) (pos:nat)
  : parse_result (list a) =
  let fuel = fs_byte_length input - pos + 1 in
  match p input pos with
  | ParseOk v pos' ->
    if fuel >= 0 then
      begin match psep_by_rest p sep input pos' fuel with
      | ParseOk vs pos'' -> ParseOk (v :: vs) pos''
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    else ParseOk [v] pos'
  | ParseFail _ _ -> ParseOk [] pos


(* ================================================================ *)
(* Character class parsers                                           *)
(* ================================================================ *)

(** Match a digit [0-9] *)
let pdigit : parser char =
  psat (fun c ->
    let code = Char.int_of_char c in
    code >= 0x30 && code <= 0x39)

(** Match a whitespace character (space, tab, newline, carriage return) *)
let pspace : parser char =
  psat (fun c ->
    let code = Char.int_of_char c in
    code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D)

(** Match an alphabetic character [a-zA-Z] *)
let palpha : parser char =
  psat (fun c ->
    let code = Char.int_of_char c in
    (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A))

(** Match a hexadecimal digit [0-9a-fA-F] *)
let phex : parser char =
  psat (fun c ->
    let code = Char.int_of_char c in
    (code >= 0x30 && code <= 0x39) ||
    (code >= 0x41 && code <= 0x46) ||
    (code >= 0x61 && code <= 0x66))


(* ================================================================ *)
(* String-building parsers                                           *)
(* ================================================================ *)

(** Take characters while predicate holds, return as string *)
let rec ptake_while_acc (pred: char -> bool) (input:string) (pos:nat) (acc: list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseOk (String.string_of_list (List.Tot.rev acc)) pos
  else
    let len = fs_byte_length input in
    if pos < len then
      let ch = fs_byte_index input pos in
      if pred ch then ptake_while_acc pred input (pos + 1) (ch :: acc) (fuel - 1)
      else ParseOk (String.string_of_list (List.Tot.rev acc)) pos
    else ParseOk (String.string_of_list (List.Tot.rev acc)) pos

let ptake_while (pred: char -> bool) (input:string) (pos:nat)
  : parse_result string =
  let fuel = fs_byte_length input - pos + 1 in
  if fuel >= 0 then ptake_while_acc pred input pos [] fuel
  else ParseOk "" pos

// Position-scan version: find the end position, then extract substring in one shot.
// Avoids building a char list and reversing it. O(n) predicate calls, O(1) substring.
let rec ptake_while_scan (pred: char -> bool) (input:string) (pos:nat) (fuel:nat)
  : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else if pos < fs_byte_length input then
    let ch = fs_byte_index input pos in
    if pred ch then ptake_while_scan pred input (pos + 1) (fuel - 1)
    else pos
  else pos

let ptake_while_pos (pred: char -> bool) (input:string) (pos:nat)
  : parse_result string =
  let len = fs_byte_length input in
  if pos > len then ParseOk "" pos
  else
    let fuel : nat = len - pos + 1 in
    let end_pos = ptake_while_scan pred input pos fuel in
    if end_pos > pos && end_pos <= len then
      ParseOk (fs_byte_sub input pos (end_pos - pos)) end_pos
    else
      ParseOk "" pos

let ptake_while1_pos (pred: char -> bool) (input:string) (pos:nat)
  : parse_result string =
  let len = fs_byte_length input in
  if pos > len then ParseFail "expected at least one matching character" pos
  else
    let fuel : nat = len - pos + 1 in
    let end_pos = ptake_while_scan pred input pos fuel in
    if end_pos > pos && end_pos <= len then
      ParseOk (fs_byte_sub input pos (end_pos - pos)) end_pos
    else
      ParseFail "expected at least one matching character" pos

(** Take 1+ characters while predicate holds *)
let ptake_while1 (pred: char -> bool) (input:string) (pos:nat)
  : parse_result string =
  match ptake_while pred input pos with
  | ParseOk s pos' ->
    if String.length s > 0 then ParseOk s pos'
    else ParseFail "expected at least one matching character" pos
  | ParseFail msg fpos -> ParseFail msg fpos

(** Parse a natural number (sequence of digits) as string *)
let pnatural (input:string) (pos:nat) : parse_result string =
  ptake_while1 (fun c ->
    let code = Char.int_of_char c in
    code >= 0x30 && code <= 0x39) input pos

(** Parse a quoted string with backslash escape handling.
    The quote character delimits the string.
    Backslash escapes the next character. *)
let backslash_char : char = Char.char_of_int 0x5C

let rec pquoted_body (qch: char) (input:string) (pos:nat) (acc: list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated quoted string" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated quoted string" pos
    else
      let ch = fs_byte_index input pos in
      if ch = qch then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if ch = backslash_char then
        if pos + 1 < len then
          let escaped = fs_byte_index input (pos + 1) in
          pquoted_body qch input (pos + 2) (escaped :: ch :: acc) (fuel - 1)
        else ParseFail "backslash at end of input" pos
      else
        pquoted_body qch input (pos + 1) (ch :: acc) (fuel - 1)

let pquoted_string (qch: char) (input:string) (pos:nat)
  : parse_result string =
  let len = fs_byte_length input in
  if pos < len then
    let ch = fs_byte_index input pos in
    if ch = qch then
      let fuel = len - pos in
      pquoted_body qch input (pos + 1) [] fuel
    else ParseFail "expected opening quote" pos
  else ParseFail "unexpected end of input" pos


(* ================================================================ *)
(* Utility combinators                                               *)
(* ================================================================ *)

(** Parse c between opening a and closing b: a c b -> c *)
let pbetween (#a #b #c:Type) (popen: parser a) (pclose: parser b) (p: parser c) : parser c =
  fun input pos ->
    match popen input pos with
    | ParseOk _ pos1 ->
      begin match p input pos1 with
      | ParseOk v pos2 ->
        begin match pclose input pos2 with
        | ParseOk _ pos3 -> ParseOk v pos3
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos

(** Parse a then b, return a's result *)
let pleft (#a #b:Type) (pa: parser a) (pb: parser b) : parser a =
  fun input pos ->
    match pa input pos with
    | ParseOk va pos1 ->
      begin match pb input pos1 with
      | ParseOk _ pos2 -> ParseOk va pos2
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos

(** Parse a then b, return b's result *)
let pright (#a #b:Type) (pa: parser a) (pb: parser b) : parser b =
  fun input pos ->
    match pa input pos with
    | ParseOk _ pos1 -> pb input pos1
    | ParseFail msg fpos -> ParseFail msg fpos

(** Skip all whitespace characters *)
let pskip_whitespace (input:string) (pos:nat) : parse_result unit =
  match ptake_while (fun c ->
    let code = Char.int_of_char c in
    code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D) input pos with
  | ParseOk _ pos' -> ParseOk () pos'
  | ParseFail msg fpos -> ParseFail msg fpos
