open Prims
type 'a parse_result =
  | ParseOk of 'a * Prims.nat 
  | ParseFail of Prims.string * Prims.nat 
let uu___is_ParseOk (projectee : 'a parse_result) : Prims.bool=
  match projectee with | ParseOk (value, pos) -> true | uu___ -> false
let __proj__ParseOk__item__value (projectee : 'a parse_result) : 'a=
  match projectee with | ParseOk (value, pos) -> value
let __proj__ParseOk__item__pos (projectee : 'a parse_result) : Prims.nat=
  match projectee with | ParseOk (value, pos) -> pos
let uu___is_ParseFail (projectee : 'a parse_result) : Prims.bool=
  match projectee with | ParseFail (msg, pos) -> true | uu___ -> false
let __proj__ParseFail__item__msg (projectee : 'a parse_result) :
  Prims.string= match projectee with | ParseFail (msg, pos) -> msg
let __proj__ParseFail__item__pos (projectee : 'a parse_result) : Prims.nat=
  match projectee with | ParseFail (msg, pos) -> pos
type 'a parser = Prims.string -> Prims.nat -> 'a parse_result
let preturn (v : 'a) : 'a parser= fun _input pos -> ParseOk (v, pos)
let pfail (msg : Prims.string) : 'a parser=
  fun _input pos -> ParseFail (msg, pos)
let pchar (c : FStar_Char.char) : FStar_Char.char parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos < len
    then
      let ch = Parser_FastString.fs_byte_index input pos in
      (if ch = c
       then ParseOk (ch, (pos + Prims.int_one))
       else
         ParseFail
           ((FStar_String.concat ""
               ["expected '"; FStar_String.string_of_char c; "'"]), pos))
    else ParseFail ("unexpected end of input", pos)
let psat (pred : FStar_Char.char -> Prims.bool) : FStar_Char.char parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos < len
    then
      let ch = Parser_FastString.fs_byte_index input pos in
      (if pred ch
       then ParseOk (ch, (pos + Prims.int_one))
       else ParseFail ("character did not satisfy predicate", pos))
    else ParseFail ("unexpected end of input", pos)
let pany : FStar_Char.char parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos < len
    then
      let ch = Parser_FastString.fs_byte_index input pos in
      ParseOk (ch, (pos + Prims.int_one))
    else ParseFail ("unexpected end of input", pos)
let peof : unit parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos >= len
    then ParseOk ((), pos)
    else ParseFail ("expected end of input", pos)
let pstring (s : Prims.string) : Prims.string parser=
  fun input pos ->
    let slen = Parser_FastString.fs_byte_length s in
    let ilen = Parser_FastString.fs_byte_length input in
    if (pos + slen) <= ilen
    then
      let sub_str = Parser_FastString.fs_byte_sub input pos slen in
      (if sub_str = s
       then ParseOk (s, (pos + slen))
       else
         ParseFail ((FStar_String.concat "" ["expected \""; s; "\""]), pos))
    else ParseFail ((FStar_String.concat "" ["expected \""; s; "\""]), pos)
let pbind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser=
  fun input pos ->
    match p input pos with
    | ParseOk (v, pos') -> f v input pos'
    | ParseFail (msg, pos') -> ParseFail (msg, pos')
let pmap (f : 'a -> 'b) (p : 'a parser) : 'b parser=
  fun input pos ->
    match p input pos with
    | ParseOk (v, pos') -> ParseOk ((f v), pos')
    | ParseFail (msg, pos') -> ParseFail (msg, pos')
let palt (p1 : 'a parser) (p2 : 'a parser) : 'a parser=
  fun input pos ->
    match p1 input pos with
    | ParseOk (v, pos') -> ParseOk (v, pos')
    | ParseFail (uu___, uu___1) -> p2 input pos
let popt (p : 'a parser) : 'a FStar_Pervasives_Native.option parser=
  fun input pos ->
    match p input pos with
    | ParseOk (v, pos') -> ParseOk ((FStar_Pervasives_Native.Some v), pos')
    | ParseFail (uu___, uu___1) ->
        ParseOk (FStar_Pervasives_Native.None, pos)
let rec pmany_fuel :
  'a .
    'a parser ->
      Prims.string -> Prims.nat -> Prims.nat -> 'a Prims.list parse_result
  =
  fun p input pos fuel ->
    if fuel = Prims.int_zero
    then ParseOk ([], pos)
    else
      (match p input pos with
       | ParseOk (v, pos') ->
           if pos' = pos
           then ParseOk ([v], pos')
           else
             (match pmany_fuel p input pos' (fuel - Prims.int_one) with
              | ParseOk (vs, pos'') -> ParseOk ((v :: vs), pos'')
              | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
       | ParseFail (uu___1, uu___2) -> ParseOk ([], pos))
let pmany (p : 'a parser) (input : Prims.string) (pos : Prims.nat) :
  'a Prims.list parse_result=
  let fuel = ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then pmany_fuel p input pos fuel
  else ParseOk ([], pos)
let pmany1_from (p : 'a parser) (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : 'a Prims.list parse_result=
  match p input pos with
  | ParseOk (v, pos') ->
      if pos' = pos
      then ParseOk ([v], pos')
      else
        (match pmany_fuel p input pos' fuel with
         | ParseOk (vs, pos'') -> ParseOk ((v :: vs), pos'')
         | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
  | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
let pmany1 (p : 'a parser) (input : Prims.string) (pos : Prims.nat) :
  'a Prims.list parse_result=
  let fuel = ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then pmany1_from p input pos fuel
  else ParseFail ("unexpected end of input", pos)
let rec pskip_many_from :
  'a .
    'a parser -> Prims.string -> Prims.nat -> Prims.nat -> unit parse_result
  =
  fun p input pos fuel ->
    if fuel = Prims.int_zero
    then ParseOk ((), pos)
    else
      (match p input pos with
       | ParseOk (uu___1, pos') ->
           if pos' = pos
           then ParseOk ((), pos')
           else pskip_many_from p input pos' (fuel - Prims.int_one)
       | ParseFail (uu___1, uu___2) -> ParseOk ((), pos))
let pskip_many (p : 'a parser) (input : Prims.string) (pos : Prims.nat) :
  unit parse_result=
  let fuel = ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then pskip_many_from p input pos fuel
  else ParseOk ((), pos)
let rec psep_by_rest :
  'a 'b .
    'a parser ->
      'b parser ->
        Prims.string -> Prims.nat -> Prims.nat -> 'a Prims.list parse_result
  =
  fun p sep input pos fuel ->
    if fuel = Prims.int_zero
    then ParseOk ([], pos)
    else
      (match sep input pos with
       | ParseOk (uu___1, pos') ->
           (match p input pos' with
            | ParseOk (v, pos'') ->
                if pos'' = pos
                then ParseOk ([v], pos'')
                else
                  (match psep_by_rest p sep input pos''
                           (fuel - Prims.int_one)
                   with
                   | ParseOk (vs, pos''') -> ParseOk ((v :: vs), pos''')
                   | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
            | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
       | ParseFail (uu___1, uu___2) -> ParseOk ([], pos))
let psep_by (p : 'a parser) (sep : 'b parser) (input : Prims.string)
  (pos : Prims.nat) : 'a Prims.list parse_result=
  let fuel = ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one in
  match p input pos with
  | ParseOk (v, pos') ->
      if fuel >= Prims.int_zero
      then
        (match psep_by_rest p sep input pos' fuel with
         | ParseOk (vs, pos'') -> ParseOk ((v :: vs), pos'')
         | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
      else ParseOk ([v], pos')
  | ParseFail (uu___, uu___1) -> ParseOk ([], pos)
let pdigit : FStar_Char.char parser=
  psat
    (fun c ->
       let code = FStar_Char.int_of_char c in
       (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39))))
let pspace : FStar_Char.char parser=
  psat
    (fun c ->
       let code = FStar_Char.int_of_char c in
       (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
          (code = (Prims.of_int (0x0A))))
         || (code = (Prims.of_int (0x0D))))
let palpha : FStar_Char.char parser=
  psat
    (fun c ->
       let code = FStar_Char.int_of_char c in
       ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A))))
         ||
         ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
let phex : FStar_Char.char parser=
  psat
    (fun c ->
       let code = FStar_Char.int_of_char c in
       (((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39))))
          ||
          ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))))
         ||
         ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66)))))
let rec ptake_while_acc (pred : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) (acc : FStar_Char.char Prims.list)
  (fuel : Prims.nat) : Prims.string parse_result=
  if fuel = Prims.int_zero
  then
    ParseOk
      ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos < len
     then
       let ch = Parser_FastString.fs_byte_index input pos in
       (if pred ch
        then
          ptake_while_acc pred input (pos + Prims.int_one) (ch :: acc)
            (fuel - Prims.int_one)
        else
          ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              pos))
     else
       ParseOk
         ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)), pos))
let ptake_while (pred : FStar_Char.char -> Prims.bool) (input : Prims.string)
  (pos : Prims.nat) : Prims.string parse_result=
  let fuel = ((Parser_FastString.fs_byte_length input) - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then ptake_while_acc pred input pos [] fuel
  else ParseOk ("", pos)
let rec ptake_while_scan (pred : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    if pos < (Parser_FastString.fs_byte_length input)
    then
      (let ch = Parser_FastString.fs_byte_index input pos in
       if pred ch
       then
         ptake_while_scan pred input (pos + Prims.int_one)
           (fuel - Prims.int_one)
       else pos)
    else pos
let ptake_while_pos (pred : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) : Prims.string parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos > len
  then ParseOk ("", pos)
  else
    (let fuel = (len - pos) + Prims.int_one in
     let end_pos = ptake_while_scan pred input pos fuel in
     if (end_pos > pos) && (end_pos <= len)
     then
       ParseOk
         ((Parser_FastString.fs_byte_sub input pos (end_pos - pos)), end_pos)
     else ParseOk ("", pos))
let ptake_while1_pos (pred : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) : Prims.string parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos > len
  then ParseFail ("expected at least one matching character", pos)
  else
    (let fuel = (len - pos) + Prims.int_one in
     let end_pos = ptake_while_scan pred input pos fuel in
     if (end_pos > pos) && (end_pos <= len)
     then
       ParseOk
         ((Parser_FastString.fs_byte_sub input pos (end_pos - pos)), end_pos)
     else ParseFail ("expected at least one matching character", pos))
let ptake_while1 (pred : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) : Prims.string parse_result=
  match ptake_while pred input pos with
  | ParseOk (s, pos') ->
      if (FStar_String.strlen s) > Prims.int_zero
      then ParseOk (s, pos')
      else ParseFail ("expected at least one matching character", pos)
  | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
let pnatural (input : Prims.string) (pos : Prims.nat) :
  Prims.string parse_result=
  ptake_while1
    (fun c ->
       let code = FStar_Char.int_of_char c in
       (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39))))
    input pos
let backslash_char : FStar_Char.char=
  FStar_Char.char_of_int (Prims.of_int (0x5C))
let rec pquoted_body (qch : FStar_Char.char) (input : Prims.string)
  (pos : Prims.nat) (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string parse_result=
  if fuel = Prims.int_zero
  then ParseFail ("unterminated quoted string", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then ParseFail ("unterminated quoted string", pos)
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
        if ch = qch
        then
          ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if ch = backslash_char
          then
            (if (pos + Prims.int_one) < len
             then
               let escaped =
                 Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
               pquoted_body qch input (pos + (Prims.of_int (2))) (escaped ::
                 ch :: acc) (fuel - Prims.int_one)
             else ParseFail ("backslash at end of input", pos))
          else
            pquoted_body qch input (pos + Prims.int_one) (ch :: acc)
              (fuel - Prims.int_one)))
let pquoted_string (qch : FStar_Char.char) (input : Prims.string)
  (pos : Prims.nat) : Prims.string parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos < len
  then
    let ch = Parser_FastString.fs_byte_index input pos in
    (if ch = qch
     then
       let fuel = len - pos in
       pquoted_body qch input (pos + Prims.int_one) [] fuel
     else ParseFail ("expected opening quote", pos))
  else ParseFail ("unexpected end of input", pos)
let pbetween (popen : 'a parser) (pclose : 'b parser) (p : 'c parser) :
  'c parser=
  fun input pos ->
    match popen input pos with
    | ParseOk (uu___, pos1) ->
        (match p input pos1 with
         | ParseOk (v, pos2) ->
             (match pclose input pos2 with
              | ParseOk (uu___1, pos3) -> ParseOk (v, pos3)
              | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
         | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
    | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
let pleft (pa : 'a parser) (pb : 'b parser) : 'a parser=
  fun input pos ->
    match pa input pos with
    | ParseOk (va, pos1) ->
        (match pb input pos1 with
         | ParseOk (uu___, pos2) -> ParseOk (va, pos2)
         | ParseFail (msg, fpos) -> ParseFail (msg, fpos))
    | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
let pright (pa : 'a parser) (pb : 'b parser) : 'b parser=
  fun input pos ->
    match pa input pos with
    | ParseOk (uu___, pos1) -> pb input pos1
    | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
let pskip_whitespace (input : Prims.string) (pos : Prims.nat) :
  unit parse_result=
  match ptake_while
          (fun c ->
             let code = FStar_Char.int_of_char c in
             (((code = (Prims.of_int (0x20))) ||
                 (code = (Prims.of_int (0x09))))
                || (code = (Prims.of_int (0x0A))))
               || (code = (Prims.of_int (0x0D)))) input pos
  with
  | ParseOk (uu___, pos') -> ParseOk ((), pos')
  | ParseFail (msg, fpos) -> ParseFail (msg, fpos)
