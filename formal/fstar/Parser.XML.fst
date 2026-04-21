module Parser.XML

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString
open Parser.Combinators

// Issue #89: byte-indexed primitives on the parser hot path.
// XML is ASCII-delimited (tags, attributes, declarations) so byte
// semantics are safe. See Parser.FastString.fst.

(* ================================================================ *)
(* XML AST                                                           *)
(* ================================================================ *)

type xml_attribute = { attr_name: string; attr_value: string }

type xml_node =
  | XText : text:string -> xml_node
  | XElement : tag:string -> attrs:list xml_attribute -> children:list xml_node -> xml_node
  | XComment : text:string -> xml_node
  | XCDATA : text:string -> xml_node


(* ================================================================ *)
(* Character classification helpers                                  *)
(* ================================================================ *)

let is_name_start_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    code = 0x5F || code = 0x3A
  else
    code >= 0xC0

// Flattened: single function, ASCII fast-path
let is_name_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) ||
    (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) ||
    code = 0x5F || code = 0x3A ||
    code = 0x2D || code = 0x2E
  else
    code >= 0xC0 || code = 0xB7

let is_xml_space (c:char) : bool =
  let code = Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D


(* ================================================================ *)
(* XML Name parser                                                   *)
(* ================================================================ *)

let parse_xml_name : parser string =
  fun input pos ->
    let len = fs_byte_length input in
    if pos >= len then ParseFail "expected XML name" pos
    else
      let ch = fs_byte_index input pos in
      if is_name_start_char ch then
        match ptake_while_pos is_name_char input (pos + 1) with
        | ParseOk rest pos' ->
          ParseOk (String.concat "" [String.string_of_char ch; rest]) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
      else ParseFail "expected XML name start character" pos


(* ================================================================ *)
(* Entity and character reference decoding                           *)
(* ================================================================ *)

let hex_digit_value (c:char) : int =
  let code = Char.int_of_char c in
  if code >= 0x30 && code <= 0x39 then code - 0x30
  else if code >= 0x41 && code <= 0x46 then code - 0x41 + 10
  else if code >= 0x61 && code <= 0x66 then code - 0x61 + 10
  else 0

let rec parse_ref_digits (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result (list char)) (decreases fuel) =
  if fuel = 0 then ParseFail "character reference too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated character reference" pos
    else
      let ch = fs_byte_index input pos in
      if ch = ';' then
        ParseOk (List.Tot.rev acc) (pos + 1)
      else
        parse_ref_digits input (pos + 1) (ch :: acc) (fuel - 1)

let rec pow10 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (pow10 (n - 1))

let rec pow16 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 16 (pow16 (n - 1))

let rec chars_to_dec (cs:list char) : Tot int (decreases cs) =
  match cs with
  | [] -> 0
  | c :: rest ->
    let digit = Char.int_of_char c - 0x30 in
    op_Multiply digit (pow10 (List.Tot.length rest)) + chars_to_dec rest

let rec chars_to_hex (cs:list char) : Tot int (decreases cs) =
  match cs with
  | [] -> 0
  | c :: rest ->
    op_Multiply (hex_digit_value c) (pow16 (List.Tot.length rest)) + chars_to_hex rest

let codepoint_to_string (cp:int) : string =
  if cp >= 0 && cp <= 127 then
    String.string_of_char (Char.char_of_int cp)
  else if cp > 127 && cp <= 0xFFFF then
    String.string_of_char (Char.char_of_int (cp % 256))
  else
    "?"

let parse_reference (input:string) (pos:nat) : parse_result string =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "unterminated reference" pos
  else
    let ch = fs_byte_index input pos in
    if ch = '#' then
      if pos + 1 >= len then ParseFail "unterminated character reference" pos
      else
        let ch2 = fs_byte_index input (pos + 1) in
        if ch2 = 'x' || ch2 = 'X' then
          match parse_ref_digits input (pos + 2) [] 10 with
          | ParseOk digits pos' ->
            ParseOk (codepoint_to_string (chars_to_hex digits)) pos'
          | ParseFail msg fpos -> ParseFail msg fpos
        else
          match parse_ref_digits input (pos + 1) [] 10 with
          | ParseOk digits pos' ->
            ParseOk (codepoint_to_string (chars_to_dec digits)) pos'
          | ParseFail msg fpos -> ParseFail msg fpos
    else
      match pstring "amp;" input pos with
      | ParseOk _ pos' -> ParseOk "&" pos'
      | ParseFail _ _ ->
      match pstring "lt;" input pos with
      | ParseOk _ pos' -> ParseOk "<" pos'
      | ParseFail _ _ ->
      match pstring "gt;" input pos with
      | ParseOk _ pos' -> ParseOk ">" pos'
      | ParseFail _ _ ->
      match pstring "quot;" input pos with
      | ParseOk _ pos' -> ParseOk "\"" pos'
      | ParseFail _ _ ->
      match pstring "apos;" input pos with
      | ParseOk _ pos' -> ParseOk "'" pos'
      | ParseFail _ _ ->
      ParseFail "unknown entity reference" pos


(* ================================================================ *)
(* Attribute value parser (with entity decoding)                     *)
(* ================================================================ *)

let rec parse_attr_value_body (qch:char) (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "attribute value too long" pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseFail "unterminated attribute value" pos
    else
      let ch = fs_byte_index input pos in
      if ch = qch then
        ParseOk (String.concat "" (List.Tot.rev acc)) (pos + 1)
      else if ch = '&' then
        match parse_reference input (pos + 1) with
        | ParseOk decoded pos' ->
          parse_attr_value_body qch input pos' (decoded :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        match ptake_while_pos (fun c -> c <> qch && c <> '&') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            parse_attr_value_body qch input pos' (s :: acc) (fuel - 1)
          else
            parse_attr_value_body qch input (pos + 1)
              (String.string_of_char ch :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos

let parse_attr_value (input:string) (pos:nat) : parse_result string =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "expected attribute value" pos
  else
    let qch = fs_byte_index input pos in
    if qch = '"' || qch = '\'' then
      let fuel = len - pos in
      parse_attr_value_body qch input (pos + 1) [] fuel
    else ParseFail "expected quote to start attribute value" pos


(* ================================================================ *)
(* XML Attribute parser                                              *)
(* ================================================================ *)

let skip_xml_space (input:string) (pos:nat) : parse_result unit =
  match ptake_while_pos is_xml_space input pos with
  | ParseOk _ pos' -> ParseOk () pos'
  | ParseFail msg fpos -> ParseFail msg fpos

let parse_xml_attribute (input:string) (pos:nat) : parse_result xml_attribute =
  match parse_xml_name input pos with
  | ParseOk name pos1 ->
    begin match skip_xml_space input pos1 with
    | ParseOk () pos2 ->
      begin match pchar '=' input pos2 with
      | ParseOk _ pos3 ->
        begin match skip_xml_space input pos3 with
        | ParseOk () pos4 ->
          begin match parse_attr_value input pos4 with
          | ParseOk value pos5 ->
            ParseOk ({ attr_name = name; attr_value = value }) pos5
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos

let rec parse_attributes (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xml_attribute)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk [] pos
    else
      match ptake_while1_pos is_xml_space input pos with
      | ParseOk _ pos1 ->
        if pos1 < len then
          let ch = fs_byte_index input pos1 in
          if is_name_start_char ch then
            match parse_xml_attribute input pos1 with
            | ParseOk attr pos2 ->
              begin match parse_attributes input pos2 (fuel - 1) with
              | ParseOk attrs pos3 -> ParseOk (attr :: attrs) pos3
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail msg fpos -> ParseFail msg fpos
          else
            ParseOk [] pos1
        else ParseOk [] pos1
      | ParseFail _ _ ->
        ParseOk [] pos


(* ================================================================ *)
(* XML text content parser (with entity decoding)                    *)
(* ================================================================ *)

let rec parse_text_content (input:string) (pos:nat) (acc:list string) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseOk (String.concat "" (List.Tot.rev acc)) pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk (String.concat "" (List.Tot.rev acc)) pos
    else
      let ch = fs_byte_index input pos in
      if ch = '<' then
        ParseOk (String.concat "" (List.Tot.rev acc)) pos
      else if ch = '&' then
        match parse_reference input (pos + 1) with
        | ParseOk decoded pos' ->
          parse_text_content input pos' (decoded :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos
      else
        match ptake_while_pos (fun c -> c <> '<' && c <> '&') input pos with
        | ParseOk s pos' ->
          if fs_byte_length s > 0 then
            parse_text_content input pos' (s :: acc) (fuel - 1)
          else
            parse_text_content input (pos + 1)
              (String.string_of_char ch :: acc) (fuel - 1)
        | ParseFail msg fpos -> ParseFail msg fpos

let parse_xml_text (input:string) (pos:nat) : parse_result xml_node =
  let len = fs_byte_length input in
  let fuel = len - pos + 1 in
  if fuel >= 0 then
    match parse_text_content input pos [] fuel with
    | ParseOk text pos' ->
      if fs_byte_length text > 0 then ParseOk (XText text) pos'
      else ParseFail "empty text node" pos
    | ParseFail msg fpos -> ParseFail msg fpos
  else ParseFail "unexpected position" pos


(* ================================================================ *)
(* XML Comment parser                                                *)
(* ================================================================ *)

let rec parse_comment_body (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated comment" pos
  else
    let len = fs_byte_length input in
    if pos + 2 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      let c2 = fs_byte_index input (pos + 2) in
      if c0 = '-' && c1 = '-' && c2 = '>' then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 3)
      else
        parse_comment_body input (pos + 1) (c0 :: acc) (fuel - 1)
    else if pos < len then
      let c0 = fs_byte_index input pos in
      parse_comment_body input (pos + 1) (c0 :: acc) (fuel - 1)
    else ParseFail "unterminated comment" pos

let parse_xml_comment (input:string) (pos:nat) : parse_result xml_node =
  match pstring "<!--" input pos with
  | ParseOk _ pos1 ->
    let len = fs_byte_length input in
    let fuel = len - pos1 + 1 in
    begin match parse_comment_body input pos1 [] fuel with
    | ParseOk text pos2 -> ParseOk (XComment text) pos2
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* CDATA section parser                                              *)
(* ================================================================ *)

let rec parse_cdata_body (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated CDATA section" pos
  else
    let len = fs_byte_length input in
    if pos + 2 < len then
      let c0 = fs_byte_index input pos in
      let c1 = fs_byte_index input (pos + 1) in
      let c2 = fs_byte_index input (pos + 2) in
      if c0 = ']' && c1 = ']' && c2 = '>' then
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 3)
      else
        parse_cdata_body input (pos + 1) (c0 :: acc) (fuel - 1)
    else if pos < len then
      let c0 = fs_byte_index input pos in
      parse_cdata_body input (pos + 1) (c0 :: acc) (fuel - 1)
    else ParseFail "unterminated CDATA section" pos

let parse_xml_cdata (input:string) (pos:nat) : parse_result xml_node =
  match pstring "<![CDATA[" input pos with
  | ParseOk _ pos1 ->
    let len = fs_byte_length input in
    let fuel = len - pos1 + 1 in
    begin match parse_cdata_body input pos1 [] fuel with
    | ParseOk text pos2 -> ParseOk (XCDATA text) pos2
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* XML Declaration parser                                            *)
(* ================================================================ *)

let parse_xml_declaration (input:string) (pos:nat) : parse_result (list xml_attribute) =
  match pstring "<?xml" input pos with
  | ParseOk _ pos1 ->
    let len = fs_byte_length input in
    let fuel = len - pos1 + 1 in
    begin match parse_attributes input pos1 fuel with
    | ParseOk attrs pos2 ->
      begin match skip_xml_space input pos2 with
      | ParseOk () pos3 ->
        begin match pstring "?>" input pos3 with
        | ParseOk _ pos4 -> ParseOk attrs pos4
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* XML Element parser (recursive, fuel-based)                        *)
(* ================================================================ *)

let rec parse_children (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xml_node)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    let len = fs_byte_length input in
    if pos >= len then ParseOk [] pos
    else
      let ch = fs_byte_index input pos in
      if ch = '<' then
        if pos + 1 < len then
          let ch2 = fs_byte_index input (pos + 1) in
          if ch2 = '/' then
            ParseOk [] pos
          else if ch2 = '!' then
            begin match parse_xml_comment input pos with
            | ParseOk comment pos' ->
              begin match parse_children input pos' (fuel - 1) with
              | ParseOk rest pos'' -> ParseOk (comment :: rest) pos''
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail _ _ ->
              begin match parse_xml_cdata input pos with
              | ParseOk cdata pos' ->
                begin match parse_children input pos' (fuel - 1) with
                | ParseOk rest pos'' -> ParseOk (cdata :: rest) pos''
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            end
          else
            begin match parse_xml_element input pos (fuel - 1) with
            | ParseOk elem pos' ->
              begin match parse_children input pos' (fuel - 1) with
              | ParseOk rest pos'' -> ParseOk (elem :: rest) pos''
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        else ParseFail "unexpected end after '<'" pos
      else
        match parse_xml_text input pos with
        | ParseOk text_node pos' ->
          if pos' = pos then ParseOk [] pos
          else
            begin match parse_children input pos' (fuel - 1) with
            | ParseOk rest pos'' -> ParseOk (text_node :: rest) pos''
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        | ParseFail _ _ -> ParseOk [] pos

and parse_xml_element (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xml_node) (decreases fuel) =
  if fuel = 0 then ParseFail "element nesting too deep (out of fuel)" pos
  else
    match pchar '<' input pos with
    | ParseOk _ pos1 ->
      begin match parse_xml_name input pos1 with
      | ParseOk tag pos2 ->
        let len = fs_byte_length input in
        let attr_fuel = if pos2 <= len then len - pos2 + 1 else 1 in
        begin match parse_attributes input pos2 attr_fuel with
        | ParseOk attrs pos3 ->
          begin match skip_xml_space input pos3 with
          | ParseOk () pos4 ->
            begin match pstring "/>" input pos4 with
            | ParseOk _ pos5 ->
              ParseOk (XElement tag attrs []) pos5
            | ParseFail _ _ ->
              begin match pchar '>' input pos4 with
              | ParseOk _ pos5 ->
                begin match parse_children input pos5 (fuel - 1) with
                | ParseOk children pos6 ->
                  begin match pstring "</" input pos6 with
                  | ParseOk _ pos7 ->
                    begin match parse_xml_name input pos7 with
                    | ParseOk close_tag pos8 ->
                      if close_tag = tag then
                        begin match skip_xml_space input pos8 with
                        | ParseOk () pos9 ->
                          begin match pchar '>' input pos9 with
                          | ParseOk _ pos10 ->
                            ParseOk (XElement tag attrs children) pos10
                          | ParseFail msg fpos -> ParseFail msg fpos
                          end
                        | ParseFail msg fpos -> ParseFail msg fpos
                        end
                      else
                        ParseFail (String.concat "" [
                          "closing tag '</"; close_tag;
                          ">' does not match opening '<"; tag; ">'"])
                          pos7
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
                  | ParseFail msg fpos -> ParseFail msg fpos
                  end
                | ParseFail msg fpos -> ParseFail msg fpos
                end
              | ParseFail msg fpos -> ParseFail msg fpos
              end
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* Misc / Prolog helpers                                             *)
(* ================================================================ *)

let rec skip_misc (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result unit) (decreases fuel) =
  if fuel = 0 then ParseOk () pos
  else
    match skip_xml_space input pos with
    | ParseOk () pos1 ->
      begin match parse_xml_comment input pos1 with
      | ParseOk _ pos2 -> skip_misc input pos2 (fuel - 1)
      | ParseFail _ _ -> ParseOk () pos1
      end
    | ParseFail msg fpos -> ParseFail msg fpos


(* ================================================================ *)
(* Document-level entry point                                        *)
(* ================================================================ *)

let parse_xml_document (input:string) : option xml_node =
  let len = fs_byte_length input in
  let fuel = len + 1 in
  match skip_xml_space input 0 with
  | ParseOk () pos0 ->
    let pos1 =
      match parse_xml_declaration input pos0 with
      | ParseOk _attrs pos' -> pos'
      | ParseFail _ _ -> pos0
    in
    begin match skip_misc input pos1 fuel with
    | ParseOk () pos2 ->
      begin match parse_xml_element input pos2 fuel with
      | ParseOk root _pos3 -> Some root
      | ParseFail _ _ -> None
      end
    | ParseFail _ _ -> None
    end
  | ParseFail _ _ -> None


(* ================================================================ *)
(* Convenience accessors                                             *)
(* ================================================================ *)

let element_tag (node:xml_node) : option string =
  match node with
  | XElement tag _ _ -> Some tag
  | _ -> None

let element_attrs (node:xml_node) : list xml_attribute =
  match node with
  | XElement _ attrs _ -> attrs
  | _ -> []

let element_children (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children -> children
  | _ -> []

let find_attr (name:string) (attrs:list xml_attribute) : option string =
  match List.Tot.find (fun (a:xml_attribute) -> a.attr_name = name) attrs with
  | Some a -> Some a.attr_value
  | None -> None

let rec text_content (node:xml_node) : Tot string (decreases node) =
  match node with
  | XText t -> t
  | XCDATA t -> t
  | XComment _ -> ""
  | XElement _ _ children ->
    String.concat "" (text_content_list children)

and text_content_list (nodes:list xml_node) : Tot (list string) (decreases nodes) =
  match nodes with
  | [] -> []
  | hd :: tl -> text_content hd :: text_content_list tl

let child_elements (tag:string) (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children ->
    List.Tot.filter (fun (child:xml_node) ->
      match child with
      | XElement t _ _ -> t = tag
      | _ -> false) children
  | _ -> []

let child_element (tag:string) (node:xml_node) : option xml_node =
  match child_elements tag node with
  | hd :: _ -> Some hd
  | [] -> None

let all_child_elements (node:xml_node) : list xml_node =
  match node with
  | XElement _ _ children ->
    List.Tot.filter (fun (child:xml_node) ->
      match child with
      | XElement _ _ _ -> true
      | _ -> false) children
  | _ -> []
