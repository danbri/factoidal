module Parser.Turtle

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.Combinators
open Parser.NTriples
open RDF.Graph.Executable

(* ================================================================ *)
(* Turtle parser state                                               *)
(* ================================================================ *)

(* Turtle extends N-Triples with prefixes, base IRIs, and syntactic sugar.
   The parser threads state through all productions. *)
noeq type turtle_state = {
  prefixes: list (string & string);   (* prefix -> IRI base mapping *)
  base_iri: string;                   (* current base IRI for relative resolution *)
  bnode_counter: nat;                 (* counter for generating anonymous blank node IDs *)
}

let empty_turtle_state : turtle_state = {
  prefixes = [];
  base_iri = "";
  bnode_counter = 0;
}

(* Generate a fresh blank node ID and increment counter *)
let fresh_bnode (st: turtle_state) : (bnode_id & turtle_state) =
  let id = String.concat "" ["_anon"; string_of_int st.bnode_counter] in
  (id, { st with bnode_counter = st.bnode_counter + 1 })

(* ================================================================ *)
(* Prefix resolution                                                 *)
(* ================================================================ *)

(* Look up a prefix in the state *)
let rec lookup_prefix (pfx: string) (ps: list (string & string)) : option string =
  match ps with
  | [] -> None
  | (k, v) :: rest -> if k = pfx then Some v else lookup_prefix pfx rest

(* Resolve a prefixed name: prefix:localname -> full IRI *)
let resolve_prefixed_name (st: turtle_state) (prefix: string) (local: string) : option string =
  match lookup_prefix prefix st.prefixes with
  | Some base -> Some (String.concat "" [base; local])
  | None -> None

(* ================================================================ *)
(* RFC 3986 Section 5 — Relative IRI Resolution                     *)
(* ================================================================ *)

(* Helper: find the position of the first occurrence of char code in s
   starting at pos. Returns None if not found. *)
let rec find_char_from (s: string) (pos: nat) (code: nat) (fuel: nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if pos >= String.length s then None
  else if FStar.Char.int_of_char (String.index s pos) = code then Some pos
  else find_char_from s (pos + 1) code (fuel - 1)

(* Helper: find the last occurrence of '/' up to position `limit` (exclusive).
   Returns index + 1 (position after last slash), or 0 if not found. *)
let rec find_last_slash (s: string) (pos: nat) : nat =
  if pos = 0 then 0
  else
    let idx = pos - 1 in
    if idx < String.length s && FStar.Char.int_of_char (String.index s idx) = 0x2F
    then pos
    else find_last_slash s idx

(* Helper: check if string starts with given prefix at position *)
let rec string_starts_with_at (s: string) (pos: nat) (pfx: string) (pi: nat) (fuel: nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else if pi >= String.length pfx then true
  else if pos >= String.length s then false
  else if String.index s pos = String.index pfx pi
  then string_starts_with_at s (pos + 1) pfx (pi + 1) (fuel - 1)
  else false

let string_starts_with (s: string) (pfx: string) : bool =
  string_starts_with_at s 0 pfx 0 (String.length pfx + 1)

(* Extract scheme from a URI.  Returns (scheme, rest) where scheme includes
   the trailing colon.  E.g. "http://a/b" -> Some ("http:", "//a/b").
   Returns None if no scheme found (i.e. it's a relative reference). *)
let parse_uri_scheme (uri: string) : option (string & string) =
  let len = String.length uri in
  if len = 0 then None
  else
    (* scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." ) ":" *)
    let c0 = FStar.Char.int_of_char (String.index uri 0) in
    if not ((c0 >= 0x41 && c0 <= 0x5A) || (c0 >= 0x61 && c0 <= 0x7A)) then None
    else
      match find_char_from uri 1 0x3A len with (* ':' *)
      | None -> None
      | Some colon_pos ->
        (* Verify everything before colon is valid scheme char *)
        Some (String.sub uri 0 (colon_pos + 1),
              String.sub uri (colon_pos + 1) (len - colon_pos - 1))

(* Parse authority from the remainder after scheme.
   If it starts with "//", returns Some (authority, rest-path).
   authority is everything up to the next '/', '?', '#', or end.
   E.g. "//a/b/c" -> Some ("a", "/b/c")
        "//g"     -> Some ("g", "")       *)
let parse_uri_authority (s: string) : option (string & string) =
  let len = String.length s in
  if len >= 2 &&
     FStar.Char.int_of_char (String.index s 0) = 0x2F &&
     FStar.Char.int_of_char (String.index s 1) = 0x2F
  then
    (* Find end of authority: next '/', '?', or '#' *)
    let rec find_auth_end (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
      if fuel = 0 then pos
      else if pos >= len then pos
      else
        let code = FStar.Char.int_of_char (String.index s pos) in
        if code = 0x2F || code = 0x3F || code = 0x23 then pos
        else find_auth_end (pos + 1) (fuel - 1)
    in
    let auth_end = find_auth_end 2 (len - 2 + 1) in
    Some (String.sub s 2 (auth_end - 2),
          String.sub s auth_end (len - auth_end))
  else None

(* Split a string at the first occurrence of char code.
   Returns (before, after) where after does NOT include the delimiter.
   If not found, returns (s, ""). *)
let split_at_char (s: string) (code: nat) : (string & string) =
  let len = String.length s in
  match find_char_from s 0 code len with
  | Some pos -> (String.sub s 0 pos, String.sub s (pos + 1) (len - pos - 1))
  | None -> (s, "")

(* Parse path, query, fragment from a string.
   Input is the part after scheme and authority.
   Returns (path, query_option, fragment_option). *)
let parse_path_query_fragment (s: string) : (string & option string & option string) =
  let len = String.length s in
  (* Split off fragment first *)
  match find_char_from s 0 0x23 len with  (* '#' *)
  | Some frag_pos ->
    let before_frag = String.sub s 0 frag_pos in
    let frag = String.sub s (frag_pos + 1) (len - frag_pos - 1) in
    let bf_len = String.length before_frag in
    begin match find_char_from before_frag 0 0x3F bf_len with  (* '?' *)
    | Some q_pos ->
      (String.sub before_frag 0 q_pos,
       Some (String.sub before_frag (q_pos + 1) (bf_len - q_pos - 1)),
       Some frag)
    | None -> (before_frag, None, Some frag)
    end
  | None ->
    begin match find_char_from s 0 0x3F len with  (* '?' *)
    | Some q_pos ->
      (String.sub s 0 q_pos,
       Some (String.sub s (q_pos + 1) (len - q_pos - 1)),
       None)
    | None -> (s, None, None)
    end

(* URI components record *)
noeq type uri_components = {
  uc_scheme: option string;     (* e.g. "http:" — includes colon *)
  uc_authority: option string;  (* e.g. "a" — without // prefix *)
  uc_path: string;
  uc_query: option string;      (* without '?' *)
  uc_fragment: option string;   (* without '#' *)
}

(* Parse a URI into its components *)
let parse_uri_components (uri: string) : uri_components =
  let (scheme, after_scheme) =
    match parse_uri_scheme uri with
    | Some (s, rest) -> (Some s, rest)
    | None -> (None, uri)
  in
  let (authority, after_auth) =
    match parse_uri_authority after_scheme with
    | Some (a, rest) -> (Some a, rest)
    | None -> (None, after_scheme)
  in
  let (path, query, fragment) = parse_path_query_fragment after_auth in
  { uc_scheme = scheme;
    uc_authority = authority;
    uc_path = path;
    uc_query = query;
    uc_fragment = fragment }

(* Recompose a URI from its components per RFC 3986 Section 5.3 *)
let recompose_uri (c: uri_components) : string =
  let parts : list string = [] in
  let parts = match c.uc_scheme with
    | Some s -> [s] | None -> [] in
  let parts = match c.uc_authority with
    | Some a -> parts @ ["//"; a] | None -> parts in
  let parts = parts @ [c.uc_path] in
  let parts = match c.uc_query with
    | Some q -> parts @ ["?"; q] | None -> parts in
  let parts = match c.uc_fragment with
    | Some f -> parts @ ["#"; f] | None -> parts in
  String.concat "" parts

(* Remove dot segments from a path per RFC 3986 Section 5.2.4.
   Uses input buffer + output buffer approach.
   fuel parameter ensures termination. *)
let rec remove_dot_segments_loop (input: string) (output: string) (fuel: nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then String.concat "" [output; input]
  else
    let ilen = String.length input in
    if ilen = 0 then output
    else
      (* A: If input starts with "../" or "./" — remove that prefix *)
      if string_starts_with input "../" then
        remove_dot_segments_loop
          (String.sub input 3 (ilen - 3)) output (fuel - 1)
      else if string_starts_with input "./" then
        remove_dot_segments_loop
          (String.sub input 2 (ilen - 2)) output (fuel - 1)
      (* B: If input starts with "/./" or is "/." exactly *)
      else if string_starts_with input "/./" then
        remove_dot_segments_loop
          (String.concat "" ["/"; String.sub input 3 (ilen - 3)])
          output (fuel - 1)
      else if input = "/." then
        remove_dot_segments_loop "/" output (fuel - 1)
      (* C: If input starts with "/../" or is "/.." exactly *)
      else if string_starts_with input "/../" then
        let new_input = String.concat "" ["/"; String.sub input 4 (ilen - 4)] in
        let olen = String.length output in
        let cut = find_last_slash output olen in
        let new_output = if cut <= 1 then
          (if olen > 0 && FStar.Char.int_of_char (String.index output 0) = 0x2F
           then "" else "")
          else String.sub output 0 (cut - 1) in
        remove_dot_segments_loop new_input new_output (fuel - 1)
      else if input = "/.." then
        let olen = String.length output in
        let cut = find_last_slash output olen in
        let new_output = if cut <= 1 then
          (if olen > 0 && FStar.Char.int_of_char (String.index output 0) = 0x2F
           then "" else "")
          else String.sub output 0 (cut - 1) in
        remove_dot_segments_loop "/" new_output (fuel - 1)
      (* D: If input is "." or ".." exactly *)
      else if input = "." || input = ".." then
        remove_dot_segments_loop "" output (fuel - 1)
      (* E: Move first path segment (including initial "/" if any) to output *)
      else
        (* Find the next "/" after position 0 (or 1 if starts with "/") *)
        let start = if FStar.Char.int_of_char (String.index input 0) = 0x2F
                    then 1 else 0 in
        let seg_end =
          match find_char_from input start 0x2F ilen with
          | Some pos -> pos
          | None -> ilen
        in
        let seg = String.sub input 0 seg_end in
        let rest = String.sub input seg_end (ilen - seg_end) in
        remove_dot_segments_loop rest (String.concat "" [output; seg]) (fuel - 1)

let remove_dot_segments (path: string) : string =
  let fuel = (String.length path + 1) `op_Multiply` 2 in
  remove_dot_segments_loop path "" fuel

(* Merge base path with relative path per RFC 3986 Section 5.2.3 *)
let merge_paths (base: uri_components) (rel_path: string) : string =
  match base.uc_authority with
  | Some _ ->
    if String.length base.uc_path = 0
    then String.concat "" ["/"; rel_path]
    else
      let blen = String.length base.uc_path in
      let cut = find_last_slash base.uc_path blen in
      if cut = 0 then String.concat "" ["/"; rel_path]
      else String.concat "" [String.sub base.uc_path 0 cut; rel_path]
  | None ->
    let blen = String.length base.uc_path in
    let cut = find_last_slash base.uc_path blen in
    if cut = 0 then rel_path
    else String.concat "" [String.sub base.uc_path 0 cut; rel_path]

(* RFC 3986 Section 5.2.2 — main resolution algorithm *)
let resolve_iri_rfc3986 (base: uri_components) (ref_uri: uri_components) : uri_components =
  match ref_uri.uc_scheme with
  | Some _ ->
    (* R has scheme — use it as-is with dot segment removal *)
    { ref_uri with uc_path = remove_dot_segments ref_uri.uc_path }
  | None ->
    match ref_uri.uc_authority with
    | Some _ ->
      (* R has authority — use R's authority/path/query with base scheme *)
      { uc_scheme = base.uc_scheme;
        uc_authority = ref_uri.uc_authority;
        uc_path = remove_dot_segments ref_uri.uc_path;
        uc_query = ref_uri.uc_query;
        uc_fragment = ref_uri.uc_fragment }
    | None ->
      if String.length ref_uri.uc_path = 0 then
        (* Empty path — use base path, maybe override query *)
        { uc_scheme = base.uc_scheme;
          uc_authority = base.uc_authority;
          uc_path = base.uc_path;
          uc_query = (match ref_uri.uc_query with
                      | Some _ -> ref_uri.uc_query
                      | None -> base.uc_query);
          uc_fragment = ref_uri.uc_fragment }
      else
        let merged_path =
          if String.length ref_uri.uc_path > 0 &&
             FStar.Char.int_of_char (String.index ref_uri.uc_path 0) = 0x2F
          then remove_dot_segments ref_uri.uc_path
          else remove_dot_segments (merge_paths base ref_uri.uc_path)
        in
        { uc_scheme = base.uc_scheme;
          uc_authority = base.uc_authority;
          uc_path = merged_path;
          uc_query = ref_uri.uc_query;
          uc_fragment = ref_uri.uc_fragment }

(* Resolve a relative IRI against the base IRI per RFC 3986 Section 5.
   This is the main entry point used by the Turtle parser. *)
let resolve_iri (st: turtle_state) (rel: string) : string =
  if String.length rel = 0 && String.length st.base_iri = 0 then ""
  else
    let base_components = parse_uri_components st.base_iri in
    let ref_components = parse_uri_components rel in
    let resolved = resolve_iri_rfc3986 base_components ref_components in
    recompose_uri resolved

(* ================================================================ *)
(* Turtle whitespace: spaces, tabs, newlines, and comments           *)
(* ================================================================ *)

let is_turtle_ws (c: char) : bool =
  let code = int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

(* Skip a single comment: # to end of line *)
let rec skip_to_eol (input: string) (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x0A || code = 0x0D then pos
      else skip_to_eol input (pos + 1) (fuel - 1)

(* Skip whitespace and comments (which start with # and go to end of line) *)
let rec skip_ws_and_comments (input: string) (pos: nat) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length input in
    if pos >= len then pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if is_turtle_ws c then
        skip_ws_and_comments input (pos + 1) (fuel - 1)
      else if code = 0x23 then  (* '#' — comment *)
        let pos' = skip_to_eol input (pos + 1) (len - pos) in
        skip_ws_and_comments input pos' (fuel - 1)
      else
        pos

let turtle_ws (input: string) (pos: nat) : parse_result unit =
  let len = String.length input in
  let fuel = len - pos + 1 in
  if fuel >= 0 then
    ParseOk () (skip_ws_and_comments input pos fuel)
  else
    ParseOk () pos

(* ================================================================ *)
(* PN_CHARS_BASE, PN_CHARS_U, PN_CHARS — per Turtle grammar         *)
(* ================================================================ *)

let is_pn_chars_base (c: char) : bool =
  let code = int_of_char c in
  (code >= 0x41 && code <= 0x5A) ||       (* A-Z *)
  (code >= 0x61 && code <= 0x7A) ||       (* a-z *)
  (code >= 0x00C0 && code <= 0x00D6) ||
  (code >= 0x00D8 && code <= 0x00F6) ||
  (code >= 0x00F8 && code <= 0x02FF) ||
  (code >= 0x0370 && code <= 0x037D) ||
  (code >= 0x037F && code <= 0x1FFF) ||
  (code >= 0x200C && code <= 0x200D) ||
  (code >= 0x2070 && code <= 0x218F) ||
  (code >= 0x2C00 && code <= 0x2FEF) ||
  (code >= 0x3001 && code <= 0xD7FF) ||
  (code >= 0xF900 && code <= 0xFDCF) ||
  (code >= 0xFDF0 && code <= 0xFFFD) ||
  (code >= 0x10000 && code <= 0xEFFFF)

let is_pn_chars_u (c: char) : bool =
  is_pn_chars_base c || int_of_char c = 0x5F  (* '_' *)

let is_pn_chars (c: char) : bool =
  is_pn_chars_u c ||
  (let code = int_of_char c in
   code = 0x2D ||                             (* '-' *)
   (code >= 0x30 && code <= 0x39) ||          (* 0-9 *)
   code = 0xB7 ||
   (code >= 0x0300 && code <= 0x036F) ||
   (code >= 0x203F && code <= 0x2040))

(* ================================================================ *)
(* Prefixed name parser: prefix:local                                *)
(* ================================================================ *)

(* Parse the prefix part (before the colon). Can be empty for default prefix. *)
let rec parse_pname_ns_acc (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "prefix name too long" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "expected ':' in prefixed name" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3A then  (* ':' found — end of prefix namespace *)
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if is_pn_chars c || code = 0x2E then  (* Allow dots in prefix name body *)
        parse_pname_ns_acc input (pos + 1) (c :: acc) (fuel - 1)
      else
        ParseFail "invalid character in prefix name" pos

(* Parse prefix namespace: letters followed by colon *)
let parse_pname_ns (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseFail "expected prefix name" pos
  else
    let c = String.index input pos in
    let code = int_of_char c in
    if code = 0x3A then  (* empty prefix — just ':' *)
      ParseOk "" (pos + 1)
    else if is_pn_chars_base c then
      let fuel = len - pos in
      parse_pname_ns_acc input (pos + 1) [c] fuel
    else
      ParseFail "expected prefix name" pos

(* Parse local name part (after the colon).
   Local names can contain PN_CHARS, '.', ':', and percent-encoded chars.
   For now we handle the common ASCII subset. *)
let is_pn_local_char (c: char) : bool =
  is_pn_chars c ||
  (let code = int_of_char c in
   code = 0x3A ||    (* ':' *)
   code = 0x2E ||    (* '.' *)
   code = 0x25 ||    (* '%' for percent-encoded *)
   code = 0x5C)      (* '\' for local escapes *)

let is_pn_local_start (c: char) : bool =
  is_pn_chars_u c ||
  (let code = int_of_char c in
   code = 0x3A ||
   (code >= 0x30 && code <= 0x39) ||
   code = 0x25 ||
   code = 0x5C)

(* Strip PN_LOCAL_ESC backslashes: \X -> X for recognized escape chars.
   Per Turtle grammar, PN_LOCAL_ESC ::= '\' ('_' | '~' | '.' | '-' | '!' | '$' |
   '&' | "'" | '(' | ')' | '*' | '+' | ',' | ';' | '=' | '/' | '?' | '#' | '@' | '%') *)
let is_pn_local_esc_char (c:char) : bool =
  let code = int_of_char c in
  code = 0x5F || code = 0x7E || code = 0x2E || code = 0x2D ||
  code = 0x21 || code = 0x24 || code = 0x26 || code = 0x27 ||
  code = 0x28 || code = 0x29 || code = 0x2A || code = 0x2B ||
  code = 0x2C || code = 0x3B || code = 0x3D || code = 0x2F ||
  code = 0x3F || code = 0x23 || code = 0x40 || code = 0x25

let rec strip_pn_local_esc_acc (s:string) (i:nat) (acc:list char) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then String.string_of_list (List.Tot.rev acc)
  else
    let len = String.length s in
    if i >= len then String.string_of_list (List.Tot.rev acc)
    else
      let c = String.index s i in
      if int_of_char c = 0x5C && i + 1 < len then
        let next = String.index s (i + 1) in
        if is_pn_local_esc_char next then
          strip_pn_local_esc_acc s (i + 2) (next :: acc) (fuel - 1)
        else
          strip_pn_local_esc_acc s (i + 1) (c :: acc) (fuel - 1)
      else
        strip_pn_local_esc_acc s (i + 1) (c :: acc) (fuel - 1)

let strip_pn_local_esc (s:string) : string =
  strip_pn_local_esc_acc s 0 [] (String.length s)

(* Parse PN_LOCAL character by character, handling backslash escapes and percent encoding
   as multi-character units. Returns the decoded local name. *)
let rec parse_pn_local_acc (input:string) (pos:nat) (acc:list char) (fuel:nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseOk (String.string_of_list (List.Tot.rev acc)) pos
  else
    let len = String.length input in
    if pos >= len then ParseOk (String.string_of_list (List.Tot.rev acc)) pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x5C && pos + 1 < len then  (* backslash escape *)
        let next = String.index input (pos + 1) in
        if is_pn_local_esc_char next then
          parse_pn_local_acc input (pos + 2) (next :: acc) (fuel - 1)
        else
          ParseOk (String.string_of_list (List.Tot.rev acc)) pos
      else if code = 0x25 && pos + 2 < len then  (* percent encoding — keep as-is *)
        let h1 = String.index input (pos + 1) in
        let h2 = String.index input (pos + 2) in
        parse_pn_local_acc input (pos + 3) (h2 :: h1 :: c :: acc) (fuel - 1)
      else if is_pn_chars c || code = 0x3A || code = 0x2E then
        parse_pn_local_acc input (pos + 1) (c :: acc) (fuel - 1)
      else
        ParseOk (String.string_of_list (List.Tot.rev acc)) pos

let parse_pn_local (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseOk "" pos  (* empty local name is valid *)
  else
    let c = String.index input pos in
    if is_pn_local_start c then
      let fuel = len - pos in
      match parse_pn_local_acc input pos [] fuel with
      | ParseOk s pos' ->
        (* Strip trailing dots — not part of local name *)
        let slen = String.length s in
        if slen > 0 then
          let last = String.index s (slen - 1) in
          if int_of_char last = 0x2E then
            ParseOk (String.sub s 0 (slen - 1)) (pos' - 1)
          else
            ParseOk s pos'
        else
          ParseOk "" pos
      | ParseFail msg fpos -> ParseFail msg fpos
    else
      ParseOk "" pos  (* empty local name *)

(* Full prefixed name: pname_ns + pn_local *)
let parse_prefixed_name (input: string) (pos: nat) : parse_result (string & string) =
  match parse_pname_ns input pos with
  | ParseOk ns pos' ->
    begin match parse_pn_local input pos' with
    | ParseOk local pos'' -> ParseOk (ns, local) pos''
    | ParseFail msg fpos -> ParseFail msg fpos
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* IRI parsing (full IRIs and prefixed names)                        *)
(* ================================================================ *)

(* Parse a Turtle IRI: either <full-iri> or prefix:local *)
let parse_turtle_iri (st: turtle_state) (input: string) (pos: nat) : parse_result iri =
  let len = String.length input in
  if pos >= len then ParseFail "expected IRI" pos
  else
    let c = String.index input pos in
    let code = int_of_char c in
    if code = 0x3C then  (* '<' — full IRI *)
      begin match parse_iri input pos with
      | ParseOk i pos' ->
        (* Resolve relative IRI if needed *)
        let resolved = resolve_iri st i in
        ParseOk resolved pos'
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    else  (* Try prefixed name *)
      begin match parse_prefixed_name input pos with
      | ParseOk (prefix, local) pos' ->
        begin match resolve_prefixed_name st prefix local with
        | Some resolved -> ParseOk resolved pos'
        | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end

(* ================================================================ *)
(* Directive parsers: @prefix, @base, PREFIX, BASE                   *)
(* ================================================================ *)

(* Parse @prefix directive: @prefix prefix: <iri> . *)
let parse_at_prefix (input: string) (pos: nat) : parse_result (string & string) =
  match pstring "@prefix" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_pname_ns input pos2 with
      | ParseOk ns pos3 ->
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          begin match parse_iri input pos4 with
          | ParseOk iri_val pos5 ->
            begin match turtle_ws input pos5 with
            | ParseOk () pos6 ->
              let len = String.length input in
              if pos6 < len then
                let dot = String.index input pos6 in
                if int_of_char dot = 0x2E then
                  ParseOk (ns, iri_val) (pos6 + 1)
                else
                  ParseFail "expected '.' after @prefix directive" pos6
              else
                ParseFail "expected '.' after @prefix directive" pos6
            end
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* Parse SPARQL-style PREFIX directive: PREFIX prefix: <iri> (no dot) *)
let parse_sparql_prefix (input: string) (pos: nat) : parse_result (string & string) =
  match pstring "PREFIX" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_pname_ns input pos2 with
      | ParseOk ns pos3 ->
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          begin match parse_iri input pos4 with
          | ParseOk iri_val pos5 ->
            ParseOk (ns, iri_val) pos5
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* Parse @base directive: @base <iri> . *)
let parse_at_base (input: string) (pos: nat) : parse_result string =
  match pstring "@base" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_iri input pos2 with
      | ParseOk iri_val pos3 ->
        begin match turtle_ws input pos3 with
        | ParseOk () pos4 ->
          let len = String.length input in
          if pos4 < len then
            let dot = String.index input pos4 in
            if int_of_char dot = 0x2E then
              ParseOk iri_val (pos4 + 1)
            else
              ParseFail "expected '.' after @base directive" pos4
          else
            ParseFail "expected '.' after @base directive" pos4
        end
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* Parse SPARQL-style BASE directive: BASE <iri> (no dot) *)
let parse_sparql_base (input: string) (pos: nat) : parse_result string =
  match pstring "BASE" input pos with
  | ParseOk _ pos1 ->
    begin match turtle_ws input pos1 with
    | ParseOk () pos2 ->
      begin match parse_iri input pos2 with
      | ParseOk iri_val pos3 ->
        ParseOk iri_val pos3
      | ParseFail msg fpos -> ParseFail msg fpos
      end
    end
  | ParseFail msg fpos -> ParseFail msg fpos

(* Parse any prefix directive (@prefix or PREFIX) *)
let parse_prefix_directive (input: string) (pos: nat) : parse_result (string & string) =
  match parse_at_prefix input pos with
  | ParseOk v p -> ParseOk v p
  | ParseFail _ _ -> parse_sparql_prefix input pos

(* Parse any base directive (@base or BASE) *)
let parse_base_directive (input: string) (pos: nat) : parse_result string =
  match parse_at_base input pos with
  | ParseOk v p -> ParseOk v p
  | ParseFail _ _ -> parse_sparql_base input pos

(* ================================================================ *)
(* Numeric literal parsers                                           *)
(* ================================================================ *)

let is_digit_char (c: char) : bool =
  let code = int_of_char c in
  code >= 0x30 && code <= 0x39

(* Parse an integer literal: [+-]?[0-9]+ *)
(* Parse a numeric literal: integer, decimal, or double.
   Returns (lexical_form, datatype_iri). *)
let parse_numeric_literal (input: string) (pos: nat) : parse_result (string & iri) =
  let len = String.length input in
  if pos >= len then ParseFail "expected numeric literal" pos
  else
    (* Consume optional sign *)
    let c0 = String.index input pos in
    let code0 = int_of_char c0 in
    let (sign_str, dpos) =
      if code0 = 0x2B then ("+", pos + 1)     (* '+' *)
      else if code0 = 0x2D then ("-", pos + 1) (* '-' *)
      else ("", pos)
    in
    (* Accumulate the numeric part: digits, dots, e/E *)
    let rec collect_num (p: nat) (acc: list char) (has_dot: bool) (has_e: bool) (fuel: nat)
      : Tot (parse_result (list char & bool & bool)) (decreases fuel) =
      if fuel = 0 then ParseOk (acc, has_dot, has_e) p
      else if p >= len then ParseOk (acc, has_dot, has_e) p
      else
        let ch = String.index input p in
        let cd = int_of_char ch in
        if is_digit_char ch then
          collect_num (p + 1) (ch :: acc) has_dot has_e (fuel - 1)
        else if cd = 0x2E && not has_dot && not has_e then
          (* Check: dot followed by digit means decimal, otherwise it's the statement terminator *)
          if p + 1 < len then
            let next = String.index input (p + 1) in
            if is_digit_char next then
              collect_num (p + 1) (ch :: acc) true has_e (fuel - 1)
            else
              (* Dot but no digit after => might be "123." which in Turtle is integer + dot terminator,
                 OR it could be a decimal like ".1" starting case. We include the dot as part of
                 the number since we already have digits before it. Actually for Turtle "123." is
                 ambiguous. Let's check: if we have digits accumulated, stop before the dot. *)
              ParseOk (acc, has_dot, has_e) p
          else
            (* Dot at end of input — don't consume it *)
            ParseOk (acc, has_dot, has_e) p
        else if (cd = 0x65 || cd = 0x45) && not has_e then  (* 'e' or 'E' *)
          (* Exponent part: optional sign + digits *)
          if p + 1 < len then
            let enext = String.index input (p + 1) in
            let ecode = int_of_char enext in
            if ecode = 0x2B || ecode = 0x2D then  (* sign after e *)
              collect_num (p + 2) (enext :: ch :: acc) has_dot true (fuel - 1)
            else if is_digit_char enext then
              collect_num (p + 1) (ch :: acc) has_dot true (fuel - 1)
            else
              ParseOk (acc, has_dot, has_e) p
          else
            ParseOk (acc, has_dot, has_e) p
        else
          ParseOk (acc, has_dot, has_e) p
    in
    (* Handle case where number starts with '.' (like .5) *)
    let starts_with_dot =
      if dpos < len then int_of_char (String.index input dpos) = 0x2E else false
    in
    if starts_with_dot then
      (* .DIGITS case => decimal *)
      if dpos + 1 < len && is_digit_char (String.index input (dpos + 1)) then
        let fuel = len - dpos in
        begin match collect_num (dpos + 1) [String.index input dpos] false true fuel with
        | ParseOk (acc, _, has_e) pos' ->
          let num_str = String.string_of_list (List.Tot.rev acc) in
          let lexical = String.concat "" [sign_str; num_str] in
          let dt = if has_e then xsd_double else xsd_decimal in
          ParseOk (lexical, dt) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        ParseFail "expected digit after '.'" dpos
    else
      let fuel = len - dpos in
      begin match collect_num dpos [] false false fuel with
      | ParseOk (acc, has_dot, has_e) pos' ->
        if List.Tot.length acc = 0 then
          ParseFail "expected numeric literal" pos
        else
          let num_str = String.string_of_list (List.Tot.rev acc) in
          let lexical = String.concat "" [sign_str; num_str] in
          let dt =
            if has_e then xsd_double
            else if has_dot then xsd_decimal
            else xsd_integer
          in
          ParseOk (lexical, dt) pos'
      | ParseFail msg fpos -> ParseFail msg fpos
      end

(* ================================================================ *)
(* String literal parsers (single/double, short/long)                *)
(* ================================================================ *)

(* Parse long string body (triple-quoted): """...""" or '''...''' *)
let rec parse_long_string_body (qch: char) (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "unterminated long string" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated long string" pos
    else
      let ch = String.index input pos in
      let code = int_of_char ch in
      if ch = qch then
        (* Check for triple quote ending *)
        if pos + 2 < len then
          let c1 = String.index input (pos + 1) in
          let c2 = String.index input (pos + 2) in
          if c1 = qch && c2 = qch then
            ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 3)
          else
            (* Single quote char — part of content *)
            parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)
        else
          (* Not enough chars for triple quote — part of content *)
          parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)
      else if code = 0x5C then  (* backslash — escape *)
        if pos + 1 >= len then ParseFail "backslash at end of long string" pos
        else
          let esc = String.index input (pos + 1) in
          let esc_code = int_of_char esc in
          if esc_code = 0x74 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x6E then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x5C then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x22 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x27 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x27 :: acc) (fuel - 1)
          else if esc_code = 0x62 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then
            parse_long_string_body qch input (pos + 2) (char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then  (* \uXXXX *)
            if pos + 6 > len then ParseFail "incomplete \\u escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
              parse_long_string_body qch input (pos + 6) (char_of_int cp :: acc) (fuel - 1)
          else if esc_code = 0x55 then  (* \UXXXXXXXX *)
            if pos + 10 > len then ParseFail "incomplete \\U escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let h4 = hex_val (String.index input (pos + 6)) in
              let h5 = hex_val (String.index input (pos + 7)) in
              let h6 = hex_val (String.index input (pos + 8)) in
              let h7 = hex_val (String.index input (pos + 9)) in
              let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                        (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                        (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                        (h6 `op_Multiply` 16) + h7) in
              parse_long_string_body qch input (pos + 10) (char_of_int cp :: acc) (fuel - 1)
          else
            ParseFail (String.concat "" ["invalid escape in long string: \\"; string_of_char esc]) pos
      else
        parse_long_string_body qch input (pos + 1) (ch :: acc) (fuel - 1)

(* Parse single-quoted string body (for 'short' strings) *)
let rec parse_single_string_body (input: string) (pos: nat) (acc: list char) (fuel: nat)
  : Tot (parse_result string) (decreases fuel) =
  if fuel = 0 then ParseFail "string too long" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "unterminated string literal" pos
    else
      let ch = String.index input pos in
      let code = int_of_char ch in
      if code = 0x27 then  (* single quote — end *)
        ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
      else if code = 0x5C then  (* backslash *)
        if pos + 1 >= len then ParseFail "backslash at end of string" pos
        else
          let esc = String.index input (pos + 1) in
          let esc_code = int_of_char esc in
          if esc_code = 0x74 then
            parse_single_string_body input (pos + 2) (char_of_int 0x09 :: acc) (fuel - 1)
          else if esc_code = 0x6E then
            parse_single_string_body input (pos + 2) (char_of_int 0x0A :: acc) (fuel - 1)
          else if esc_code = 0x72 then
            parse_single_string_body input (pos + 2) (char_of_int 0x0D :: acc) (fuel - 1)
          else if esc_code = 0x5C then
            parse_single_string_body input (pos + 2) (char_of_int 0x5C :: acc) (fuel - 1)
          else if esc_code = 0x27 then
            parse_single_string_body input (pos + 2) (char_of_int 0x27 :: acc) (fuel - 1)
          else if esc_code = 0x22 then
            parse_single_string_body input (pos + 2) (char_of_int 0x22 :: acc) (fuel - 1)
          else if esc_code = 0x62 then
            parse_single_string_body input (pos + 2) (char_of_int 0x08 :: acc) (fuel - 1)
          else if esc_code = 0x66 then
            parse_single_string_body input (pos + 2) (char_of_int 0x0C :: acc) (fuel - 1)
          else if esc_code = 0x75 then
            if pos + 6 > len then ParseFail "incomplete \\u escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let cp = ((h0 `op_Multiply` 4096) + (h1 `op_Multiply` 256) + (h2 `op_Multiply` 16) + h3) in
              parse_single_string_body input (pos + 6) (char_of_int cp :: acc) (fuel - 1)
          else if esc_code = 0x55 then
            if pos + 10 > len then ParseFail "incomplete \\U escape" pos
            else
              let h0 = hex_val (String.index input (pos + 2)) in
              let h1 = hex_val (String.index input (pos + 3)) in
              let h2 = hex_val (String.index input (pos + 4)) in
              let h3 = hex_val (String.index input (pos + 5)) in
              let h4 = hex_val (String.index input (pos + 6)) in
              let h5 = hex_val (String.index input (pos + 7)) in
              let h6 = hex_val (String.index input (pos + 8)) in
              let h7 = hex_val (String.index input (pos + 9)) in
              let cp = ((h0 `op_Multiply` 268435456) + (h1 `op_Multiply` 16777216) +
                        (h2 `op_Multiply` 1048576) + (h3 `op_Multiply` 65536) +
                        (h4 `op_Multiply` 4096) + (h5 `op_Multiply` 256) +
                        (h6 `op_Multiply` 16) + h7) in
              parse_single_string_body input (pos + 10) (char_of_int cp :: acc) (fuel - 1)
          else
            ParseFail (String.concat "" ["invalid escape: \\"; string_of_char esc]) pos
      else if code = 0x0A || code = 0x0D then
        ParseFail "unescaped newline in short string literal" pos
      else
        parse_single_string_body input (pos + 1) (ch :: acc) (fuel - 1)

(* Parse a Turtle string literal: handles "", '', """""", '''''' variants *)
let parse_turtle_string (input: string) (pos: nat) : parse_result string =
  let len = String.length input in
  if pos >= len then ParseFail "expected string literal" pos
  else
    let c0 = String.index input pos in
    let code0 = int_of_char c0 in
    if code0 = 0x22 then  (* double quote *)
      (* Check for long string """.."""" *)
      if pos + 2 < len then
        let c1 = String.index input (pos + 1) in
        let c2 = String.index input (pos + 2) in
        if int_of_char c1 = 0x22 && int_of_char c2 = 0x22 then
          (* Long double-quoted string *)
          let fuel = len - pos in
          parse_long_string_body (char_of_int 0x22) input (pos + 3) [] fuel
        else
          (* Short double-quoted string — reuse N-Triples string parser *)
          parse_string_literal input pos
      else
        (* Too short for long — try short *)
        parse_string_literal input pos
    else if code0 = 0x27 then  (* single quote *)
      if pos + 2 < len then
        let c1 = String.index input (pos + 1) in
        let c2 = String.index input (pos + 2) in
        if int_of_char c1 = 0x27 && int_of_char c2 = 0x27 then
          (* Long single-quoted string *)
          let fuel = len - pos in
          parse_long_string_body (char_of_int 0x27) input (pos + 3) [] fuel
        else
          (* Short single-quoted string *)
          let fuel = len - pos in
          parse_single_string_body input (pos + 1) [] fuel
      else
        let fuel = len - pos in
        parse_single_string_body input (pos + 1) [] fuel
    else
      ParseFail "expected string literal" pos

(* ================================================================ *)
(* Turtle literal parser with language tag or datatype               *)
(* ================================================================ *)

let parse_turtle_literal (st: turtle_state) (input: string) (pos: nat) : parse_result literal =
  match parse_turtle_string input pos with
  | ParseOk lexical pos' ->
    let len = String.length input in
    if pos' >= len then
      ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
    else
      let next = String.index input pos' in
      let next_code = int_of_char next in
      if next_code = 0x40 then  (* '@' — language tag *)
        begin match parse_lang_tag input pos' with
        | ParseOk lang pos'' ->
          ParseOk ({ lexical_form = lexical; datatype = rdf_lang_string; lang_tag = Some lang }) pos''
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if next_code = 0x5E then  (* '^' — might be '^^' datatype *)
        if pos' + 1 < len then
          let next2 = String.index input (pos' + 1) in
          if int_of_char next2 = 0x5E then
            (* '^^' followed by IRI or prefixed name *)
            begin match parse_turtle_iri st input (pos' + 2) with
            | ParseOk dt pos'' ->
              ParseOk ({ lexical_form = lexical; datatype = dt; lang_tag = None }) pos''
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          else
            ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
        else
          ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
      else
        ParseOk ({ lexical_form = lexical; datatype = xsd_string; lang_tag = None }) pos'
  | ParseFail msg fpos -> ParseFail msg fpos

(* ================================================================ *)
(* Boolean literal parser                                            *)
(* ================================================================ *)

let parse_boolean_literal (input: string) (pos: nat) : parse_result literal =
  match pstring "true" input pos with
  | ParseOk _ pos' ->
    (* Make sure next char is not alphanumeric (not part of a longer token) *)
    let len = String.length input in
    if pos' < len && is_pn_chars (String.index input pos') then
      ParseFail "expected boolean literal" pos
    else
      ParseOk ({ lexical_form = "true"; datatype = xsd_boolean; lang_tag = None }) pos'
  | ParseFail _ _ ->
    begin match pstring "false" input pos with
    | ParseOk _ pos' ->
      let len = String.length input in
      if pos' < len && is_pn_chars (String.index input pos') then
        ParseFail "expected boolean literal" pos
      else
        ParseOk ({ lexical_form = "false"; datatype = xsd_boolean; lang_tag = None }) pos'
    | ParseFail _ _ -> ParseFail "expected boolean literal" pos
    end

(* ================================================================ *)
(* The 'a' keyword (shorthand for rdf:type)                          *)
(* ================================================================ *)

let rdf_type_iri : iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let parse_a_keyword (input: string) (pos: nat) : parse_result iri =
  let len = String.length input in
  if pos >= len then ParseFail "expected 'a'" pos
  else
    let c = String.index input pos in
    if int_of_char c = 0x61 then  (* 'a' *)
      let next_pos = pos + 1 in
      (* Must be followed by whitespace or end to be a keyword, not part of a prefixed name *)
      if next_pos >= len then
        ParseOk rdf_type_iri next_pos
      else
        let nc = String.index input next_pos in
        if is_turtle_ws nc || int_of_char nc = 0x23 then  (* whitespace or comment *)
          ParseOk rdf_type_iri next_pos
        else
          ParseFail "expected 'a' keyword" pos
    else
      ParseFail "expected 'a'" pos

(* ================================================================ *)
(* RDF collection constants                                          *)
(* ================================================================ *)

let rdf_first_iri : iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest_iri : iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

(* ================================================================ *)
(* Forward declarations for mutually recursive parsers               *)
(* We use fuel-based recursion with explicit state threading.        *)
(* ================================================================ *)

(* Result type for object parsing: object term + generated triples + updated state *)
type object_result = {
  or_term: rdf_term;
  or_triples: list triple;
  or_state: turtle_state;
}

(* Result type for subject parsing *)
type subject_result = {
  sr_subject: subject;
  sr_triples: list triple;
  sr_state: turtle_state;
}

(* ================================================================ *)
(* Main recursive Turtle parser — all productions in one mutual      *)
(* recursion block using fuel for termination.                       *)
(* ================================================================ *)

(* Parse a Turtle object: IRI, blank node, literal, boolean, numeric,
   anonymous blank node [], blank node property list [p o; ...],
   or collection (...) *)
let rec parse_turtle_object (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result object_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "expected object" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3C then  (* '<' — full IRI *)
        begin match parse_turtle_iri st input pos with
        | ParseOk i pos' -> ParseOk ({ or_term = T_IRI i; or_triples = []; or_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then  (* '_' — blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk ({ or_term = T_BNode b; or_triples = []; or_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x22 || code = 0x27 then  (* '"' or '\'' — string literal *)
        begin match parse_turtle_literal st input pos with
        | ParseOk lit pos' -> ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5B then  (* '[' — anonymous blank node or blank node property list *)
        let (bnode_id, st1) = fresh_bnode st in
        (* Skip '[' *)
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 < len && int_of_char (String.index input pos2) = 0x5D then
            (* [] — empty anonymous blank node *)
            ParseOk ({ or_term = T_BNode bnode_id; or_triples = []; or_state = st1 }) (pos2 + 1)
          else
            (* [ predicate-object-list ] *)
            begin match parse_predicate_object_list st1 (S_BNode bnode_id) input pos2 (fuel - 1) with
            | ParseOk (triples, st2) pos3 ->
              begin match turtle_ws input pos3 with
              | ParseOk () pos4 ->
                if pos4 < len && int_of_char (String.index input pos4) = 0x5D then
                  ParseOk ({ or_term = T_BNode bnode_id; or_triples = triples; or_state = st2 }) (pos4 + 1)
                else
                  ParseFail "expected ']'" pos4
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        end
      else if code = 0x28 then  (* '(' — collection *)
        parse_collection st input (pos + 1) (fuel - 1)
      else
        (* Try boolean *)
        begin match parse_boolean_literal input pos with
        | ParseOk lit pos' -> ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
        | ParseFail _ _ ->
          (* Try numeric literal *)
          begin match parse_numeric_literal input pos with
          | ParseOk (lexical, dt) pos' ->
            let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = None } in
            ParseOk ({ or_term = T_Literal lit; or_triples = []; or_state = st }) pos'
          | ParseFail _ _ ->
            (* Try prefixed name *)
            begin match parse_prefixed_name input pos with
            | ParseOk (prefix, local) pos' ->
              begin match resolve_prefixed_name st prefix local with
              | Some resolved -> ParseOk ({ or_term = T_IRI resolved; or_triples = []; or_state = st }) pos'
              | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
              end
            | ParseFail _ _ -> ParseFail "expected object" pos
            end
          end
        end

(* Parse an RDF collection: ( item1 item2 ... ) *)
and parse_collection (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result object_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in collection" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseFail "unterminated collection" pos1
      else if int_of_char (String.index input pos1) = 0x29 then  (* ')' — empty collection *)
        ParseOk ({ or_term = T_IRI rdf_nil_iri; or_triples = []; or_state = st }) (pos1 + 1)
      else
        (* Parse first item *)
        begin match parse_turtle_object st input pos1 (fuel - 1) with
        | ParseOk first_obj pos2 ->
          let (node_id, st2) = fresh_bnode first_obj.or_state in
          let node_subj = S_BNode node_id in
          let first_triple : triple = { s = node_subj; p = rdf_first_iri; o = first_obj.or_term } in
          (* Parse remaining items *)
          begin match parse_collection_rest st2 node_subj input pos2 (fuel - 1) with
          | ParseOk (rest_triples, rest_term, st3) pos3 ->
            let rest_triple : triple = { s = node_subj; p = rdf_rest_iri; o = rest_term } in
            let all_triples = first_obj.or_triples @ [first_triple; rest_triple] @ rest_triples in
            ParseOk ({ or_term = T_BNode node_id; or_triples = all_triples; or_state = st3 }) pos3
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end

(* Parse remaining collection items after the first *)
and parse_collection_rest (st: turtle_state) (prev_subj: subject) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & rdf_term & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in collection rest" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseFail "unterminated collection" pos1
      else if int_of_char (String.index input pos1) = 0x29 then  (* ')' — end *)
        ParseOk ([], T_IRI rdf_nil_iri, st) (pos1 + 1)
      else
        (* Parse next item *)
        begin match parse_turtle_object st input pos1 (fuel - 1) with
        | ParseOk next_obj pos2 ->
          let (node_id, st2) = fresh_bnode next_obj.or_state in
          let node_subj = S_BNode node_id in
          let first_triple : triple = { s = node_subj; p = rdf_first_iri; o = next_obj.or_term } in
          begin match parse_collection_rest st2 node_subj input pos2 (fuel - 1) with
          | ParseOk (rest_triples, rest_term, st3) pos3 ->
            let rest_triple : triple = { s = node_subj; p = rdf_rest_iri; o = rest_term } in
            let all_triples = next_obj.or_triples @ [first_triple; rest_triple] @ rest_triples in
            ParseOk (all_triples, T_BNode node_id, st3) pos3
          | ParseFail msg fpos -> ParseFail msg fpos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end

(* Parse object list: object (',' object)* *)
and parse_object_list (st: turtle_state) (subj: subject) (pred: iri) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in object list" pos
  else
    begin match parse_turtle_object st input pos fuel with
    | ParseOk obj_res pos1 ->
      let t : triple = { s = subj; p = pred; o = obj_res.or_term } in
      let triples1 = obj_res.or_triples @ [t] in
      (* Check for comma *)
      begin match turtle_ws input pos1 with
      | ParseOk () pos2 ->
        let len = String.length input in
        if pos2 < len && int_of_char (String.index input pos2) = 0x2C then
          (* More objects *)
          begin match turtle_ws input (pos2 + 1) with
          | ParseOk () pos3 ->
            begin match parse_object_list obj_res.or_state subj pred input pos3 (fuel - 1) with
            | ParseOk (more_triples, st2) pos4 ->
              ParseOk (triples1 @ more_triples, st2) pos4
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          end
        else
          ParseOk (triples1, obj_res.or_state) pos2
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end

(* Parse a predicate: IRI, prefixed name, or 'a' keyword *)
and parse_turtle_predicate (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result iri) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    (* Try 'a' keyword first *)
    match parse_a_keyword input pos with
    | ParseOk iri_val pos' -> ParseOk iri_val pos'
    | ParseFail _ _ -> parse_turtle_iri st input pos

(* Parse predicate-object list: predicate objectList (';' predicate objectList)* ';'? *)
and parse_predicate_object_list (st: turtle_state) (subj: subject) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit in predicate-object list" pos
  else
    begin match parse_turtle_predicate st input pos fuel with
    | ParseOk pred pos1 ->
      begin match turtle_ws input pos1 with
      | ParseOk () pos2 ->
        begin match parse_object_list st subj pred input pos2 (fuel - 1) with
        | ParseOk (triples1, st1) pos3 ->
          (* Check for semicolon *)
          begin match turtle_ws input pos3 with
          | ParseOk () pos4 ->
            let len = String.length input in
            if pos4 < len && int_of_char (String.index input pos4) = 0x3B then
              (* Skip semicolon and whitespace *)
              begin match turtle_ws input (pos4 + 1) with
              | ParseOk () pos5 ->
                (* Check if there's another predicate or just trailing semicolons *)
                if pos5 >= len then
                  ParseOk (triples1, st1) pos5
                else
                  let nc = String.index input pos5 in
                  let ncode = int_of_char nc in
                  if ncode = 0x2E || ncode = 0x5D || ncode = 0x3B then
                    (* End of predicate-object list (dot, close bracket, or another semicolon) *)
                    if ncode = 0x3B then
                      (* Skip additional trailing semicolons *)
                      parse_trailing_semicolons st1 triples1 subj input pos5 (fuel - 1)
                    else
                      ParseOk (triples1, st1) pos5
                  else
                    (* Another predicate-object pair *)
                    begin match parse_predicate_object_list st1 subj input pos5 (fuel - 1) with
                    | ParseOk (more_triples, st2) pos6 ->
                      ParseOk (triples1 @ more_triples, st2) pos6
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
              end
            else
              ParseOk (triples1, st1) pos4
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      end
    | ParseFail msg fpos -> ParseFail msg fpos
    end

(* Skip trailing semicolons: ; ; ; before . or ] *)
and parse_trailing_semicolons (st: turtle_state) (triples: list triple) (subj: subject)
    (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseOk (triples, st) pos
  else
    let len = String.length input in
    if pos >= len then ParseOk (triples, st) pos
    else
      let c = String.index input pos in
      if int_of_char c = 0x3B then
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 >= len then ParseOk (triples, st) pos2
          else
            let nc = String.index input pos2 in
            let ncode = int_of_char nc in
            if ncode = 0x2E || ncode = 0x5D || ncode = 0x3B then
              parse_trailing_semicolons st triples subj input pos2 (fuel - 1)
            else
              (* Another predicate-object pair after semicolons *)
              begin match parse_predicate_object_list st subj input pos2 (fuel - 1) with
              | ParseOk (more_triples, st2) pos3 ->
                ParseOk (triples @ more_triples, st2) pos3
              | ParseFail msg fpos -> ParseFail msg fpos
              end
        end
      else
        ParseOk (triples, st) pos

(* Parse a Turtle subject: IRI, blank node, prefixed name, anonymous [], or collection () *)
let parse_turtle_subject (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result subject_result) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    if pos >= len then ParseFail "expected subject" pos
    else
      let c = String.index input pos in
      let code = int_of_char c in
      if code = 0x3C then  (* '<' — full IRI *)
        begin match parse_turtle_iri st input pos with
        | ParseOk i pos' -> ParseOk ({ sr_subject = S_IRI i; sr_triples = []; sr_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5F then  (* '_' — labeled blank node *)
        begin match parse_bnode input pos with
        | ParseOk b pos' -> ParseOk ({ sr_subject = S_BNode b; sr_triples = []; sr_state = st }) pos'
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else if code = 0x5B then  (* '[' — anonymous blank node or property list *)
        let (bnode_id, st1) = fresh_bnode st in
        begin match turtle_ws input (pos + 1) with
        | ParseOk () pos2 ->
          if pos2 < len && int_of_char (String.index input pos2) = 0x5D then
            (* [] — empty anonymous blank node *)
            ParseOk ({ sr_subject = S_BNode bnode_id; sr_triples = []; sr_state = st1 }) (pos2 + 1)
          else
            (* [ predicate-object-list ] *)
            begin match parse_predicate_object_list st1 (S_BNode bnode_id) input pos2 (fuel - 1) with
            | ParseOk (triples, st2) pos3 ->
              begin match turtle_ws input pos3 with
              | ParseOk () pos4 ->
                if pos4 < len && int_of_char (String.index input pos4) = 0x5D then
                  ParseOk ({ sr_subject = S_BNode bnode_id; sr_triples = triples; sr_state = st2 }) (pos4 + 1)
                else
                  ParseFail "expected ']'" pos4
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
        end
      else if code = 0x28 then  (* '(' — collection as subject *)
        begin match parse_collection st input (pos + 1) (fuel - 1) with
        | ParseOk obj_res pos' ->
          begin match obj_res.or_term with
          | T_IRI i ->
            ParseOk ({ sr_subject = S_IRI i; sr_triples = obj_res.or_triples; sr_state = obj_res.or_state }) pos'
          | T_BNode b ->
            ParseOk ({ sr_subject = S_BNode b; sr_triples = obj_res.or_triples; sr_state = obj_res.or_state }) pos'
          | _ -> ParseFail "collection did not produce a valid subject" pos
          end
        | ParseFail msg fpos -> ParseFail msg fpos
        end
      else
        (* Try prefixed name *)
        begin match parse_prefixed_name input pos with
        | ParseOk (prefix, local) pos' ->
          begin match resolve_prefixed_name st prefix local with
          | Some resolved -> ParseOk ({ sr_subject = S_IRI resolved; sr_triples = []; sr_state = st }) pos'
          | None -> ParseFail (String.concat "" ["undefined prefix: "; prefix]) pos
          end
        | ParseFail _ _ -> ParseFail "expected subject" pos
        end

(* ================================================================ *)
(* Top-level Turtle document parser                                  *)
(* ================================================================ *)

(* Parse a single Turtle statement: directive or triples statement *)
let parse_turtle_statement (st: turtle_state) (input: string) (pos: nat) (fuel: nat)
  : Tot (parse_result (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then ParseFail "recursion limit" pos
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then ParseOk ([], st) pos1
      else
        (* Try prefix directive *)
        begin match parse_prefix_directive input pos1 with
        | ParseOk (prefix, iri_val) pos2 ->
          let resolved_iri = resolve_iri st iri_val in
          let new_prefixes = (prefix, resolved_iri) :: st.prefixes in
          ParseOk ([], { st with prefixes = new_prefixes }) pos2
        | ParseFail _ _ ->
          (* Try base directive *)
          begin match parse_base_directive input pos1 with
          | ParseOk base_val pos2 ->
            let resolved_base = resolve_iri st base_val in
            ParseOk ([], { st with base_iri = resolved_base }) pos2
          | ParseFail _ _ ->
            (* Must be a triples statement *)
            begin match parse_turtle_subject st input pos1 fuel with
            | ParseOk subj_res pos2 ->
              begin match turtle_ws input pos2 with
              | ParseOk () pos3 ->
                (* Check if subject has property list (blank node property list as subject
                   can be followed by just '.') *)
                if pos3 >= len then
                  (* Only subject triples, no predicate-object list *)
                  if List.Tot.length subj_res.sr_triples > 0 then
                    ParseOk (subj_res.sr_triples, subj_res.sr_state) pos3
                  else
                    ParseFail "expected predicate after subject" pos3
                else
                  let nc = String.index input pos3 in
                  if int_of_char nc = 0x2E then
                    (* Subject followed directly by dot — valid only if subject generated triples *)
                    if List.Tot.length subj_res.sr_triples > 0 then
                      ParseOk (subj_res.sr_triples, subj_res.sr_state) (pos3 + 1)
                    else
                      ParseFail "expected predicate after subject" pos3
                  else
                    begin match parse_predicate_object_list subj_res.sr_state subj_res.sr_subject input pos3 (fuel - 1) with
                    | ParseOk (po_triples, st2) pos4 ->
                      let all_triples = subj_res.sr_triples @ po_triples in
                      (* Expect '.' *)
                      begin match turtle_ws input pos4 with
                      | ParseOk () pos5 ->
                        if pos5 < len && int_of_char (String.index input pos5) = 0x2E then
                          ParseOk (all_triples, st2) (pos5 + 1)
                        else
                          (* Some Turtle allows missing final dot — be lenient *)
                          ParseOk (all_triples, st2) pos5
                      end
                    | ParseFail msg fpos -> ParseFail msg fpos
                    end
              end
            | ParseFail msg fpos -> ParseFail msg fpos
            end
          end
        end

(* Parse the full Turtle document: sequence of statements *)
let rec parse_turtle_doc (st: turtle_state) (input: string) (pos: nat) (acc: list triple) (fuel: nat)
  : Tot (list triple & turtle_state) (decreases fuel) =
  if fuel = 0 then (List.Tot.rev acc, st)
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then (List.Tot.rev acc, st)
      else
        begin match parse_turtle_statement st input pos1 fuel with
        | ParseOk (triples, st') pos2 ->
          if pos2 = pos1 then
            (* No progress — stop *)
            (List.Tot.rev ((List.Tot.rev triples) @ acc), st')
          else
            parse_turtle_doc st' input pos2 ((List.Tot.rev triples) @ acc) (fuel - 1)
        | ParseFail _ _ ->
          (* Skip to next line on failure *)
          let rec skip_line (p: nat) (f: nat) : Tot nat (decreases f) =
            if f = 0 then p
            else if p >= len then p
            else
              let c = String.index input p in
              let cd = int_of_char c in
              if cd = 0x0A || cd = 0x0D then p + 1
              else skip_line (p + 1) (f - 1)
          in
          let pos2 = skip_line pos1 (len - pos1) in
          if pos2 = pos1 then (List.Tot.rev acc, st)
          else parse_turtle_doc st input pos2 acc (fuel - 1)
        end

(* ================================================================ *)
(* Strict document parser (returns None on any parse error)          *)
(* ================================================================ *)

(* Like parse_turtle_doc but propagates errors instead of skipping *)
let rec parse_turtle_doc_strict (st: turtle_state) (input: string) (pos: nat) (acc: list triple) (fuel: nat)
  : Tot (option (list triple & turtle_state)) (decreases fuel) =
  if fuel = 0 then Some (List.Tot.rev acc, st)
  else
    let len = String.length input in
    match turtle_ws input pos with
    | ParseOk () pos1 ->
      if pos1 >= len then Some (List.Tot.rev acc, st)
      else
        begin match parse_turtle_statement st input pos1 fuel with
        | ParseOk (triples, st') pos2 ->
          if pos2 = pos1 then
            (* No progress — stop *)
            Some (List.Tot.rev ((List.Tot.rev triples) @ acc), st')
          else
            parse_turtle_doc_strict st' input pos2 ((List.Tot.rev triples) @ acc) (fuel - 1)
        | ParseFail _ _ ->
          (* Strict mode: any parse failure means the document is invalid *)
          None
        end

(* ================================================================ *)
(* Entry point                                                       *)
(* ================================================================ *)

(* Parse a Turtle document string into a list of triples *)
let parse_turtle (input: string) : list triple =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let (triples, _) = parse_turtle_doc empty_turtle_state input 0 [] fuel in
  triples

(* Parse with initial state (e.g., with a base IRI) *)
let parse_turtle_with_base (input: string) (base: string) : list triple =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let st = { empty_turtle_state with base_iri = base } in
  let (triples, _) = parse_turtle_doc st input 0 [] fuel in
  triples

(* Strict parse: returns None on any parse error *)
let parse_turtle_strict (input: string) : option (list triple) =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  match parse_turtle_doc_strict empty_turtle_state input 0 [] fuel with
  | Some (triples, _) -> Some triples
  | None -> None

(* Strict parse with base IRI: returns None on any parse error *)
let parse_turtle_with_base_strict (input: string) (base: string) : option (list triple) =
  let len = String.length input in
  let fuel = (len + 1) `op_Multiply` 2 in
  let st = { empty_turtle_state with base_iri = base } in
  match parse_turtle_doc_strict st input 0 [] fuel with
  | Some (triples, _) -> Some triples
  | None -> None
