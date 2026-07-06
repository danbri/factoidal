module Parser.WKT

open FStar.String
open FStar.List.Tot
open FStar.Char
open FStar.Mul
open Parser.FastString
open Parser.Combinators
open RDF.Geo.Types

// Later "_rest" recursive descent helpers accumulate a heavy ambient
// proof context (RDF.Geo.Types + Parser.Combinators + this file's own
// definitions); the default z3rlimit occasionally times out on the
// otherwise-trivial `fuel <> 0 ==> fuel - 1 : nat` obligation these
// helpers all share. Bump once for the whole file rather than
// scattering per-function pragmas.
#set-options "--z3rlimit 40"

(* ================================================================ *)
(* WKT (Well-Known Text) geometry literal parser.                    *)
(*                                                                    *)
(* Grammar (informal, following OGC SFA / GeoSPARQL 1.1 §8.5):        *)
(*                                                                    *)
(*   wkt_literal   ::= crs_prefix? geometry                           *)
(*   crs_prefix    ::= '<' iri_chars '>' ws*                          *)
(*   geometry      ::= tag ws (EMPTY | body)                          *)
(*   tag           ::= 'POINT' | 'LINESTRING' | 'POLYGON'             *)
(*                    | 'MULTIPOINT' | 'MULTILINESTRING'              *)
(*                    | 'MULTIPOLYGON' | 'GEOMETRYCOLLECTION'         *)
(*                    (case-insensitive, as real-world producers vary)*)
(*                                                                    *)
(* Coordinates parse to `geo_scaled` (exact decimal rationals) via    *)
(* RDF.Geo.Types — see that module's header for why scaled-decimal    *)
(* rather than a (num,den) fraction.                                  *)
(*                                                                    *)
(* SCOPE NOTES (v0, deliberate, matching                              *)
(* docs/designissues/2026-05-07-geosparql-fstar-investigation.md):    *)
(*  - 2D only. A third (Z/M) coordinate number on a point is a parse  *)
(*    failure, not silently dropped — 3D/M geometries are out of      *)
(*    scope per the plan, and a loud parse failure is safer than       *)
(*    silently discarding data.                                       *)
(*  - Numbers are plain decimal (optional sign, digits, optional      *)
(*    '.', digits). Scientific/E-notation is NOT supported — WKT       *)
(*    producers overwhelmingly emit plain decimal coordinates          *)
(*    (Wikidata, Ordnance Survey, GeoJSON-to-WKT converters); adding    *)
(*    E-notation is a small, isolated follow-up if a producer needs    *)
(*    it (mirror SPARQL11.Algebra's parse_double_to_scaled, not        *)
(*    imported here — see RDF.Geo.Types's header on the dependency     *)
(*    direction).                                                     *)
(*  - MULTIPOINT accepts both the parenthesized-point form            *)
(*    ("MULTIPOINT((1 2),(3 4))") and the bare-coordinate form         *)
(*    ("MULTIPOINT(1 2, 3 4)"), both legal per the OGC grammar.        *)
(*  - The CRS prefix IRI is parsed and carried but never used to       *)
(*    transform coordinates (identity/opaque only, per plan).          *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(* Character classes                                                  *)
(* ---------------------------------------------------------------- *)

let wkt_dot : char = FStar.Char.char_of_int 0x2E
let wkt_minus : char = FStar.Char.char_of_int 0x2D
let wkt_plus : char = FStar.Char.char_of_int 0x2B
let wkt_lparen : char = FStar.Char.char_of_int 0x28
let wkt_rparen : char = FStar.Char.char_of_int 0x29
let wkt_comma : char = FStar.Char.char_of_int 0x2C
let wkt_lt : char = FStar.Char.char_of_int 0x3C
let wkt_gt : char = FStar.Char.char_of_int 0x3E

let is_wkt_digit (c : char) : bool =
  let code = FStar.Char.int_of_char c in code >= 0x30 && code <= 0x39

let is_wkt_ws (c : char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

// Uppercase an ASCII letter (for case-insensitive keyword matching);
// non-letters pass through unchanged.
let wkt_upper_char (c : char) : char =
  let code = FStar.Char.int_of_char c in
  if code >= 0x61 && code <= 0x7A then FStar.Char.char_of_int (code - 0x20) else c

let rec wkt_upper_chars (cs : list char) : Tot (list char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest -> wkt_upper_char c :: wkt_upper_chars rest

let wkt_upper (s : string) : string = String.string_of_list (wkt_upper_chars (String.list_of_string s))

// Remaining-input-based fuel bound, clamped at 0 (mirrors Parser.
// Combinators' `pmany`/`pmany1` fuel computation, which guards the
// same "pos may exceed length" case with `if fuel >= 0`).
let wkt_fuel_of (input : string) (pos : nat) : nat =
  if fs_byte_length input >= pos then fs_byte_length input - pos + 1 else 0

let skip_ws (input : string) (pos : nat) : nat =
  match ptake_while is_wkt_ws input pos with
  | ParseOk _ pos' -> pos'
  | ParseFail _ _ -> pos

(* ---------------------------------------------------------------- *)
(* Numbers -> geo_scaled                                              *)
(* ---------------------------------------------------------------- *)

// Digit char -> value; callers only ever pass chars already filtered
// by is_wkt_digit (via wkt_scan_number_end's construction), but this
// clamps defensively rather than requiring a refinement type threaded
// through the token-splitting helpers below (mirrors Parser.NTriples'
// `hex_val` clamp-to-0 fallback for the analogous "not actually
// reachable with a bad char, but keep the function total and simple"
// situation).
let wkt_digit_val (c : char) : nat =
  let v = FStar.Char.int_of_char c - 0x30 in
  if v < 0 then 0 else v

let rec wkt_digits_to_nat (cs : list char) (acc : nat) : Tot nat (decreases cs) =
  match cs with
  | [] -> acc
  | c :: rest -> wkt_digits_to_nat rest (acc * 10 + wkt_digit_val c)

let rec wkt_scan_number_end (input : string) (pos : nat) (seen_dot : bool) (fuel : nat)
  : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else if pos >= fs_byte_length input then pos
  else
    let c = fs_byte_index input pos in
    if is_wkt_digit c then wkt_scan_number_end input (pos + 1) seen_dot (fuel - 1)
    else if c = wkt_dot && not seen_dot then wkt_scan_number_end input (pos + 1) true (fuel - 1)
    else pos

// Local mirrors of SPARQL11.Algebra's list_take_while/list_drop_while
// (not imported — this module sits below SPARQL11.Algebra in the
// dependency graph, see the module header).
let rec wkt_list_take_while (#a:Type) (f : a -> bool) (l : list a)
  : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> if f x then x :: wkt_list_take_while f xs else []

let rec wkt_list_drop_while (#a:Type) (f : a -> bool) (l : list a)
  : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> if f x then wkt_list_drop_while f xs else x :: xs

// Split a signless digit(.digit)* token into (mantissa, scale).
// None only for a malformed token (no digits at all, e.g. a bare ".").
let wkt_split_number_token (tok : string) : option (int & nat) =
  let chars = String.list_of_string tok in
  let before = wkt_list_take_while (fun c -> c <> wkt_dot) chars in
  let after_with_dot = wkt_list_drop_while (fun c -> c <> wkt_dot) chars in
  let has_dot = not (Nil? after_with_dot) in
  let frac = if has_dot then List.Tot.tl after_with_dot else [] in
  if Nil? before && Nil? frac then None
  else
    let scale = List.Tot.length frac in
    let mant = wkt_digits_to_nat before 0 * geo_pow10 scale + wkt_digits_to_nat frac 0 in
    Some (mant, scale)

// Parse one signed decimal number starting at `pos` (leading whitespace
// must already be skipped by the caller).
let parse_wkt_number (input : string) (pos : nat) : parse_result geo_scaled =
  let len = fs_byte_length input in
  if pos >= len then ParseFail "expected a number" pos
  else
    let c0 = fs_byte_index input pos in
    let (is_neg, start) =
      if c0 = wkt_minus then (true, pos + 1)
      else if c0 = wkt_plus then (false, pos + 1)
      else (false, pos) in
    if start >= len then ParseFail "expected digits after sign" pos
    else
      let fuel = len - start + 1 in
      let end_pos = wkt_scan_number_end input start false fuel in
      if end_pos = start then ParseFail "expected digits" pos
      else
        let tok = fs_byte_sub input start (end_pos - start) in
        (match wkt_split_number_token tok with
         | None -> ParseFail "malformed number token" pos
         | Some (mant, scale) ->
           ParseOk { gs_mantissa = (if is_neg then 0 - mant else mant); gs_scale = scale } end_pos)

(* ---------------------------------------------------------------- *)
(* Keywords / punctuation                                             *)
(* ---------------------------------------------------------------- *)

// Case-insensitive fixed-keyword match. `kw` must already be uppercase.
let match_keyword (kw : string) (input : string) (pos : nat) : parse_result unit =
  let klen = fs_byte_length kw in
  let ilen = fs_byte_length input in
  if pos + klen <= ilen then
    let candidate = fs_byte_sub input pos klen in
    if wkt_upper candidate = kw then ParseOk () (pos + klen)
    else ParseFail (String.concat "" ["expected "; kw]) pos
  else ParseFail (String.concat "" ["expected "; kw]) pos

let parse_char_tok (c : char) (input : string) (pos : nat) : parse_result unit =
  let pos1 = skip_ws input pos in
  match pchar c input pos1 with
  | ParseOk _ pos2 -> ParseOk () pos2
  | ParseFail msg fpos -> ParseFail msg fpos

// EMPTY keyword, tried after skipping whitespace.
let try_empty (input : string) (pos : nat) : option nat =
  let pos1 = skip_ws input pos in
  match match_keyword "EMPTY" input pos1 with
  | ParseOk () pos2 -> Some pos2
  | ParseFail _ _ -> None

(* ---------------------------------------------------------------- *)
(* Coordinates / point lists                                          *)
(* ---------------------------------------------------------------- *)

// A single "x y" coordinate pair (2D only — a third number is a
// parse failure per the module header's scope note).
let parse_coordinate (input : string) (pos : nat) : parse_result geo_point =
  let pos1 = skip_ws input pos in
  match parse_wkt_number input pos1 with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk x pos2 ->
    let pos3 = skip_ws input pos2 in
    (match parse_wkt_number input pos3 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk y pos4 ->
       // Reject a 3rd (Z) coordinate number rather than silently
       // dropping it: peek past whitespace for another number start.
       let pos5 = skip_ws input pos4 in
       let has_more_num =
         pos5 < fs_byte_length input &&
         (let c = fs_byte_index input pos5 in
          is_wkt_digit c || c = wkt_minus || c = wkt_plus || c = wkt_dot) in
       if has_more_num then ParseFail "3D/M coordinates are out of scope for v0" pos5
       else ParseOk { gp_x = x; gp_y = y } pos4)

// "(" coord ("," coord)* ")"  -- fuel-bounded on remaining input length,
// mirroring Parser.Combinators' pmany_fuel idiom.
let rec parse_point_list_rest (input : string) (pos : nat) (acc : list geo_point) (fuel : nat)
  : Tot (parse_result (list geo_point)) (decreases fuel) =
  if fuel = 0 then ParseFail "point list too long" pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_coordinate input pos2 with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk p pos3 -> parse_point_list_rest input pos3 (p :: acc) (fuel - 1))

let parse_point_list (input : string) (pos : nat) : parse_result (list geo_point) =
  match parse_char_tok wkt_lparen input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    (match parse_coordinate input pos1 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk p pos2 ->
       let fuel = wkt_fuel_of input pos2 in
       (match parse_point_list_rest input pos2 [p] fuel with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk pts pos3 ->
          (match parse_char_tok wkt_rparen input pos3 with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk () pos4 -> ParseOk pts pos4)))

(* ---------------------------------------------------------------- *)
(* Rings / polygons                                                   *)
(* ---------------------------------------------------------------- *)

// "(" ring ("," ring)* ")"  where each ring is itself a parenthesized
// point list.
let rec parse_ring_list_rest (input : string) (pos : nat) (acc : list geo_ring) (fuel : nat)
  : Tot (parse_result (list geo_ring)) (decreases fuel) =
  if fuel = 0 then ParseFail "ring list too long" pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_point_list input pos2 with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk r pos3 -> parse_ring_list_rest input pos3 (r :: acc) (fuel - 1))

let parse_polygon_body (input : string) (pos : nat) : parse_result geo_polygon =
  match parse_char_tok wkt_lparen input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    (match parse_point_list input pos1 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk ext pos2 ->
       let fuel = wkt_fuel_of input pos2 in
       (match parse_ring_list_rest input pos2 [] fuel with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk holes pos3 ->
          (match parse_char_tok wkt_rparen input pos3 with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk () pos4 -> ParseOk { gpoly_ext = ext; gpoly_holes = holes } pos4)))

// "(" polygon_body ("," polygon_body)* ")"
let rec parse_polygon_list_rest (input : string) (pos : nat) (acc : list geo_polygon) (fuel : nat)
  : Tot (parse_result (list geo_polygon)) (decreases fuel) =
  if fuel = 0 then ParseFail "polygon list too long" pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_polygon_body input pos2 with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk p pos3 -> parse_polygon_list_rest input pos3 (p :: acc) (fuel - 1))

let parse_multipolygon_body (input : string) (pos : nat) : parse_result (list geo_polygon) =
  match parse_char_tok wkt_lparen input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    (match parse_polygon_body input pos1 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk p pos2 ->
       let fuel = wkt_fuel_of input pos2 in
       (match parse_polygon_list_rest input pos2 [p] fuel with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk ps pos3 ->
          (match parse_char_tok wkt_rparen input pos3 with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk () pos4 -> ParseOk ps pos4)))

// "(" linestring ("," linestring)* ")" for MULTILINESTRING, where
// each linestring is a parenthesized point list.
let rec parse_linestring_list_rest (input : string) (pos : nat) (acc : list (list geo_point)) (fuel : nat)
  : Tot (parse_result (list (list geo_point))) (decreases fuel) =
  if fuel = 0 then ParseFail "linestring list too long" pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_point_list input pos2 with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk l pos3 -> parse_linestring_list_rest input pos3 (l :: acc) (fuel - 1))

let parse_multilinestring_body (input : string) (pos : nat) : parse_result (list (list geo_point)) =
  match parse_char_tok wkt_lparen input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    (match parse_point_list input pos1 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk l pos2 ->
       let fuel = wkt_fuel_of input pos2 in
       (match parse_linestring_list_rest input pos2 [l] fuel with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk ls pos3 ->
          (match parse_char_tok wkt_rparen input pos3 with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk () pos4 -> ParseOk ls pos4)))

// MULTIPOINT accepts both "(1 2),(3 4)" and "1 2, 3 4" component forms.
let parse_multipoint_component (input : string) (pos : nat) : parse_result geo_point =
  let pos1 = skip_ws input pos in
  match pchar wkt_lparen input pos1 with
  | ParseOk _ pos2 ->
    (match parse_coordinate input pos2 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk p pos3 ->
       (match parse_char_tok wkt_rparen input pos3 with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk () pos4 -> ParseOk p pos4))
  | ParseFail _ _ -> parse_coordinate input pos1

let rec parse_multipoint_rest (input : string) (pos : nat) (acc : list geo_point) (fuel : nat)
  : Tot (parse_result (list geo_point)) (decreases fuel) =
  if fuel = 0 then ParseFail "multipoint list too long" pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_multipoint_component input pos2 with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk p pos3 -> parse_multipoint_rest input pos3 (p :: acc) (fuel - 1))

let parse_multipoint_body (input : string) (pos : nat) : parse_result (list geo_point) =
  match parse_char_tok wkt_lparen input pos with
  | ParseFail msg fpos -> ParseFail msg fpos
  | ParseOk () pos1 ->
    (match parse_multipoint_component input pos1 with
     | ParseFail msg fpos -> ParseFail msg fpos
     | ParseOk p pos2 ->
       let fuel = wkt_fuel_of input pos2 in
       (match parse_multipoint_rest input pos2 [p] fuel with
        | ParseFail msg fpos -> ParseFail msg fpos
        | ParseOk pts pos3 ->
          (match parse_char_tok wkt_rparen input pos3 with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk () pos4 -> ParseOk pts pos4)))

(* ---------------------------------------------------------------- *)
(* Tagged geometry text (mutually recursive with GEOMETRYCOLLECTION)  *)
(*                                                                    *)
(* Fuel = remaining input length, exactly the Parser.Combinators       *)
(* `pmany_fuel` idiom: every recursive call into a nested geometry     *)
(* consumes at least the tag keyword's worth of input, so fuel         *)
(* strictly decreases across the recursion into GEOMETRYCOLLECTION     *)
(* members. This is the "genuine recursive-descent over an input       *)
(* string position" case, not the XPath.Eval "evaluate AST against a   *)
(* runtime list" case — no separate fuel-sizing heuristic is needed.   *)
(* ---------------------------------------------------------------- *)

let rec parse_tagged_geometry (input : string) (pos : nat) (fuel : nat)
  : Tot (parse_result geo_geometry) (decreases fuel) =
  if fuel = 0 then ParseFail "geometry nesting exceeds available input" pos
  else
    let pos0 = skip_ws input pos in
    match match_keyword "GEOMETRYCOLLECTION" input pos0 with
    | ParseOk () pos1 ->
      (match try_empty input pos1 with
       | Some pos2 -> ParseOk (G_Empty GK_GeometryCollection) pos2
       | None ->
         (match parse_char_tok wkt_lparen input pos1 with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk () pos2 ->
            (match parse_tagged_geometry input pos2 (fuel - 1) with
             | ParseFail msg fpos -> ParseFail msg fpos
             | ParseOk g pos3 ->
               (match parse_geometry_list_rest input pos3 [g] (fuel - 1) with
                | ParseFail msg fpos -> ParseFail msg fpos
                | ParseOk gs pos4 ->
                  (match parse_char_tok wkt_rparen input pos4 with
                   | ParseFail msg fpos -> ParseFail msg fpos
                   | ParseOk () pos5 -> ParseOk (G_GeometryCollection gs) pos5)))))
    | ParseFail _ _ ->
      (match match_keyword "MULTIPOLYGON" input pos0 with
       | ParseOk () pos1 ->
         (match try_empty input pos1 with
          | Some pos2 -> ParseOk (G_Empty GK_MultiPolygon) pos2
          | None ->
            (match parse_multipolygon_body input pos1 with
             | ParseFail msg fpos -> ParseFail msg fpos
             | ParseOk ps pos2 -> ParseOk (G_MultiPolygon ps) pos2))
       | ParseFail _ _ ->
         (match match_keyword "MULTILINESTRING" input pos0 with
          | ParseOk () pos1 ->
            (match try_empty input pos1 with
             | Some pos2 -> ParseOk (G_Empty GK_MultiLineString) pos2
             | None ->
               (match parse_multilinestring_body input pos1 with
                | ParseFail msg fpos -> ParseFail msg fpos
                | ParseOk ls pos2 -> ParseOk (G_MultiLineString ls) pos2))
          | ParseFail _ _ ->
            (match match_keyword "MULTIPOINT" input pos0 with
             | ParseOk () pos1 ->
               (match try_empty input pos1 with
                | Some pos2 -> ParseOk (G_Empty GK_MultiPoint) pos2
                | None ->
                  (match parse_multipoint_body input pos1 with
                   | ParseFail msg fpos -> ParseFail msg fpos
                   | ParseOk pts pos2 -> ParseOk (G_MultiPoint pts) pos2))
             | ParseFail _ _ ->
               (match match_keyword "LINESTRING" input pos0 with
                | ParseOk () pos1 ->
                  (match try_empty input pos1 with
                   | Some pos2 -> ParseOk (G_Empty GK_LineString) pos2
                   | None ->
                     (match parse_point_list input pos1 with
                      | ParseFail msg fpos -> ParseFail msg fpos
                      | ParseOk l pos2 -> ParseOk (G_LineString l) pos2))
                | ParseFail _ _ ->
                  (match match_keyword "POLYGON" input pos0 with
                   | ParseOk () pos1 ->
                     (match try_empty input pos1 with
                      | Some pos2 -> ParseOk (G_Empty GK_Polygon) pos2
                      | None ->
                        (match parse_polygon_body input pos1 with
                         | ParseFail msg fpos -> ParseFail msg fpos
                         | ParseOk p pos2 -> ParseOk (G_Polygon p) pos2))
                   | ParseFail _ _ ->
                     (match match_keyword "POINT" input pos0 with
                      | ParseOk () pos1 ->
                        (match try_empty input pos1 with
                         | Some pos2 -> ParseOk (G_Empty GK_Point) pos2
                         | None ->
                           (match parse_char_tok wkt_lparen input pos1 with
                            | ParseFail msg fpos -> ParseFail msg fpos
                            | ParseOk () pos2 ->
                              (match parse_coordinate input pos2 with
                               | ParseFail msg fpos -> ParseFail msg fpos
                               | ParseOk p pos3 ->
                                 (match parse_char_tok wkt_rparen input pos3 with
                                  | ParseFail msg fpos -> ParseFail msg fpos
                                  | ParseOk () pos4 -> ParseOk (G_Point p) pos4))))
                      | ParseFail _ _ -> ParseFail "expected a WKT geometry tag" pos0))))))

and parse_geometry_list_rest (input : string) (pos : nat) (acc : list geo_geometry) (fuel : nat)
  : Tot (parse_result (list geo_geometry)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) pos
  else
    let pos1 = skip_ws input pos in
    match pchar wkt_comma input pos1 with
    | ParseFail _ _ -> ParseOk (List.Tot.rev acc) pos1
    | ParseOk _ pos2 ->
      (match parse_tagged_geometry input pos2 (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk g pos3 -> parse_geometry_list_rest input pos3 (g :: acc) (fuel - 1))

(* ---------------------------------------------------------------- *)
(* Optional CRS prefix + top-level entry point                        *)
(* ---------------------------------------------------------------- *)

// CRS prefix: '<' iri-content '>'. IRI content here is simply "not '>'"
// (CRS registry IRIs never contain '>').
let rec scan_crs_end (input : string) (pos : nat) (fuel : nat) : Tot (r:nat{r >= pos}) (decreases fuel) =
  if fuel = 0 then pos
  else if pos >= fs_byte_length input then pos
  else if fs_byte_index input pos = wkt_gt then pos
  else scan_crs_end input (pos + 1) (fuel - 1)

let try_parse_crs_prefix (input : string) (pos : nat) : (option string & nat) =
  let pos0 = skip_ws input pos in
  if pos0 < fs_byte_length input && fs_byte_index input pos0 = wkt_lt then
    let fuel = wkt_fuel_of input pos0 in
    let end_pos = scan_crs_end input (pos0 + 1) fuel in
    if end_pos < fs_byte_length input && fs_byte_index input end_pos = wkt_gt then
      let iri = fs_byte_sub input (pos0 + 1) (end_pos - pos0 - 1) in
      (Some iri, end_pos + 1)
    else (None, pos)  // unterminated '<...' — not a CRS prefix, let the geometry parser fail with a clearer message
  else (None, pos)

// Parse a complete WKT literal string (optional CRS prefix + geometry),
// requiring the whole string to be consumed modulo trailing whitespace.
let parse_wkt_literal (input : string) : option geo_wkt_value =
  let (crs, pos1) = try_parse_crs_prefix input 0 in
  let fuel = wkt_fuel_of input pos1 in
  match parse_tagged_geometry input pos1 fuel with
  | ParseFail _ _ -> None
  | ParseOk g pos2 ->
    let pos3 = skip_ws input pos2 in
    if pos3 = fs_byte_length input then Some { gw_crs = crs; gw_geom = g }
    else None

(* ================================================================ *)
(* Serialization (WKT geometry -> string), the inverse of the parser  *)
(* above. Co-located here rather than in a separate                   *)
(* RDF.Geo.WKT.Serialize.fst — this is a small, tightly-coupled        *)
(* parse/unparse pair and the v0 slice's total module count is         *)
(* already large; split out later if the serializer grows (e.g. to    *)
(* support a canonicalized/trimmed output form).                       *)
(* ================================================================ *)

let rec serialize_points (pts : list geo_point) : Tot string (decreases pts) =
  match pts with
  | [] -> ""
  | [p] -> gs_to_string p.gp_x ^ " " ^ gs_to_string p.gp_y
  | p :: rest -> gs_to_string p.gp_x ^ " " ^ gs_to_string p.gp_y ^ ", " ^ serialize_points rest

let serialize_ring (r : geo_ring) : string = "(" ^ serialize_points r ^ ")"

let rec serialize_rings (rs : list geo_ring) : Tot string (decreases rs) =
  match rs with
  | [] -> ""
  | [r] -> serialize_ring r
  | r :: rest -> serialize_ring r ^ ", " ^ serialize_rings rest

let serialize_polygon_body (p : geo_polygon) : string =
  "(" ^ serialize_rings (p.gpoly_ext :: p.gpoly_holes) ^ ")"

let rec serialize_polygons (ps : list geo_polygon) : Tot string (decreases ps) =
  match ps with
  | [] -> ""
  | [p] -> serialize_polygon_body p
  | p :: rest -> serialize_polygon_body p ^ ", " ^ serialize_polygons rest

let rec serialize_linestrings (ls : list (list geo_point)) : Tot string (decreases ls) =
  match ls with
  | [] -> ""
  | [l] -> "(" ^ serialize_points l ^ ")"
  | l :: rest -> "(" ^ serialize_points l ^ ")" ^ ", " ^ serialize_linestrings rest

let geo_kind_tag (k : geo_kind) : string =
  match k with
  | GK_Point -> "POINT"
  | GK_LineString -> "LINESTRING"
  | GK_Polygon -> "POLYGON"
  | GK_MultiPoint -> "MULTIPOINT"
  | GK_MultiLineString -> "MULTILINESTRING"
  | GK_MultiPolygon -> "MULTIPOLYGON"
  | GK_GeometryCollection -> "GEOMETRYCOLLECTION"

let rec serialize_geometry (g : geo_geometry) : Tot string (decreases g) =
  match g with
  | G_Point p -> "POINT(" ^ gs_to_string p.gp_x ^ " " ^ gs_to_string p.gp_y ^ ")"
  | G_LineString l -> "LINESTRING(" ^ serialize_points l ^ ")"
  | G_Polygon p -> "POLYGON" ^ serialize_polygon_body p
  | G_MultiPoint pts -> "MULTIPOINT(" ^ serialize_points pts ^ ")"
  | G_MultiLineString ls -> "MULTILINESTRING(" ^ serialize_linestrings ls ^ ")"
  | G_MultiPolygon ps -> "MULTIPOLYGON(" ^ serialize_polygons ps ^ ")"
  | G_GeometryCollection gs -> "GEOMETRYCOLLECTION(" ^ serialize_geometry_list gs ^ ")"
  | G_Empty k -> geo_kind_tag k ^ " EMPTY"
and serialize_geometry_list (gs : list geo_geometry) : Tot string (decreases gs) =
  match gs with
  | [] -> ""
  | [g] -> serialize_geometry g
  | g :: rest -> serialize_geometry g ^ ", " ^ serialize_geometry_list rest

let serialize_wkt_value (v : geo_wkt_value) : string =
  match v.gw_crs with
  | None -> serialize_geometry v.gw_geom
  | Some crs -> "<" ^ crs ^ "> " ^ serialize_geometry v.gw_geom
