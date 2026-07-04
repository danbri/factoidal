module SPARQL11.IRI.Resolve

(* RFC 3986 reference-resolution algorithm + lightweight helpers,
   factored out of `SPARQL11.Algebra.fst`. The resolution functions
   themselves are unchanged from the original location (lines 1640..1726
   pre-factor); only the ambient string/list helpers are duplicated
   here so the new module has no dependency on `SPARQL11.Algebra`.

   #200 / #65 Step 1 (clean refactor; no behavior change). The Step 2
   migration — threading `option wf_iri` through `eval_expr` to retire
   the OCaml mutable `current_base_iri_ref` — is a follow-up that
   imports this module.

   Design constraint: keeping the module dependency-free of
   SPARQL11.Algebra (apart from the upstream `RDF.Graph.Executable`
   that defines `wf_iri` / `is_iri`) means duplicating
   `list_is_prefix`, `list_contains_sublist`, `string_contains`, and
   `string_to_iri` here. They're tiny and stable; consolidation into
   a shared helper module is a separate cleanup.

   2026-07-04 (JSON-LD Phase 5, IRI Resolution bucket): `resolve_iri`
   was a "SPARQL-lite" heuristic (fragment / absolute-path / last-
   segment-replace cases only) that never implemented RFC 3986 5.2's
   dot-segment removal, network-path references ("//g"), or
   query-only references ("?y") — it silently mishandled all three,
   which the JSON-LD toRdf test suite's "IRI Resolution (0..12)"
   battery (the RFC 3986 5.4 worked-examples, ~42 cases x 3 manifest
   entries) caught outright (see docs/designissues — JSON-LD Phase 5
   lessons). Replaced with a direct transliteration of RFC 3986 §5.2
   (Transform-References): split base/reference into
   scheme/authority/path/query/fragment (jir_split_ref), the merge
   algorithm (§5.2.3, jir_merge), and the dot-segment-removal
   algorithm (§5.2.4, jir_remove_dot_segments), then combine per §5.3.
   Verified against the full RFC 3986 5.4.1/5.4.2 example battery
   (Python prototype, 42/42) before porting. SPARQL query-IRI
   resolution (SPARQL11.Algebra's only other consumer of resolve_iri)
   only gets MORE correct from this — no caller-visible signature
   change. *)

open FStar.List.Tot
open FStar.Char
open RDF.Graph.Executable
open Parser.FastString

(* --- Local helpers (duplicated from SPARQL11.Algebra) ---------------- *)

let rec list_is_prefix (#a:eqtype) (prefix lst : list a) : Tot bool (decreases prefix) =
  match prefix, lst with
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys -> x = y && list_is_prefix xs ys

let rec list_contains_sublist (#a:eqtype) (needle haystack : list a)
  : Tot bool (decreases haystack) =
  match haystack with
  | [] -> Nil? needle
  | _ :: rest -> list_is_prefix needle haystack || list_contains_sublist needle rest

let string_contains (s sub : string) : bool =
  list_contains_sublist (String.list_of_string sub) (String.list_of_string s)

let string_to_iri (s : string) : option wf_iri =
  if is_iri s then Some s else None

(** RFC 3986 §5.2 reference resolution — byte-level helpers **)

// Total byte peek: the byte at pos as an int in [0, 255], or -1 when pos
// is out of range (duplicated from Parser.JSON.jbyte_at — this module
// stays dependency-free of the JSON parser layer, same rationale as the
// list-helper duplication above).
let jir_byte_at (input:string) (pos:nat) : int =
  if pos < fs_byte_length input then fs_byte_at input pos else (-1)

let jir_b_colon    = 0x3A
let jir_b_slash    = 0x2F
let jir_b_question = 0x3F
let jir_b_hash     = 0x23

// Drop the first k bytes of s (clamped — never calls fs_byte_sub
// out of range even if k > length, matching this codebase's
// defensive-substring convention, e.g. jld_strip_bnode_prefix).
let jir_drop (s:string) (k:nat) : string =
  let n = fs_byte_length s in
  if k >= n then "" else fs_byte_sub s k (n - k)

let jir_starts_with (s:string) (prefix:string) : bool =
  let pl = fs_byte_length prefix in
  fs_byte_length s >= pl && fs_byte_sub s 0 pl = prefix

// First occurrence of byte `b` in s at or after `from`, fuel-bounded. The
// refined result type (index < fs_byte_length s) lets every call site's
// "length minus index" arithmetic typecheck without a separate proof.
let rec jir_find_byte (s:string) (b:int) (pos:nat) (fuel:nat)
  : Tot (option (i:nat{i < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jir_byte_at s pos = b then Some pos
    else jir_find_byte s b (pos + 1) (fuel - 1)

let jir_find (s:string) (b:int) (from:nat) : option (i:nat{i < fs_byte_length s}) =
  jir_find_byte s b from (fs_byte_length s + 1)

// Last occurrence of byte `b` in s, fuel-bounded.
let rec jir_find_last_byte (s:string) (b:int) (pos:nat) (best:option (i:nat{i < fs_byte_length s})) (fuel:nat)
  : Tot (option (i:nat{i < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then best
  else
    let n = fs_byte_length s in
    if pos >= n then best
    else
      let best' = (if jir_byte_at s pos = b then Some pos else best) in
      jir_find_last_byte s b (pos + 1) best' (fuel - 1)

let jir_find_last (s:string) (b:int) : option (i:nat{i < fs_byte_length s}) =
  jir_find_last_byte s b 0 None (fs_byte_length s + 1)

let jir_is_alpha (b:int) : bool = (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A)
let jir_is_digit (b:int) : bool = b >= 0x30 && b <= 0x39
let jir_is_scheme_byte (b:int) : bool =
  jir_is_alpha b || jir_is_digit b || b = 0x2B (* + *) || b = 0x2D (* - *) || b = 0x2E (* . *)

// Scan for a valid RFC 3986 `scheme ":"` prefix (ALPHA *(ALPHA/DIGIT/+/-/.)),
// returning the index of the colon. None when the byte sequence up to the
// first non-scheme-char is not immediately followed by ':' (e.g. it hits
// '/', '?', '#', or the end of string first) — i.e. `s` is a
// relative-reference, not one carrying its own scheme.
let rec jir_scheme_scan (s:string) (pos:nat) (fuel:nat) : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else
      let b = jir_byte_at s pos in
      if b = jir_b_colon then Some pos
      else if jir_is_scheme_byte b then jir_scheme_scan s (pos + 1) (fuel - 1)
      else None

let jir_find_scheme_colon (s:string) : option nat =
  let n = fs_byte_length s in
  if n = 0 then None
  else if not (jir_is_alpha (jir_byte_at s 0)) then None
  else jir_scheme_scan s 0 (n + 1)

// Split a URI-or-relative-reference into (scheme, authority, path, query,
// fragment) — RFC 3986 Appendix B, restricted to what §5.2/5.3 need
// (scheme/authority without their trailing ":"/"//" delimiters; query and
// fragment without their leading "?"/"#").
let jir_split_ref (s:string)
  : (option string & option string & string & option string & option string) =
  let n0 = fs_byte_length s in
  let (s1, frag) =
    (match jir_find s jir_b_hash 0 with
     | Some i -> (fs_byte_sub s 0 i, Some (fs_byte_sub s (i + 1) (n0 - i - 1)))
     | None -> (s, None)) in
  let n1 = fs_byte_length s1 in
  let (s2, query) =
    (match jir_find s1 jir_b_question 0 with
     | Some i -> (fs_byte_sub s1 0 i, Some (fs_byte_sub s1 (i + 1) (n1 - i - 1)))
     | None -> (s1, None)) in
  let (scheme, rest) =
    (match jir_find_scheme_colon s2 with
     | Some i -> (Some (fs_byte_sub s2 0 i), jir_drop s2 (i + 1))
     | None -> (None, s2)) in
  let nr = fs_byte_length rest in
  let (authority, path) =
    (if nr >= 2 && jir_byte_at rest 0 = jir_b_slash && jir_byte_at rest 1 = jir_b_slash then
       let rest2 = jir_drop rest 2 in
       (match jir_find rest2 jir_b_slash 0 with
        | Some i -> (Some (fs_byte_sub rest2 0 i), fs_byte_sub rest2 i (fs_byte_length rest2 - i))
        | None -> (Some rest2, ""))
     else (None, rest)) in
  (scheme, authority, path, query, frag)

(** RFC 3986 §5.2.4 "Remove Dot Segments" **)

// Remove up to and including the last "/" in `output` (or all of it, if
// none) — the "output buffer pop" step of §5.2.4's "/../" / "/.." cases.
let jir_remove_last_segment (output:string) : string =
  match jir_find_last output jir_b_slash with
  | Some i -> fs_byte_sub output 0 i
  | None -> ""

// Move the first path segment of `input` (its leading "/", if any, plus
// every byte up to but excluding the next "/") into the output buffer.
let jir_first_path_segment (input:string) : (string & string) =
  let n = fs_byte_length input in
  let start = (if n > 0 && jir_byte_at input 0 = jir_b_slash then 1 else 0) in
  (match jir_find input jir_b_slash start with
   | Some i -> (fs_byte_sub input 0 i, fs_byte_sub input i (n - i))
   | None -> (input, ""))

// The §5.2.4 algorithm verbatim: each branch below strictly shortens
// `input` by at least one byte, so `fuel = fs_byte_length path + 1`
// (set by the wrapper) is always enough to reach input = "".
let rec jir_remove_dot_segments_loop (input:string) (output:string) (fuel:nat)
  : Tot string (decreases fuel) =
  if fuel = 0 then output
  else if fs_byte_length input = 0 then output
  else if jir_starts_with input "../" then
    jir_remove_dot_segments_loop (jir_drop input 3) output (fuel - 1)
  else if jir_starts_with input "./" then
    jir_remove_dot_segments_loop (jir_drop input 2) output (fuel - 1)
  else if jir_starts_with input "/./" then
    jir_remove_dot_segments_loop (String.concat "" ["/"; jir_drop input 3]) output (fuel - 1)
  else if input = "/." then
    jir_remove_dot_segments_loop "/" output (fuel - 1)
  else if jir_starts_with input "/../" then
    jir_remove_dot_segments_loop (String.concat "" ["/"; jir_drop input 4])
                                  (jir_remove_last_segment output) (fuel - 1)
  else if input = "/.." then
    jir_remove_dot_segments_loop "/" (jir_remove_last_segment output) (fuel - 1)
  else if input = "." || input = ".." then
    jir_remove_dot_segments_loop "" output (fuel - 1)
  else
    let (seg, rest) = jir_first_path_segment input in
    jir_remove_dot_segments_loop rest (String.concat "" [output; seg]) (fuel - 1)

let jir_remove_dot_segments (path:string) : string =
  jir_remove_dot_segments_loop path "" (fs_byte_length path + 1)

(** RFC 3986 §5.2.3 "Merge Paths" **)

let jir_merge (base_has_authority:bool) (base_path:string) (ref_path:string) : string =
  if base_has_authority && fs_byte_length base_path = 0 then
    String.concat "" ["/"; ref_path]
  else
    match jir_find_last base_path jir_b_slash with
    | Some i -> String.concat "" [fs_byte_sub base_path 0 (i + 1); ref_path]
    | None -> ref_path

(** 6.1 IRI resolution against BASE (§5.1.1 / §5.3 "Transform References") **)

// Resolve a relative IRI reference against a base IRI per RFC 3986 §5.3,
// using the §5.2.3 merge and §5.2.4 dot-segment-removal algorithms above.
// `base` is assumed absolute (wf_iri); a result that fails is_iri (e.g.
// `base` itself did not parse a recognizable scheme, per jir_find_scheme_colon's
// alpha-first requirement — is_iri only requires "contains a colon
// somewhere", not a conformant scheme) falls back to `base` unchanged,
// same defensive contract the pre-Phase-5 implementation had.
let resolve_iri (base : wf_iri) (relative : string) : wf_iri =
  let (bscheme, bauth, bpath, bquery, _bfrag) = jir_split_ref base in
  let (rscheme, rauth, rpath, rquery, rfrag) = jir_split_ref relative in
  let (t_scheme, t_auth, t_path, t_query) =
    (match rscheme with
     | Some rs -> (Some rs, rauth, jir_remove_dot_segments rpath, rquery)
     | None ->
       (match rauth with
        | Some ra -> (bscheme, Some ra, jir_remove_dot_segments rpath, rquery)
        | None ->
          if fs_byte_length rpath = 0 then
            (bscheme, bauth, bpath, (match rquery with Some _ -> rquery | None -> bquery))
          else
            let is_abs = fs_byte_length rpath > 0 && jir_byte_at rpath 0 = jir_b_slash in
            let merged_path =
              (if is_abs then jir_remove_dot_segments rpath
               else jir_remove_dot_segments (jir_merge (Some? bauth) bpath rpath)) in
            (bscheme, bauth, merged_path, rquery))) in
  let result =
    String.concat "" [
      (match t_scheme with Some sc -> String.concat "" [sc; ":"] | None -> "");
      (match t_auth with Some a -> String.concat "" ["//"; a] | None -> "");
      t_path;
      (match t_query with Some q -> String.concat "" ["?"; q] | None -> "");
      (match rfrag with Some f -> String.concat "" ["#"; f] | None -> "")
    ] in
  if is_iri result then result else base

(* Prefix namespace IRIs are resolved against BASE during parsing.
   All IRIs in the query body are then resolved against BASE.
   This ensures that relative IRIs like <x> or <#x> become absolute. *)
let resolve_query_iri (base : option wf_iri) (rel : string) : option wf_iri =
  match base with
  | Some b -> Some (resolve_iri b rel)
  | None -> string_to_iri rel
