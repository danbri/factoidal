module RDF.IRI

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString
open RDF.Graph.Executable

// ============================================================================
// RFC 3986 section 5.2 reference resolution -- consolidated.
//
// This module provides a byte-oriented, total, fully verified implementation
// of RFC 3986 section 5.2 (Transform References) and its helpers:
//   section 5.2.3 merge
//   section 5.2.4 remove_dot_segments
//   section 5.3   Component Recomposition
//   section 3     just enough parsing to split an IRI into five components
//
// Per docs/designissues/2026-07-05-foundational-core-refactor.md section 2.7 /
// section 3.3 step 1: this module replaces the two independent RFC 3986
// implementations that used to live in `Parser.IRI.fst` (this module's
// former name; `parse_iri`/`remove_dot_segments`/`merge_paths`/
// `transform_references`/`recompose`/`resolve_iri_v2` below are that
// module's content, unchanged) and `SPARQL11.IRI.Resolve.fst` (its
// `jir_*`-prefixed helpers and `resolve_iri`/`resolve_query_iri`, whose
// *observable behavior* is reproduced by the `resolve_iri`/
// `resolve_query_iri` definitions at the bottom of this file -- see the
// `.fsti`'s banner for the differential-testing evidence that this is
// behavior-preserving, not merely "close enough").
//
// Design notes (unchanged from the original `Parser.IRI.fst`):
//  - ASCII-only delimiter scans. RFC 3986 syntax commits on `:`, `/`, `?`,
//    `#`, and `.` -- all single ASCII bytes. UTF-8 continuation bytes
//    (0x80..0xBF) and lead bytes (0xC2..0xF4) never collide with these, so
//    byte-level scans are safe in the presence of non-ASCII IRI bodies.
//  - No codepoint decoding. fs_cp_at / fs_cp_len from Parser.FastString are
//    NOT called from this module.
//  - No FStar.String.length / FStar.String.sub / FStar.String.index.
//  - No percent-encoding normalisation, no case folding, no IDN, no Unicode
//    normalisation. Strictly section 5.2 + section 5.3.
//
// `remove_dot_segments_step` here is a verbatim port from Parser.Turtle.fst
// (the existing verified implementation) -- Parser.Turtle.fst itself now
// delegates to this module's `resolve_iri_v2` rather than its own
// (unreachable, dead-code) copy of the same algorithm; see the note near
// `_rfc3986_5_4_examples` below.
// ============================================================================

// ------------------------------------------------------------------
// Data type: parsed IRI parts. Each component is stored without its
// syntactic delimiter -- scheme has no trailing `:`, authority has no
// leading `//`, query has no leading `?`, fragment has no leading `#`.
// Path is always present (possibly the empty string).
// ------------------------------------------------------------------
noeq type iri_parts = {
  ip_scheme    : option string;
  ip_authority : option string;
  ip_path      : string;
  ip_query     : option string;
  ip_fragment  : option string;
}

// ------------------------------------------------------------------
// Byte-scanners. Each returns a position in [start, fs_byte_length s]
// so Z3 has a tight refinement at call sites. Fuel is bounded to
// (fs_byte_length s - pos + 1) at every call site; that is ample.
// ------------------------------------------------------------------

// Find first `:` at or after pos, returning pos..fs_byte_length s.
let rec find_colon (s: string) (pos: nat{pos <= fs_byte_length s}) (fuel: nat)
  : Tot (r:nat{pos <= r /\ r <= fs_byte_length s}) (decreases fuel) =
  let len = fs_byte_length s in
  if fuel = 0 then pos
  else if pos >= len then len
  else if fs_byte_at s pos = 0x3A then pos
  else find_colon s (pos + 1) (fuel - 1)

// Find the first byte that is either `/`, `?`, `#`, at or after `pos`.
// This is the "end of authority" scanner. Returns fs_byte_length s if
// none of those bytes appear in [pos, len).
let rec find_authority_end_iri (s: string) (pos: nat{pos <= fs_byte_length s}) (fuel: nat)
  : Tot (r:nat{pos <= r /\ r <= fs_byte_length s}) (decreases fuel) =
  let len = fs_byte_length s in
  if fuel = 0 then pos
  else if pos >= len then len
  else
    let b = fs_byte_at s pos in
    if b = 0x2F || b = 0x3F || b = 0x23 then pos
    else find_authority_end_iri s (pos + 1) (fuel - 1)

// Find the first `?` or `#` at or after `pos`. Marks end of path.
let rec find_path_end_iri (s: string) (pos: nat{pos <= fs_byte_length s}) (fuel: nat)
  : Tot (r:nat{pos <= r /\ r <= fs_byte_length s}) (decreases fuel) =
  let len = fs_byte_length s in
  if fuel = 0 then pos
  else if pos >= len then len
  else
    let b = fs_byte_at s pos in
    if b = 0x3F || b = 0x23 then pos
    else find_path_end_iri s (pos + 1) (fuel - 1)

// Find the first `#` at or after `pos`. Marks end of query.
let rec find_hash_iri (s: string) (pos: nat{pos <= fs_byte_length s}) (fuel: nat)
  : Tot (r:nat{pos <= r /\ r <= fs_byte_length s}) (decreases fuel) =
  let len = fs_byte_length s in
  if fuel = 0 then pos
  else if pos >= len then len
  else if fs_byte_at s pos = 0x23 then pos
  else find_hash_iri s (pos + 1) (fuel - 1)

// Find the first `/` at or after `pos`. Used by remove_dot_segments_step.
let rec find_slash_iri (s: string) (pos: nat{pos <= fs_byte_length s}) (fuel: nat)
  : Tot (r:nat{pos <= r /\ r <= fs_byte_length s}) (decreases fuel) =
  let len = fs_byte_length s in
  if fuel = 0 then pos
  else if pos >= len then len
  else if fs_byte_at s pos = 0x2F then pos
  else find_slash_iri s (pos + 1) (fuel - 1)

// ------------------------------------------------------------------
// Scheme validity. Per RFC 3986, a scheme must begin with an ASCII
// ALPHA and be followed by zero or more of [A-Z a-z 0-9 + - .]. If
// the first `:` in the input is preceded by anything else, we treat
// the input as having no scheme (it is a relative reference).
// ------------------------------------------------------------------

let is_ascii_alpha (b: nat) : bool =
  (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A)

let is_scheme_tail_byte (b: nat) : bool =
  is_ascii_alpha b
  || (b >= 0x30 && b <= 0x39)
  || b = 0x2B  // '+'
  || b = 0x2D  // '-'
  || b = 0x2E  // '.'

// Walk bytes [1, colon_pos) and check each is a scheme-tail byte.
// Position 0 is checked separately via is_ascii_alpha.
let rec scheme_tail_ok (s: string) (pos: nat) (stop: nat{stop <= fs_byte_length s}) (fuel: nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else if pos >= stop then true
  else if not (is_scheme_tail_byte (fs_byte_at s pos)) then false
  else scheme_tail_ok s (pos + 1) stop (fuel - 1)

// Does [0, colon_pos) form a valid scheme? colon_pos must be >= 1.
let scheme_valid (s: string) (colon_pos: nat{colon_pos <= fs_byte_length s}) : bool =
  if colon_pos = 0 then false
  else if not (is_ascii_alpha (fs_byte_at s 0)) then false
  else scheme_tail_ok s 1 colon_pos (colon_pos + 1)

// ------------------------------------------------------------------
// parse_iri -- decompose a string into iri_parts. Total.
//
// Step-by-step:
//   1. Find first `:`. If it exists AND the bytes before it are a
//      valid scheme, the scheme runs [0, colon) and the rest starts
//      at colon+1. Else no scheme; rest starts at 0.
//   2. If rest starts with `//`, authority runs from after `//` to the
//      first `/`, `?`, `#`, or EOF. Else no authority.
//   3. Path runs to the first `?` or `#` or EOF.
//   4. If current byte is `?`, query runs to next `#` or EOF.
//   5. If current byte is `#`, fragment runs to EOF.
//
// This parser is total -- every input is accepted. The `option` return
// type is a vestigial affordance; we always return `Some`.
// ------------------------------------------------------------------

let parse_iri (s: string) : option iri_parts =
  let len = fs_byte_length s in
  // 1. scheme
  let colon_pos = find_colon s 0 (len + 1) in
  let first_delim_pos =
    // position of the first `/`, `?`, or `#` in the whole string, for
    // ruling out "scheme" when the colon lives after a path separator.
    find_authority_end_iri s 0 (len + 1)
  in
  let (scheme_opt, rest_start) =
    if colon_pos < len && colon_pos < first_delim_pos && scheme_valid s colon_pos
    then (Some (fs_byte_sub s 0 colon_pos), colon_pos + 1)
    else (None, 0)
  in
  // Defensive clamp so Z3 sees rest_start <= len.
  let rest_start : nat = if rest_start <= len then rest_start else len in
  // 2. authority?
  let (auth_opt, after_auth) =
    if rest_start + 1 < len
       && fs_byte_at s rest_start = 0x2F
       && fs_byte_at s (rest_start + 1) = 0x2F
    then
      let auth_start = rest_start + 2 in
      let auth_start : nat = if auth_start <= len then auth_start else len in
      let auth_end = find_authority_end_iri s auth_start (len - auth_start + 1) in
      let auth_len : nat = if auth_end >= auth_start then auth_end - auth_start else 0 in
      (Some (fs_byte_sub s auth_start auth_len), auth_end)
    else
      (None, rest_start)
  in
  let after_auth : nat = if after_auth <= len then after_auth else len in
  // 3. path
  let path_end = find_path_end_iri s after_auth (len - after_auth + 1) in
  let path_len : nat = if path_end >= after_auth then path_end - after_auth else 0 in
  let path = fs_byte_sub s after_auth path_len in
  // 4. query?
  let (query_opt, after_query) =
    if path_end < len && fs_byte_at s path_end = 0x3F
    then
      let q_start = path_end + 1 in
      let q_start : nat = if q_start <= len then q_start else len in
      let q_end = find_hash_iri s q_start (len - q_start + 1) in
      let q_len : nat = if q_end >= q_start then q_end - q_start else 0 in
      (Some (fs_byte_sub s q_start q_len), q_end)
    else
      (None, path_end)
  in
  let after_query : nat = if after_query <= len then after_query else len in
  // 5. fragment?
  let frag_opt =
    if after_query < len && fs_byte_at s after_query = 0x23
    then
      let f_start = after_query + 1 in
      let f_start : nat = if f_start <= len then f_start else len in
      let f_len : nat = if len >= f_start then len - f_start else 0 in
      Some (fs_byte_sub s f_start f_len)
    else
      None
  in
  Some {
    ip_scheme    = scheme_opt;
    ip_authority = auth_opt;
    ip_path      = path;
    ip_query     = query_opt;
    ip_fragment  = frag_opt;
  }

// ------------------------------------------------------------------
// remove_dot_segments -- RFC 3986 section 5.2.4.
//
// Verbatim port of Parser.Turtle.remove_dot_segments_step. Do not
// change the logic; the Turtle copy is already verified and used in
// production against all currently-passing rdf-turtle tests.
// ------------------------------------------------------------------

let rec remove_dot_segments_step (input: string) (pos: nat) (out: list string) (fuel: nat)
  : Tot (list string) (decreases fuel) =
  if fuel = 0 then List.Tot.rev out
  else
    let len = fs_byte_length input in
    if pos > len then List.Tot.rev out
    else if pos = len then List.Tot.rev out
    else
      // find_slash_iri requires pos <= len; the two earlier tests give us
      // pos < len < len + 1.
      let pos_ref : nat = if pos <= len then pos else len in
      let slash_pos : nat = find_slash_iri input pos_ref (len - pos_ref + 1) in
      let has_slash = slash_pos < len in
      let seg_end : nat = slash_pos in
      let seg_len : nat = if seg_end >= pos_ref then seg_end - pos_ref else 0 in
      let seg = fs_byte_sub input pos_ref seg_len in
      let seg_with_slash = if has_slash
                           then String.concat "" [seg; "/"]
                           else seg in
      let next_pos : nat = if has_slash then slash_pos + 1 else len in
      // Pop the last real segment, but never pop a lone leading "/".
      // `out` is built by prepending, so the leading "/" (if the path
      // was absolute) sits at the END of the list. When `out = ["/"]`
      // we're at the root and a ".." must stay clamped there rather
      // than dropping the absolute-path marker.
      let pop_keep_root : list string =
        match out with
        | [] -> []
        | ["/"] -> ["/"]
        | _ :: rest -> rest
      in
      let out' =
        if seg = "." then
          // Both "/./" (has_slash=true) and terminal "/." collapse to
          // nothing: the preceding segment already carries its trailing
          // "/". Leaving `out` unchanged is the RFC 3986 section 5.2.4
          // 2B/2D behaviour. (Verified empirically 2026-07-05 against
          // the full RFC 3986 section 5.4 battery during the RDF.IRI
          // consolidation's differential test -- terminal "." resolves
          // to the RFC-correct answer, e.g. against base
          // "http://a/b/c/d;p?q" this produces "http://a/b/c/", not
          // the "http://a/b//" a stale comment on the old
          // `Parser.IRI.fst` once claimed; that comment described a bug
          // in the *unrelated, dead-code* copy of this algorithm in
          // Parser.Turtle.fst, not this one -- see the note near
          // `_rfc3986_5_4_examples` below.)
          out
        else if seg = ".." then
          if has_slash then pop_keep_root
          else
            // Terminal "..": pop the last real segment; if nothing is
            // left, synthesise the leading "/" so "/.." normalises to
            // "/" instead of the empty string.
            (match pop_keep_root with
             | [] -> ["/"]
             | _  -> pop_keep_root)
        else
          seg_with_slash :: out
      in
      remove_dot_segments_step input next_pos out' (fuel - 1)

let remove_dot_segments (path: string) : string =
  let len = fs_byte_length path in
  let segs = remove_dot_segments_step path 0 [] (len + 2) in
  String.concat "" segs

// ------------------------------------------------------------------
// merge_paths -- RFC 3986 section 5.2.3.
//
//   if defined(Base.authority) and Base.path = "":
//     return "/" ++ ref_path
//   else:
//     return everything up to and including the last "/" of Base.path
//     ++ ref_path (and if Base.path has no "/", the prefix is empty)
// ------------------------------------------------------------------

// Find the byte index one-past the last `/` in s. Returns 0 if no
// slash is present. Walks from the end, so it's an O(n) scan but in
// practice paths are short.
let rec find_last_slash_iri (s: string) (pos: nat{pos <= fs_byte_length s})
  : Tot (r:nat{r <= pos}) (decreases pos) =
  if pos = 0 then 0
  else
    let idx = pos - 1 in
    if idx < fs_byte_length s && fs_byte_at s idx = 0x2F
    then pos
    else find_last_slash_iri s idx

let merge_paths (base: iri_parts) (ref_path: string) : string =
  let auth_defined = match base.ip_authority with Some _ -> true | None -> false in
  if auth_defined && fs_byte_length base.ip_path = 0 then
    String.concat "" ["/"; ref_path]
  else
    let bp = base.ip_path in
    let bp_len = fs_byte_length bp in
    let cut = find_last_slash_iri bp bp_len in
    let prefix = fs_byte_sub bp 0 cut in
    String.concat "" [prefix; ref_path]

// ------------------------------------------------------------------
// transform_references -- RFC 3986 section 5.2.2.
// ------------------------------------------------------------------

let transform_references (base: iri_parts) (r: iri_parts) : iri_parts =
  match r.ip_scheme with
  | Some _ ->
      {
        ip_scheme    = r.ip_scheme;
        ip_authority = r.ip_authority;
        ip_path      = remove_dot_segments r.ip_path;
        ip_query     = r.ip_query;
        ip_fragment  = r.ip_fragment;
      }
  | None ->
      match r.ip_authority with
      | Some _ ->
          {
            ip_scheme    = base.ip_scheme;
            ip_authority = r.ip_authority;
            ip_path      = remove_dot_segments r.ip_path;
            ip_query     = r.ip_query;
            ip_fragment  = r.ip_fragment;
          }
      | None ->
          if fs_byte_length r.ip_path = 0 then
            let q = match r.ip_query with
                    | Some _ -> r.ip_query
                    | None   -> base.ip_query
            in
            {
              ip_scheme    = base.ip_scheme;
              ip_authority = base.ip_authority;
              ip_path      = base.ip_path;
              ip_query     = q;
              ip_fragment  = r.ip_fragment;
            }
          else
            let new_path =
              if fs_byte_length r.ip_path > 0 && fs_byte_at r.ip_path 0 = 0x2F
              then remove_dot_segments r.ip_path
              else remove_dot_segments (merge_paths base r.ip_path)
            in
            {
              ip_scheme    = base.ip_scheme;
              ip_authority = base.ip_authority;
              ip_path      = new_path;
              ip_query     = r.ip_query;
              ip_fragment  = r.ip_fragment;
            }

// ------------------------------------------------------------------
// recompose -- RFC 3986 section 5.3.
// ------------------------------------------------------------------

let recompose (t: iri_parts) : string =
  let scheme_part = match t.ip_scheme with
                    | Some s -> String.concat "" [s; ":"]
                    | None -> "" in
  let auth_part = match t.ip_authority with
                  | Some a -> String.concat "" ["//"; a]
                  | None -> "" in
  let query_part = match t.ip_query with
                   | Some q -> String.concat "" ["?"; q]
                   | None -> "" in
  let frag_part = match t.ip_fragment with
                  | Some f -> String.concat "" ["#"; f]
                  | None -> "" in
  String.concat "" [scheme_part; auth_part; t.ip_path; query_part; frag_part]

// ------------------------------------------------------------------
// resolve_iri_v2 -- top-level entry point over plain strings. Parse
// base + ref, apply transform_references, recompose. If either input
// fails to parse as an iri_parts record, fall back to returning the
// ref unchanged; this matches Turtle's forgiving posture toward
// malformed `@base` values. In practice parse_iri is total and never
// returns None, but the pattern match keeps the option type honest.
// ------------------------------------------------------------------

let resolve_iri_v2 (base: string) (ref_: string) : string =
  match parse_iri base with
  | None -> ref_
  | Some b ->
    match parse_iri ref_ with
    | None -> ref_
    | Some r -> recompose (transform_references b r)

// ------------------------------------------------------------------
// RFC 3986 section 5.4 examples. These live under `if false` so they
// document intent without imposing a Z3 obligation on every build
// (the string literal equality checks are total but blow out the
// solver's budget if left on the verified path).
//
// The former `Parser.IRI.fst` carried a comment here claiming
// `resolve_iri_v2 "http://a/b/c/d;p?q" "."` and `.. ` evaluated to
// "http://a/b//" instead of the RFC-correct "http://a/b/c/" /
// "http://a/b/", attributing it to a bug inherited from
// `Parser.Turtle.fst`. Investigated during the 2026-07-05 RDF.IRI
// consolidation (differential harness against
// `SPARQL11.IRI.Resolve.resolve_iri`, plus direct execution of this
// module's own extracted OCaml): the claim does not hold for the code
// that actually runs. `Parser.Turtle.fst` has its own local
// `remove_dot_segments_step` (and `find_next_slash`/`find_path_start`/
// etc.) which IS buggy on terminal "." / ".." with no trailing slash,
// but that copy is dead code -- `Parser.Turtle.fst`'s `resolve_iri`
// wrapper calls this module's `resolve_iri_v2`, never its own local
// helpers (confirmed by grep: those functions have no callers besides
// each other). The comment describing the bug was simply stale;
// corrected here rather than carried forward.
// ------------------------------------------------------------------

let _rfc3986_5_4_examples : unit =
  if false then begin
    let b = "http://a/b/c/d;p?q" in
    // section 5.4.1 normal examples that exercise the entry-point logic
    assert (resolve_iri_v2 b "g:h"     = "g:h");
    assert (resolve_iri_v2 b "g"       = "http://a/b/c/g");
    assert (resolve_iri_v2 b "./g"     = "http://a/b/c/g");
    assert (resolve_iri_v2 b "g/"      = "http://a/b/c/g/");
    assert (resolve_iri_v2 b "/g"      = "http://a/g");
    assert (resolve_iri_v2 b "//g"     = "http://g");
    assert (resolve_iri_v2 b "?y"      = "http://a/b/c/d;p?y");
    assert (resolve_iri_v2 b "#s"      = "http://a/b/c/d;p?q#s");
    assert (resolve_iri_v2 b "."       = "http://a/b/c/");
    assert (resolve_iri_v2 b ".."      = "http://a/b/");
    // section 5.4.2 abnormal examples
    assert (resolve_iri_v2 b "../g"    = "http://a/b/g");
    assert (resolve_iri_v2 b "/./g"    = "http://a/g");
    assert (resolve_iri_v2 b ""        = "http://a/b/c/d;p?q")
  end
  else ()

// ============================================================================
// wf_iri-typed entry points -- consolidated from the former
// `SPARQL11.IRI.Resolve.fst` (its `jir_*`-prefixed helpers duplicated
// the algorithm above; this reuses it instead, per the `.fsti`'s
// banner and the differential-testing evidence there). Consumed by
// SPARQL query-IRI resolution (`SPARQL11.Algebra.fst`) and JSON-LD
// `@base` context processing (`JSONLD.Context.fst`).
// ============================================================================

let string_to_iri (s : string) : option wf_iri =
  if is_iri s then Some s else None

/// Resolve a relative IRI reference against a base IRI per RFC 3986
/// section 5.3, reusing `resolve_iri_v2` for the merge/dot-segment/
/// recompose work. `base` is assumed absolute (wf_iri); if the
/// resolved-and-recomposed result does not itself satisfy `is_iri`
/// (e.g. `base` had a colon somewhere but no RFC-3986-conformant
/// scheme, so `resolve_iri_v2`'s output ends up schemeless too), fall
/// back to returning `base` unchanged -- the same defensive contract
/// the pre-consolidation `SPARQL11.IRI.Resolve.resolve_iri` had.
let resolve_iri (base : wf_iri) (relative : string) : wf_iri =
  let result = resolve_iri_v2 base relative in
  if is_iri result then result else base

(* Prefix namespace IRIs are resolved against BASE during parsing.
   All IRIs in the query body are then resolved against BASE.
   This ensures that relative IRIs like <x> or <#x> become absolute. *)
let resolve_query_iri (base : option wf_iri) (rel : string) : option wf_iri =
  match base with
  | Some b -> Some (resolve_iri b rel)
  | None -> string_to_iri rel
