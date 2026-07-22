module Parser.JSONLD.Html

// HTML "script extraction" for JSON-LD embedded in HTML documents
// (JSON-LD 1.1 API, "HTML Content Algorithms"; the json-ld html-manifest
// test suite). This is NOT a full HTML parser: per the spec, a
// `<script type="application/ld+json">` element's content is raw text
// (CDATA-like — no HTML entity decoding), so we byte-scan for such
// elements and slice out their content verbatim, then hand the JSON on to
// the ordinary expand / toRdf / compact / flatten algorithms.
//
// Selection (JSON-LD API §"Load document"):
//   * `fragment = Some id` — the script whose `id` attribute equals it.
//   * `extract_all = true` — every ld+json script, combined into a single
//     JSON array (`[ script1 , script2 , ... ]`).
//   * otherwise            — the FIRST ld+json script's content.
// Returns None when no matching script is present (drives the suite's
// negative "no script" cases; malformed JSON is caught downstream when
// the extracted text fails to parse).
//
// Byte-scanned via Parser.FastString, like the other F* format parsers
// (Iron Rule #4). Termination is fuel-bounded: every scan is passed the
// document length as fuel, more than enough for any single left-to-right
// pass, so each recursion trivially `decreases fuel`.

open Parser.FastString
open FStar.List.Tot

// ASCII case fold for a single byte (A-Z -> a-z); other bytes untouched.
let lc_byte (b : nat) : nat = if b >= 0x41 && b <= 0x5A then b + 0x20 else b

// Saturating subtraction: `nat - nat` is `int` in F* (can go negative), so
// slice lengths must go through this to stay `nat`. At every use site the
// positions are already ordered, so the saturating branch is unreachable.
let sat_sub (a b : nat) : nat = if a >= b then a - b else 0

// Case-insensitive match of the lowercase-ASCII literal `pat` at html[pos..].
let rec ci_match_at (pat : string) (plen : nat) (html : string)
                    (hlen pos : nat) (i : nat { i <= plen })
  : Tot bool (decreases (plen - i)) =
  if i >= plen then true
  else if pos + i >= hlen then false
  else if lc_byte (fs_byte_at html (pos + i)) = fs_byte_at pat i
       then ci_match_at pat plen html hlen pos (i + 1)
       else false

// First index >= pos at which the ci-literal `pat` occurs, else None.
let rec ci_find (pat : string) (plen : nat) (html : string)
                (hlen pos : nat) (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 || pos >= hlen then None
  else if ci_match_at pat plen html hlen pos 0 then Some pos
  else ci_find pat plen html hlen (pos + 1) (fuel - 1)

// First index >= pos of the byte `b`, else None.
let rec find_byte (s : string) (slen pos b : nat) (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 || pos >= slen then None
  else if fs_byte_at s pos = b then Some pos
  else find_byte s slen (pos + 1) b (fuel - 1)

// Value of a quoted attribute `name="..."` / `name='...'` in an open-tag
// slice. `name` includes the trailing `=` (e.g. "id=", "href="); `nlen`
// is its byte length.
let extract_attr (opentag : string) (name : string) (nlen : nat) : option string =
  let olen = fs_byte_length opentag in
  match ci_find name nlen opentag olen 0 olen with
  | None -> None
  | Some p ->
    let qpos = p + nlen in
    if qpos >= olen then None
    else
      let q = fs_byte_at opentag qpos in
      if q = 0x22 || q = 0x27 then
        (match find_byte opentag olen (qpos + 1) q olen with
         | None -> None
         | Some ep -> Some (fs_byte_sub opentag (qpos + 1) (sat_sub ep (qpos + 1))))
      else None

let extract_id (opentag : string) : option string = extract_attr opentag "id=" 3

// The `href` of the document's first `<base ... href="...">` element, if
// any (HTML documents may set the base IRI via <base>). Returned verbatim
// — the caller resolves a relative href against the document URL.
let extract_html_base (html : string) : option string =
  let hlen = fs_byte_length html in
  match ci_find "<base" 5 html hlen 0 hlen with
  | None -> None
  | Some bp ->
    (match find_byte html hlen (bp + 5) 0x3E hlen with
     | None -> None
     | Some gt -> extract_attr (fs_byte_sub html bp (sat_sub gt bp + 1)) "href=" 5)

// Collect (id?, content) for every `<script ... application/ld+json ...>`
// element. Positions are monotonically ordered (`>` after `<script`,
// `</script` after the content start), so the length subtractions below
// never underflow at runtime; nat subtraction keeps them well-typed.
let rec collect_scripts (html : string) (hlen pos fuel : nat)
                        (acc : list (option string & string))
  : Tot (list (option string & string)) (decreases fuel) =
  if fuel = 0 then rev acc
  else
    match ci_find "<script" 7 html hlen pos hlen with
    | None -> rev acc
    | Some sp ->
      (match find_byte html hlen (sp + 7) 0x3E hlen with   // 0x3E = '>'
       | None -> rev acc
       | Some gt ->
         let opentag = fs_byte_sub html sp (sat_sub gt sp + 1) in
         let cstart = gt + 1 in
         (match ci_find "</script" 8 html hlen cstart hlen with
          | None -> rev acc
          | Some ep ->
            let content = fs_byte_sub html cstart (sat_sub ep cstart) in
            let otlen = fs_byte_length opentag in
            let is_ld = Some? (ci_find "application/ld+json" 19 opentag otlen 0 otlen) in
            let acc' = if is_ld then (extract_id opentag, content) :: acc else acc in
            collect_scripts html hlen (ep + 8) (fuel - 1) acc'))

let rec find_script_by_id (scripts : list (option string & string)) (fid : string)
  : option string =
  match scripts with
  | [] -> None
  | (Some i, c) :: rest -> if i = fid then Some c else find_script_by_id rest fid
  | (None,   _) :: rest -> find_script_by_id rest fid

let is_ws (b : nat) : bool = b = 0x20 || b = 0x09 || b = 0x0A || b = 0x0D

// First / last index of a non-whitespace byte in s, else None.
let rec first_nonws (s : string) (slen pos fuel : nat) : Tot (option nat) (decreases fuel) =
  if fuel = 0 || pos >= slen then None
  else if is_ws (fs_byte_at s pos) then first_nonws s slen (pos + 1) (fuel - 1)
  else Some pos
let rec last_nonws (s : string) (slen : nat) (pos : int) (fuel : nat) : Tot (option nat) (decreases fuel) =
  if fuel = 0 || pos < 0 then None
  else
    let p : nat = if pos >= 0 && pos < slen then pos else 0 in
    if pos >= 0 && pos < slen && not (is_ws (fs_byte_at s p)) then Some p
    else last_nonws s slen (pos - 1) (fuel - 1)

// When an extractAllScripts member is itself a top-level JSON array, its
// ELEMENTS are appended to the combined array (spliced), not nested — so
// strip the outer `[ ... ]`. A non-array (object) member is kept whole.
let splice_if_array (c : string) : string =
  let clen = fs_byte_length c in
  match first_nonws c clen 0 clen, last_nonws c clen (clen - 1) clen with
  | Some i, Some j ->
    if fs_byte_at c i = 0x5B && fs_byte_at c j = 0x5D && j > i + 1
    then fs_byte_sub c (i + 1) (sat_sub j (i + 1))
    else c
  | _, _ -> c

// Contents joined with commas (interior of the `[ ... ]` array).
let rec join_contents (scripts : list (option string & string)) : string =
  match scripts with
  | [] -> ""
  | [(_, c)] -> splice_if_array c
  | (_, c) :: rest -> splice_if_array c ^ "," ^ join_contents rest

let json_array_of (scripts : list (option string & string)) : string =
  "[" ^ join_contents scripts ^ "]"

// Extract the JSON-LD source text from an HTML document.
let extract_jsonld_from_html (html : string) (fragment : option string) (extract_all : bool)
  : option string =
  let hlen = fs_byte_length html in
  let scripts = collect_scripts html hlen 0 hlen [] in
  match fragment with
  | Some fid -> find_script_by_id scripts fid
  | None ->
    (match scripts with
     // No fragment and no script. With extractAllScripts this is the empty
     // document `[]` (expands to []); WITHOUT it, loading a document that
     // carries no JSON-LD is an error (None) — the suite distinguishes the
     // two. (A missing FRAGMENT target above is always the error case.)
     | [] -> if extract_all then Some "[]" else None
     | first :: _ -> if extract_all then Some (json_array_of scripts) else Some (snd first))
