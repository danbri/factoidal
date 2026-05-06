module SPARQL.HTTP.StaticFiles

// Static-file serving primitives — the "decision" parts.
//
// Migrated from factoidal_http.ml's content_type_for_path and
// path_has_dotdot. Both are pure string analysis; both encode policy
// (file-extension -> MIME type mapping; "no path traversal") that
// belongs in F* per Iron Rule #1.
//
// The actual file I/O (open, read, stat) stays in the OCaml caller
// because that's a syscall.

module S = FStar.String

// ---------------------------------------------------------------
// content_type_for_path
//
// Maps a path's extension to an HTTP Content-Type response header
// value. Restricted to the file types the server actually serves
// from the demo / web directories. Anything else falls back to
// application/octet-stream so the browser doesn't auto-execute
// unknown content.
// ---------------------------------------------------------------

let ends_with (s : string) (suf : string) : Tot bool =
  let lp = S.length s in
  let ls = S.length suf in
  if lp >= ls then S.sub s (lp - ls) ls = suf
  else false

let content_type_for_path (path : string) : Tot string =
  let p = S.lowercase path in
  if ends_with p ".html" || ends_with p ".htm"
    then "text/html; charset=utf-8"
  else if ends_with p ".css"
    then "text/css; charset=utf-8"
  else if ends_with p ".js" || ends_with p ".mjs"
    then "application/javascript; charset=utf-8"
  else if ends_with p ".json"
    then "application/json; charset=utf-8"
  else if ends_with p ".svg"
    then "image/svg+xml; charset=utf-8"
  else if ends_with p ".png"
    then "image/png"
  else if ends_with p ".jpg" || ends_with p ".jpeg"
    then "image/jpeg"
  else if ends_with p ".ico"
    then "image/x-icon"
  else if ends_with p ".txt" || ends_with p ".md"
    then "text/plain; charset=utf-8"
  else if ends_with p ".ttl"
    then "text/turtle; charset=utf-8"
  else if ends_with p ".nt"
    then "application/n-triples; charset=utf-8"
  else if ends_with p ".nq"
    then "application/n-quads; charset=utf-8"
  else "application/octet-stream"

// ---------------------------------------------------------------
// path_has_dotdot
//
// Coarse path-traversal guard: the URL path must not contain "..".
// We only ever concatenate the URL path onto a resolved demo root,
// so this is sufficient — no full URL canonicalisation needed.
//
// Return true iff the input contains the byte sequence "..".
// ---------------------------------------------------------------

let rec contains_dotdot_at (s : string) (i : nat) : Tot bool (decreases (S.length s - i)) =
  let n = S.length s in
  if i + 2 > n then false
  else if S.sub s i 2 = ".." then true
  else if i + 1 > n then false
  else contains_dotdot_at s (i + 1)

let path_has_dotdot (p : string) : Tot bool =
  contains_dotdot_at p 0
