/-
L4Factoidal.Syntax.IriResolve — RFC 3986 reference resolution.

Port of `formal/fstar/RDF.IRI.fst` (the consolidated IRI module that
`Parser.Turtle.fst`'s `resolve_iri` wrapper and
`SPARQL11.IRI.Resolve.fst` both delegate to). Implements:

  RFC 3986 §3   — the generic-syntax decomposition (`parseIri`)
  RFC 3986 §5.2.2 — `transform_references`  (`transformReferences`)
  RFC 3986 §5.2.3 — `merge`                 (`mergePaths`)
  RFC 3986 §5.2.4 — `remove_dot_segments`   (`removeDotSegments`)
  RFC 3986 §5.3   — component recomposition (`recompose`)

Turtle, TriG, and the W3C manifests are full of relative IRI
references resolved against a document base (`@base` / `BASE` /
the retrieval IRI), so this module is a prerequisite for the Turtle
port, not an optional extra.

F* → Lean correspondences:
  * The F* source scans BYTES through the `Parser.FastString`
    `assume val` layer (`fs_byte_at` / `fs_byte_sub` / `fs_byte_length`)
    with an explicit `fuel : nat` on every scanner
    (`find_colon`, `find_authority_end_iri`, `find_path_end_iri`,
    `find_hash_iri`, `find_slash_iri`, `find_last_slash_iri`,
    `scheme_tail_ok`). Here every one of those collapses into a
    `List.span` / `List.dropWhile` / `List.all` over `List Char` —
    core-Lean total functions needing no fuel, and codepoint-correct
    rather than byte-correct (all the delimiters involved are ASCII,
    so the two agree, but the Lean form has no `assume val` under it).
  * `remove_dot_segments_step` KEEPS its fuel parameter: it is the one
    loop whose recursive argument is not a syntactic sub-term of its
    input (the tail comes back out of a `span`), exactly the situation
    the F* source used `decreases fuel` for. Fuel is `path.length + 2`
    at the top-level call, mirroring the F* `len + 2`.
  * `parse_iri : option iri_parts` in F* is total and never returns
    `None` (the F* source says so in a comment); this port drops the
    vestigial `Option` and returns `IriParts` directly.

The RFC 3986 §5.4 example battery — all 24 normal and all 20 abnormal
examples — is checked below as `#guard`s, so a regression in any of
the five phases is a BUILD failure rather than a silently wrong IRI.
The F* source carries the same battery but parked behind `if false`
to keep it off Z3's budget; Lean evaluates them during elaboration at
no proof cost, so this port checks strictly more than the original.
-/

namespace L4Factoidal.Syntax

/-! ## §3 — generic syntax components

`URI = scheme ":" hier-part [ "?" query ] [ "#" fragment ]`, where the
hierarchical part optionally carries an authority. Every component is
kept in its DECODED-DELIMITER form: `scheme` without its `:`,
`authority` without its `//`, `query` without its `?`, `fragment`
without its `#`; `path` keeps its leading `/` when it has one, since
`transformReferences` branches on exactly that. Port of the F* record
`iri_parts`. -/

/-- The five RFC 3986 §3 components of an IRI reference. `path` is
never optional (RFC 3986: "The path component is always defined for a
URI, though the defined path may be empty"). -/
structure IriParts where
  scheme    : Option String
  authority : Option String
  path      : String
  query     : Option String
  fragment  : Option String
  deriving DecidableEq, Repr

/-! ## Scheme validity — RFC 3986 §3.1

`scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`

If the first `:` in the reference is not preceded by a valid scheme,
the whole string is a RELATIVE reference (this is what makes
`this:is/not:a:scheme` — a path containing colons — resolve as a path
rather than as an absolute IRI). Port of `scheme_valid` /
`is_ascii_alpha` / `is_scheme_tail_byte` / `scheme_tail_ok`. -/

/-- ASCII letter. Port of `is_ascii_alpha`. -/
def isAsciiAlpha (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z')

/-- A character legal after the first in a scheme (RFC 3986 §3.1).
Port of `is_scheme_tail_byte`. -/
def isSchemeTailChar (c : Char) : Bool :=
  isAsciiAlpha c || ('0' ≤ c ∧ c ≤ '9') || c == '+' || c == '-' || c == '.'

/-- Is this character run a syntactically valid scheme? Port of
`scheme_valid` (which returns `false` for the empty run — the F*
source's `if colon_pos = 0 then false`). -/
def schemeValid : List Char → Bool
  | []      => false
  | c :: cs => isAsciiAlpha c && cs.all isSchemeTailChar

/-! ## §3 decomposition — `parseIri`

The five-step walk the F* `parse_iri` performs, with each of its
fuel-bounded byte scanners replaced by one `List.span`:

  1. scheme    — up to the first `:`, but only if that `:` precedes
                 every `/`, `?`, `#` AND the run before it is a valid
                 scheme (`find_colon` + `find_authority_end_iri` +
                 `scheme_valid`);
  2. authority — after a literal `//`, up to the first `/`, `?`, `#`
                 (`find_authority_end_iri`);
  3. path      — up to the first `?` or `#` (`find_path_end_iri`);
  4. query     — after `?`, up to the first `#` (`find_hash_iri`);
  5. fragment  — after `#`, to the end.

Total on every input: the F* source's `option` return is always
`Some`, so this port returns `IriParts` outright. -/

/-- Characters that terminate the "could still be a scheme" prefix:
the scheme's own `:` plus the three component delimiters. A `/`, `?`,
or `#` reached before any `:` proves the reference is relative. -/
def isSchemeStopChar (c : Char) : Bool :=
  c == ':' || c == '/' || c == '?' || c == '#'

/-- Decompose an IRI reference into its RFC 3986 §3 components. Port
of `parse_iri`. -/
def parseIri (s : String) : IriParts :=
  let cs := s.toList
  -- 1. scheme
  let (schemeOpt, rest0) :=
    let (before, after) := cs.span (fun c => !isSchemeStopChar c)
    match after with
    | ':' :: tl => if schemeValid before then (some (String.ofList before), tl) else (none, cs)
    | _         => (none, cs)
  -- 2. authority (only after a literal "//" with at least two chars present)
  let (authOpt, rest1) :=
    match rest0 with
    | '/' :: '/' :: tl =>
        let (a, r) := tl.span (fun c => !(c == '/' || c == '?' || c == '#'))
        (some (String.ofList a), r)
    | _ => (none, rest0)
  -- 3. path
  let (pathCs, rest2) := rest1.span (fun c => !(c == '?' || c == '#'))
  -- 4. query
  let (queryOpt, rest3) :=
    match rest2 with
    | '?' :: tl =>
        let (q, r) := tl.span (fun c => !(c == '#'))
        (some (String.ofList q), r)
    | _ => (none, rest2)
  -- 5. fragment
  let fragOpt :=
    match rest3 with
    | '#' :: tl => some (String.ofList tl)
    | _         => none
  { scheme := schemeOpt, authority := authOpt, path := String.ofList pathCs,
    query := queryOpt, fragment := fragOpt }

/-! ## §5.2.4 — `remove_dot_segments`

The F* source works over a "segment plus its trailing slash" list
rather than over bare segments, which is what makes the terminal-`.`
and terminal-`..` cases come out right (RFC 3986 §5.2.4 steps 2B/2D
and 2C/2E respectively). Two details of the F* source that this port
keeps EXACTLY, because the whole §5.4 abnormal battery depends on
them:

  * `popKeepRoot` never pops a lone leading `"/"`. The output list is
    built by PREPENDING, so an absolute path's leading `/` sits at the
    END; `["/"]` means "at the root", and a further `..` clamps there
    (RFC 3986 §5.2.4's note that the algorithm cannot ascend past the
    root) instead of dropping the absolute-path marker. This is what
    makes `../../../g` against `http://a/b/c/d;p?q` resolve to
    `http://a/g` and not to `http://ag`.
  * a terminal `..` with nothing left to pop SYNTHESISES `["/"]`, so
    `/..` normalises to `/` rather than to the empty string.

An older comment on the retired `Parser.IRI.fst` claimed this
algorithm mishandled terminal `.` / `..`; the F* source records
(2026-07-05) that the claim described a DEAD local copy inside
`Parser.Turtle.fst`, not this algorithm. The §5.4 `#guard`s at the
bottom of this file settle the question by execution. -/

/-- One step of the §5.2.4 loop: split off the next segment (up to and
excluding the next `/`), classify it, and either drop it (`.`), pop
(`..`), or push it. `fuel` bounds the loop exactly as the F* source's
`decreases fuel` does — the remaining-input argument comes out of a
`span`, so it is not a syntactic sub-term Lean's structural check can
use. Port of `remove_dot_segments_step`. -/
def removeDotSegmentsStep : Nat → List Char → List String → List String
  | 0,        _,  out => out.reverse
  | _,        [], out => out.reverse
  | fuel + 1, cs, out =>
      let (segCs, afterSeg) := cs.span (fun c => !(c == '/'))
      let hasSlash := match afterSeg with | '/' :: _ => true | _ => false
      let next     := match afterSeg with | _ :: tl  => tl    | []  => []
      let seg := String.ofList segCs
      -- Pop the last real segment, but never pop a lone leading "/".
      let popKeepRoot : List String :=
        match out with
        | []       => []
        | ["/"]    => ["/"]
        | _ :: tl  => tl
      let out' :=
        if seg == "." then
          out
        else if seg == ".." then
          if hasSlash then popKeepRoot
          else match popKeepRoot with
               | [] => ["/"]
               | l  => l
        else
          (if hasSlash then seg ++ "/" else seg) :: out
      removeDotSegmentsStep fuel next out'

/-- RFC 3986 §5.2.4: remove `.` and `..` segments from a path. Port of
`remove_dot_segments` (fuel `len + 2`, as in the F* source). -/
def removeDotSegments (path : String) : String :=
  String.join (removeDotSegmentsStep (path.length + 2) path.toList [])

/-! ## §5.2.3 — `merge`

```
if defined(Base.authority) and Base.path is empty:
    return "/" ++ Reference.path
else:
    return (Base.path up to and including its last "/") ++ Reference.path
```
Port of `merge_paths` / `find_last_slash_iri`. -/

/-- Everything up to AND INCLUDING the last `/`, or `""` when there is
no `/`. Port of `find_last_slash_iri` + the `fs_byte_sub` that follows
it — a reverse-then-`dropWhile` here, since Lean lists walk forwards. -/
def upToLastSlash (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => !(c == '/'))).reverse

/-- RFC 3986 §5.2.3 merge. Port of `merge_paths`. -/
def mergePaths (base : IriParts) (refPath : String) : String :=
  match base.authority with
  | some _ => if base.path.isEmpty then "/" ++ refPath
              else upToLastSlash base.path ++ refPath
  | none   => upToLastSlash base.path ++ refPath

/-! ## §5.2.2 — `transform_references`

The RFC's pseudo-code, case for case. This port is STRICT (RFC 3986
§5.2.2's non-strict variant, which ignores a reference scheme equal to
the base scheme, is deliberately not implemented — the F* source is
strict too, which is why `http:g` against `http://a/b/c/d;p?q`
resolves to `http:g`, the §5.4 abnormal answer for a strict parser). -/

/-- RFC 3986 §5.2.2 reference transformation. Port of
`transform_references`. -/
def transformReferences (base r : IriParts) : IriParts :=
  match r.scheme with
  | some _ =>
      { scheme := r.scheme, authority := r.authority,
        path := removeDotSegments r.path, query := r.query, fragment := r.fragment }
  | none =>
      match r.authority with
      | some _ =>
          { scheme := base.scheme, authority := r.authority,
            path := removeDotSegments r.path, query := r.query, fragment := r.fragment }
      | none =>
          if r.path.isEmpty then
            { scheme := base.scheme, authority := base.authority, path := base.path,
              query := (match r.query with | some _ => r.query | none => base.query),
              fragment := r.fragment }
          else
            let newPath :=
              if r.path.startsWith "/" then removeDotSegments r.path
              else removeDotSegments (mergePaths base r.path)
            { scheme := base.scheme, authority := base.authority, path := newPath,
              query := r.query, fragment := r.fragment }

/-! ## §5.3 — component recomposition -/

/-- RFC 3986 §5.3: reassemble components into a reference string. Port
of `recompose`. -/
def recompose (t : IriParts) : String :=
  (match t.scheme    with | some s => s ++ ":"  | none => "") ++
  (match t.authority with | some a => "//" ++ a | none => "") ++
  t.path ++
  (match t.query     with | some q => "?" ++ q  | none => "") ++
  (match t.fragment  with | some f => "#" ++ f  | none => "")

/-! ## §5.2 — the whole resolution -/

/-- Resolve `ref` against `base` (RFC 3986 §5.2: parse both, transform,
recompose). Port of `resolve_iri_v2`, which is what
`Parser.Turtle.resolve_iri` and `SPARQL11.IRI.Resolve.resolve_iri` both
call. Total: an unparseable base or reference cannot arise, since
`parseIri` accepts every string. -/
def resolveIri (base ref : String) : String :=
  recompose (transformReferences (parseIri base) (parseIri ref))

/-- Resolve against an OPTIONAL base — the Turtle/TriG situation, where
a document without a `@base` directive and without a retrieval IRI
leaves relative references unresolved. Port of `resolve_query_iri`'s
shape (the F* source returns the reference unchanged when there is no
base; a `NegativeSyntaxTest` on the resulting non-absolute IRI is then
raised one layer up, by `RDF.isIri`). -/
def resolveAgainst? (base : Option String) (ref : String) : String :=
  match base with
  | none   => ref
  | some b => resolveIri b ref

/-! ## RFC 3986 §5.4 — the reference-resolution examples

All of §5.4.1 (24 "normal" examples) and all of §5.4.2 (20 "abnormal"
examples) against the RFC's base `http://a/b/c/d;p?q`, evaluated at
elaboration time. A regression in `parseIri`, `removeDotSegments`,
`mergePaths`, `transformReferences`, or `recompose` breaks the BUILD.

The two `#guard`s the RFC marks as parser-dependent are given their
STRICT answers (`http:g` stays `http:g`), matching the F* source. -/

/-- The RFC 3986 §5.4 base URI. -/
def rfcBase : String := "http://a/b/c/d;p?q"

-- §5.4.1 Normal Examples
#guard resolveIri rfcBase "g:h"           == "g:h"
#guard resolveIri rfcBase "g"             == "http://a/b/c/g"
#guard resolveIri rfcBase "./g"           == "http://a/b/c/g"
#guard resolveIri rfcBase "g/"            == "http://a/b/c/g/"
#guard resolveIri rfcBase "/g"            == "http://a/g"
#guard resolveIri rfcBase "//g"           == "http://g"
#guard resolveIri rfcBase "?y"            == "http://a/b/c/d;p?y"
#guard resolveIri rfcBase "g?y"           == "http://a/b/c/g?y"
#guard resolveIri rfcBase "#s"            == "http://a/b/c/d;p?q#s"
#guard resolveIri rfcBase "g#s"           == "http://a/b/c/g#s"
#guard resolveIri rfcBase "g?y#s"         == "http://a/b/c/g?y#s"
#guard resolveIri rfcBase ";x"            == "http://a/b/c/;x"
#guard resolveIri rfcBase "g;x"           == "http://a/b/c/g;x"
#guard resolveIri rfcBase "g;x?y#s"       == "http://a/b/c/g;x?y#s"
#guard resolveIri rfcBase ""              == "http://a/b/c/d;p?q"
#guard resolveIri rfcBase "."             == "http://a/b/c/"
#guard resolveIri rfcBase "./"            == "http://a/b/c/"
#guard resolveIri rfcBase ".."            == "http://a/b/"
#guard resolveIri rfcBase "../"           == "http://a/b/"
#guard resolveIri rfcBase "../g"          == "http://a/b/g"
#guard resolveIri rfcBase "../.."         == "http://a/"
#guard resolveIri rfcBase "../../"        == "http://a/"
#guard resolveIri rfcBase "../../g"       == "http://a/g"

-- §5.4.2 Abnormal Examples
#guard resolveIri rfcBase "../../../g"    == "http://a/g"
#guard resolveIri rfcBase "../../../../g" == "http://a/g"
#guard resolveIri rfcBase "/./g"          == "http://a/g"
#guard resolveIri rfcBase "/../g"         == "http://a/g"
#guard resolveIri rfcBase "g."            == "http://a/b/c/g."
#guard resolveIri rfcBase ".g"            == "http://a/b/c/.g"
#guard resolveIri rfcBase "g.."           == "http://a/b/c/g.."
#guard resolveIri rfcBase "..g"           == "http://a/b/c/..g"
#guard resolveIri rfcBase "./../g"        == "http://a/b/g"
#guard resolveIri rfcBase "./g/."         == "http://a/b/c/g/"
#guard resolveIri rfcBase "g/./h"         == "http://a/b/c/g/h"
#guard resolveIri rfcBase "g/../h"        == "http://a/b/c/h"
#guard resolveIri rfcBase "g;x=1/./y"     == "http://a/b/c/g;x=1/y"
#guard resolveIri rfcBase "g;x=1/../y"    == "http://a/b/c/y"
#guard resolveIri rfcBase "g?y/./x"       == "http://a/b/c/g?y/./x"
#guard resolveIri rfcBase "g?y/../x"      == "http://a/b/c/g?y/../x"
#guard resolveIri rfcBase "g#s/./x"       == "http://a/b/c/g#s/./x"
#guard resolveIri rfcBase "g#s/../x"      == "http://a/b/c/g#s/../x"
-- Strict parser (RFC 3986 §5.4.2's parser-dependent pair):
#guard resolveIri rfcBase "http:g"        == "http:g"
#guard resolveIri rfcBase "http:"         == "http:"

/-! ### Component-decomposition checks (RFC 3986 §3)

A relative reference whose path contains a colon must NOT be read as
having a scheme — the colon is only a scheme delimiter when it precedes
every `/`, `?`, `#` and the run before it is a valid scheme. -/

#guard (parseIri "this:is/a:path").scheme == some "this"
#guard (parseIri "1nvalid:x").scheme == none
#guard (parseIri "no/colon:here").scheme == none
#guard (parseIri "no?colon:here").scheme == none
#guard (parseIri "http://ex.org/p?q#f").authority == some "ex.org"
#guard (parseIri "http://ex.org/p?q#f").path == "/p"
#guard (parseIri "http://ex.org/p?q#f").query == some "q"
#guard (parseIri "http://ex.org/p?q#f").fragment == some "f"
#guard (parseIri "http://ex.org").path == ""
#guard (parseIri "mailto:x@example.org").authority == none
#guard (parseIri "").path == ""

/-! ### `remove_dot_segments` directly (RFC 3986 §5.2.4 worked examples) -/

#guard removeDotSegments "/a/b/c/./../../g" == "/a/g"
#guard removeDotSegments "mid/content=5/../6" == "mid/6"
#guard removeDotSegments "/../" == "/"
#guard removeDotSegments "/.." == "/"
#guard removeDotSegments "" == ""
#guard removeDotSegments "/a/b/" == "/a/b/"

/-! ### Bases without an authority, and empty-path bases (RFC 3986 §5.2.3) -/

#guard resolveIri "http://ex.org" "g" == "http://ex.org/g"
#guard resolveIri "urn:example:base" "g" == "urn:g"
#guard resolveIri "file:///tmp/x/y" "z" == "file:///tmp/x/z"

end L4Factoidal.Syntax
