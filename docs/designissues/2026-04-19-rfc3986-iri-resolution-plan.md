# RFC 3986 §5.2 IRI resolution — scoping note

**Date:** 2026-04-19. Read-only planning.
**Scope:** The four Turtle/TriG tests `IRI-resolution-01/02/07/08`
(and their TriG siblings) exercise ~165 distinct RFC 3986 §5.2
relative-reference shapes. Our current `resolve_iri` in
`Parser.Turtle.fst` gets "count matches, content mismatch" on all
four — that is, the parser emits the right number of triples, but
many of the resolved IRIs are wrong.

## 1. What the tests cover

Four Turtle files, each with a different `@base`:

| File | Base IRI | Rel-refs | Key feature of this base |
|---|---|---:|---|
| IRI-resolution-01 | `http://a/bb/ccc/d;p?q` | 41 | Base has query; base path ends without slash; non-empty query |
| IRI-resolution-02 | `http://a/bb/ccc/d/` | 41 | Base path ends with slash; no query |
| IRI-resolution-07 | `file:///a/bb/ccc/d;p?q` | 42 | `file:` scheme; empty authority (`///`); includes strict-mode scheme-preserving ref `http:g` |
| IRI-resolution-08 | `http://abc/def/ghi`, `http://ab//de//ghi`, `http://abc/d:f/ghi` | 12 | Three different bases; empty path segments (`//`) and colon in path |

Each TriG test of the same name wraps the same cases in a graph
block; the resolver is shared between Turtle and TriG so fixing one
fixes both.

**Total relative-reference cases across the four files: ~165.** Plus
the same set in TriG → another ~165 tests worth of resolver coverage.

## 2. The RFC 3986 §5.2 algorithm (the real one)

The spec defines this in four steps, and all four need to be
implemented faithfully:

- **§5.2.1 Pre-parse base URI** into (scheme, authority, path, query,
  fragment) five-tuple. Required for every resolution.
- **§5.2.2 Transform References.** The big state machine. Given a
  parsed `R = (R.scheme, R.authority, R.path, R.query, R.fragment)`
  and `Base = (B.scheme, B.authority, B.path, B.query, B.fragment)`,
  produce `T`. Branches on:
  - R.scheme defined → T = R (absolute ref, just normalise dot-segs
    in R.path)
  - else R.authority defined → T.scheme = B.scheme; T.authority =
    R.authority; T.path = remove_dot_segments(R.path); T.query =
    R.query
  - else R.path empty → T.scheme = B.scheme, T.authority = B.authority,
    T.path = B.path; if R.query defined, T.query = R.query; else
    T.query = B.query. T.fragment = R.fragment. **(This is the
    fragment-only / empty-ref / query-only case.)**
  - else R.path starts with "/" → T.path = remove_dot_segments(R.path)
  - else → T.path = remove_dot_segments(merge(B, R.path)); T.query =
    R.query
  - In all cases, T.fragment = R.fragment, T.scheme = B.scheme.
- **§5.2.3 Merge Paths.** If Base has an authority and empty path,
  return `"/" + R.path`; else return "everything up to and including
  the last `/` of B.path" + R.path.
- **§5.2.4 Remove Dot Segments.** The two-buffer algorithm we already
  have (`remove_dot_segments_step`).
- **§5.3 Component Recomposition.** Reassemble T back into a string.

## 3. Current code — what it does, what it gets wrong

`Parser.Turtle.fst` `resolve_iri` (line 232) branches on the *first
character* of `rel`, not on a parsed (scheme, authority, path, query,
fragment). Specifically:

```
if rel is empty             → return base_iri unchanged
else if rel has colon       → return rel (absolute)
else if rel starts '#'      → strip base fragment, append rel
else if rel starts '/'      → authority + remove_dot_segments(rel)
else                        → strip base query+fragment, take base_dir,
                              concat with rel, remove_dot_segments
```

This skips, misroutes, or mishandles **several RFC 3986 branches**:

### 3.1 Bugs I expect, by shape

Walk each shape through the current code, mentally, against
IRI-resolution-01 (base `http://a/bb/ccc/d;p?q`).

| s0XX | Rel ref | Expected | What current code does | OK? |
|---|---|---|---|---|
| s001 | `g:h` | `g:h` | has-colon → `g:h` | OK |
| s002 | `g` | `http://a/bb/ccc/g` | no-slash branch: strip `?q` → `http://a/bb/ccc/d;p`, base_dir up to last `/` → `http://a/bb/ccc/`, merge → `http://a/bb/ccc/g` | OK |
| s007 | `?y` | `http://a/bb/ccc/d;p?y` | **BUG**: no-slash branch strips query, base_dir cuts to `http://a/bb/ccc/`, merges with `?y` → `http://a/bb/ccc/?y`. Expected: **keep** base path `d;p`, replace query. | **WRONG** |
| s009 | `#s` | `http://a/bb/ccc/d;p?q#s` | frag-only branch: strip base fragment (none) → `http://a/bb/ccc/d;p?q`, append `#s` → correct | OK |
| s011 | `g?y#s` | `http://a/bb/ccc/g?y#s` | no-slash branch: base_dir=`http://a/bb/ccc/`, merged=`http://a/bb/ccc/g?y#s`, `remove_dot_segments` runs on path+query+fragment together — **BUG**: dot-segment algorithm treats `?` and `#` as path chars. For this case there are no dots so we survive, but for s038 `g?y/./x` → expected `http://a/bb/ccc/g?y/./x` (dots inside query are **not** removed), our code would try to normalise them. | **WRONG for s038** |
| s015 | `<>` (empty) | `http://a/bb/ccc/d;p?q` | empty-ref branch returns `base_iri` unchanged → correct | OK |
| s016 | `.` | `http://a/bb/ccc/` | no-slash branch: merged=`http://a/bb/ccc/.`, remove_dot_segments → `http://a/bb/ccc/` | OK (probably) |
| s017 | `./` | `http://a/bb/ccc/` | no-slash branch: merged=`http://a/bb/ccc/./`, dot seg → `http://a/bb/ccc/` | OK |
| s018 | `..` | `http://a/bb/` | merged=`http://a/bb/ccc/..`, dot seg → `http://a/bb/` | OK (probably) |
| s026 | `/./g` | `http://a/g` | abs-path branch: authority+`remove_dot_segments("/./g")` → `http://a/g` | OK |
| s027 | `/../g` | `http://a/g` | similarly → `http://a/g` | OK |
| s028 | `g.` | `http://a/bb/ccc/g.` | no-slash branch: merged=`http://a/bb/ccc/g.`, dot-seg — segment `g.` is **not** `.` or `..`, so it stays. | OK (check the code's `seg = "."` literal comparison — good, it checks exact match) |
| s029 | `.g` | `http://a/bb/ccc/.g` | same logic, `.g` isn't `.` or `..` → OK |
| s030 | `g..` | `http://a/bb/ccc/g..` | OK |
| s031 | `..g` | `http://a/bb/ccc/..g` | OK |
| s036 | `g;x=1/./y` | `http://a/bb/ccc/g;x=1/y` | merged=`http://a/bb/ccc/g;x=1/./y`, dot seg collapses `./` → `http://a/bb/ccc/g;x=1/y` | OK |
| s038 | `g?y/./x` | `http://a/bb/ccc/g?y/./x` | **BUG**: merged contains `?y/./x`; our dot-seg runs over the **whole merged string** and removes `/./` inside the query. | **WRONG** |
| s039 | `g?y/../x` | `http://a/bb/ccc/g?y/../x` | same bug | **WRONG** |
| s040 | `g#s/./x` | `http://a/bb/ccc/g#s/./x` | same bug (fragment) | **WRONG** |
| s041 | `g#s/../x` | `http://a/bb/ccc/g#s/../x` | same bug | **WRONG** |
| s006 | `//g` | `http://g` | no-slash branch sees first char `/`, takes abs-path branch: authority=`http://a`, `remove_dot_segments("//g")` → `//g`, concat → `http://a//g`. **Expected `http://g`** (network-path ref). | **WRONG** |
| s012 | `;x` | `http://a/bb/ccc/;x` | no-slash branch: merged=`http://a/bb/ccc/;x`, no dots, → `http://a/bb/ccc/;x` | OK |

### 3.2 Catalogue of shapes in IRI-resolution-01 (base has query `?q`)

Grouping the 41 rel-refs in `-01.ttl` by resolution strategy needed:

| Shape | Examples (sNNN) | Count | Our code | Status |
|---|---|---:|---|---|
| Absolute (has colon) | s001 | 1 | return as-is | OK |
| Empty ref `<>` | s015 | 1 | return base unchanged | OK — but **spec says** drop fragment only, keep path+query+scheme+auth. We return full base including fragment. Base 01 has no fragment, so we survive here. (Bug latent — see §3.3.) |
| Fragment-only `#s` | s009 | 1 | strip base fragment, append | OK |
| Query-only `?y` | s007 | 1 | strip base query, treat as path ref | **WRONG** — should keep base path, replace query |
| Path with query+fragment (no dots) | s008, s010, s011, s013, s014 | 5 | merged, dot-seg over whole | OK (no dots inside query/frag) |
| Path with dots inside query | s038, s039 | 2 | dot-seg over whole | **WRONG** |
| Path with dots inside fragment | s040, s041 | 2 | dot-seg over whole | **WRONG** |
| Net-path `//g` | s006 | 1 | abs-path branch produces wrong result | **WRONG** |
| Abs-path `/g`, `/./g`, `/../g` | s005, s026, s027 | 3 | abs-path + dot-seg | OK |
| Rel path `g`, `g/`, `./g`, `../g` etc. | s002–s004, s020, s023–s025 | 7 | merge + dot-seg | OK |
| `.` / `./` / `..` / `../` as rel | s016–s019, s021, s022 | 6 | merge + dot-seg | OK |
| Path-internal `./`/`../` | s032–s037 | 6 | merge + dot-seg | OK |
| Leading `;x` matrix | s012 | 1 | merge (no dot) | OK |
| Rel with query `g?y`, `;x?y` etc. | s008, s014 | 2 | merge + dot-seg | OK (no dots in query) |
| Rel with fragment `g#s` etc. | s010, s011 | 2 | same | OK (no dots in fragment) |
| Leading dots not a dot-seg (`g.`, `.g`, `g..`, `..g`) | s028–s031 | 4 | segment literal match `.` or `..` catches only exact | OK |
| (Plus s042: `http:g` strict-mode — commented out) | — | — | — | — |

Current failing: **~7 of 41** in `-01`. Plus the subtle empty-ref
"returns full base" behaviour that happens to be right for -01 but
wrong for -07 (see §3.3).

### 3.3 IRI-resolution-07 (file:/// base, includes strict scheme `http:g`)

Base: `file:///a/bb/ccc/d;p?q`. The `file:` scheme has an **empty
authority** (`file://` + `/a/...`). Our `find_path_start` should
handle this — it looks for the first `/` after `scheme://`. Given
`file:///a/bb/...`, `find_authority_end` starts at position 7 (after
`file://`), sees `/` immediately, returns 7. So authority = `file://`
(empty host), path starts at `/a/bb/...`. That looks right.

`s294` = `http:g` → **expected `http:g`** (strict mode). Our code sees
the colon, returns `rel` as-is → `http:g`. OK.

The `?y` bug (s259), `//g` bug (s258), and dots-in-query bugs
(s290–s293) all reproduce here.

**Empty ref `<>` (s267):** expected `file:///a/bb/ccc/d;p?q`. Our
code returns `base_iri` unchanged → `file:///a/bb/ccc/d;p?q`. OK
(base has no fragment).

But the **spec** says empty ref → keep base minus fragment. If the
base had a fragment, our code would wrongly preserve it. No test
exercises that here — all four bases are fragment-free — but it's
worth a note.

### 3.4 IRI-resolution-08 (three bases, edge cases)

**Base `http://abc/def/ghi`** (no query, no fragment):

- s295 `.` → `http://abc/def/`. Our code: merged=`http://abc/def/.`,
  dot-seg → `http://abc/def/`. OK.
- s296 `.?a=b` → `http://abc/def/?a=b`. Our code: merged=
  `http://abc/def/.?a=b`. Dot-seg sees segment `.?a=b` — this is
  **one segment** with `?` in it. `.?a=b` ≠ `.` literally, so it is
  kept as a path segment. Result: `http://abc/def/.?a=b`. **WRONG**.
  Expected: dot-seg of `.`, then `?a=b` as the query.
- s297 `.#a=b` → `http://abc/def/#a=b`. Same bug, with fragment.
- s298..s300: same pattern with `..`.

**Base `http://ab//de//ghi`** (empty path segments):

- s301 `xyz` → `http://ab//de//xyz`. Merge expects us to preserve
  the double-slash segments. `remove_dot_segments` does not collapse
  empty segments — it should just pass them through. Our `seg_with_slash`
  logic should handle this correctly since empty `seg` is not equal
  to `.` or `..`. **Likely OK**.
- s303 `../xyz` → `http://ab//de/xyz`. Starts at base_dir
  `http://ab//de//`, merge → `http://ab//de//../xyz`, dot-seg should
  pop one empty segment leaving `http://ab//de/xyz`. **Plausible** —
  depends on empty segment handling in the dot-seg state machine.

**Base `http://abc/d:f/ghi`** (colon in path):

- s304 `xyz` → `http://abc/d:f/xyz`. No colon in rel → relative
  branch → merge + dot-seg. `string_contains_colon rel` = false. OK.
- s305 `./xyz` → same result. OK.
- s306 `../xyz` → `http://abc/xyz`. Dot-seg pops `d:f/` → OK.

### 3.5 IRI-resolution-02 (base `http://a/bb/ccc/d/` — ends in slash)

- s057 `<>` → `http://a/bb/ccc/d/`. Our code returns base unchanged.
  OK.
- s049 `?y` → `http://a/bb/ccc/d/?y`. Query-only bug same as s007.
  **WRONG**.
- s051 `#s` → `http://a/bb/ccc/d/#s`. Our code strips base fragment
  (none), appends → `http://a/bb/ccc/d/#s`. OK.

Most `-02` cases work because the base path ends in `/`, making
merge trivial. The query-only and dots-in-query bugs persist.

## 4. Bug summary — how many corner cases we miss

Counting only confirmed wrongs from the walkthrough (across all four files):

| Bug | Count across 4 files |
|---|---:|
| Query-only relative ref `?y` (should keep base path, replace query) | 2 (s007, s049, s259 — s259 only in -07; and the three `.?a=b` / `..?a=b` in -08 → 2+1+3=6 if we include s259 and s296/s299) |
| Fragment-after-dot `.#a=b`, `..#a=b` | 2 (s297, s300) |
| Network-path ref `//g` (should replace auth+path, keep scheme only) | 2 (s006, s258) |
| Dots inside query (`g?y/./x`, `g?y/../x`) | 4 (s038, s039, s290, s291) |
| Dots inside fragment (`g#s/./x`, `g#s/../x`) | 4 (s040, s041, s292, s293) |
| `.?a=b` / `..?a=b` / `.#a=b` / `..#a=b` in -08 | 6 (s296–s300, s299) |
| Empty-ref drops fragment (latent; no test exercises) | 0 today |

**Conservative lower bound: ~20 wrong out of ~165 corner cases.**
Observed failure signature ("expected N, got N, content mismatch")
is consistent with many-but-minority-wrong rather than catastrophic
breakage.

## 5. The proposed fix

### 5.1 Architecture: parse-then-transform

Replace `resolve_iri`'s character-peek dispatch with a proper
RFC 3986 §5.2.2 "Transform References" algorithm on a parsed IRI.

**New data type:**

```fstar
type iri_parts = {
  ip_scheme:    option string;    // without the trailing ':'
  ip_authority: option string;    // without the '//'
  ip_path:      string;           // may be empty
  ip_query:     option string;    // without the '?'
  ip_fragment:  option string;    // without the '#'
}
```

**New functions:**

1. `parse_iri : string -> iri_parts` — a small scanner. `authority`
   starts after `scheme:` if next two chars are `//`; `path` starts
   after authority (or after `:` if no `//`); `query` starts at first
   `?` (outside authority); `fragment` starts at first `#`. ~50 LOC.
2. `merge_paths : iri_parts -> string -> string` — §5.2.3. ~10 LOC.
3. `transform_references : iri_parts (base) -> iri_parts (ref) ->
   iri_parts (result)` — §5.2.2 verbatim. The five-way branch on ref.
   ~30 LOC.
4. `recompose : iri_parts -> string` — §5.3. ~10 LOC.
5. `remove_dot_segments : string -> string` — already done, keep.

Total: ~100 new LOC F*, replacing the existing 60-ish LOC of
`resolve_iri`. Plus ~30 LOC for `parse_iri`. Net delta roughly
+80 LOC.

### 5.2 Drop the `has_dot_segment` hack

The current `resolve_iri_hint` guards full §5.2 resolution behind
`has_dot_segment(rel)` because an earlier RFC 3986 normaliser broke
simple refs. With the proper parse-then-transform implementation,
`resolve_iri` **must** run on every relative ref — the dispatch is
data-driven, not heuristic. Delete `has_dot_segment` and
`resolve_iri_hint`, keep a single `resolve_iri`.

**Risk:** the RDF-XML regression from the original attempt
(`rdf-ns-prefix-confusion 0004/0011/0012/0013/0014`) was caused by
the normaliser running on references that looked like local names.
The root cause was that the RDF-XML parser was calling the same
routine with bare local names (e.g. `lit`) and `http://example.org/`
as base, expecting `http://example.org/lit`. That **is** what a
proper merge gives you. The regression was probably something else —
spot-check those five tests specifically after deploying the rewrite.

### 5.3 Correct handling of specific bugs

- **Query-only (`?y`):** §5.2.2 R.path empty branch: keep B.path,
  take R.query, drop B.query. Current code runs dot-seg over the
  merged path-plus-query mashup.
- **Network-path (`//g`):** §5.2.2 R.authority defined branch: keep
  B.scheme, take R.authority+path+query. Current code treats `//` as
  `/` + `/g` and hits the authority branch with a double-slashed
  path.
- **Dots inside query/fragment:** With parts-parsing, dot-seg runs on
  `R.path` only, never touching query or fragment. Free fix.
- **Empty-ref `<>`:** §5.2.2 R.path empty + R.query undefined branch
  → T.scheme = B.scheme, T.authority = B.authority, T.path = B.path,
  T.query = B.query, T.fragment = R.fragment (undefined → absent).
  So `<>` strips the fragment from base. Our current code does not,
  but no test here exercises this.

### 5.4 Estimated LOC / effort

- New F* code: ~80–120 lines (parse + transform + recompose, plus
  minor helpers).
- Deleted F* code: ~60 lines (current `resolve_iri` + `has_dot_segment`
  + `resolve_iri_hint` plumbing).
- Extraction + patch run: standard pipeline, no new `assume val`.
- Test gain: ~17–20 corner cases per file, plus the trailing subtleties
  in -08. Converts 4 FAIL tests to PASS (one per file, since test
  equality is all-or-nothing).
- TriG mirror: same resolver → another 4 tests pass, so **8 W3C tests
  unlocked total** for ~120 LOC net.

One session's work, including F* verification debugging.

## 6. F* verifier gotchas to expect

1. **Fuel for `parse_iri`.** Scanning for `:`, `/`, `?`, `#` needs
   fuel parameters bounded by `String.length`. The existing code
   already uses this pattern (`find_next_slash`, `find_scheme_end`);
   copy the shape.
2. **`remove_dot_segments` already verifies.** Don't touch its
   termination proof. Just make sure the new call-site passes a
   path that is shorter or equal in length to the merge input (it
   will be).
3. **String concatenation with options.** `option string` for query
   and fragment means every recompose step is:
   ```
   match t.ip_query with
   | None -> ""
   | Some q -> String.concat "" ["?"; q]
   ```
   F* handles this fine but the concat count balloons. Consider a
   helper `append_opt : string -> string -> option string -> string`.
4. **Termination for merge_paths.** Pure non-recursive. No issue.
5. **`parse_iri` must be total.** No `assume val`, no `admit`. The
   scanner has clear structural termination on string position.
6. **Type-level nats.** `find_next_slash` et al. use refinement
   types `{pos <= String.length s}`. Keep that discipline —
   we know from existing code it threads through without Z3
   blowups.
7. **No `--admit_smt_queries`.** The existing resolver verifies
   without that flag. Don't regress it.
8. **Avoid regex-ish splitting.** OCaml's `Str` module is not a
   dependency of the Turtle parser. Keep pure string index/sub
   primitives.

## 7. Order of operations for the subagent

1. Define `iri_parts` record + `parse_iri` function. Property-test in
   F*: `recompose (parse_iri s) = s` for absolute IRIs (string
   equality round-trip).
2. Port §5.2.2 as `transform_references`. Write it out ladder-style
   matching the RFC text.
3. Replace `resolve_iri`:
   ```fstar
   let resolve_iri (st: turtle_state) (rel: string) : string =
     let base = parse_iri st.base_iri in
     let r    = parse_iri rel in
     let t    = transform_references base r in
     recompose t
   ```
4. Delete `resolve_iri_hint` + `has_dot_segment`. Update call sites
   (three or four in `Parser.Turtle.fst`) to use the single
   `resolve_iri`.
5. Run `make verify` — expect Z3 rlimit tuning. Probably need to
   push `--fuel 3 --ifuel 3` for the transform-references branch.
6. Extract, compile, run `./w3c_runner rdf-turtle rdf-trig`.
   Expect +8 (4 Turtle + 4 TriG).
7. Run the full rdf suite to check no regressions, especially
   `rdf-ns-prefix-confusion 0004/0011/0012/0013/0014` in rdf-xml.
8. Commit.

## 8. What NOT to do

- **Do not add more special-case heuristics.** `has_dot_segment`
  was a stopgap to avoid a regression; the right fix is to stop
  dispatching on character shape and dispatch on parsed structure.
- **Do not try to be "strict mode" for scheme-preserving refs** like
  `s042` (commented-out `<http:g>`). That test is explicitly
  commented out in the test file. Strict mode is a spec variant
  factoidal does not need to opt into.
- **Do not normalise case, percent-encoding, or host parts.** The
  tests don't require it, and the RDF spec says IRI comparison is
  character-string comparison. Keep our resolver as a pure
  transformation — no normalisation beyond dot-segment removal.
- **Do not change `remove_dot_segments`.** It's already correct
  (and carries a termination proof); our bugs are outside it.
- **Do not fold this work into the OWL reasoning branch.** Different
  module, different reviewer surface. Small, scoped commit.

## 9. Summary

- ~165 corner cases across 4 Turtle + 4 TriG tests.
- ~20 currently-wrong cases, mostly clustered into 5 bug families
  (query-only, network-path, dots-in-query/fragment, empty-ref,
  `.?a=b`).
- Fix = proper RFC 3986 §5.2.2 parse-then-transform in F*.
- Net ~+80 LOC, one session, no new `assume val`, no `--lax`.
- Unblocks 8 W3C tests, no expected regressions.
