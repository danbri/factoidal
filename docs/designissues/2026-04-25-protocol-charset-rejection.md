# SPARQL Protocol — Reject non-UTF-8 charset (§2.1.6)

Agent: Samekh
Date: 2026-04-25
Branch: claude/main
Wave: 9

## Context

He landed Phase 1 (`f2d1492` — query/update happy paths in-process).
Yod just landed Phase 2 duplicate-key rejection (`7f9870d` —
`sparql-protocol: reject duplicate query= / update= keys per §2.1.4`).

Two Phase 2 tests remain red:
- `bad_query_non_utf8`
- `bad_update_non_utf8`

Both feed a `Content-Type` header with an explicit non-UTF-8 charset
parameter (e.g. `application/sparql-query; charset=utf-16`) and expect
the protocol layer to reject the request with `PR_Bad`.

## W3C spec reference

SPARQL 1.1 Protocol §2.1.6 (and §2.2.x for updates):

> "the service MUST reject the request if the Content-Type declares a
>  charset other than UTF-8."

Cases to handle:

| Header                                                        | Verdict |
|---------------------------------------------------------------|---------|
| `application/sparql-query`                                    | accept (default UTF-8) |
| `application/sparql-query; charset=utf-8`                     | accept |
| `application/sparql-query; charset=UTF-8`                     | accept (case-insensitive) |
| `application/sparql-query; charset=utf8`                      | accept (tolerate hyphenless) |
| `application/sparql-query; charset=utf-16`                    | REJECT (PR_Bad) |
| `application/sparql-update; charset=iso-8859-1`               | REJECT |
| `application/x-www-form-urlencoded`                           | accept (no charset specifier expected) |
| `application/x-www-form-urlencoded; charset=utf-8`            | accept (tolerated) |

## Edit plan (`formal/fstar/SPARQL.Protocol.fst`)

Today `content_type_base` (line 449) only extracts the bare media type
and discards parameters. Required:

1. Add helper `extract_charset_param : string -> option string` that
   walks the `;`-separated parameter list of the Content-Type, finds
   any `charset=...` (case-insensitive on the key), trims, lowercases
   the value, and returns it.

2. Add helper `charset_is_utf8_or_absent : string -> bool` that returns
   `true` if no `charset` parameter is present, or if the value is one
   of `utf-8`, `utf8` (already lowercased).

3. In `decode_request`, on the POST branch, after computing
   `content_type_base`, also test the full `content_type` string with
   `charset_is_utf8_or_absent`. If false, return
   `PR_Bad ("non-UTF-8 charset rejected per Protocol 2.1.6")`.

This composes cleanly with Yod's `build_from_kvs` change — the charset
check fires earlier (POST branch dispatch) so duplicate-key logic
remains intact.

## Verification

`fstar.exe --include . --cache_dir .cache SPARQL.Protocol.fst` — must
succeed without `--lax`. Because the new helpers are pure list/string
manipulation following the same shape as existing helpers
(`content_type_base`, `parse_accept_entry`'s parameter loop), they
should verify under the existing `#push-options` block (z3rlimit 50,
fuel 2, ifuel 2).

## Out of scope

- No edit to `w3c_runner.ml` (He's lane).
- No `./build-ocaml.sh extract` / `compile` (Wave 9 in flight).
- The runner's existing test harness will pick up the new branch
  through normal extraction once the wave rebuild lands.
