# Shrink the unverified boundary — scoping doc for issue #87

**Date:** 2026-04-20. Read-only planning, no code in this commit.
**Issue:** [#87 — Shrink the unverified boundary](https://github.com/danbri/factoidal/issues/87)
**Scope:** Turn the three-commit outline in #87 into concrete subagent
prompts. Each section below ships as one commit. Each subagent prompt is
self-contained and carries the exact signatures, file locations, and
replacement edits the implementer needs — no further research required
(rule #24).

## 0. Context recap (pre-work, before any subagent starts)

Protocol server is currently ~60% verified by LOC. The remaining glue in
`formal/fstar/ocaml-output/factoidal_http.ml` (~695 LOC relevant, ~1232
total) breaks down as:

| Band | Lines | Status | Action |
|---|---:|---|---|
| HTTP/1.1 framing: `read_line_crlf`, `parse_request_line`, `parse_header`, `read_headers`, `read_body` | ~65 | unverified | **§1** — move to `SPARQL.HTTP.fst` |
| Auth sandbox rewriter: `sandbox_op`, `sandbox_update`, `check_ggp_graph_target`, `wrap_if_unwrapped` | ~150 | unverified, walks verified AST | **§2** — move to `SPARQL11.Algebra.fst` |
| N-Quads emitter: `nq_escape_literal`, `nq_term_to_string`, `nq_subject_to_string`, `nq_line_for_triple` | ~45 | unverified | **§3** — move to `Parser.NQuads.fst` |
| Socket accept/bind/listen, signal handlers, argv, file I/O, mutable `dataset_ref`, dump-on-exit driver | ~150 | genuinely effectful | keep as glue (see §4) |
| CORS header builder, response write, status-text table, response-body struct | ~75 | mostly string-concat glue | keep for now; optional later |

Total expected migration: ~260 LOC glue removed, replaced by ~320 LOC F*
(F* is more verbose because of explicit fuel + `result`-threading).

---

## §1 — `SPARQL.HTTP.fst` (new module) — subagent prompt

### Goal

Create `formal/fstar/SPARQL.HTTP.fst`. Parse the HTTP/1.1 request-line +
headers + body framing that `factoidal_http.ml` currently does by hand.
After this commit, `read_line_crlf`, `parse_request_line`, `parse_header`,
`read_headers`, `read_body`, and `split_uri` in the OCaml glue all
disappear; the `handle_connection` loop reads the socket into a single
`string` (up to a configurable cap) and calls
`SPARQL_HTTP.parse_http_request`.

### Types

```fstar
module SPARQL.HTTP

open FStar.String
open Parser.Combinators

noeq type http_request = {
  hr_method    : string;       // "GET", "POST", "OPTIONS" — ASCII-upper, canonicalised
  hr_path      : string;       // "/query"  (no query string)
  hr_query_str : string;       // "a=1&b=2" (no leading '?'), "" if absent
  hr_version   : string;       // "HTTP/1.1"
  hr_headers   : list (string & string);  // (lowercased-name, trimmed-value) — case-insensitive
  hr_body      : string;
}

type http_error =
  | HE_BadRequest    : string -> http_error  // generic parse failure w/ diagnostic
  | HE_TooLarge      : http_error             // headers or body exceeded caller cap
  | HE_MalformedLine : http_error             // CRLF missing, bad request-line shape
  | HE_MissingCRLF   : http_error             // header block not terminated by blank line
```

Use `FStar.Pervasives.either http_request http_error` as the return shape
(match what `SPARQL.Protocol.fst` already uses — `result` is not in scope
there either). If the existing module imports `FStar.Pervasives.result`,
use that instead for consistency; grep first.

### Entry points

```fstar
val parse_request_line : string -> either (string & string & string) http_error
// "GET /path?qs HTTP/1.1" -> (method, uri, version). URI split is deferred
// to split_path_qs below — keep request-line parse dumb + total.

val split_path_qs       : string -> (string & string)
// "/query?a=1" -> ("/query", "a=1"). "" qs if no '?'. Already exists in
// SPARQL.Protocol.fst under this exact name — reuse it via `open SPARQL.Protocol`
// or copy (decide by grepping current module layout).

val parse_header_line  : string -> either (string & string) http_error
// "Content-Type: application/sparql-query\r\n" (CRLF already stripped by caller)
// -> ("content-type", "application/sparql-query"). Lowercase the name,
// trim ASCII ws from both sides of the value.

val header_lookup_ci    : list (string & string) -> string -> option string
// Case-insensitive lookup. Input header name is lowercased by parse_header_line,
// so lookup lowercases its needle and does straight `assoc`.

val parse_http_request
  : raw              : string
 -> max_header_bytes : nat
 -> max_body_bytes   : nat
 -> either http_request http_error
// The main entry point. `raw` is the fully-buffered connection contents
// (OCaml glue reads up to max_header_bytes + max_body_bytes and hands
// the whole string in).
//
// Algorithm:
//   1. Find the first "\r\n\r\n" within max_header_bytes. HE_MissingCRLF if absent.
//   2. Split head / body. HE_TooLarge if head > max_header_bytes.
//   3. Parse head: first line = request line, rest = header lines.
//   4. Look up "content-length" case-insensitively. If present, require body
//      length >= that value (take prefix; trailing bytes are caller problem).
//      If absent, treat body as empty (GET / OPTIONS / bodiless POST).
//   5. HE_TooLarge if body > max_body_bytes.
```

### Termination

Every recursion takes either (a) `fuel : nat` decreasing, with initial
`fuel = String.length input - pos + 1`, or (b) a measure
`String.length input - pos`. This is the same pattern as the rest of
`Parser.*.fst`. **No `--admit_smt_queries`, no `assume val`, no `--lax`.**
If verification gets stuck on a lemma, narrow the interface rather than
admit.

### File layout (propose, keep verification fast)

```
module SPARQL.HTTP
open FStar.String
open FStar.List.Tot
open FStar.Char

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

// Section 1: types (http_request, http_error)
// Section 2: character/byte helpers — is_crlf, ascii_upper_string,
//            ascii_lower_string (steal from SPARQL.Protocol.fst)
// Section 3: parse_request_line   — split on single spaces, exactly 3 parts
// Section 4: parse_header_line    — find first ':', lowercase name, trim value
// Section 5: split head (find "\r\n\r\n")
// Section 6: iterate header lines (CRLF-split loop, fuel-bounded)
// Section 7: parse_http_request   — glue the above + content-length bounds

#pop-options

// Section 8: smoke tests — `let _ = assert_norm (parse_http_request ... == ...)`
// Keep these small; they are the only unit-test the F* layer gets.
```

### OCaml glue edits (factoidal_http.ml)

Delete:
- `read_line_crlf` (lines ~400–414)
- `parse_request_line` (lines ~417–421)
- `parse_header` (lines ~424–430)
- `read_headers` (lines ~433–446)
- `read_body` (lines ~453–466)
- `split_uri` (lines ~469–473)
- `header_value` (lines ~448–450) — replaced by `SPARQL_HTTP.header_lookup_ci`

Replace the top of `handle_connection` (~line 988) with:
```ocaml
let max_head = 65536 in
let max_body = 8 * 1024 * 1024 in
let raw = read_up_to ic (max_head + max_body) in
match SPARQL_HTTP.parse_http_request raw max_head max_body with
| Inr (HE_BadRequest msg)  -> reply_400 oc msg
| Inr HE_TooLarge          -> reply_413 oc
| Inr HE_MalformedLine     -> reply_400 oc "malformed request line"
| Inr HE_MissingCRLF       -> reply_400 oc "missing CRLF header terminator"
| Inl req ->
  let meth   = req.hr_method in
  let path   = req.hr_path in
  let qs     = req.hr_query_str in
  let body   = req.hr_body in
  let ct     = match SPARQL_HTTP.header_lookup_ci req.hr_headers "content-type" with
               | Some v -> v | None -> "" in
  (* ... rest of handle_connection unchanged ... *)
```

Add a new tiny helper `read_up_to : in_channel -> int -> string` (bounded
`Buffer.add_channel` loop — ~15 LOC genuinely-effectful I/O that stays in
OCaml). Add a new `reply_413` helper mirroring `reply_400`.

### Design alternatives (decide, document, ship)

**A. Buffer the whole connection first** (recommended, described above).
Simple, small API, easy to verify. Costs one extra `String.length` scan.
Fine for the Protocol use case where requests are small.

**B. Keep streaming reads** — have OCaml read the header block into a
string (up to blank line), call `SPARQL_HTTP.parse_headers`, then read
exactly `content-length` more bytes and set them into the parsed
structure post-hoc. More moving parts; harder to keep the OCaml side
honest. Reject unless the first approach measurably regresses memory.

**Ship A. Document B in a comment as the path if a customer ever asks
for multi-MB request bodies.**

### LOC estimate

~150 LOC F* (types 25, helpers 40, request-line + header line 40,
top-level parse_http_request 35, smoke tests 10). Removes ~65 LOC OCaml.

### Commit

```
SPARQL.HTTP.fst: verified HTTP/1.1 request framing

Replaces read_line_crlf / parse_request_line / read_headers / read_body
/ split_uri in factoidal_http.ml with parse_http_request extracted from
F*. Fuel-bounded, no --admit_smt_queries, no assume val, no --lax.

factoidal_http.ml drops ~65 LOC of hand-written framing and gains a
~15-LOC read_up_to helper. Rebuild bin/<platform>/factoidal-http and
regenerate docs/fstar-extracted/*.js per rule #9.

Refs #87
```

---

## §2 — `rewrite_update_for_authid` in `SPARQL11.Algebra.fst` — subagent prompt

### Goal

Move the `sandbox_op` / `sandbox_update` auth rewriter (`factoidal_http.ml`
lines 754–872) from OCaml glue into verified F*. This is an AST traversal
over `sparql_update` and belongs next to `apply_update_op` (CLAUDE.md
rule #15, anti-pattern #4). The glue code was shipped in 46f7104 as a
first pass; this commit is the durable F* version.

### Types

```fstar
type rewrite_error =
  | RW_CrossUserGraph   : iri:wf_iri -> rewrite_error
  // Update targets a named graph other than the user's sandbox.
  // Carries the offending graph IRI.
  | RW_NonIriGraph      : rewrite_error
  // Update targets a named graph via a variable (not a specific IRI) —
  // we can't prove at parse time that this stays in the sandbox.
  | RW_DefaultGraph     : rewrite_error
  // Update targets GR_Default explicitly.
  | RW_NamedWildcard    : rewrite_error
  // Update targets GR_Named or GR_All (wildcard over named graphs).
  | RW_LoadNotAllowed   : rewrite_error
  // U_Load present. Rejected outright in sandbox mode (no HTTP fetch).
  | RW_TemplateMissing  : rewrite_error
  // Template did not contain "{authid}". Caller error; startup check
  // should have caught this, but we validate defensively.
```

### Entry point

```fstar
val expand_user_graph
  : template : string
 -> authid   : string
 -> string   // template with every "{authid}" replaced by authid

val rewrite_update_for_authid
  : authid         : string
 -> graph_template : string            // must contain "{authid}"
 -> u              : sparql_update
 -> either sparql_update rewrite_error
```

Return `Inl u'` when every op was accepted (possibly rewritten); return
`Inr err` on the first offending op.

### Rules — one `match` per update_op constructor

Must be semantically identical to the OCaml version in
`sandbox_op` (46f7104). The table below is the ground truth; reference
`factoidal_http.ml` lines 754–857 for the original.

Let `USERGRAPH = expand_user_graph template authid` (a `wf_iri` —
refine at the boundary; require `is_iri USERGRAPH`).

| Constructor | Rule |
|---|---|
| `U_InsertData gp` | `check_top_level_graph gp USERGRAPH`. On `Ok` wrap if needed; on mismatch → `RW_CrossUserGraph iri`. |
| `U_DeleteData gp` | Same as U_InsertData. |
| `U_DeleteWhere gp` | Same as U_InsertData. |
| `U_Modify (w, del, ins, using, where)` | `w` (WITH): must be `None` or `Some USERGRAPH` (else cross-user). `del`: `None` OK, else `check_top_level_graph`. `ins`: `None` OK, else `check_top_level_graph`. `using`, `where`: **leave alone** (read-only; see design hole below). |
| `U_Clear (_, gr)` | `gr` must be `GR_Graph USERGRAPH`. Reject `GR_Default` (`RW_DefaultGraph`), `GR_Named` / `GR_All` (`RW_NamedWildcard`), `GR_Graph other` (`RW_CrossUserGraph other`). |
| `U_Drop (_, gr)` | Same as U_Clear. |
| `U_Create (_, iri)` | `iri` must equal USERGRAPH. Else `RW_CrossUserGraph iri`. |
| `U_Add (_, src, dst)` | Both `src` and `dst` must be `GR_Graph USERGRAPH`. First failure wins. |
| `U_Move (_, src, dst)` | Same as U_Add. |
| `U_Copy (_, src, dst)` | Same as U_Add. |
| `U_Load _ _ _` | Always `RW_LoadNotAllowed`. Out of scope for v1. |

Helper (~15 LOC):

```fstar
// Wrap `gp` in GP_Graph (PT_IRI usergraph) gp if it has no top-level
// GP_Graph wrapper. If it has one targeting the same IRI, leave alone.
// If it has one targeting a different IRI, return Inr.
// If it has one using a variable (PT_Var _), return Inr RW_NonIriGraph.
let check_top_level_graph
  (gp : group_graph_pattern)
  (usergraph : wf_iri)
  : either group_graph_pattern rewrite_error
  = match gp with
    | GP_Graph (PT_IRI iri) _ ->
        if iri = usergraph then Inl gp
        else Inr (RW_CrossUserGraph iri)
    | GP_Graph (PT_Var _) _ -> Inr RW_NonIriGraph
    | _ -> Inl (GP_Graph (PT_IRI usergraph) gp)
```

Note `group_graph_pattern` and `pattern_term` are both already `noeq
type`s in scope — no new imports required.

### Known design hole — carry forward, document

The OCaml version only checks **top-level** `GP_Graph` wrappers. A
`U_Modify` whose DELETE/INSERT template contains a deeply nested
`GP_Graph` (e.g. inside a `GP_Union` or `GP_Optional`) is NOT caught.
In practice this is a low-severity hole because:
- `U_InsertData` / `U_DeleteData` only accept ground quad patterns
  (no Union/Optional/etc per SPARQL grammar);
- `U_Modify` templates are typically flat in real clients;
- the read side (USING, WHERE) is deliberately unrestricted, so a
  reader can already observe any named graph — the sandbox is
  write-only.

**Ship with the same top-level-only check** and add a doc comment at
the F* call-site:

```fstar
// NOTE: We only check the TOP-LEVEL GP_Graph wrapper. A nested
// GP_Graph inside a template (e.g. DELETE { GRAPH <other> { ?s ?p ?o } })
// is NOT caught. This matches the existing OCaml behaviour (see
// factoidal_http.ml:730). Tracked: a future commit should either
// (a) walk the template tree and reject any inner GP_Graph, or
// (b) hoist the check into the INSERT DATA / DELETE DATA parser.
// See #87 follow-up.
```

### OCaml glue edits

Delete from `factoidal_http.ml`:
- `string_replace_all` (lines ~682–706)
- `expand_user_graph` (lines ~708–709) — replaced by F* `expand_user_graph`
- `check_ggp_graph_target` (lines ~730–739)
- `wrap_if_unwrapped` (lines ~743–747)
- `sandbox_result` type (~749–751)
- `sandbox_op` (lines ~754–857)
- `sandbox_update` (lines ~861–872)

Leave `template_prefix` (used by dump-on-exit) where it is for now — it's
string surgery on the CLI flag, not AST logic. (A follow-up could lift
it to F*, but no rush.)

Replace the sandbox call-site (~line 1083) with:

```ocaml
| `Sandboxed (template, authid, _usergraph) ->
  match SPARQL11_Algebra.rewrite_update_for_authid authid template u with
  | Inl u' -> Ok u'
  | Inr (RW_CrossUserGraph iri) ->
      Error (Printf.sprintf "update targets graph <%s>; your sandbox is <%s>"
               iri (expand_user_graph ~template ~authid))
  | Inr RW_NonIriGraph ->
      Error "update uses a non-IRI graph target; specific IRI required"
  | Inr RW_DefaultGraph ->
      Error "update targets the default graph; sandboxed to a named graph"
  | Inr RW_NamedWildcard ->
      Error "update targets NAMED/ALL; sandboxed to a specific named graph"
  | Inr RW_LoadNotAllowed ->
      Error "LOAD is not permitted in sandboxed updates"
  | Inr RW_TemplateMissing ->
      Error "server misconfigured: auth template missing {authid}"
```

(Keep an `expand_user_graph` helper in OCaml for message formatting, or
call through the F*-extracted one.)

### LOC estimate

~120 LOC F* (types 15, `expand_user_graph` 15, `check_top_level_graph`
15, per-constructor match 50, `rewrite_update_for_authid` top level 10,
doc comments 15). Removes ~150 LOC OCaml.

### Commit

```
SPARQL11.Algebra: rewrite_update_for_authid

Auth-sandbox rewriter lives next to apply_update_op, per anti-pattern
#15 — the AST traversal belongs in F*, not in OCaml glue. Behaviour is
semantically identical to the OCaml version shipped in 46f7104.

factoidal_http.ml drops ~150 LOC of sandbox_op / sandbox_update /
check_ggp_graph_target and calls rewrite_update_for_authid at the
sandbox pass. Rebuild bin/<platform>/factoidal-http and regenerate
docs/fstar-extracted/*.js per rule #9.

Known design hole (top-level GP_Graph only) is preserved and
documented; follow-up issue to walk nested templates.

Refs #87
```

---

## §3 — N-Quads serializer in `Parser.NQuads.fst` — subagent prompt

### Goal

Add `emit_nquad` and `emit_nquads` in `Parser.NQuads.fst`. Replace the
inline `nq_escape_literal` / `nq_term_to_string` / `nq_subject_to_string`
/ `nq_line_for_triple` in `factoidal_http.ml` (lines 882–926) with a
single call through the F*-extracted function. Round-trip property: the
parser in the same module must re-parse everything this serializer emits.

### Entry points

```fstar
val escape_string_literal : string -> string
// Escape '\', '"', '\n', '\r', '\t', and any char with code < 0x20
// (as \uXXXX four-hex-digit). All other chars pass through — N-Quads
// allows full UTF-8 in quoted strings.

val emit_iri      : wf_iri -> string
// "<iri>" — no escaping (is_iri guarantees no '<', '>' in value).

val emit_subject  : subject -> string
// S_IRI  -> "<iri>"
// S_BNode label -> "_:label"

val emit_term     : rdf_term -> string
// T_IRI    -> "<iri>"
// T_BNode  -> "_:label"
// T_Literal -> quoted + optional @lang or ^^<dt>

val emit_nquad
  : t     : triple
 -> graph : option wf_iri
 -> string
// "<s> <p> <o> .\n"          when graph = None
// "<s> <p> <o> <g> .\n"      when graph = Some g
// Always emit trailing "\n".

val emit_nquads   : rdf_dataset -> string
// Concatenate:
//   for t in ds.ds_default: emit_nquad t None
//   for ng in ds.ds_named:
//     for t in ng.ng_graph: emit_nquad t (Some ng.ng_name)
// ng_name is `iri` not `wf_iri` today — verify with `is_iri` at the
// boundary. If it fails, skip the named graph (emit nothing) or
// emit to default (decide: *skip*, since a non-iri graph name is
// pathological and N-Quads can't represent it).
```

### Escaping rules (round-trip with `Parser.NTriples.fst`)

Grep `Parser.NTriples.fst` for the literal body parser to confirm the
exact escape set. Minimum set required for round-trip:

| Code point / char | Emit as |
|---|---|
| `\\` (0x5C) | `\\` |
| `"` (0x22) | `\"` |
| `\n` (0x0A) | `\n` |
| `\r` (0x0D) | `\r` |
| `\t` (0x09) | `\t` |
| 0x00–0x08, 0x0B, 0x0C, 0x0E–0x1F | `\uXXXX` (four hex digits, upper or lower — pick **upper** for W3C test match) |
| 0x20–0x21, 0x23–0x5B, 0x5D–0x7E, 0x80+ | pass through (no escape) |

Lang tag: literal body has `@lang` (e.g. `@en-US`) when `l.lang_tag = Some
"en-US"`.
Datatype: `^^<uri>` when `l.datatype` is not `xsd:string` and lang is
`None`. The existing F* `xsd_string` constant in `RDF.Graph.Executable.fst`
is `"http://www.w3.org/2001/XMLSchema#string"` — use that.
`rdf:langString` with `None` lang is malformed input; preserve
lexically (`"lex"^^<...langString>`) to stay round-trippable.

### Termination

`escape_string_literal` recurses over `list FStar.Char.char` — structural
termination. `emit_nquads` recurses over `list triple` and `list
named_graph` — structural. No fuel needed.

### Round-trip smoke tests (in-module)

```fstar
let _ =
  let t : triple = { s = S_IRI "http://a/x"; p = "http://a/p";
                     o = T_Literal { lexical_form = "hello\nworld";
                                     datatype = xsd_string;
                                     lang_tag = None } } in
  let s = emit_nquad t None in
  assert_norm (s = "<http://a/x> <http://a/p> \"hello\\nworld\" .\n")
```

Keep it to 2–3 cases; CI runs verification, not a regression suite here.

### OCaml glue edits

Delete from `factoidal_http.ml`:
- `nq_escape_literal` (lines ~883–894)
- `nq_term_to_string` (lines ~896–914)
- `nq_subject_to_string` (lines ~916–919)
- `nq_line_for_triple` (lines ~921–926)

Replace in `dump_rw_graphs` (~line 969):

```ocaml
let dump_rw_graphs ~dir ~snapshot_iris (ds : rdf_dataset) =
  try
    mkdir_p dir;
    let rw = diff_named_graphs ~snapshot_iris ds in
    let fname = Filename.concat dir
        (Printf.sprintf "rw-graphs-%s.nq" (timestamp_compact ())) in
    let oc = open_out fname in
    (* One named-graph subset of the full dataset. *)
    let ds_subset : rdf_dataset =
      { ds_default = []; ds_named = rw } in
    output_string oc (Parser_NQuads.emit_nquads ds_subset);
    close_out oc;
    ...
```

### LOC estimate

~60 LOC F* (escape 25, emit_iri/subject/term 15, emit_nquad 5,
emit_nquads 10, smoke tests 5). Removes ~45 LOC OCaml.

### Commit

```
Parser.NQuads: emit_nquads serializer

Inverse of the existing parser. Round-trip tested in-module. Replaces
the inline nq_* helpers in factoidal_http.ml used by --dump-rw-graphs.

Rebuild bin/<platform>/factoidal-http and regenerate
docs/fstar-extracted/*.js per rule #9.

Refs #87
```

---

## §4 — sequencing, risk, residual glue

### Commit order

1. **§3 first** (N-Quads serializer). Smallest, zero F* forward-refs,
   independent from the others. Establishes the workflow pattern
   (F* add → `build-ocaml.sh extract` → `ocaml-patches.sh` → rebuild
   binaries) before the riskier changes.
2. **§1 next** (HTTP parser). Independent from §2. Can land in parallel
   with a follow-up subagent if time allows, but serializing is safer
   because both §1 and §2 edit `factoidal_http.ml`.
3. **§2 last** (auth rewriter). Depends on §1 in that the call-site
   diff is cleaner once the HTTP glue has been trimmed; also depends on
   `SPARQL11.Algebra.fst` not currently being touched by the COTTAS
   Phase 2 subagent — confirm before starting.

Each commit MUST:
- Run `make verify` clean
- Run `./build-ocaml.sh` clean (= extract + patches + compile)
- Run `w3c_runner` and confirm the SPARQL 1.1 + RDF 1.1 baseline
  (375 / 972 / whatever the current numbers are — read `.claude-worklog.md`
  at start-of-session) is **unchanged**
- Rebuild and commit `bin/<platform>/factoidal-http` per rule #9
- Regenerate `docs/fstar-extracted/*.js` and the wasm asset per rule #9
- Append worklog entry per rule #18

### What stays UNVERIFIED after all three commits land

Explicit inventory — this is the residual unverified surface in
`factoidal_http.ml`:

| Thing | Why unverifiable |
|---|---|
| `Unix.listen` / `Unix.bind` / `Unix.accept` / `Unix.setsockopt` | Kernel syscalls; fundamentally effectful |
| `Sys.set_signal` for SIGTERM/SIGINT | Global mutable OS state |
| `Sys.argv`, `Arg.parse_dynamic` equivalent | Process boundary |
| `open_in` / `really_input` / `close_in` for `--dataset`, `--load-rw-graphs` | File I/O |
| `open_out` / `output_string` for dump | File I/O |
| `ref` holding current dataset, mutated by POST /update | OCaml `ref` — if we add a thread pool later, needs a `Mutex.t`; still glue |
| `Mutex.t` around the dataset ref (future, for concurrent connections) | Concurrency primitive; glue |
| Call-site wiring: socket `in_channel`/`out_channel` → `SPARQL_HTTP.parse_http_request` input, F* response → `output_string oc` | Glue that binds verified F* to network I/O |
| CORS header string construction (`cors_headers`) | Optional follow-up; it's just Printf, easy to lift if we care |
| Response-write status-table (`status_text`, `write_response`) | Could lift to F* trivially; low value, low urgency |
| Timestamp formatting (`timestamp_compact`) | Uses `Unix.gmtime`; stays glue |

**Percent verified estimate after all three land:** ~85% of Protocol LOC.
Matches the projection in issue #87.

### Risk register

- **F* verification stall on §1's fuel.** Request bodies up to 8 MB
  imply fuel up to ~8 × 10^6. `pmany_fuel` in `Parser.Combinators.fst`
  already handles this for the other parsers; reuse the same pattern.
  If Z3 times out on the bound, raise `--z3rlimit` to 100 first before
  narrowing the interface.
- **§2 `wf_iri` refinement.** `expand_user_graph` returns `string`; we
  need `wf_iri`. Either (a) refine with `is_iri` at the boundary (safe,
  returns `option wf_iri`), or (b) push the refinement into the type
  via `s:string{is_iri s}`. **Prefer (a)** — returning `Inr
  RW_TemplateMissing` (or new `RW_BadGraphIri`) when
  `expand_user_graph` yields a non-IRI is honest and matches the
  CLI's startup validation.
- **§3 `ng_name : iri` not `wf_iri`.** Filtering on `is_iri` is safe;
  log to stderr on skip so it's visible if somehow a malformed named
  graph exists at dump time.
- **`ocaml-patches.sh` vs direct edits** (anti-pattern #13). The
  sandboxed diff to `factoidal_http.ml` is a direct hand-edit — that
  file is hand-written I/O glue, not F*-extracted, so it's the correct
  place. But if the glue needs any forward-ref wiring to the new F*
  functions (e.g. module open order), that goes in `ocaml-patches.sh`
  as an individual patch under
  `minimal_regrettable_glue_code_each_with_an_open_issue/87_*.sh`.

### Rebuild checklist per commit

Per rule #9 and rule #11:

```bash
cd formal/fstar
./build-ocaml.sh extract     # applies ocaml-patches.sh
./build-ocaml.sh compile     # produces bin/<platform>/factoidal-http
cd ocaml-output
./w3c_runner --all 2>&1 | tee ../../.claude-runs/w3c-YYYYMMDD-HHMMSS.log
# diff the summary against baseline, FAIL if regression
```

If `build-ocaml.sh compile` is used without `extract`, the new F*
definitions won't reach OCaml — silent regression. **Always run
`extract` first after F* changes** (rule #11).

---

## §5 — tech-debt cross-links

This workstream sits alongside, and partially overlaps with:

- **[2026-04-20-oidc-jwt-auth-plan.md](2026-04-20-oidc-jwt-auth-plan.md)** —
  OIDC/JWT auth for the HTTP endpoint. RSA signature verification via
  HACL* is a separate workstream with its own path to verification.
  The auth rewriter in §2 here is downstream of whatever auth decision
  the OIDC layer makes (the only input it takes is a string `authid`),
  so the two workstreams can land independently.
- **[2026-04-19-tableau-owl-plan.md](2026-04-19-tableau-owl-plan.md)** —
  Unrelated feature but same architectural pattern: F* is the source
  of truth, OCaml stays thin. Use §2 as the reference for "AST
  traversal lives in F*, not in glue."
- **[2026-04-19-turtle-parser-speed.md](2026-04-19-turtle-parser-speed.md)** —
  Turtle parser is O(n²ish) on file size (see CLAUDE.md
  "Known Performance Issues"). Neither §1 nor §3 worsens this — the HTTP
  body parser does one pass for CRLF-split and one pass for header
  lines, and the N-Quads serializer is linear in dataset size. If §3's
  serializer is used for large dumps, measure and add the result to
  that doc.
- **[2026-04-19-hdt-fstar-status.md](2026-04-19-hdt-fstar-status.md)** —
  Debt logged around HDT/COTTAS backends; orthogonal to this
  workstream but worth reading before benching §3 on large datasets.

## §6 — things I could not scope precisely from reading

Be honest about the gaps:

- **Exact OCaml side of `rdf_dataset` construction.** The F*-extracted
  type has `ds_default : list triple; ds_named : list named_graph`. The
  OCaml glue uses it directly. Both sides appear aligned — no mangling
  — but a build-time check would confirm the binary layout before
  anyone touches §3.
- **SRX streaming.** Not in this plan; if streaming large SELECT
  results ever matters, the whole response-format layer will need to
  move from "build whole string then write" to a chunk-at-a-time
  protocol. Out of scope for #87.
- **HE_TooLarge vs 413 semantics.** §1's OCaml side needs a
  `reply_413` helper; the F* module doesn't know anything about HTTP
  status codes. This is fine — `SPARQL.HTTP.fst` returns a typed
  error and the glue maps it to a status. The 413 plumbing is ~5
  lines but was not present in the current glue; the subagent must
  add it.
- **`mirage-crypto-pk` / HACL\* linking story.** Out of scope here.
  Called out in the OIDC doc. Note only because #87 says "RSA via
  HACL* is a separate workstream" and the cross-link needs to survive.

---

*End of scoping doc for #87.*
