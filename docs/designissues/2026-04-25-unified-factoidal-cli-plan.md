# Unified `factoidal` CLI — Phase 0 plan + Phase 1 shim

Date: 2026-04-25
Owner: Agent Bet3 (this doc) — coordination with Sade2 (factoidal_http
landing page) and Aleph3 (JS).

## Why

We currently ship six entry points with overlapping concerns:

| Today                                  | Lives in                                    | Role |
|----------------------------------------|---------------------------------------------|------|
| `factoidal`                            | `formal/fstar/ocaml-output/factoidal_cli.ml`| SPARQL query + RDF dump/count |
| `factoidal-http`                       | `formal/fstar/ocaml-output/factoidal_http.ml`| SPARQL 1.1 Protocol server |
| `w3c_runner`                           | `formal/fstar/ocaml-output/w3c_runner.ml`   | W3C SPARQL/RDF test runner |
| `owl_runner`                           | `formal/fstar/ocaml-output/owl_runner.ml`   | OWL 2 RL profile test runner |
| `rdfc10_runner`                        | `formal/fstar/ocaml-output/rdfc10_runner.ml`| RDFC-1.0 canonicalisation tests |
| `tools/corpus_pipeline.py`             | Python (rdflib + pycottas)                  | TriG/Turtle → COTTAS, sharding, partitioning |

This is hostile to new users. They have to know which binary does what,
where each lives, and which set of flags applies. The aim: one `factoidal`
binary with subcommands, the way `git`, `cargo`, `kubectl`, `gh` do it.

## Target surface

```
factoidal query        --data X --query Q.rq          # current factoidal CLI shape
factoidal serve        --port 3030 --dataset X        # was factoidal-http
factoidal cottas-import X.trig --out D.cottas         # was tools/corpus_pipeline.py materialize-nq-cottas-corpus
factoidal cottas-info  D.cottas                       # new: stats from cottas (Phase 2)
factoidal test w3c     [...]                          # was w3c_runner
factoidal test owl-rl  [...]                          # was owl_runner
factoidal test rdfc10  [...]                          # was rdfc10_runner
factoidal dump         X.ttl                          # was --dump
factoidal count        X.ttl                          # was --count
factoidal help                                        # navigation aid (Phase 0)
factoidal version
```

`factoidal` invoked with no subcommand prints the navigation help and exits 0.

Backward compat: legacy flag forms (`factoidal --data X --query Q.rq`,
`factoidal --dump`, `factoidal --count`) keep working until we cut a 1.0.
Detection rule: if `argv[1]` does NOT match a known subcommand AND starts
with `-` (or there are no positional args), fall through to the legacy
parser. This is the minimum-viable consolidation — we don't rip out the
old surface.

## Phased rollout

### Phase 0 — this commit (navigation only)

- This design doc.
- `factoidal help` subcommand: lists every existing entry point AND the
  proposed unified subcommand. Tells users what to invoke today and what
  it'll be called once consolidation lands.
- No behaviour change to the existing CLI; legacy flags untouched.

### Phase 1 — this commit if time permits (in-process dispatchers)

- `factoidal serve …` → exec the existing `factoidal-http` binary
  (sibling-binary discovery: same dir as `argv[0]`). Keeps Sade2's edits
  to `factoidal_http.ml` untouched.
- `factoidal cottas-import …` → exec `python3 tools/corpus_pipeline.py
  materialize-nq-cottas-corpus …`. Repo root is found via env var
  `FACTOIDAL_REPO_ROOT` or by walking up from `argv[0]`.
- `factoidal test {w3c,owl-rl,rdfc10}` → exec the corresponding sibling
  binary, forwarding all remaining args.
- `factoidal query …` → routes to the existing query path (rename only).
- `factoidal dump FILE` / `factoidal count FILE` → routes to existing
  modes.

### Phase 2 — deferred (NOT in this commit)

- Fully merge w3c_runner / owl_runner / rdfc10_runner into one binary.
  They have substantial state machines (manifest parsing, per-suite
  expected-row matching, OWL profile classification). A single binary
  is fine but it's a bigger refactor than the 60 min budget allows.
  For now, `factoidal test SUITE` is a thin shim.
- `factoidal cottas-info` (would need either an OCaml COTTAS reader
  exposing stats or a pycottas wrapper — defer until we have the right
  F\* surface).
- Drop the standalone `factoidal-http`, `w3c_runner`, `owl_runner`,
  `rdfc10_runner` binaries. Keep them through at least one release of
  the unified CLI for users with scripts.
- Update `bin/<platform>/` to ship a single `factoidal` and symlinks
  for the legacy names (`factoidal-http -> factoidal`, etc.) using
  argv[0]-dispatch the way busybox does.

## Hard constraints (per the prompt)

- ≤ 200 LoC OCaml glue, ≤ 100 LoC Python glue.
- No `.fst` edits. All consolidation is hand-written CLI dispatch
  (rule #15 territory: I/O glue, not RDF semantics).
- Don't touch `factoidal_http.ml` in this commit window — Sade2 owns it.
- Don't collapse the test runners; they stay standalone, exec-shimmed.

## Sibling-binary discovery

Strategy used by the dispatcher when `factoidal serve` / `factoidal test
…` need to invoke a sibling binary:

1. Compute `argv0_dir = Filename.dirname Sys.executable_name`.
2. Look for `<argv0_dir>/<binary>` (e.g. `<argv0_dir>/factoidal-http`).
3. If absent, fall back to PATH lookup (Unix `execvp`).
4. If still absent, exit 127 with a helpful message:
   `factoidal: 'serve' subcommand requires factoidal-http binary, expected
    at <argv0_dir>/factoidal-http or on PATH. Run build-ocaml.sh.`

This works for both the developer layout (`bin/darwin-arm64/factoidal`
finds `bin/darwin-arm64/factoidal-http`) and any future install layout
(`/usr/local/bin/factoidal` finds `/usr/local/bin/factoidal-http`).

## What this commit ships

1. This doc.
2. New OCaml dispatcher in `factoidal_cli.ml` (Phase 0 + Phase 1):
   - `factoidal help` — lists today's entry points and unified mapping.
   - `factoidal version` — calls existing version().
   - `factoidal serve [args...]` — exec sibling `factoidal-http`.
   - `factoidal test {w3c,owl-rl,rdfc10} [args...]` — exec sibling
     `w3c_runner` / `owl_runner` / `rdfc10_runner`.
   - `factoidal cottas-import [args...]` — exec
     `python3 tools/corpus_pipeline.py materialize-nq-cottas-corpus`.
   - `factoidal query [args...]` — strips the `query` token and runs
     the existing query path.
   - `factoidal dump FILE [args...]` — equivalent to
     `factoidal --dump --data FILE`.
   - `factoidal count FILE [args...]` — equivalent to
     `factoidal --count --data FILE`.
   - Legacy invocations continue to work.
3. Deferred to Phase 2: full merge of test runners, `cottas-info`,
   busybox-style argv[0] dispatch, deprecation warnings on the
   standalone binaries.

## Risks / non-goals

- **Not a re-architecture**, just a navigation veneer. The
  test runners stay separate processes. `serve` and `cottas-import` are
  exec shims, not in-process dispatchers — keeps coupling minimal and
  avoids dragging the 1295-line `factoidal_http.ml` into the CLI link
  unit (and avoids stepping on Sade2).
- **Doesn't reduce binary count yet.** Phase 2 does that. Phase 1 just
  gives users one entry point that knows how to find the others.
- **Coordination**: this commit edits `factoidal_cli.ml` only. Sade2
  edits `factoidal_http.ml` for the landing page in a different commit
  window — no conflict.
