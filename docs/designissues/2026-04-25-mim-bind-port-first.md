# 2026-04-25 — Bind HTTP port at t=0, load COTTAS in background (#99)

## Problem

`factoidal serve --data-cottas <parquet>` blocks the port bind on the
COTTAS load. With a parquet artifact of any size (e.g. ~60 s for the UK
Parliament dump) the user sees nothing on `:3032` until the entire
in-memory `rdf_dataset` has been materialised. From the outside this
looks like a hung server.

## Scope of this fix (small win)

This is **not** the lazy-column-read fix (issue #99 deep work). It is a
sequencing fix:

1. Bind the listener immediately.
2. Spawn a worker thread that does `load_cottas_dataset` (and the
   `--load-rw-graphs` post-step, and the `snapshot_iris` capture).
3. While the worker is running, the request loop:
   - Serves static / landing-page / `/backend-info.json` routes normally.
   - Returns `HTTP 503 Service Unavailable` with `Retry-After: 5` for any
     route that needs the dataset (`/sparql`, `/query`, `/update`).
4. When the worker finishes it stores the dataset into `dataset_ref`,
   captures `snapshot_iris`, and flips an atomic `loading` flag.

Lazy column reads / mmap'd parquet store remain out of scope.

## Architecture facts

- `factoidal_http.ml` uses **plain `Unix` sockets**, not Cohttp/Lwt.
  Single-threaded accept loop. (See `let run_server cfg` ~line 1838.)
- `dataset_ref : rdf_dataset ref` is already mutable — UPDATE traffic
  swaps it. We therefore already have one writer.
- Adding the loader thread gives us **two writers** to `dataset_ref` —
  but they don't overlap in time: the loader writes once at completion,
  before the loading flag flips false. UPDATE traffic is rejected by the
  503 gate until that point, so there's no concurrent write.
- We still need a `Mutex` to make the flag flip + ref swap visible to the
  request thread (memory ordering), and to keep the read-side check
  (`is_loading ()`) honest.

## Why threads.posix and not Lwt

The whole server is `Unix.accept` / blocking I/O. Introducing Lwt would
require rewriting the request loop. `threads.posix` (already shipped
with the OCaml distribution; just needs `-package threads.posix`) lets
us spawn a single background thread without touching the existing
single-threaded accept loop.

## Files touched

- `formal/fstar/ocaml-output/factoidal_http.ml`
  - Add `loading : bool ref` + `loading_mu : Mutex.t` (module-level,
    threaded through `handle_connection` like `dataset_ref` is).
  - Split `load_dataset cfg` into:
    - `load_dataset_fast cfg` — base RDF + nquads only, no COTTAS.
    - `load_dataset_cottas_part cfg base` — the COTTAS fold; runs in
      the worker.
  - Add `add_503_loading_response` for the gate.
  - Modify `try_static_route` (or wrap it) to return 503 for SPARQL
    paths when loading.
  - In `run_server`: bind + listen first, then spawn the worker, then
    enter the accept loop.
- `formal/fstar/build-ocaml.sh`
  - Add `threads.posix` to the `-package` list for the two binaries
    that link `factoidal_http.ml` (`factoidal` and `factoidal-http`).

## Acceptance test

```bash
$ time (./bin/darwin-arm64/factoidal serve --port 3033 \
    --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas \
    --host 127.0.0.1 --read-only > /tmp/mim-bind-port-test.log 2>&1 &)
real    < 2s
$ curl http://127.0.0.1:3033/             # 200 (static landing)
$ curl http://127.0.0.1:3033/sparql?...   # 503 + Retry-After: 5
# wait ~60s
$ curl http://127.0.0.1:3033/sparql?...   # 200 with results
```

## Caveats

- Dataset count printouts at startup (e.g. "default graph: 12345
  triples") are now wrong because the load is async. We print
  `loading…` instead and the existing
  `/backend-info.json` endpoint already reads the live `dataset_ref`,
  so the web UI's pill will reflect "loading" → real count.
- `--read-only` is the natural pairing with COTTAS today; if someone
  combines `--data-cottas` with read-write traffic, UPDATE attempts
  during the load window will still be rejected with 503 (not 403),
  which is the correct behaviour — once loaded the existing 403 (if
  read-only) / mutation path resumes.
