## OCaml Profiling Mechanism

This note records the temporary OCaml-side profiling mechanism that was used while investigating Turtle parser hotspots in extracted code.

It was intentionally lightweight and sat entirely in `formal/fstar/ocaml-output/`, outside the F* source modules.

### Mechanism

The profiling support had three pieces:

1. A small runtime module at `formal/fstar/ocaml-output/Profile_runtime.ml`
2. Manual wrapper bindings added near the top of selected extracted modules:
   `let profile name f = Profile_runtime.record name f`
3. Manual wrapping of hot functions with calls such as:
   `profile "Parser_NTriples.parse_iri_raw" (fun () -> ...)`

At runtime, profiling was enabled only when `FACTOIDAL_PROFILE` was set to one of:

- `1`
- `true`
- `TRUE`
- `yes`
- `YES`

When enabled, the runtime:

- used `Sys.time ()` for per-call CPU timing
- accumulated `calls` and `cpu_seconds` in a `Hashtbl`
- printed a sorted report from an `at_exit` hook

### What Was Instrumented

In the current tree state before removal, the active instrumentation was present in:

- `formal/fstar/ocaml-output/RDF_Graph_Executable.ml`
- `formal/fstar/ocaml-output/Parser_NTriples.ml`
- `formal/fstar/ocaml-output/Profile_runtime.ml`

There was also a small standalone helper script at `formal/fstar/prof_t`, but it was not wired into the build pipeline.

### Why It Is Being Removed

This mechanism was useful for discovery, but it is not a stable or desirable long-term part of the extracted OCaml build because:

- it lives outside the F* source of truth
- it requires manual reinsertion after extraction
- it changes the extracted-output surface and can break normal compile paths
- it is the wrong level for the current re-engineering, which is now happening in F*

### If We Need OCaml Profiling Again

Use it as a temporary, explicitly documented post-extraction step:

1. Extract F* modules normally.
2. Add a profiling runtime module in `ocaml-output/`.
3. Insert wrappers only in the specific extracted modules under investigation.
4. Gate activation behind an environment variable.
5. Remove the instrumentation again before treating the extracted tree as the baseline.

The preferred path forward is to keep performance work driven by F* architecture changes and use OCaml profiling only as a temporary observational tool.
