# G2 partial: F\* → krml → gcc pipeline lights up

**Date**: 2026-05-10
**#200 Section G**: G1 ✅ (krml installed); G2 partial (this commit); G3 pending.

## What works end-to-end

```bash
cd formal/fstar
eval $(opam env --switch=fstar)

# 1. F* → krml intermediate.
fstar.exe --z3version 4.13.3 --include . \
  --codegen krml \
  --extract '+RDF.Bytes,+SPARQL.JSON.Escape' \
  --odir krml-output \
  SPARQL.JSON.Escape.fst
# ⇒ krml-output/SPARQL_JSON_Escape.krml

# 2. krml → C source.
krml -skip-compilation -tmpdir c-output \
  -warn-error -2-9-11-15 \
  -add-include '"krml/internal/compat.h"' \
  krml-output/SPARQL_JSON_Escape.krml
# ⇒ c-output/SPARQL_JSON_Escape.{c,h} (175 + 53 lines)
# ⇒ c-output/internal/Prims.h
# ⇒ c-output/Makefile.{basic,include}

# 3. gcc → object file.
cd c-output
gcc -c -Wno-implicit-function-declaration \
  -I /tmp/karamel/krmllib/dist/generic \
  -I /tmp/karamel/include \
  -I . \
  SPARQL_JSON_Escape.c \
  -o SPARQL_JSON_Escape.o
# ⇒ Object file produced. Symbols: SPARQL_JSON_Escape_hex_digit_lc,
#   _push_u_escape, _walk, _json_escape; references to FStar_Char_*,
#   FStar_String_*, FStar_List_Tot_Base_rev, Parser_FastString_fs_*,
#   Prims_op_* (linker-resolved against krmllib).
```

## What needed setup beyond G1

Per the krml install in `a6b1d68`, the binary alone wasn't enough. krml emits Makefile shims pointing at `/usr/local/share/krml/`, which doesn't get populated by `make minimal`. Manual install:

```bash
sudo mkdir -p /usr/local/share/krml/{misc,include}
sudo cp /tmp/karamel/misc/Makefile.basic /usr/local/share/krml/misc/
sudo cp -r /tmp/karamel/include/krml /usr/local/share/krml/include/
```

After that, `krml -tmpdir <dir> ...` writes the .c/.h/.Makefile.* files cleanly.

## Warnings tolerated (ignored via `-warn-error -2-9-11-15`)

- **Warning 2** (missing C implementation): `FStar.Char.char_of_int` / `FStar.String.string_of_list` / `Parser.FastString.fs_byte_*` are declared `assume val` in F\* and need a C implementation. The krmllib runtime in `/tmp/karamel/krmllib/` provides most (e.g. `fstar_char.c`); `Parser.FastString` is a project-local `assume val` that needs its own C realisation for full G2 link.
- **Warning 9** (static initializers): empty graph globals.
- **Warning 11** (closures): function pointers from F\* lambdas.
- **Warning 15** (GC types): F\*'s `list` type is GC'd; krml emits it as a linked structure leaking memory at runtime. Acceptable for first demo.

## What's still missing for a runnable executable

To link to an actual `format_demo` binary calling `SPARQL_JSON_Escape_json_escape` and printing the result, we'd need:

1. **krmllib C runtime sources** — the `Prims_op_*` ops and `FStar_*` impls. Available at `/tmp/karamel/krmllib/dist/generic/*.c`. Building them as `libkrmllib.a`:
   ```bash
   cd /tmp/karamel/krmllib/dist/generic
   make -f ../../../misc/Makefile.basic   # tries to build libkrmllib.a
   ```
   (Has its own dependency chain — needs zarith / gmp linkage if integers are unbounded.)

2. **C realisations of project-local `assume val`s** — `Parser.FastString.fs_byte_at`, `fs_byte_length`, etc. Currently realised via OCaml patches (`89_fast_string_primitives.sh`); for the C path we'd need parallel C stubs.

3. **A `c-demo/format_demo.c` consumer** — calls `SPARQL_JSON_Escape_json_escape("Hello\nWorld")` and prints the escaped output. ~30 lines.

4. **Makefile** — links the demo + project objects + libkrmllib.

These are all bounded engineering steps but each carries its own gotcha (in particular the GC-type runtime is the long pole — proper memory management for F\*'s list output is a real cleanup).

## Recommendation for G3 / next

Per the C-build plan doc §2.3, **G3 is `RDF.Format.fst` string-pattern-match refactor** (KaRaMeL Warning 250). That's an F\* source change. With G2's `.c` output now reproducible, doing G3 is a clean follow-up: refactor `RDF.Format.fst` to use `if/else if` chains instead of literal-string `match`, re-run the krml pipeline, confirm Warning 250 is gone.

After G3: the C-build pilot has cleared its formal blockers. The remaining work to a *runnable* C demo is engineering plumbing (krmllib link, project-local `assume val` C stubs, demo consumer + Makefile). Tracked under G2/G3 in #200.

## Next-PR sketch

Title: `c-build: G3 — refactor RDF.Format.fst string-pattern-match for KaRaMeL`

Files touched:
- **EDIT**: `formal/fstar/RDF.Format.fst` — replace any `match s with | "ttl" -> ... | "nq" -> ...` with `if string_equal s "ttl" then ... else if string_equal s "nq" then ...`. The audit doc names `format_of_extension` and `format_of_string` as the affected functions.
- **EDIT**: `formal/fstar/build-ocaml.sh karamel` step — extend allowlist to include `RDF.Format.fst`.
- **VERIFY**: re-run the `--codegen krml` step on the extended allowlist; confirm Warning 250 is absent.

CI gate: existing W3C suites must still pass (no behavioural change from the refactor).
