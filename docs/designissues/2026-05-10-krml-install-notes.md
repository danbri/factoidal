# krml install notes — 2026-05-10

Successful path-(c) variant of the C-build pilot install. Closes #200 G1.

## What worked

```bash
# 1. New opam switch (separate from fstar; ocaml 4.14.1 OK).
opam switch create karamel ocaml-base-compiler.4.14.1
eval $(opam env --switch=karamel)

# 2. Clone karamel master.
git clone --depth=1 https://github.com/FStarLang/karamel.git /tmp/karamel
cd /tmp/karamel

# 3. Build via the Makefile's `minimal` target — bypasses krmllib /
#    F*-side .fst.checked compilation; just builds the krml binary.
#    Deps were already installed by an earlier subagent attempt; if
#    starting fresh, run `opam install -y batteries zarith stdint
#    yojson ocamlbuild fileutils menhir pprint process fix visitors
#    ppx_deriving ppx_deriving_yojson ctypes ctypes-foreign uucp wasm`
#    in the karamel switch first.
make minimal

# 4. Install system-wide.
sudo install -m 755 _build/default/src/Karamel.exe /usr/local/bin/krml

# 5. Verify.
krml          # prints usage / "KaRaMeL: from a ML-like subset to C"
which krml    # /usr/local/bin/krml
```

`fstar` switch unmodified — confirmed via
`opam switch show` (still default), `which fstar.exe` (still
`~/.opam/fstar/bin/fstar.exe`), `fstar.exe --version`
(still `F* 2025.12.15`).

## Why the original opam install path fails

`opam install karamel` from the default opam repo grabs karamel
**v1.0.0** (released 2022), which pins:
- `wasm = "1.1.1"` (requires OCaml < 4.13; conflicts with our 4.14.1)
- `fstar = "2022.01.15"` (would downgrade our F\* and break every
  proof in the repo)
- `conf-python-2-7` (Python 2.7 not available on Ubuntu 24.04)

Karamel master post-2022 fixed all three:
- `wasm >= "2.0.0"` (works on OCaml 4.14)
- F\* dep is a `build` dep only, satisfied by what's on PATH
- No Python 2 dep

So **the right path is git-master, not the opam package.** The C-build
plan doc (§2.3) listed three possible paths — path-(c) ("pin newer
wasm in karamel's opam file") is what upstream already did; we just
needed to clone master rather than the v1.0.0 archive.

## Next steps for #200 Section G

- **G1 ✅** — `krml` on PATH (this commit).
- **G2** — `format_demo.c` linking F\*-extracted `SPARQL.JSON.Escape`.
  Run `fstar.exe --codegen krml SPARQL.JSON.Escape.fst` to get the
  `.krml` output, then `krml -skip-compilation
  -tmpdir c-output SPARQL_JSON_Escape.krml` for the `.c` + `.h`.
  Add a `c-demo/json_escape_demo.c` consumer; cross-check byte-for-byte
  against the OCaml path.
- **G3** — `RDF.Format.fst` string-pattern-match refactor for
  KaRaMeL Warning 250 (per the C-build plan doc §2.3.1's listing of
  the one outstanding krml-warns module).

## Operational notes

- The karamel opam switch (`/root/.opam/karamel/`) is a one-time
  install on this VM; not committed to the repo.
- `/tmp/karamel/` source clone: ephemeral; can be deleted. The
  installed binary at `/usr/local/bin/krml` is what counts.
- `krml --help` does not exist; bare `krml` prints usage.
