# Vav — rdf-xml "regression" diagnosis (2026-04-25)

Status: **READ-ONLY diagnosis. Do not commit until reviewed.**

## TL;DR

**The 19 rdf-xml failures attributed to Tav3 (`a893fe8`) are NOT a Tav3
regression.** They are a pre-existing path/cwd bug in `w3c_runner.ml`
(`relpath_under` + `make_turtle_base_tc`) that manifests **only when the
runner is invoked from `formal/fstar/ocaml-output/` with a relative
manifest path containing `../`**. From the repo root the suite scores
166/166 (zero fails). Yod4 misattributed the count because their build
script runs the suite from `ocaml-output/` and they didn't compare
against the historical baseline. The pre-Tav3 logs (Wave 14, 25 Apr
09:52Z) and earlier (`rebuild-20260424-222734-revert.log`, 24 Apr
22:46) both already report `rdf-xml pass:147 fail:19`.

Confidence: **HIGH** for the path-bug diagnosis and the not-a-Tav3-fault
conclusion. Same binary (5872856 bytes, built 14:44:58) produces 0
fails from one cwd and 19 fails from the other; runner.ml is byte-
identical from `be99936` (pre-Tav3) through HEAD.

## Evidence trail

### 1. Same binary, two cwds, two scores

```
$ ./bin/darwin-arm64/w3c_runner --rdf rdf-xml | tail -3
  rdf-xml                             pass:166 fail:0 skip:0 unsupported:0
TOTAL: 166 pass, 0 fail, 0 skip, 0 unsupported

$ cd formal/fstar/ocaml-output && ./w3c_runner --rdf rdf-xml | tail -3
  rdf-xml                             pass:147 fail:19 skip:0 unsupported:0
TOTAL: 147 pass, 19 fail, 0 skip, 0 unsupported
```

Three back-to-back runs from each cwd are bit-identical → not flaky.

### 2. The 19 "regression" failures are old

`grep "rdf-xml" .claude-runs/*.log`:

| log                                                    | when (Apr 2026) | rdf-xml score |
|--------------------------------------------------------|-----------------|---------------|
| `rebuild-20260424-222734-revert.log`                   | 24 Apr 22:46    | 147 / 19      |
| `rebuild-20260424-234623-wave6.log`                    | 24 Apr 23:46    | 147 / 19      |
| `rebuild-20260424-232610-wave5.log`                    | 24 Apr 23:26    | 147 / 19      |
| `wave14-build-20260425T0952Z.log`                      | 25 Apr 11:13    | 147 / 19      |
| `yod4-build-20260425.log` (Tav3+Yod4)                  | 25 Apr 14:48    | 147 / 19      |

Tav3 commits at 14:29 on 25 Apr. The 19-fail count is at least 16
hours older than Tav3 and unchanged across the Tav3 boundary.

### 3. `w3c_runner.ml` is identical pre-/post-Tav3

```
$ git diff be99936 a893fe8 -- formal/fstar/ocaml-output/w3c_runner.ml | wc -l
0
$ git diff be99936 HEAD   -- formal/fstar/ocaml-output/w3c_runner.ml | wc -l
0
```

Only the F\* source `RDF.Graph.Executable.fst` (and via re-extraction
`RDF_Graph_Executable.ml`) changed in `a893fe8`. Tav3's two added
rules (`owl_rule_disjoint_with_propagation`,
`owl_rule_svf2_existential_witness`) are guarded by closure-step
predicates and only invoked from `apply_entailment_regime`, which
in turn is only called from `PositiveEntailmentTest` /
`NegativeEntailmentTest` (rdf-mt suite, lines 2576–2615 of
`w3c_runner.ml`). **Neither `TestXMLEval` (line 2533) nor
`TestXMLNegativeSyntax` (line 2553) calls any closure code.**

### 4. The cwd-sensitivity mechanism

`run_rdf_test` for `TestXMLEval` calls

```ocaml
let base = make_turtle_base_tc assumed_base tc.manifest_dir tc.query_file in
let actual = parse_rdfxml_fstar input (Some base) in
```

`make_turtle_base_tc` (line 2348) computes
`base ^ relpath_under manifest_dir filepath`. `relpath_under`
absolutises both paths via `Sys.getcwd ()` and then does a string-
prefix subtraction:

```ocaml
let md = if Filename.is_relative manifest_dir
         then Filename.concat (Sys.getcwd ()) manifest_dir
         else manifest_dir in
let fp = if Filename.is_relative filepath
         then Filename.concat (Sys.getcwd ()) filepath
         else filepath in
...
if String.length fp > String.length md_slash
   && String.sub fp 0 (String.length md_slash) = md_slash then
  String.sub fp (String.length md_slash) (...)
else
  Filename.basename filepath  (* <-- fallback strips subdirectory *)
```

When `build-ocaml.sh` runs the suite from `formal/fstar/ocaml-output/`,
it passes the manifest as `../../../third_party/.../rdf-xml/manifest.ttl`.
`manifest_dir` becomes `../../../third_party/.../rdf-xml`. After
`Filename.concat (Sys.getcwd ()) manifest_dir`, the result still
contains the literal `../../../` segments — `Filename.concat` does
not normalise. Meanwhile `tc.query_file` is parsed out of the
turtle manifest's `mf:action` IRI and absolutised differently
(it goes through `iri_to_local_path` with `manifest_dir` joined
to a file:// resolved path), so its absolutised form does NOT
share the literal-prefix shape with the cwd-prepended manifest_dir.

Result: prefix subtraction fails, `relpath_under` returns
`Filename.basename filepath`, the subdirectory (e.g.
`rdf-ns-prefix-confusion/`) is lost from the test base IRI, and
every subject/object IRI parsed by `parse_rdfxml_fstar` ends up
under `https://w3c.github.io/.../rdf-xml/test0004.rdf#foo` instead
of `https://w3c.github.io/.../rdf-xml/rdf-ns-prefix-confusion/test0004.rdf#foo`.
That is the entirety of the "Triples mismatch: expected N, got N"
delta — same triple count, IRI strings differ, `triple_sets_match`
returns false.

### 5. Why the user's prompt mentioned "Should reject but parsed OK"

It didn't, in the Yod4 log. All 19 failures are
`Triples mismatch: expected N, got N` (TestXMLEval). There are no
`Should reject but parsed OK` lines in either Yod4's log or my
fresh runs. The user-facing prompt appears to have over-summarised.
This is consistent with the cwd-bug diagnosis (negative-syntax tests
fail-closed without consulting the base IRI; eval tests fail-open
with a bad base).

## Hypothesis-tree resolution

1. **"Runner runs OWL-RL closure during rdf-xml triple comparison."**
   FALSE. `TestXMLEval` (line 2533) calls `parse_rdfxml_fstar` then
   `triple_sets_match`. No `apply_entailment_regime`, no closure
   call.

2. **"Tav3's bnode skolems leak into find_objects/find_subjects used
   by parser comparator."** FALSE. The parser-side comparator uses
   `triple_to_canonical_key` (line 2127), which is independent of
   `find_objects`/`find_subjects` and only sees triples that
   `parse_rdfxml_fstar` returned. Tav3's skolems would have to be
   injected during parsing — they are not.

3. **"svf2 witness affects N-Quads canonical serialisation used in
   negative tests."** FALSE. `TestXMLNegativeSyntax` (line 2553)
   only calls `Parser_RDFXML.parse_rdfxml_strict`. No serialisation,
   no closure.

4. **"Tav3 broke a shared helper (decreases / Tot)."** FALSE.
   `git diff` shows the runner ML and unrelated parser ML are
   byte-identical across the Tav3 commit; F\* extraction completed
   cleanly (Yod4's build log confirms all 32 modules extracted).
   Both new rules are wired in the same `owl_rl_closure_step`
   pipeline; nothing else changed.

5. **(Fifth hypothesis, the actual cause): pre-existing cwd-
   sensitive `relpath_under` fallback in `w3c_runner.ml`.** This
   diagnosis fits all evidence:
   - Predates Tav3 (logs from 24 Apr 22:46 onward).
   - Identical 19-test failure list across all post-empprop builds.
   - Disappears when the runner is invoked from the repo root.
   - Independent of any closure code path.

## Specific failing-test mechanism

`rdf-ns-prefix-confusion-test0004` (one triple, no bnodes):

- input IRI base (intended): `https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-xml/rdf-ns-prefix-confusion/test0004.rdf`
- input IRI base (actual, from ocaml-output cwd): `https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-xml/test0004.rdf` (subdirectory dropped)
- expected triple: `<...rdf-ns-prefix-confusion/test0004.rdf#foo> <http://example.org/property> "bar" .`
- parsed actual: `<...test0004.rdf#foo> <http://example.org/property> "bar" .`
- `triple_sets_match` compares canonical keys; subject IRI strings
  differ → false → `Triples mismatch: expected 1, got 1`.

The failure has nothing to do with bnodes; it is a base-IRI subdir
loss. The "Triples mismatch: expected N, got N" pattern with
matching N is a classic IRI-mismatch signature.

## Recommended action

**Not (a) revert Tav3.** Tav3's commit is innocent of this regression
and verified clean (and the F\* file changes only add new top-level
functions wired into the closure pipeline).

**Not (b) gate on a flag.** Tav3 is not on the path; gating helps
nothing.

**Not (c) move closure rules out of the rdf-xml path.** Closure rules
already are not on the rdf-xml path.

**Actual fix (separate, low-risk): make `relpath_under` normalise
the `..` segments.** Two safe options:

i. Use `realpath` (via `Unix.realpath` if available, or a small
   normaliser) on both `md` and `fp` before the prefix subtraction.

ii. Have `build-ocaml.sh` invoke `w3c_runner` with an absolute
    manifest path (`$(realpath ...)`).

Option (i) is the F\*-spirit fix (semantic correctness independent
of build-script invocation). Option (ii) is a one-liner shell
patch and would unblock immediately.

Either fix would land all 19 from the build-script invocation and
should not be conflated with merging Tav3.

## Merge decision recommendation

**Merge Tav3 (`a893fe8`).** It does not cause the 19 rdf-xml fails
attributed to it. Yod4's report (`7384b7d`) is correct as a build
unblock for the `gs_indexed` schema evolution; their numerator
"625/631 SPARQL pass + 1012/1031 RDF pass" is from the
build-script cwd and includes the pre-existing 19 rdf-xml fails as
a baseline issue — not a Tav3 delta. From the repo root the score
is 1031/1031 RDF pass; the 2 SPARQL `entailment` fails are
unrelated to this diagnosis (they are paper-Q3 residuals and rdfs9
OWL-Direct residuals already on file).

If desired I can stage the `relpath_under` normalisation as a
separate small patch — but that is not required to merge Tav3.

## What I checked, what I did not

- Checked: the same binary scoring 166/0 from one cwd and 147/19
  from another, deterministically; runner.ml byte-identity across
  Tav3; presence of Tav3 svf2/disjointWith symbols in the binary;
  call paths from `TestXMLEval` and `TestXMLNegativeSyntax` (no
  closure invoked); historical baseline from `.claude-runs/*.log`.
- Did not run: the linux-x86_64 binary (different platform); a
  rebuild without Tav3 (constraint says no compile / no extract);
  a bisect against the rdf-xml fails (already accounted for by
  the 24 Apr baseline).
