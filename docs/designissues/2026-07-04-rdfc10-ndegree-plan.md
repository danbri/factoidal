# RDFC-1.0 N-Degree Hash conformance — root cause + fix plan (2026-07-04)

**Status:** diagnosis complete, fix not yet implemented. Ground truth:
`bin/linux-x86_64/rdfc10_runner` → 63 pass, 22 fail, 1 stub (out of 86).

## Summary of the finding

`formal/fstar/RDF.Canonical.fst` already contains a **full** Hash
N-Degree Quads (HNDQ) implementation — permutation enumeration over
related-bnode buckets, a cloned issuer, recursive descent into
unresolved neighbours, lex-smallest-path selection (`hndq_run` /
`walk_buckets` / `best_permutation` / `pick_best` / `walk_perm`,
lines 935–1023). This is **not** the "single-level neighbour hash"
described in the file's own header comment (lines 3–27) or in
`docs/designissues/2026-04-25-rdfc10-hndq-plan.md` — that plan's
"Section 6b" code (`compute_all_nbr1/2/3`, `build_full_keys`,
`sort_full_keys`, lines 452–745) is **dead code**, never called from
`build_canonical_mapping`. The live path is the newer "Section 6d"
permutation machinery. No design doc documents it — this doc fills
that gap.

The 22 failures do **not** mean HNDQ is absent. They mean the live
HNDQ's **Hash Related Blank Node** step (RDFC-1.0 §4.8) diverges from
spec in two specific, small, precisely located ways. Confirmed against
the vendored spec copy at
`third_party/testing/rdf-canon/spec/index.html` (sections
`#hash-related-blank-node`, `#hash-nd-quads-algorithm`).

## The two concrete bugs

### Bug 1 — `build_buckets_for` never checks the issuer state

`RDF.Canonical.fst:848-877`:

```
let rec build_buckets_for
    (target : bnode_id)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (acc : list bucket)
  : Tot (list bucket) (decreases qs) =
  ...
      let entry = (match related_bnode target q with
        | None -> None
        | Some rb -> Some (rb, lookup_hfdq rb hfdq_table)) in
```

Per spec §4.8 (Hash Related Blank Node), the *identifier* used for a
related bnode is:

1. its already-issued **canonical** identifier, if any, else
2. its already-issued **temporary/path** identifier (from the issuer
   passed into this Hash-N-Degree-Quads call), if any, else
3. its Hash First Degree Quads value (no `_:` prefix) — only in this
   fallback case is the static HFDQ used.

`build_buckets_for` takes no `issuer_state` parameter at all — it
*always* uses branch 3 (`lookup_hfdq`), even when the related bnode
already carries a canonical or in-progress temporary label. Every
symmetric/collision-heavy test in the suite is exactly the case where
several bnodes share one HFDQ, so this is the discriminator the spec
relies on and we're discarding it.

### Bug 2 — the bucket key is an unhashed string, not the spec's hash

`RDF.Canonical.fst:874` (and the `"*"` sentinel variant at line 871)
builds the bucket key as a **raw, unhashed** concatenation:

```
let k = pos ^ "|" ^ pred ^ "|" ^ rhash in
bucket_insert k rb acc
```

Per spec §4.8 step-by-step: `input := position [+ "<" + predicate +
">" if position ≠ g] + identifier`, then **`hash := hash_algorithm(input)`**
— the function returns a SHA-256 **hash**, not the preimage. That hash
is (a) the map key used to iterate `Hn` in code-point order (§4.9 step
4: "for each related hash to blank node list mapping in Hn, code point
ordered by related hash") and (b) the literal bytes appended to
`data to hash` before each bucket's chosen path
(`RDF.Canonical.fst:958`, `data1 = data ^ k`).

Using the raw preimage instead of its hash changes both the
bucket-iteration order and the bytes fed into the final
`hash_sha256 data` call in `walk_buckets` (line 956). Canonical
labelling requires reproducing the *exact* reference tie-break, not
merely "a" stable isomorphism-consistent choice — this is why
`test023c` (circle of 3) doesn't error, it produces the **mirror**
orientation of the correct cycle (`got`: `c14n0→c14n2→c14n1→c14n0`
vs `expected`: `c14n0→c14n1→c14n2→c14n0` — same cycle, opposite
rotation, same byte count). That signature — same length, swapped
labels, isomorphic structure — is present in every Cluster-A failure
below and is the fingerprint of "hash-recipe conformance bug", not
"missing recursion".

### What is *not* broken

- `permutations` / `take_n` / `insert_at_all` / `remove_first`
  (lines 879–913): correct, total, structurally recursive — reusable
  as-is.
- `hndq_run` / `walk_buckets` / `best_permutation` / `pick_best` /
  `walk_perm` control flow (lines 935–1023): matches spec's shape
  step-for-step (bucket loop appends the *related hash* then the
  *chosen path* per bucket; the whole accumulated string is hashed
  exactly once at the end; `issuer` is threaded/replaced across
  buckets in the same order as spec's "Replace issuer, by reference,
  with chosen issuer"). No change needed here for Stage 1.
- `str_le` / `str_compare` / `insertion_sort` (lines 304–344): correct
  lexicographic ordering, reusable.
- `nbr_position_tag` / `related_bnode` / `graph_bnode_of` (lines
  494–557): correctly identify position tag and the "other" bnode in
  a quad, reusable as-is by Bug-1's fix.
- Fuel/termination (`fuel = List.Tot.length bs + 1`,
  `build_canonical_mapping:1128`): sufficient. `hndq_run` decrements
  fuel by 1 per recursive descent, and descent only happens when a
  *fresh* (previously unissued) bnode is discovered — bounded by the
  dataset's total bnode count, not by permutation count. The
  `take_n 6` cap is an independent **performance** bound on
  permutation-enumeration size (6! = 720), not a termination
  requirement — F*'s `permutations` is `Tot` for any list length. Do
  not conflate the two: raising the cap (if needed, see Gate 0 below)
  is a compute-cost decision, not a soundness one.

## Secondary, lower-confidence risk: shared counter vs. spec's fresh local issuer

Per spec (§ preceding "5.2" in the Canonicalization Algorithm, "hash
path list" construction): **every** member of an HFDQ-collision group
gets its own **independent** Hash-N-Degree-Quads exploration using a
**fresh** temporary issuer with prefix `b` (i.e., every candidate's
first new label is `_:b0`, regardless of how many bnodes have already
been canonically committed by earlier groups). Only *after* all
members' results are collected and sorted by resulting hash does the
winning (lex-smallest) member's temporary-issuance sequence get
replayed, in order, through the real canonical issuer.

Our `process_collision_members` (lines 1063–1088) instead issues
**canonical** `c14n<N>` labels directly during exploration, continuing
the dataset-wide running counter — but it does restart every candidate
`m` from the *same* incoming `st` (line 1075's `match ... None ->` arm
always issues from the untouched `st` passed into the function, not an
accumulated one), so candidates within one group *are* compared fairly
against each other. The deviation from spec is that the absolute
label values (and therefore where a candidate's labels cross the
9→10 digit-length boundary, which changes lexicographic comparison
behaviour: `"c14n9" > "c14n10"` as strings) depend on how many bnodes
were already committed by *prior* groups — something spec's 0-anchored
`b`-prefixed scheme never does. This cannot affect small tests
(≤ 8ish total prior + group bnodes), but is a plausible contributor for
the three largest failures (`test044-046` poison-evil at 12 bnodes,
`test054` t-graph at 16, `test059` n-quads-parsing at 19).

## Failure clustering (22 IDs)

### Cluster A — Hash Related Blank Node conformance gap (Bugs 1+2). 18 IDs.

Fixed by Stage 1 alone (small/shallow — no digit-boundary risk):
`test023c` (circle of 3), `test033c`/`test034c` (disjoint identical
subgraphs 1/2), `test035c`/`test036c` (reordered w/strings 1/2),
`test038c`/`test039c` (reordered 4 bnodes 1/2), `test040c` (reordered 6
bnodes), `test058c` (unnamed graph with blank node objects),
`test047c`/`test047m` (deep diff 1), `test048c`/`test048m` (deep diff
2). — **13 IDs.**

Likely need Stage 1 **and** Stage 2 (large enough that the
shared-counter digit-boundary risk applies): `test044c`/`test045c`/
`test046c` (poison – evil 1/2/3), `test054c` (t-graph), `test059c`
(n-quads parsing). — **5 IDs.**

All 18 share the fingerprint verified above: byte-identical `expected`
vs `got` lengths, content differs only in which canonical label a
bnode received (isomorphic relabelling), never in structure or triple
count.

### Cluster B — hash algorithm dispatch (unrelated to N-degree). 2 IDs.

`test075c`/`test075m` — "blank node - diamond (uses SHA-384)". Same
shape as `test020c` (which passes under SHA-256). The manifest sets
`rdfc:hashAlgorithm "SHA384"`; `RDF.Canonical.fst:37` hardcodes
`assume val hash_sha256 : string -> string` and
`canonicalize_to_nquads` (line 1175) has no hash-algorithm parameter;
`bin/rdfc10-runner/rdfc10_runner.ml`'s manifest parsing doesn't even
read `rdfc:hashAlgorithm`. `Fstar_pure_hashes` (OCaml glue, wired per
`build-ocaml.sh:661-662`) already exposes `sha384` — the primitive
exists, it's just not threaded through. **Not part of this plan**;
separate small ticket (parameterize `canonicalize_to_nquads` by hash
function, read the manifest predicate in the runner).

### Cluster C — vendored-fixture artifact, not our bug. 1 ID.

`test073m` — expected/got content is byte-identical except the
fixture file `third_party/testing/rdf-canon/tests/rdfc10/
test073-rdfc10map.json` is missing its trailing `\n` (verified via
`od -c`: every other `*-rdfc10map.json` fixture in the suite ends
`}\n`; this is the only one ending bare `}`). Our
`mapping_to_json` (rdfc10_runner.ml:264-282) always emits the trailing
newline, matching every other fixture. **Not part of this plan**;
optionally make the map-test comparison trim trailing whitespace
before `=`, but this is a harness-tolerance nicety, not an algorithm
fix.

### Cluster D — N-Quads serialization/escaping bug, no blank nodes involved. 1 ID.

`test060c` — "n-quads escaping". Input has **zero** blank nodes
(all subjects/objects are IRIs or literals with `\uXXXX`/`\UXXXXXXXX`/
control-char escapes); `got` is 253 bytes **shorter** than `expected`
(1920 vs 2173), i.e. content is being dropped, not relabelled — this
cannot be an HNDQ symptom. Matches the already-filed diagnosis in
`docs/designissues/2026-04-25-rdfc10-phase3-investigation.md` line 27:
"(d) serialiser bug — `escape_lit_char` lacks `\uXXXX`/`\UXXXXXXXX`
escaping for < 0x20 codepoints, IRI escapes too." **Not part of this
plan**; separate ticket against `escape_lit`/`canon_term`
(`RDF.Canonical.fst:68-107`) and/or `Parser_NQuads`.

**Count check:** 18 + 2 + 1 + 1 = 22. Matches the runner's FAIL count.

## Implementation plan

### Stage 1 — Hash Related Blank Node conformance (small diff, `RDF.Canonical.fst` only)

New helper (place after `hash_sha256` / near `nbr_position_tag`):

```fstar
// RDFC-1.0 §4.8 Hash Related Blank Node: input := position
// [+ "<" + predicate + ">" if position <> "g"] + identifier; return
// hash_algorithm(input). `identifier` is resolved by the caller
// (already-issued "_:<label>" or the bare HFDQ fallback).
let hash_related_blank_node (pos : string) (pred : string) (identifier : string)
  : string =
  let input = pos ^ (if pos <> "g" then "<" ^ pred ^ ">" else "") ^ identifier in
  hash_sha256 input
```

Change `build_buckets_for` to take the issuer state and resolve the
identifier per spec's three-way branch before hashing:

```fstar
let rec build_buckets_for
    (target : bnode_id)
    (qs : list qquad)
    (hfdq_table : list bn_hfdq_pair)
    (st : issuer_state)                 // NEW — needed for the
                                         // already-issued check
    (acc : list bucket)
  : Tot (list bucket) (decreases qs) =
  match qs with
  | [] -> acc
  | q :: rest ->
    if not (quad_mentions_bnode target q) then
      build_buckets_for target rest hfdq_table st acc
    else
      let (_, t) = q in
      let pos = nbr_position_tag target q in
      let pred = t.p in
      let entry = (match related_bnode target q with
        | None -> None
        | Some rb ->
          let identifier =
            match lookup_issued rb st.is_issued with
            | Some lbl -> "_:" ^ lbl              // branch 1/2 (unified:
                                                   // st already carries
                                                   // both canonical and
                                                   // in-progress temp ids)
            | None -> lookup_hfdq rb hfdq_table    // branch 3
          in
          Some (rb, hash_related_blank_node pos pred identifier)) in
      let acc' = match entry with
        | None ->
          let k = "*" ^ pos ^ "|" ^ pred ^ "|_" in   // unchanged —
                                                       // see note below
          bucket_insert k "_" acc
        | Some (rb, related_hash) ->
          bucket_insert related_hash rb acc          // key is now the
                                                       // spec hash, not
                                                       // the raw preimage
      in
      build_buckets_for target rest hfdq_table st acc'
```

Update the one call site (`hndq_run`, `RDF.Canonical.fst:944`):

```fstar
    let buckets = build_buckets_for target qs hfdq_table st [] in
```
becomes
```fstar
    let buckets = build_buckets_for target qs hfdq_table st st [] in
```
(`st` passed both for the lookup table build and as the initial
`acc`-position — check the actual arg order against the file; the
point is: `st` must be in scope at this call, which it already is as
`hndq_run`'s own parameter, so this is a pure threading change with no
new plumbing needed above `hndq_run`.)

Note on the `"*"` no-related-bnode sentinel bucket (the `entry = None`
arm): per spec, quads with no related-bnode component contribute
**nothing** to `Hn` at all (Hash Related Blank Node is only invoked
"for each component in quad ... that is a blank node not equal to
identifier"). Our code manufactures an extra bucket for these to fold
target's own literal/IRI-only quads into the N-degree hash. This is
*not* spec-literal but is deterministic and constant per `target`
(same contribution every time `target` is explored, from any calling
context), so it is very unlikely to be the cause of any of the 22
failures — leave it alone for Stage 1; revisit only if a specific test
still fails after Stage 1+2 and traces back to this bucket.

**Gate 0 (do this before writing any code):** instrument
`build_buckets_for` (or add a debug print behind a flag) to report the
max bucket size actually reached, for each of the 18 Cluster-A tests,
with the CURRENT (buggy) code. If any bucket for `test044-046`,
`test054`, or `test059` exceeds 6 members, `take_n 6` is silently
truncating permutation input and must be raised (e.g. to 8 or 10) —
this is a one-line change (`take_n 6` → `take_n N`) but changes the
factorial cost (`8! = 40320` vs `6! = 720`); confirm the runner still
finishes within the project's ad-hoc-run cap (10 min, rule #17) before
committing to a specific N.

### Stage 2 — fresh local issuer + replay (needed for the 5 larger IDs, `RDF.Canonical.fst` only)

Only attempt this if Gate 0 / Stage 1 measurement shows `test044-046`,
`test054`, `test059` still fail after Stage 1 lands and the failure
signature still looks like a labelling swap (not a bucket-truncation
symptom already fixed by Gate 0's cap raise).

1. Add a prefix field to the issuer record so the same type serves
   both roles:

   ```fstar
   type issuer_state = {
     is_counter : nat;
     is_issued  : list (bnode_id * string);
     is_prefix  : string;      // NEW — "c14n" for the real canonical
                                // issuer, "tmp" (or any non-c14n
                                // string) for a per-candidate scratch
                                // issuer used only during exploration
   }

   let empty_issuer : issuer_state = { is_counter = 0; is_issued = []; is_prefix = "c14n" }
   let empty_local_issuer : issuer_state = { is_counter = 0; is_issued = []; is_prefix = "tmp" }
   ```

   `issue_identifier` changes one line: `"c14n" ^ nat_to_string ...` →
   `st.is_prefix ^ nat_to_string ...`.

2. Thread **two** issuer states through the HNDQ recursion instead of
   one: `canon_st` (read-only during exploration — used by
   `build_buckets_for`'s `lookup_issued` check, per spec branch 1/2
   unified since a canonically-committed id and an in-progress local
   id are still distinguishable by checking `canon_st` first, then
   `local_st`) and `local_st` (read-write, the fresh 0-anchored scratch
   issuer for this one candidate's exploration). Every function in the
   `hndq_run`/`walk_buckets`/`best_permutation`/`pick_best`/`walk_perm`
   mutual-recursion group gains a `canon_st : issuer_state` parameter
   alongside its existing `st` (which becomes `local_st`).

3. `process_collision_members` (lines 1063-1088): for each unissued
   member `m`, start `local0 = { empty_local_issuer with is_issued = [] }`
   (fresh every time, NOT derived from `st`), issue `m` into `local0`,
   call `hndq_run fuel qs hfdq_table canon_st local0 m`, compare
   resulting hashes as today, keep the winner's `(m, local_final)`.

4. New replay step, run once per collision group after the winner is
   chosen (replaces the current "commit `best_st` directly" with an
   explicit fold over the winner's issuance order — which
   `is_issued`'s append-only construction already preserves):

   ```fstar
   let rec replay_into_canonical (canon_st : issuer_state)
       (temp_issued : list (bnode_id * string))
     : Tot issuer_state (decreases temp_issued) =
     match temp_issued with
     | [] -> canon_st
     | (b, _) :: rest ->
       let (canon_st', _) = issue_identifier canon_st b in
       replay_into_canonical canon_st' rest
   ```

   `process_collision_members` returns `replay_into_canonical st
   best_local.is_issued` instead of `best_st` directly.

Termination for Stage 2: no new fuel construct needed. `local_st`'s
exploration still uses the existing `fuel = |bs| + 1` bound (each
candidate's own exploration is still one bounded `hndq_run` call);
`replay_into_canonical` is structurally recursive on a finite,
already-computed list — trivially `Tot`.

## Predicted score after each stage

- **Stage 1 only:** 63 → ~76 pass (the 13 small Cluster-A IDs flip:
  `test023c`, `test033c`, `test034c`, `test035c`, `test036c`,
  `test038c`, `test039c`, `test040c`, `test058c`, `test047c`,
  `test047m`, `test048c`, `test048m`). The 5 large Cluster-A IDs
  (`test044c/045c/046c/054c/059c`) may or may not flip — depends on
  whether Gate 0 finds bucket truncation and whether the
  shared-counter digit-boundary risk actually bites for these
  specific graphs (untested; requires running the fixed code, which
  this diagnosis session did not do per its scope).
- **Stage 1 + Stage 2:** 63 → ~81 pass if all 5 large IDs flip (18/18
  of Cluster A). Clusters B/C/D (4 IDs: `test075c/075m`, `test073m`,
  `test060c`) remain — separate, already-scoped-out tickets.
- Ceiling for *this* plan: 81/86 (94%), with the remaining 5
  (`test074c` poison-clique NegEval stub is not in the 22 fail count
  and is separately deferred per the file's own header note at line
  483/1121) attributable to Clusters B/C/D, not N-degree.

## One-cycle implementation brief

- **File touched:** `formal/fstar/RDF.Canonical.fst` only. No OCaml
  changes (`build_canonical_mapping`'s public signature is unchanged
  in Stage 1; Stage 2 changes only internal helpers, not
  `canonicalize` / `canonicalize_to_nquads` / `build_canonical_mapping`
  signatures, so `bin/rdfc10-runner/rdfc10_runner.ml` needs no edits
  for either stage).
- **Stage 1 diff:** ~25 LoC (1 new function, 1 signature change + body
  rewrite in `build_buckets_for`, 1 call-site update in `hndq_run`).
- **Stage 2 diff (conditional on Gate 0/Stage-1 results):** ~60-80 LoC
  (1 record field, threading a second issuer param through 5 mutually
  recursive functions, 1 new `replay_into_canonical` fold).
- **Gates before landing:**
  1. Gate 0 (bucket-size instrumentation) run *before* Stage 1 lands,
     to decide whether `take_n 6` needs raising alongside Stage 1.
  2. `fstar.exe RDF.Canonical.fst` verifies clean — no `--lax`, no
     `--admit_smt_queries` (rule #10).
  3. `build-ocaml.sh extract` (not `compile` — rule #11) then rebuild
     `rdfc10_runner`.
  4. Re-run `bin/linux-x86_64/rdfc10_runner` (and darwin-arm64 if
     available) and diff the FAIL list against the 18 Cluster-A IDs
     above; report the actual delta, labelled (e.g. "76 pass, 9 fail,
     1 stub — flipped 13/18, test044-046/054/059 still fail" if
     Stage 1 alone is landed first), per rule #25 (no unlabelled score
     strings).
  5. Confirm the previously-passing 63 still pass (no regressions) —
     the runner's full summary line covers this for free.
- **Non-goals for this plan** (tracked separately, see Clusters B/C/D
  above): SHA-384 dispatch (`test075c/075m`), map-test trailing-newline
  fixture tolerance (`test073m`), N-Quads literal/IRI escape
  serialization (`test060c`).
