#!/bin/bash
# tests/unit/run-jena-diff.sh
#
# Differential testing harness: runs the SAME RDF input files through
# Factoidal's extracted parser (bin/factoidal-dump-nq) and through
# Apache Jena (riot + rdfcompare), and reports where the two
# independent implementations agree or disagree.
#
# Why this exists: issue #317 (review gate 4). Our W3C suite scores
# (631/631, 1031/1031 etc. — see docs/test-results) are graded against
# expectation files we also wrote. If our reading of a spec is wrong
# in the same way our test expectations are wrong, the W3C suite
# cannot catch it. An independent engine reading the SAME raw input
# files is the only cross-check that does not share that blind spot.
#
# SCOPE (v2, 2026-08-14 — extends v1's Turtle/N-Triples-only coverage):
#   Turtle, N-Triples, TriG, N-Quads — from the W3C rdf-tests corpus
#   vendored at third_party/testing/w3c/rdf/rdf11/{rdf-turtle,
#   rdf-n-triples,rdf-trig,rdf-n-quads}/*.{ttl,nt,trig,nq}.
#   v1 (landed with PR #427) covered Turtle/N-Triples only and, by its
#   own scope note, explicitly missed TriG — the two real engine bugs
#   #433 (collection as subject) and #434 (trailing ';' before '}')
#   were BOTH TriG-only and neither was caught by v1, because TriG was
#   outside its coverage. This version closes that gap.
#   RDF/XML is still out of scope: it has no *_strict OCaml wiring
#   issue (Parser.RDFXML.fst has parse_rdfxml_strict /
#   parse_rdfxml_with_base_strict extracted and wired below in
#   factoidal-dump-nq --format rdfxml --strict), but its W3C corpus is
#   laid out in per-testcase subdirectories rather than one flat
#   directory of files, which this harness's simple `find -maxdepth 1`
#   corpus walk does not handle yet — left for a follow-up pass.
#
# PARSER MODE: this harness calls `factoidal-dump-nq --strict`, not
# the tool's plain lenient mode. Plain mode is a best-effort dump tool
# that silently drops malformed input instead of failing, so every
# W3C negative-syntax fixture ("*-bad-*") would come back as "parsed
# successfully, zero triples" — a false disagreement against Jena's
# correct rejection. --strict routes through option-returning parser
# entry points (parse_turtle_strict / parse_ntriples_strict /
# parse_trig[_with_base] / parse_nquads_strict /
# parse_rdfxml[_with_base]_strict) so this harness's accept/reject
# verdict matches what the W3C conformance suite actually grades.
# TriG's un-suffixed parse_trig / parse_trig_with_base were ALREADY
# option-returning before this harness extension — only the OCaml
# dispatch in factoidal_dump_nq.ml needed wiring, no new F* code (see
# that file's --strict comment for the full naming-history note).
#
# COMPARISON METHOD — Turtle / N-Triples (single graph, unchanged from
# v1): both engines parse the file; the resulting N-Triples outputs
# are handed to Jena's OWN `rdfcompare` tool, which checks RDF GRAPH
# ISOMORPHISM (same triples up to blank-node renaming), not string
# equality. This is the ONE normalization applied for these two
# formats, documented here so a "disagree" verdict is trusted to mean
# a real semantic disagreement, not a labelling artefact.
#
# COMPARISON METHOD — TriG / N-Quads (datasets: one default graph plus
# zero or more named graphs): Jena's rdfcompare/rdfdiff do NOT accept
# N-Quads or TriG as an input language (confirmed by running
# `rdfcompare --help` / `rdfdiff --help` — both list only RDF/XML,
# N-TRIPLE, TURTLE, JSON-LD), so the Turtle/N-Triples method does not
# extend directly to datasets. This is the exact obstacle PR #427's
# report flagged. Of the three options that report considered:
#   (a) riot --output=nq on both sides + a per-graph isomorphism-aware
#       split, still using Jena's rdfcompare for the actual isomorphism
#       judgment — CHOSEN.
#   (b) our own RDFC-1.0 canonicalizer (rdfc10_runner) on both sides —
#       REJECTED for this harness. It is a trustworthy instrument on
#       its own (W3C rdf-canon suite: 86 pass, 0 fail, of 86) but using
#       it on BOTH sides of THIS comparison means a shared bug in our
#       own canonicalizer could make two genuinely non-isomorphic
#       datasets canonicalize to the same output, masking exactly the
#       kind of disagreement this harness exists to catch (issue #317's
#       whole premise: our own tooling can share our own blind spots).
#       Jena's rdfcompare has no such shared-bug risk against our
#       parser, which is why (a) keeps using it as the actual judge.
#   (c) a small dataset-aware shell/awk comparison reimplementing
#       structural matching — REJECTED as the primary mechanism (would
#       mean hand-rolling N-Quads term parsing in shell, which is a
#       parser outside F*, the exact thing iron rule #4 / anti-pattern
#       #1 ban) but its SPIRIT survives in (a): the harness's only new
#       logic is trivial dataset-record selection (filter a parsed
#       rdf_dataset by graph name), built with the ALREADY-EXTRACTED
#       Parser_NQuads.parse_nquads_strict / RDF_Graph.lookup_named_graph
#       / RDF_Canonical.is_bnode_graph_label — no new parsing, no new
#       RDF semantics, just glue in the consumer tool (rule #11: bin/
#       is outside the verified-library boundary).
#
#   Mechanism: `factoidal-dump-nq` gained two new subcommands
#   (--list-graph-keys, --extract-graph) for this harness. Both sides'
#   N-Quads output (factoidal's own canonical form, and Jena's
#   `riot --output=NQUADS`) is re-read through our OWN already-
#   extracted N-Quads parser (N-Quads is a shared interchange format
#   both engines emit), split by graph key, and each matched graph
#   pair (default graph, or same-IRI named graph) is compared with
#   `rdfcompare` in N-TRIPLE mode — the exact same isomorphism
#   instrument the Turtle/N-Triples path already trusts.
#
#   Graph key normalization (the ONLY normalization applied beyond the
#   Turtle/N-Triples path's isomorphism check):
#     "DEFAULT"     the default graph.
#     "<iri>"       a named graph keyed by its exact IRI text — IRIs
#                   are not blank-node-renamed, so this string matches
#                   directly across engines.
#     "ANON_POOL"   KNOWN LIMITATION: TriG allows a BLANK NODE as a
#                   graph name (`_:g { }` / `[] { }`); each engine
#                   assigns that label independently, so — unlike
#                   triple-level blank nodes, which rdfcompare already
#                   handles correctly — two blank-node-named GRAPHS
#                   cannot be string-matched across engines. All
#                   blank-node-named graphs' triples are pooled into
#                   one bucket per side and compared as one unit. This
#                   can miss a disagreement where content is swapped
#                   between two distinct anonymous graphs while the
#                   pooled union stays isomorphic. Only 3 of 357
#                   vendored rdf-trig files use a blank-node graph name
#                   (alternating_bnode_graphs.trig,
#                   labeled_blank_node_graph.trig,
#                   trig-syntax-minimal-whitespace-01.trig) — an
#                   honest gap, not a silently-assumed one.
#   A GRAPH-KEY-SET mismatch (one side has a graph key the other
#   doesn't, "ANON_POOL" included) is itself reported as a disagree,
#   not silently ignored — see compare_dataset_one's key-set check.
#
# CLASSIFICATION per file (same four buckets as v1, now computed
# per-graph for TriG/N-Quads and rolled up to one file-level verdict —
# ANY graph disagreeing makes the whole file "disagree"):
#   agree-parse    both engines accept the file AND every graph
#                  (Turtle/N-Triples: the one graph; TriG/N-Quads:
#                  every matched graph key) is isomorphic.
#   agree-reject   both engines refuse to parse the file.
#   disagree       both engines accept the file but at least one graph
#                  is NOT isomorphic, OR (TriG/N-Quads only) the two
#                  sides' graph-key sets differ. Logged with the
#                  witness (both engines' N-Triples/N-Quads output, or
#                  the key-set diff).
#   either-side-error   exactly one engine accepted the file.
#
# Counts are reported PER FORMAT (turtle / ntriples / trig / nquads),
# each labelled with its own denominator, plus a combined total — never
# one unlabelled combined number (CLAUDE.md rule #25).
#
# Every disagree / either-side-error file gets its own section in the
# output (CLAUDE.md: "any disagreement is a FINDING to investigate,
# not a test to silence").
#
# Usage:
#   tests/unit/run-jena-diff.sh              # skip with reason if Jena absent
#   tests/unit/run-jena-diff.sh --jena        # same as above (explicit opt-in, CI precedent)
#   JENA_HOME=/path/to/apache-jena-6.2.0 tests/unit/run-jena-diff.sh
#   tests/unit/run-jena-diff.sh --strict      # exit 1 if disagree>0 or either-side-error>0
#
# Jena install: see README.md "Jena differential harness" section, or
# tools/install-jena-for-diff-testing.sh.
#
# Exit code: 0 on a completed run (findings are reported, not failed,
# unless --strict is passed) or on a documented skip. Non-zero only on
# a harness/environment failure (missing factoidal-dump-nq binary, a
# Jena tool crashing instead of returning a parse verdict, etc.).
#
# Rule anchors: CLAUDE.md rule #16 (no tail/head truncation), rule #25
# (labelled score line), rule #14 (documented normalization).

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

STRICT=0
ONLY="all"
skip_next=0
args=("$@")
for i in "${!args[@]}"; do
  if [[ $skip_next -eq 1 ]]; then skip_next=0; continue; fi
  arg="${args[$i]}"
  case "$arg" in
    --jena) : ;;  # explicit opt-in flag, precedent from run-jsoo-equivalence.sh --jsoo; no-op here since this script IS the opt-in entry point
    --strict) STRICT=1 ;;
    --only)
      ONLY="${args[$((i+1))]:-}"
      if [[ -z "$ONLY" ]]; then echo "run-jena-diff: --only needs an argument (turtle|ntriples|trig|nquads)" >&2; exit 2; fi
      skip_next=1
      ;;
    --help|-h)
      sed -n '2,140p' "$0"
      exit 0
      ;;
    *)
      echo "run-jena-diff: unknown argument '$arg'" >&2
      exit 2
      ;;
  esac
done
# --only FMT (2026-08-14, TriG/N-Quads extension): run a single
# format's corpus. Not for routine use -- the full run is the
# reported number -- but each format is fully independent (no shared
# state between compare_one/compare_dataset_one calls), so this lets
# the four format corpora run as separate parallel background
# processes when the full sequential run's wall-clock time (each
# comparison spawns 1-3 fresh JVMs; TriG especially, at up to one
# rdfcompare per named graph) is inconvenient, e.g. for interactive
# investigation of one format's disagreements. Results are the same
# either way; this is a wall-clock knob, not a semantic one.

# ---------------------------------------------------------------------
# Locate Jena. Skip (exit 0) with a clear reason if not found — this
# harness must never fake a comparison (CLAUDE.md: "a harness that
# pretends to compare while comparing nothing is the exact vacuity
# trap this repo bans").
# ---------------------------------------------------------------------
DEFAULT_JENA_CACHE_GLOB="$REPO_ROOT/.jena-cache/apache-jena-"*
JENA_HOME="${JENA_HOME:-}"
if [[ -z "$JENA_HOME" ]]; then
  for cand in $DEFAULT_JENA_CACHE_GLOB; do
    if [[ -x "$cand/bin/riot" ]]; then
      JENA_HOME="$cand"
      break
    fi
  done
fi

if [[ -z "$JENA_HOME" || ! -x "$JENA_HOME/bin/riot" || ! -x "$JENA_HOME/bin/rdfcompare" ]]; then
  cat <<'EOF'
run-jena-diff: SKIP (reason: Jena not found)

No usable Apache Jena installation was found. This harness compares
Factoidal's parser output against Jena's as an independent
cross-check (issue #317); without Jena there is nothing to compare
against, so this is a skip, not a silent pass.

To run this harness:
  1. Install Jena — see README.md "Jena differential harness" section
     or run: tools/install-jena-for-diff-testing.sh
  2. Either let it land at the default cache path
     ($REPO_ROOT/.jena-cache/apache-jena-<version>/), or set:
       export JENA_HOME=/path/to/apache-jena-<version>
  3. Re-run: tests/unit/run-jena-diff.sh
EOF
  exit 0
fi

RIOT="$JENA_HOME/bin/riot"
RDFCOMPARE="$JENA_HOME/bin/rdfcompare"

DUMP_NQ="$REPO_ROOT/formal/fstar/ocaml-output/factoidal-dump-nq"
if [[ ! -x "$DUMP_NQ" ]]; then
  echo "ERROR: $DUMP_NQ not found or not executable — build it first" \
       "(cd formal/fstar && ./build-ocaml-serializer.sh)" >&2
  exit 1
fi

WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

CORPUS_TURTLE="$REPO_ROOT/third_party/testing/w3c/rdf/rdf11/rdf-turtle"
CORPUS_NTRIPLES="$REPO_ROOT/third_party/testing/w3c/rdf/rdf11/rdf-n-triples"
CORPUS_TRIG="$REPO_ROOT/third_party/testing/w3c/rdf/rdf11/rdf-trig"
CORPUS_NQUADS="$REPO_ROOT/third_party/testing/w3c/rdf/rdf11/rdf-n-quads"
for d in "$CORPUS_TURTLE" "$CORPUS_NTRIPLES" "$CORPUS_TRIG" "$CORPUS_NQUADS"; do
  if [[ ! -d "$d" ]]; then
    echo "ERROR: corpus directory not found: $d" \
         "(run tools/ensure-test-env.sh to fetch W3C test submodules)" >&2
    exit 1
  fi
done

# Per-format counters (CLAUDE.md rule #25: never one unlabelled number).
declare -A n_agree_parse=( [turtle]=0 [ntriples]=0 [trig]=0 [nquads]=0 )
declare -A n_agree_reject=( [turtle]=0 [ntriples]=0 [trig]=0 [nquads]=0 )
declare -A n_disagree=( [turtle]=0 [ntriples]=0 [trig]=0 [nquads]=0 )
declare -A n_either_side_error=( [turtle]=0 [ntriples]=0 [trig]=0 [nquads]=0 )
declare -A n_total=( [turtle]=0 [ntriples]=0 [trig]=0 [nquads]=0 )

DISAGREE_LOG="$WORK_DIR/disagree.log"
ESE_LOG="$WORK_DIR/either_side_error.log"
: > "$DISAGREE_LOG"
: > "$ESE_LOG"

# strip_java_noise FILE: removes the JAVA_TOOL_OPTIONS proxy-config
# echo riot/rdfcompare print to stderr in this environment (see
# /root/.ccr/README.md) — proxy config echo, not a parse diagnostic.
strip_java_noise() {
  grep -v '^Picked up JAVA_TOOL_OPTIONS' "$1" > "$1.clean" 2>/dev/null || true
  mv "$1.clean" "$1" 2>/dev/null || true
}

# ---------------------------------------------------------------------
# Turtle / N-Triples: single-graph comparison via Jena rdfcompare
# directly on each engine's N-Triples output. Unchanged from v1.
# ---------------------------------------------------------------------
compare_one() {
  local file="$1" fmt_factoidal="$2" fmt_jena="$3" fmt_label="$4"
  n_total[$fmt_label]=$((n_total[$fmt_label] + 1))

  local f_out="$WORK_DIR/f.nt"
  local j_out="$WORK_DIR/j.nt"
  local f_err="$WORK_DIR/f.err"
  local j_err="$WORK_DIR/j.err"

  local f_rc=0 j_rc=0
  "$DUMP_NQ" --format "$fmt_factoidal" --strict "$file" > "$f_out" 2> "$f_err" || f_rc=$?
  "$RIOT" --syntax="$fmt_jena" --output=NTRIPLES "$file" > "$j_out" 2> "$j_err" || j_rc=$?
  strip_java_noise "$j_err"

  if [[ $f_rc -eq 0 && $j_rc -eq 0 ]]; then
    local cmp_out
    cmp_out="$("$RDFCOMPARE" "$f_out" "$j_out" N-TRIPLE N-TRIPLE 2>/dev/null)"
    if echo "$cmp_out" | grep -q "models are equal"; then
      n_agree_parse[$fmt_label]=$((n_agree_parse[$fmt_label] + 1))
    else
      n_disagree[$fmt_label]=$((n_disagree[$fmt_label] + 1))
      {
        echo "### DISAGREE ($fmt_label): $file"
        echo "rdfcompare verdict: $cmp_out"
        echo "--- factoidal-dump-nq output ---"
        cat "$f_out"
        echo "--- jena riot output ---"
        cat "$j_out"
        echo
      } >> "$DISAGREE_LOG"
    fi
  elif [[ $f_rc -ne 0 && $j_rc -ne 0 ]]; then
    n_agree_reject[$fmt_label]=$((n_agree_reject[$fmt_label] + 1))
  else
    n_either_side_error[$fmt_label]=$((n_either_side_error[$fmt_label] + 1))
    {
      echo "### EITHER-SIDE-ERROR ($fmt_label): $file"
      if [[ $f_rc -ne 0 ]]; then
        echo "factoidal REJECTED (rc=$f_rc), jena ACCEPTED"
        echo "--- factoidal-dump-nq stderr ---"; cat "$f_err"
        echo "--- jena riot output (accepted) ---"; cat "$j_out"
      else
        echo "jena REJECTED (rc=$j_rc), factoidal ACCEPTED"
        echo "--- jena riot stderr ---"; cat "$j_err"
        echo "--- factoidal-dump-nq output (accepted) ---"; cat "$f_out"
      fi
      echo
    } >> "$ESE_LOG"
  fi
}

# ---------------------------------------------------------------------
# TriG / N-Quads: dataset-wise comparison. See the big comment block
# at the top of this file ("COMPARISON METHOD — TriG / N-Quads") for
# the method and its documented limitation (ANON_POOL).
# ---------------------------------------------------------------------
compare_dataset_one() {
  local file="$1" fmt_factoidal="$2" fmt_jena="$3" fmt_label="$4"
  n_total[$fmt_label]=$((n_total[$fmt_label] + 1))

  local f_out="$WORK_DIR/f.nq"
  local j_out="$WORK_DIR/j.nq"
  local f_err="$WORK_DIR/f.err"
  local j_err="$WORK_DIR/j.err"

  local f_rc=0 j_rc=0
  "$DUMP_NQ" --format "$fmt_factoidal" --strict "$file" > "$f_out" 2> "$f_err" || f_rc=$?
  "$RIOT" --syntax="$fmt_jena" --output=NQUADS "$file" > "$j_out" 2> "$j_err" || j_rc=$?
  strip_java_noise "$j_err"

  if [[ $f_rc -eq 0 && $j_rc -eq 0 ]]; then
    local f_keys_file="$WORK_DIR/f.keys"
    local j_keys_file="$WORK_DIR/j.keys"
    "$DUMP_NQ" --list-graph-keys "$f_out" | sort -u > "$f_keys_file"
    "$DUMP_NQ" --list-graph-keys "$j_out" | sort -u > "$j_keys_file"

    if ! diff -q "$f_keys_file" "$j_keys_file" > /dev/null 2>&1; then
      n_disagree[$fmt_label]=$((n_disagree[$fmt_label] + 1))
      {
        echo "### DISAGREE ($fmt_label): $file"
        echo "graph-key sets differ:"
        diff "$f_keys_file" "$j_keys_file" | sed 's/^/  /'
        echo "--- factoidal-dump-nq output ---"; cat "$f_out"
        echo "--- jena riot output ---"; cat "$j_out"
        echo
      } >> "$DISAGREE_LOG"
      return
    fi

    local all_ok=1
    local verdicts=""
    while IFS= read -r key; do
      [[ -z "$key" ]] && continue
      local fg="$WORK_DIR/fg.nt"
      local jg="$WORK_DIR/jg.nt"
      "$DUMP_NQ" --extract-graph "$key" "$f_out" > "$fg" 2>/dev/null
      "$DUMP_NQ" --extract-graph "$key" "$j_out" > "$jg" 2>/dev/null
      local cmp_out
      cmp_out="$("$RDFCOMPARE" "$fg" "$jg" N-TRIPLE N-TRIPLE 2>/dev/null)"
      verdicts="${verdicts}  graph $key: $cmp_out"$'\n'
      if ! echo "$cmp_out" | grep -q "models are equal"; then
        all_ok=0
      fi
    done < "$f_keys_file"

    if [[ $all_ok -eq 1 ]]; then
      n_agree_parse[$fmt_label]=$((n_agree_parse[$fmt_label] + 1))
    else
      n_disagree[$fmt_label]=$((n_disagree[$fmt_label] + 1))
      {
        echo "### DISAGREE ($fmt_label): $file"
        echo "per-graph rdfcompare verdicts:"
        printf '%s' "$verdicts"
        echo "--- factoidal-dump-nq output ---"; cat "$f_out"
        echo "--- jena riot output ---"; cat "$j_out"
        echo
      } >> "$DISAGREE_LOG"
    fi
  elif [[ $f_rc -ne 0 && $j_rc -ne 0 ]]; then
    n_agree_reject[$fmt_label]=$((n_agree_reject[$fmt_label] + 1))
  else
    n_either_side_error[$fmt_label]=$((n_either_side_error[$fmt_label] + 1))
    {
      echo "### EITHER-SIDE-ERROR ($fmt_label): $file"
      if [[ $f_rc -ne 0 ]]; then
        echo "factoidal REJECTED (rc=$f_rc), jena ACCEPTED"
        echo "--- factoidal-dump-nq stderr ---"; cat "$f_err"
        echo "--- jena riot output (accepted) ---"; cat "$j_out"
      else
        echo "jena REJECTED (rc=$j_rc), factoidal ACCEPTED"
        echo "--- jena riot stderr ---"; cat "$j_err"
        echo "--- factoidal-dump-nq output (accepted) ---"; cat "$f_out"
      fi
      echo
    } >> "$ESE_LOG"
  fi
}

echo "run-jena-diff: Jena found at $JENA_HOME"
echo "run-jena-diff: comparing corpus files (Turtle, N-Triples, TriG, N-Quads; positive+negative alike — classification decides the bucket); --only=$ONLY"
echo

# print_fmt_summary FMT: emitted right after that format's loop
# finishes, so a run that is later interrupted (or capped by an
# external `timeout`) still leaves the already-completed formats'
# labelled counts in the log instead of losing them to a summary that
# only prints once at the very end.
print_fmt_summary() {
  local fmt="$1"
  echo "run-jena-diff: [$fmt] done (of ${n_total[$fmt]} files): ${n_agree_parse[$fmt]} agree-parse, ${n_agree_reject[$fmt]} agree-reject, ${n_disagree[$fmt]} disagree, ${n_either_side_error[$fmt]} either-side-error"
}

if [[ "$ONLY" == "all" || "$ONLY" == "turtle" ]]; then
  while IFS= read -r -d '' f; do
    compare_one "$f" "turtle" "TURTLE" "turtle"
  done < <(find "$CORPUS_TURTLE" -maxdepth 1 -type f -name '*.ttl' -print0 | sort -z)
  print_fmt_summary turtle
fi

if [[ "$ONLY" == "all" || "$ONLY" == "ntriples" ]]; then
  while IFS= read -r -d '' f; do
    compare_one "$f" "nt" "NTRIPLES" "ntriples"
  done < <(find "$CORPUS_NTRIPLES" -maxdepth 1 -type f -name '*.nt' -print0 | sort -z)
  print_fmt_summary ntriples
fi

if [[ "$ONLY" == "all" || "$ONLY" == "trig" ]]; then
  while IFS= read -r -d '' f; do
    compare_dataset_one "$f" "trig" "TRIG" "trig"
  done < <(find "$CORPUS_TRIG" -maxdepth 1 -type f -name '*.trig' -print0 | sort -z)
  print_fmt_summary trig
fi

if [[ "$ONLY" == "all" || "$ONLY" == "nquads" ]]; then
  while IFS= read -r -d '' f; do
    compare_dataset_one "$f" "nq" "NQUADS" "nquads"
  done < <(find "$CORPUS_NQUADS" -maxdepth 1 -type f -name '*.nq' -print0 | sort -z)
  print_fmt_summary nquads
fi

echo "============================================================"
if [[ -s "$DISAGREE_LOG" ]]; then
  echo "--- DISAGREEMENTS (both engines parsed, graphs not isomorphic) ---"
  cat "$DISAGREE_LOG"
fi
if [[ -s "$ESE_LOG" ]]; then
  echo "--- EITHER-SIDE-ERRORS (one engine accepted, one rejected) ---"
  cat "$ESE_LOG"
fi

echo "============================================================"
echo "run-jena-diff summary (labelled per format; CLAUDE.md rule #25):"
grand_agree_parse=0 grand_agree_reject=0 grand_disagree=0 grand_ese=0 grand_total=0
for fmt in turtle ntriples trig nquads; do
  echo "  [$fmt] (of ${n_total[$fmt]} files): ${n_agree_parse[$fmt]} agree-parse, ${n_agree_reject[$fmt]} agree-reject, ${n_disagree[$fmt]} disagree, ${n_either_side_error[$fmt]} either-side-error"
  grand_agree_parse=$((grand_agree_parse + n_agree_parse[$fmt]))
  grand_agree_reject=$((grand_agree_reject + n_agree_reject[$fmt]))
  grand_disagree=$((grand_disagree + n_disagree[$fmt]))
  grand_ese=$((grand_ese + n_either_side_error[$fmt]))
  grand_total=$((grand_total + n_total[$fmt]))
done
echo "  [combined] (of $grand_total files): $grand_agree_parse agree-parse, $grand_agree_reject agree-reject, $grand_disagree disagree, $grand_ese either-side-error"

if [[ $STRICT -eq 1 && ( $grand_disagree -gt 0 || $grand_ese -gt 0 ) ]]; then
  echo "run-jena-diff: FAIL (--strict, and disagree+either-side-error > 0)"
  exit 1
fi

exit 0
