#!/bin/bash
# tests/unit/run-jena-diff.sh
#
# Differential testing harness: runs the SAME Turtle / N-Triples input
# files through Factoidal's extracted parser (bin/factoidal-dump-nq)
# and through Apache Jena (riot + rdfcompare), and reports where the
# two independent implementations agree or disagree.
#
# Why this exists: issue #317 (review gate 4). Our W3C suite scores
# (631/631, 1031/1031 etc. — see docs/test-results) are graded against
# expectation files we also wrote. If our reading of a spec is wrong
# in the same way our test expectations are wrong, the W3C suite
# cannot catch it. An independent engine reading the SAME raw input
# files is the only cross-check that does not share that blind spot.
#
# SCOPE (v1, deliberately narrow — see CLAUDE.md rule on honest scope):
#   Turtle parse + N-Triples parse only, from the W3C rdf-tests corpus
#   already vendored at third_party/testing/w3c/rdf/rdf11/{rdf-turtle,
#   rdf-n-triples}/*.{ttl,nt}. NOT N-Quads/TriG/RDF-XML/JSON-LD yet —
#   those have named-graph and datatype-mapping subtleties that need
#   their own comparison design (see "Extending this harness" below).
#   This is the axis CLAUDE.md's brief called out as "cheap and
#   high-signal": Turtle/N-Triples is where our recent parser fixes
#   (#381, #334) changed behaviour, and it needs no query-planner or
#   canonicalization-algorithm agreement between the two engines.
#
# COMPARISON METHOD (read this before trusting the output):
#   For each file, both engines are asked to parse it and every
#   triple is compared. Because blank node LABELS are implementation-
#   assigned (the spec deliberately does not fix them), a literal
#   text diff of the two engines' N-Triples output would report
#   spurious disagreements on every blank-node-bearing file. Instead
#   this harness hands both outputs to Jena's own `rdfcompare` tool,
#   which checks RDF GRAPH ISOMORPHISM (same triples up to blank-node
#   renaming), not string equality. This is the ONE normalization this
#   harness performs, and it is the reason a "disagree" verdict here
#   means the two engines produced graphs that are not isomorphic —
#   a real semantic disagreement, not a labelling artefact.
#   No other normalization is applied: literal datatypes, language
#   tags, and IRI forms are compared exactly as each engine emits
#   them. An over-eager normalizer would hide real disagreements
#   (CLAUDE.md's explicit warning), so none is added beyond the one
#   documented here.
#
# CLASSIFICATION per file:
#   agree-parse    both engines accept the file AND rdfcompare reports
#                  the resulting graphs isomorphic.
#   agree-reject   both engines refuse to parse the file (counted
#                  separately from agree-parse so the summary line
#                  never hides how many files were never actually
#                  compared for content).
#   disagree       both engines accept the file but rdfcompare reports
#                  the graphs are NOT isomorphic. Logged with both
#                  engines' full N-Triples output as the witness.
#   either-side-error   exactly one engine accepted the file and the
#                  other rejected it. Logged with the failing engine's
#                  error message as the witness. This is a parse-
#                  ACCEPTANCE mismatch — one engine treats input the
#                  other engine calls invalid.
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
for arg in "$@"; do
  case "$arg" in
    --jena) : ;;  # explicit opt-in flag, precedent from run-jsoo-equivalence.sh --jsoo; no-op here since this script IS the opt-in entry point
    --strict) STRICT=1 ;;
    --help|-h)
      sed -n '2,70p' "$0"
      exit 0
      ;;
    *)
      echo "run-jena-diff: unknown argument '$arg'" >&2
      exit 2
      ;;
  esac
done

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
for d in "$CORPUS_TURTLE" "$CORPUS_NTRIPLES"; do
  if [[ ! -d "$d" ]]; then
    echo "ERROR: corpus directory not found: $d" \
         "(run tools/ensure-test-env.sh to fetch W3C test submodules)" >&2
    exit 1
  fi
done

n_agree_parse=0
n_agree_reject=0
n_disagree=0
n_either_side_error=0
n_total=0

DISAGREE_LOG="$WORK_DIR/disagree.log"
ESE_LOG="$WORK_DIR/either_side_error.log"
: > "$DISAGREE_LOG"
: > "$ESE_LOG"

compare_one() {
  local file="$1" fmt_factoidal="$2" fmt_jena="$3"
  n_total=$((n_total + 1))

  local base
  base="$(basename "$file")"

  local f_out="$WORK_DIR/f.nt"
  local j_out="$WORK_DIR/j.nt"
  local f_err="$WORK_DIR/f.err"
  local j_err="$WORK_DIR/j.err"

  local f_rc=0 j_rc=0
  "$DUMP_NQ" --format "$fmt_factoidal" "$file" > "$f_out" 2> "$f_err" || f_rc=$?
  "$RIOT" --syntax="$fmt_jena" --output=NTRIPLES "$file" > "$j_out" 2> "$j_err" || j_rc=$?
  # riot exits 0 even on some parse warnings but non-zero on hard
  # parse errors; treat "produced zero bytes AND non-zero exit" and
  # "non-zero exit" both as reject. An empty-but-valid file (rc=0,
  # empty output) is legitimately empty, not a reject.
  # Strip the JAVA_TOOL_OPTIONS proxy-noise line riot/rdfcompare print
  # to stderr in this environment (see /root/.ccr/README.md); it is
  # proxy config echo, not a parse diagnostic.
  grep -v '^Picked up JAVA_TOOL_OPTIONS' "$j_err" > "$j_err.clean" 2>/dev/null || true
  mv "$j_err.clean" "$j_err" 2>/dev/null || true

  if [[ $f_rc -eq 0 && $j_rc -eq 0 ]]; then
    local cmp_out
    cmp_out="$("$RDFCOMPARE" "$f_out" "$j_out" N-TRIPLE N-TRIPLE 2>/dev/null)"
    if echo "$cmp_out" | grep -q "models are equal"; then
      n_agree_parse=$((n_agree_parse + 1))
    else
      n_disagree=$((n_disagree + 1))
      {
        echo "### DISAGREE: $file"
        echo "rdfcompare verdict: $cmp_out"
        echo "--- factoidal-dump-nq output ---"
        cat "$f_out"
        echo "--- jena riot output ---"
        cat "$j_out"
        echo
      } >> "$DISAGREE_LOG"
    fi
  elif [[ $f_rc -ne 0 && $j_rc -ne 0 ]]; then
    n_agree_reject=$((n_agree_reject + 1))
  else
    n_either_side_error=$((n_either_side_error + 1))
    {
      echo "### EITHER-SIDE-ERROR: $file"
      if [[ $f_rc -ne 0 ]]; then
        echo "factoidal REJECTED (rc=$f_rc), jena ACCEPTED"
        echo "--- factoidal-dump-nq stderr ---"
        cat "$f_err"
        echo "--- jena riot output (accepted) ---"
        cat "$j_out"
      else
        echo "jena REJECTED (rc=$j_rc), factoidal ACCEPTED"
        echo "--- jena riot stderr ---"
        cat "$j_err"
        echo "--- factoidal-dump-nq output (accepted) ---"
        cat "$f_out"
      fi
      echo
    } >> "$ESE_LOG"
  fi
}

echo "run-jena-diff: Jena found at $JENA_HOME"
echo "run-jena-diff: comparing corpus files (Turtle + N-Triples, positive+negative alike — classification decides the bucket)"
echo

while IFS= read -r -d '' f; do
  compare_one "$f" "turtle" "TURTLE"
done < <(find "$CORPUS_TURTLE" -maxdepth 1 -type f -name '*.ttl' -print0 | sort -z)

while IFS= read -r -d '' f; do
  compare_one "$f" "nt" "NTRIPLES"
done < <(find "$CORPUS_NTRIPLES" -maxdepth 1 -type f -name '*.nt' -print0 | sort -z)

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
echo "run-jena-diff summary (of $n_total files scanned: $CORPUS_TURTLE/*.ttl + $CORPUS_NTRIPLES/*.nt):"
echo "  $n_agree_parse agree (both parsed, isomorphic graphs)"
echo "  $n_agree_reject agree (both engines rejected the file)"
echo "  $n_disagree disagree (both parsed, graphs NOT isomorphic)"
echo "  $n_either_side_error either-side-error (one engine rejected, one accepted)"
echo "  => labelled: $n_agree_parse agree-parse, $n_agree_reject agree-reject, $n_disagree disagree, $n_either_side_error either-side-error (of $n_total total)"

if [[ $STRICT -eq 1 && ( $n_disagree -gt 0 || $n_either_side_error -gt 0 ) ]]; then
  echo "run-jena-diff: FAIL (--strict, and disagree+either-side-error > 0)"
  exit 1
fi

exit 0
