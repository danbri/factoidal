#!/usr/bin/env bash
# EXECUTABILITY and ROW-AGREEMENT census of W3C SPARQL QueryEvaluationTests
# through the persisted Shardborough path (pack -> activate -> query via
# CURRENT).
#
# This is NOT a W3C conformance result: the answers are compared with the
# REFERENCE Lean engine's answer over the SAME input file, not with the
# suite's expected result file. It measures (a) how much of the official
# suites the disk path can ATTEMPT, and where attempts stop (pack/activate
# refusal vs query refusal), and (b) whether the disk path answers what the
# in-memory engine answers. The pass/fail conformance census is a separate,
# Lean-side milestone (`lake exe l4w3c`); see the terminology note in
# docs/20260901-blockengine-tuesday-okrs.md.
#
# Two eligibility passes:
#
#   1. default-graph tests — mf:QueryEvaluationTest entries whose action has
#      qt:query plus qt:data and NO qt:graphData. Packed as `ibk3` and queried
#      with `l4block-id-v3-query`, exactly as before.
#   2. named-graph tests — entries whose action has qt:graphData. The
#      qt:data file (if any) and every qt:graphData file are converted to
#      N-Quads by the Lean engine and concatenated into ONE input, with the
#      qt:graphData file's own IRI as the graph name (the rule
#      Harness/Manifest.lean uses). Packed as `ibk4` and queried with
#      `l4block-quad-query`.
#
# Manifest reading, RDF parsing and SPARQL evaluation are all done by the Lean
# engine; this shell never parses RDF or SPARQL itself. The one textual step
# is appending a graph label to N-Quads lines the Lean writer produced, which
# is N-Quads construction, not parsing.
#
# Known limitation of pass 2: the per-file N-Quads are concatenated without
# relabelling blank nodes, so two graph-data files that use the same blank
# node label are conflated. Both sides of the comparison read the SAME
# concatenated file, so the row agreement is still exact; the resulting
# dataset can differ from the one `lake exe l4w3c` builds, which parses each
# file into its own graph.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
bin="$repo_root/formal/lean4/.lake/build/bin"
suites=("$@")
if [ ${#suites[@]} -eq 0 ]; then
  suites=("$repo_root/third_party/testing/w3c/sparql/sparql10"
          "$repo_root/third_party/testing/w3c/sparql/sparql11")
fi

mkdir -p "$repo_root/tmp"
run_dir=$(mktemp -d "$repo_root/tmp/w3c-persisted-census.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT
tsv="$run_dir/census.tsv"
: >"$tsv"

extract='PREFIX mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#>
PREFIX qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#>
SELECT ?query ?data WHERE {
  ?t a mf:QueryEvaluationTest ; mf:action ?a .
  ?a qt:query ?query ; qt:data ?data .
  FILTER NOT EXISTS { ?a qt:graphData ?g }
}'

extract_graphdata='PREFIX mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#>
PREFIX qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#>
SELECT ?t ?query ?g ?data WHERE {
  ?t a mf:QueryEvaluationTest ; mf:action ?a .
  ?a qt:query ?query ; qt:graphData ?g .
  OPTIONAL { ?a qt:data ?data }
}'

# The Lean parser format for a fixture, by extension — the same mapping
# Harness/Run.lean's `parseDataFile` uses.
format_of() {
  case $1 in
    *.nt) echo ntriples ;;
    *.nq) echo nquads ;;
    *.trig) echo trig ;;
    *.rdf) echo rdfxml ;;
    *) echo turtle ;;
  esac
}

# The comparable answer a persisted query tool printed: "rows N", "bool X" or
# "triples N". Empty when the output carries none of the three.
persisted_answer() {
  local out=$1 n
  n=$(sed -n 's/^l4block-[a-z0-9-]* rows=\([0-9][0-9]*\) .*/\1/p' "$out" | head -1)
  if [ -n "$n" ]; then echo "rows $n"; return; fi
  n=$(sed -n 's/^l4block-[a-z0-9-]* boolean=\(.*\)$/\1/p' "$out" | head -1)
  if [ -n "$n" ]; then echo "bool $n"; return; fi
  n=$(sed -n 's/^l4block-[a-z0-9-]* triples=\([0-9][0-9]*\) .*/\1/p' "$out" | head -1)
  if [ -n "$n" ]; then echo "triples $n"; return; fi
  echo ""
}

# The same shape from the reference in-memory engine over the same file.
# $1 data file, $2 format, $3 base IRI, $4 query file, $5 kind word.
#
# The output goes to a FILE, never to a command substitution, and a SELECT is
# counted from the SPARQL Results JSON the engine prints, never from the
# `--table` rendering. Both rules were paid for: `$(...)` strips the two empty
# lines a zero-variable projection prints (`SELECT * WHERE { :a (:p)* :b }`),
# and a literal containing a newline (the sparql10 `regex-*` fixtures) spans
# several table lines, which made five row counts disagree for no engine
# reason. Reading the engine's own result envelope is not RDF or SPARQL
# parsing.
reference_answer() {
  local data=$1 format=$2 base=$3 qfile=$4 kind=$5 n
  local out="$run_dir/reference.txt"
  REF_RC=0
  case $kind in
    rows)
      timeout 60 "$bin/l4factoidal" query "$data" --format "$format" --base "$base" \
        --query "$qfile" >"$out" 2>/dev/null || REF_RC=$?
      if [ "$REF_RC" -ne 0 ]; then echo ""; return; fi
      n=$(python3 -c 'import json,sys
d = json.load(sys.stdin)
print(len(d["results"]["bindings"]))' <"$out" 2>/dev/null) || { echo ""; return; }
      [ -z "$n" ] && { echo ""; return; }
      echo "rows $n" ;;
    bool)
      timeout 60 "$bin/l4factoidal" query "$data" --format "$format" --base "$base" \
        --query "$qfile" >"$out" 2>/dev/null || REF_RC=$?
      if [ "$REF_RC" -gt 1 ]; then echo ""; return; fi
      echo "bool $(head -1 "$out")" ;;
    triples)
      timeout 60 "$bin/l4factoidal" query "$data" --format "$format" --base "$base" \
        --query "$qfile" >"$out" 2>/dev/null || REF_RC=$?
      if [ "$REF_RC" -ne 0 ]; then echo ""; return; fi
      echo "triples $(grep -c '.' "$out" || true)" ;;
    *) echo "" ;;
  esac
}

eligible=0; executed=0; refused_pack=0; refused_query=0; missing=0
matched=0; mismatched=0; uncompared=0
gd_eligible=0; gd_executed=0; gd_refused_pack=0; gd_refused_query=0; gd_missing=0
gd_matched=0; gd_mismatched=0; gd_uncompared=0
mismatch_list="$run_dir/mismatches.txt"; : >"$mismatch_list"
declare -A packed   # data file -> store root (pack each data file once)

# ---------------------------------------------------------------------------
# Pass 1: single default graph, IBK3, l4block-id-v3-query.
# ---------------------------------------------------------------------------
for suite in "${suites[@]}"; do
  while IFS= read -r manifest; do
    dir=$(dirname "$manifest")
    base="file://$dir/"
    rows=$("$bin/l4factoidal" query "$manifest" --base "$base" --table \
      --query-string "$extract" 2>/dev/null | tail -n +2) || continue
    [ -z "$rows" ] && continue
    while IFS=$'\t' read -r qiri diri; do
      qfile=${qiri#file://}; dfile=${diri#file://}
      if [ ! -f "$qfile" ] || [ ! -f "$dfile" ]; then
        missing=$((missing+1)); continue
      fi
      eligible=$((eligible+1))
      store=${packed[$dfile]:-}
      packfile=$dfile
      if [ -z "$store" ]; then
        store="$run_dir/store-$(shasum -a 256 <<<"$dfile" | cut -c1-16)"
        # The pack CLI reads Turtle. RDF/XML data files are converted by
        # the Lean engine itself (never by this shell) into N-Triples,
        # which is valid Turtle input.
        case $dfile in *.rdf)
          packfile="$store.nt"
          mkdir -p "$store"
          "$bin/l4factoidal" parse "$dfile" --format rdfxml --out nquads \
            --base "file://$dfile" >"$packfile" 2>/dev/null || packfile=$dfile
        ;; esac
        PACK_RC=0
        timeout 60 "$bin/l4block-shard-pack" "$packfile" "$store/gen" ibk3 \
          >/dev/null 2>&1 || PACK_RC=$?
        if [ "$PACK_RC" -eq 0 ]; then
          ACT_RC=0
          timeout 60 "$bin/l4block-shard-activate" "$store" gen \
            >/dev/null 2>&1 || ACT_RC=$?
          [ "$ACT_RC" -ne 0 ] && store="PACKFAIL"
        else
          store="PACKFAIL"
        fi
        packed[$dfile]=$store
        [ "$store" != "PACKFAIL" ] && printf '%s\n' "$packfile" >"$store/packfile.txt"
      elif [ "$store" != "PACKFAIL" ] && [ -f "$store/packfile.txt" ]; then
        packfile=$(<"$store/packfile.txt")
      fi
      if [ "$store" = "PACKFAIL" ]; then
        refused_pack=$((refused_pack+1))
        printf '%s\t%s\trefused-pack\n' "$qfile" "$dfile" >>"$tsv"
        continue
      fi
      Q_RC=0
      timeout 60 "$bin/l4block-id-v3-query" "$store" --query "$(<"$qfile")" \
        >"$run_dir/q.txt" 2>/dev/null || Q_RC=$?
      if [ "$Q_RC" -ne 0 ]; then
        refused_query=$((refused_query+1))
        printf '%s\t%s\trefused-query\n' "$qfile" "$dfile" >>"$tsv"
        continue
      fi
      executed=$((executed+1))
      got=$(persisted_answer "$run_dir/q.txt")
      want=$(reference_answer "$packfile" "$(format_of "$packfile")" \
        "file://$packfile" "$qfile" "${got%% *}")
      if [ -z "$got" ] || [ -z "$want" ]; then
        uncompared=$((uncompared+1))
        printf '%s\t%s\texecuted-uncompared\n' "$qfile" "$dfile" >>"$tsv"
      elif [ "$got" = "$want" ]; then
        matched=$((matched+1))
        printf '%s\t%s\texecuted-matched\n' "$qfile" "$dfile" >>"$tsv"
      else
        mismatched=$((mismatched+1))
        printf '%s\t%s\texecuted-mismatched\n' "$qfile" "$dfile" >>"$tsv"
        printf 'default-graph\t%s\tpersisted=%s\treference=%s\n' \
          "$(basename "$qfile")" "$got" "$want" >>"$mismatch_list"
      fi
    done <<<"$rows"
  done < <(find "$suite" -name manifest.ttl | sort)
done

# ---------------------------------------------------------------------------
# Pass 2: named graphs, IBK4, l4block-quad-query.
#
# Every qt:graphData row of every manifest is collected first, because one
# test carries several of them and the SELECT returns one row per graph.
# ---------------------------------------------------------------------------
gd_rows="$run_dir/graphdata.tsv"; : >"$gd_rows"
for suite in "${suites[@]}"; do
  while IFS= read -r manifest; do
    dir=$(dirname "$manifest")
    base="file://$dir/"
    "$bin/l4factoidal" query "$manifest" --base "$base" --table \
      --query-string "$extract_graphdata" 2>/dev/null | tail -n +2 >>"$gd_rows" || true
  done < <(find "$suite" -name manifest.ttl | sort)
done

declare -A gd_query gd_data gd_graphs
gd_order=()
while IFS=$'\t' read -r t qiri giri diri; do
  [ -z "$t" ] && continue
  if [ -z "${gd_query[$t]:-}" ]; then gd_order+=("$t"); fi
  gd_query[$t]=$qiri
  [ -n "$diri" ] && gd_data[$t]=$diri
  gd_graphs[$t]="${gd_graphs[$t]:-}${giri}"$'\n'
done <"$gd_rows"

for t in "${gd_order[@]:-}"; do
  [ -z "$t" ] && continue
  qfile=${gd_query[$t]#file://}
  dfile=${gd_data[$t]:-}
  dfile=${dfile#file://}
  ok=1
  [ -f "$qfile" ] || ok=0
  [ -n "$dfile" ] && [ ! -f "$dfile" ] && ok=0
  while IFS= read -r giri; do
    [ -z "$giri" ] && continue
    [ -f "${giri#file://}" ] || ok=0
  done <<<"${gd_graphs[$t]}"
  if [ "$ok" -ne 1 ]; then gd_missing=$((gd_missing+1)); continue; fi
  gd_eligible=$((gd_eligible+1))

  store="$run_dir/gd-$(shasum -a 256 <<<"$t" | cut -c1-16)"
  mkdir -p "$store"
  combined="$store/input.nq"
  : >"$combined"
  build_ok=1
  if [ -n "$dfile" ]; then
    "$bin/l4factoidal" parse "$dfile" --format "$(format_of "$dfile")" --out nquads \
      --base "file://$dfile" >>"$combined" 2>/dev/null || build_ok=0
  fi
  while IFS= read -r giri; do
    [ -z "$giri" ] && continue
    gfile=${giri#file://}
    # The qt:graphData object IRI is itself the graph name
    # (Harness/Manifest.lean, `dataAndGraphData`). The Lean writer emits one
    # statement per line ending in " ."; appending the graph label turns each
    # N-Triples line into the N-Quads line for that graph.
    "$bin/l4factoidal" parse "$gfile" --format "$(format_of "$gfile")" --out nquads \
      --base "file://$gfile" 2>/dev/null \
      | sed -e '/^[[:space:]]*$/d' -e "s| \.\$| <$giri> .|" >>"$combined" \
      || build_ok=0
  done <<<"${gd_graphs[$t]}"
  if [ "$build_ok" -ne 1 ]; then
    gd_refused_pack=$((gd_refused_pack+1))
    printf '%s\t%s\tgraphdata-refused-convert\n' "$qfile" "$t" >>"$tsv"
    continue
  fi

  PACK_RC=0
  timeout 60 "$bin/l4block-shard-pack" "$combined" "$store/gen" ibk4 \
    >/dev/null 2>&1 || PACK_RC=$?
  ACT_RC=1
  if [ "$PACK_RC" -eq 0 ]; then
    ACT_RC=0
    timeout 60 "$bin/l4block-shard-activate" "$store" gen >/dev/null 2>&1 || ACT_RC=$?
  fi
  if [ "$PACK_RC" -ne 0 ] || [ "$ACT_RC" -ne 0 ]; then
    gd_refused_pack=$((gd_refused_pack+1))
    printf '%s\t%s\tgraphdata-refused-pack\n' "$qfile" "$t" >>"$tsv"
    continue
  fi

  Q_RC=0
  timeout 60 "$bin/l4block-quad-query" "$store" --query "$(<"$qfile")" \
    >"$run_dir/gq.txt" 2>/dev/null || Q_RC=$?
  if [ "$Q_RC" -ne 0 ]; then
    gd_refused_query=$((gd_refused_query+1))
    printf '%s\t%s\tgraphdata-refused-query\n' "$qfile" "$t" >>"$tsv"
    continue
  fi
  gd_executed=$((gd_executed+1))
  got=$(persisted_answer "$run_dir/gq.txt")
  want=$(reference_answer "$combined" nquads "file://$combined" "$qfile" "${got%% *}")
  if [ -z "$got" ] || [ -z "$want" ]; then
    gd_uncompared=$((gd_uncompared+1))
    printf '%s\t%s\tgraphdata-executed-uncompared\n' "$qfile" "$t" >>"$tsv"
  elif [ "$got" = "$want" ]; then
    gd_matched=$((gd_matched+1))
    printf '%s\t%s\tgraphdata-executed-matched\n' "$qfile" "$t" >>"$tsv"
  else
    gd_mismatched=$((gd_mismatched+1))
    printf '%s\t%s\tgraphdata-executed-mismatched\n' "$qfile" "$t" >>"$tsv"
    printf 'named-graph\t%s\tpersisted=%s\treference=%s\n' \
      "${t##*#}" "$got" "$want" >>"$mismatch_list"
  fi
done

echo "w3c-persisted-census (EXECUTABILITY + row agreement with the reference engine, NOT conformance):"
echo "  default graph (IBK3, l4block-id-v3-query):"
echo "    $executed executed, $refused_pack refused at pack/activate, $refused_query refused at query (out of $eligible eligible single-default-graph QueryEvaluationTest entries; $missing entries skipped for missing files)"
echo "    of the $executed executed: $matched matched the reference engine, $mismatched differed, $uncompared not comparable"
echo "  named graphs (IBK4, l4block-quad-query):"
echo "    $gd_executed executed, $gd_refused_pack refused at convert/pack/activate, $gd_refused_query refused at query (out of $gd_eligible eligible qt:graphData QueryEvaluationTest entries; $gd_missing entries skipped for missing files)"
echo "    of the $gd_executed executed: $gd_matched matched the reference engine, $gd_mismatched differed, $gd_uncompared not comparable"
if [ -s "$mismatch_list" ]; then
  echo "  first five mismatches:"
  head -5 "$mismatch_list" | sed 's/^/    /'
fi
echo "  per-test outcomes: $tsv (deleted on exit; re-run with a kept dir to retain)"
sort "$tsv" | awk -F'\t' '{print $3}' | uniq -c
cp "$tsv" "$repo_root/tmp/w3c-persisted-census-latest.tsv"
cp "$mismatch_list" "$repo_root/tmp/w3c-persisted-census-mismatches.txt"
echo "  copies kept at tmp/w3c-persisted-census-latest.tsv and tmp/w3c-persisted-census-mismatches.txt"
