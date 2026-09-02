#!/usr/bin/env bash
# EXECUTABILITY census of W3C SPARQL QueryEvaluationTests through the
# persisted Shardborough path (pack -> activate -> query via CURRENT).
#
# This is NOT a pass/fail conformance result: answers are not compared
# to the expected result files. It measures how much of the official
# suites the disk path can currently ATTEMPT, and where attempts stop
# (pack/activate refusal vs query refusal). The pass/fail census is a
# separate, Lean-side milestone (see docs/20260901-blockengine-tuesday-
# okrs.md terminology: this is not a "W3C suite result").
#
# Eligibility: mf:QueryEvaluationTest entries whose action has exactly
# qt:query plus qt:data (single default graph) and no qt:graphData.
# Manifest reading is done by the Lean engine (l4factoidal query); this
# shell never parses RDF or SPARQL itself.
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

eligible=0; executed=0; refused_pack=0; refused_query=0; missing=0
declare -A packed   # data file -> store root (pack each data file once)

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
      if [ -z "$store" ]; then
        store="$run_dir/store-$(shasum -a 256 <<<"$dfile" | cut -c1-16)"
        # The pack CLI reads Turtle. RDF/XML data files are converted by
        # the Lean engine itself (never by this shell) into N-Triples,
        # which is valid Turtle input.
        packfile=$dfile
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
      fi
      if [ "$store" = "PACKFAIL" ]; then
        refused_pack=$((refused_pack+1))
        printf '%s\t%s\trefused-pack\n' "$qfile" "$dfile" >>"$tsv"
        continue
      fi
      Q_RC=0
      timeout 60 "$bin/l4block-id-v3-query" "$store" --query "$(<"$qfile")" \
        >/dev/null 2>&1 || Q_RC=$?
      if [ "$Q_RC" -eq 0 ]; then
        executed=$((executed+1))
        printf '%s\t%s\texecuted\n' "$qfile" "$dfile" >>"$tsv"
      else
        refused_query=$((refused_query+1))
        printf '%s\t%s\trefused-query\n' "$qfile" "$dfile" >>"$tsv"
      fi
    done <<<"$rows"
  done < <(find "$suite" -name manifest.ttl | sort)
done

echo "w3c-persisted-census (EXECUTABILITY, not conformance):"
echo "  $executed executed, $refused_pack refused at pack/activate, $refused_query refused at query (out of $eligible eligible single-default-graph QueryEvaluationTest entries; $missing entries skipped for missing files)"
echo "  per-test outcomes: $tsv (deleted on exit; re-run with a kept dir to retain)"
sort "$tsv" | awk -F'\t' '{print $3}' | uniq -c
cp "$tsv" "$repo_root/tmp/w3c-persisted-census-latest.tsv"
echo "  copy kept at tmp/w3c-persisted-census-latest.tsv"
