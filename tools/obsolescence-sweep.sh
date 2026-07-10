#!/usr/bin/env bash
# obsolescence-sweep.sh — find statements a feature landing may have
# just made false. See skills/obsolescence-sweep/SKILL.md.
#
# Usage:
#   tools/obsolescence-sweep.sh [--ci] KEYWORD [KEYWORD...]
#
# Greps the stale-claim lexicon across the repo's prose surfaces, then
# filters to lines/files that also mention one of the KEYWORDS (case-
# insensitive), so "not yet" hits about unrelated features don't drown
# the signal. With no keywords it prints every lexicon hit (noisy —
# useful for periodic full audits).
#
# Advisory by default (always exit 0). --ci exits 1 when hits exist.
set -u

CI=0
if [ "${1:-}" = "--ci" ]; then CI=1; shift; fi

cd "$(dirname "$0")/.."

LEXICON='not yet|not implemented|no runner|unscored|out of scope|parked|deferred|later stage|future work|in flight|planned|TODO|does not (yet )?(run|support|exist)|cannot|stage [0-9]|pending|unsupported|placeholder|known gap'

# Prose surfaces, public first (see the skill for rationale).
SURFACES=(
  formal/fstar/generate-report.sh
  .github/test-suites
  docs/web/hub
  README.md
  docs/index.md
  npm/factoidal/README.md
  docs/claude-rules
  skills
  CLAUDE.md
  docs/designissues
)
# .fst header comments: scan only the comment-dense first 120 lines of
# each module to keep noise down (headers are where claims live).
FST_HEADERS=$(mktemp)
for f in formal/fstar/*.fst; do
  head -120 "$f" | grep -nEi "$LEXICON" | sed "s|^|$f:|" >> "$FST_HEADERS" || true
done

TMP=$(mktemp)
grep -rnEi "$LEXICON" "${SURFACES[@]}" 2>/dev/null \
  | grep -v 'obsolescence-sweep' >> "$TMP" || true
cat "$FST_HEADERS" >> "$TMP"

if [ "$#" -gt 0 ]; then
  # Keep a hit if the LINE mentions a keyword, or the FILE's basename does.
  KW=$(printf '%s|' "$@" | sed 's/|$//')
  FILTERED=$(grep -Ei "$KW" "$TMP" || true)
  # Also include lexicon hits from files whose path matches a keyword.
  PATHHITS=$(awk -F: '{print $1}' "$TMP" | sort -u | grep -Ei "$KW" || true)
  if [ -n "$PATHHITS" ]; then
    while IFS= read -r f; do grep -F "$f:" "$TMP" || true; done <<< "$PATHHITS" >> /tmp/osweep_path_hits.$$
    FILTERED=$(printf '%s\n%s' "$FILTERED" "$(cat /tmp/osweep_path_hits.$$ 2>/dev/null)" | sort -u)
    rm -f /tmp/osweep_path_hits.$$
  fi
else
  FILTERED=$(cat "$TMP")
fi
rm -f "$TMP" "$FST_HEADERS"

FILTERED=$(printf '%s\n' "$FILTERED" | sed '/^[[:space:]]*$/d' | sort -u)
COUNT=$(printf '%s\n' "$FILTERED" | sed '/^$/d' | wc -l)

if [ "$COUNT" -eq 0 ]; then
  echo "obsolescence-sweep: no stale-claim candidates found for: $*"
  exit 0
fi

echo "obsolescence-sweep: $COUNT candidate line(s) — each needs a human/agent"
echo "verdict: still true, or falsified by what you just landed?"
echo "----------------------------------------------------------------------"
printf '%s\n' "$FILTERED"
echo "----------------------------------------------------------------------"
echo "Fix at the source, in the landing commit (skills/obsolescence-sweep)."

if [ "$CI" -eq 1 ]; then exit 1; fi
exit 0
