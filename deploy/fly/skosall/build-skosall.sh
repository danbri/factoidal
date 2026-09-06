#!/usr/bin/env bash
# Build one wire-version-10 generation of EVERY fetchable skosdex vocabulary
# and sync it to R2. Runs unattended on the Fly machine (see fly.toml); every
# step leaves a stamp under $DATA/state so a restart resumes, and every step's
# exit code is captured explicitly (anti-pattern 14: no `|| true`).
#
# Steps
#   1 clone     danbri/skosdex at $SKOSDEX_REF, then `git lfs pull` of the
#               canonical.nq.gz files (3.9 GB of LFS objects for everything)
#   2 graphed   skosdex's own `graphed` step: one .nq.gz per scheme, quads in
#               the scheme's named graph, blank nodes prefixed by slug
#   3 source    concatenate into one N-Quads file (about 65 GB for everything)
#   4 pack      factoidal pack --layout ibk5 (the npm engine; 2.3x slower
#               than the native tool, measured 2026-09-05, and needs no Lean)
#   5 activate  factoidal activate: verifies every artifact, writes CURRENT
#   6 sync      rclone sync to r2:$R2_BUCKET/$R2_PREFIX
#
# Dry run: ONLY="iptc-colorspace iptc-signal" limits steps 2-3 to those slugs
# and keeps the same code path end to end.
set -u -o pipefail

DATA=${DATA:-/data}
STATE=$DATA/state
LOGS=$DATA/logs
SRC=$DATA/skosdex
ALL=$DATA/all.nq
STORE=$DATA/store
GEN=gen-1
SKOSDEX_REF=${SKOSDEX_REF:-claude/main}
BATCH=${FACTOIDAL_BATCH_BYTES:-268435456}
ONLY=${ONLY:-}
mkdir -p "$STATE" "$LOGS" "$STORE"

log() { printf '%s %s\n' "$(date -u +%FT%TZ)" "$*"; }
done_step() { [ -f "$STATE/$1.done" ]; }
mark() { date -u +%FT%TZ > "$STATE/$1.done"; }
fail() { log "FAILED: $*"; exit 1; }

log "build-skosall start data=$DATA ref=$SKOSDEX_REF batch=$BATCH only='${ONLY}'"
df -h "$DATA" | tail -1

# 1 clone + LFS
if ! done_step clone; then
  if [ ! -d "$SRC/.git" ]; then
    # GIT_LFS_SKIP_SMUDGE: without it git-lfs downloads EVERY LFS object at
    # checkout (3.9 GB for this repository, and it filled a disk on
    # 2026-09-06 before the --include filter below could run).
    rc=0; GIT_LFS_SKIP_SMUDGE=1 git clone --depth 1 --branch "$SKOSDEX_REF" https://github.com/danbri/skosdex "$SRC" || rc=$?
    [ "$rc" -eq 0 ] || fail "git clone rc=$rc"
  fi
  # Only the canonical files: the embeddings under deploy/ are LFS too and
  # are not needed here.
  if [ -n "$ONLY" ]; then
    inc=""; for s in $ONLY; do inc="${inc:+$inc,}third_party/skos/$s/canonical.nq.gz"; done
  else
    inc="third_party/skos/**/canonical.nq.gz"
  fi
  rc=0; ( cd "$SRC" && git lfs pull --include="$inc" ) 2>&1 | tee "$LOGS/lfs-pull.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "git lfs pull rc=$rc (GitHub LFS bandwidth allowance?)"
  fetched=$(find "$SRC/third_party/skos" -name canonical.nq.gz -size +1k | wc -l)
  log "lfs: $fetched canonical.nq.gz files fetched"
  rc=0; ( cd "$SRC" && npm ci --omit=dev ) 2>&1 | tee "$LOGS/npm-ci.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "npm ci rc=$rc"
  mark clone
fi

# 2 graphed
if ! done_step graphed; then
  # shellcheck disable=SC2086
  rc=0; ( cd "$SRC" && node scripts/skosdex graphed $ONLY ) 2>&1 | tee "$LOGS/graphed.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "skosdex graphed rc=$rc"
  n=$(ls "$SRC/dist/graphed"/*.nq.gz 2>/dev/null | wc -l)
  [ "$n" -gt 0 ] || fail "graphed produced no .nq.gz"
  log "graphed: $n schemes"
  mark graphed
fi

# 3 one source file
if ! done_step source; then
  rm -f "$ALL"
  rc=0
  for f in "$SRC/dist/graphed"/*.nq.gz; do
    gzip -dc "$f" >> "$ALL" || { rc=$?; break; }
  done
  [ "$rc" -eq 0 ] || fail "concatenate rc=$rc"
  log "source: $(wc -c < "$ALL") bytes, $(wc -l < "$ALL") lines"
  df -h "$DATA" | tail -1
  mark source
fi

# 4 pack
if ! done_step pack; then
  rm -rf "$STORE/$GEN"
  rc=0; factoidal pack "$ALL" "$STORE/$GEN" --layout ibk5 --batch-bytes "$BATCH" \
    2>&1 | tee "$LOGS/pack.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "factoidal pack rc=$rc"
  log "pack: $(du -sh "$STORE/$GEN" | cut -f1) in $(ls "$STORE/$GEN" | wc -l) files"
  mark pack
fi

# 5 activate
if ! done_step activate; then
  rc=0; factoidal activate "$STORE" "$GEN" 2>&1 | tee "$LOGS/activate.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "factoidal activate rc=$rc"
  [ "$(cat "$STORE/CURRENT")" = "$GEN" ] || fail "CURRENT is not $GEN"
  log "activate: CURRENT=$(cat "$STORE/CURRENT")"
  mark activate
fi

# 6 sync to R2. rclone is configured from the environment: no config file,
# and the secret never appears on a command line.
if ! done_step sync; then
  : "${R2_ACCOUNT_ID:?set with fly secrets}" "${R2_ACCESS_KEY_ID:?}" "${R2_SECRET_ACCESS_KEY:?}" "${R2_BUCKET:?}"
  export RCLONE_CONFIG_R2_TYPE=s3 RCLONE_CONFIG_R2_PROVIDER=Cloudflare \
         RCLONE_CONFIG_R2_ACCESS_KEY_ID="$R2_ACCESS_KEY_ID" \
         RCLONE_CONFIG_R2_SECRET_ACCESS_KEY="$R2_SECRET_ACCESS_KEY" \
         RCLONE_CONFIG_R2_ENDPOINT="https://${R2_ACCOUNT_ID}.r2.cloudflarestorage.com" \
         RCLONE_CONFIG_R2_ACL=private
  dest="r2:${R2_BUCKET}/${R2_PREFIX:-skosall}"
  rc=0; rclone sync "$STORE" "$dest" --transfers 16 --checkers 16 --s3-chunk-size 64M --stats 60s --stats-one-line \
    2>&1 | tee "$LOGS/sync.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "rclone sync rc=$rc"
  rc=0; rclone check "$STORE" "$dest" --one-way 2>&1 | tee "$LOGS/check.log" || rc=$?
  [ "$rc" -eq 0 ] || fail "rclone check rc=$rc"
  log "sync: $(rclone size "$dest" 2>/dev/null | tr '\n' ' ')"
  mark sync
fi

log "build-skosall DONE"
df -h "$DATA" | tail -1
