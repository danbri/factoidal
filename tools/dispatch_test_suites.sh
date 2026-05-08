#!/bin/bash
# Per-suite test-dispatch script (#235 Step 3).
#
# Reads .github/test-suites/*.yaml and decides which suites to run for a
# given diff. Used by the W3C-tests CI workflow to fan out one job per
# affected suite, instead of running the full pipeline on every push.
#
# Usage:
#   tools/dispatch_test_suites.sh --diff <base-ref> <head-ref>
#       Print the list of affected suite names, one per line.
#   tools/dispatch_test_suites.sh --diff <base-ref> <head-ref> --verbose
#       As above, plus a per-suite explanation of WHY it was selected.
#   tools/dispatch_test_suites.sh --list
#       Print all suites, one per line.
#   tools/dispatch_test_suites.sh --foundational
#       Print the foundational paths.
#   tools/dispatch_test_suites.sh --validate
#       Validate every manifest file (schema + path existence). Exit
#       non-zero on any error. Suitable for use in CI as a guard.
#
# Output format on --diff: one suite name per line, sorted. Empty
# output means no suites affected. Foundational changes select ALL
# suites.
#
# Manifests are minimal YAML — we parse them with a tiny grep/sed
# pipeline rather than depending on yq/python so the script runs
# anywhere bash + git are available.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
TEST_SUITES_DIR="$REPO_ROOT/.github/test-suites"
FOUNDATIONAL_FILE="$TEST_SUITES_DIR/_foundational.yaml"

# ---------------------------------------------------------------------------
# Manifest readers
# ---------------------------------------------------------------------------

# list_suites — print every suite manifest's basename (without .yaml).
# Excludes anything starting with `_` (those are non-suite files like
# _foundational.yaml + _README.md).
list_suites() {
  local f
  for f in "$TEST_SUITES_DIR"/*.yaml; do
    [ -f "$f" ] || continue
    local base
    base=$(basename "$f" .yaml)
    case "$base" in
      _*) continue ;;
      *) echo "$base" ;;
    esac
  done | sort
}

# read_paths_block <yaml-file> <block-name>
#   Extract the list of paths under the named block. Handles two shapes:
#     foundational_paths:
#       - foo
#       - bar
#   and:
#     triggers:
#       paths:
#         - foo
#         - bar
#   Returns one path per line.
read_paths_block() {
  local file="$1"; local block="$2"
  awk -v want="$block" '
    BEGIN { in_block = 0; depth = 0 }
    # Top-level key matches the block name (no leading whitespace).
    /^[A-Za-z_][A-Za-z0-9_.]*:[[:space:]]*$/ {
      key = $0; sub(/:.*$/, "", key); gsub(/^[[:space:]]+/, "", key)
      if (key == want) { in_block = 1; depth = 0; next }
      else { in_block = 0 }
    }
    # Within the block, list items start with "  - " or "    - ".
    in_block && /^[[:space:]]+-[[:space:]]+/ {
      val = $0
      sub(/^[[:space:]]+-[[:space:]]+/, "", val)
      # Strip surrounding quotes if any.
      sub(/^["'\'']/, "", val); sub(/["'\'']$/, "", val)
      # Strip trailing comments + whitespace.
      sub(/[[:space:]]*#.*$/, "", val); sub(/[[:space:]]+$/, "", val)
      if (val != "") print val
    }
    # Stop at the next top-level key.
    !/^[[:space:]]/ && !/^$/ && in_block { in_block = 0 }
  ' "$file"
}

# read_paths_under_triggers <yaml-file>
#   Like read_paths_block but specifically for the triggers.paths
#   nested key shape.
read_paths_under_triggers() {
  local file="$1"
  awk '
    BEGIN { in_triggers = 0; in_paths = 0 }
    /^triggers:[[:space:]]*$/ { in_triggers = 1; in_paths = 0; next }
    in_triggers && /^[[:space:]]+paths:[[:space:]]*$/ { in_paths = 1; next }
    in_triggers && /^[[:space:]]+excludes:[[:space:]]*$/ { in_paths = 0; next }
    in_paths && /^[[:space:]]+-[[:space:]]+/ {
      val = $0
      sub(/^[[:space:]]+-[[:space:]]+/, "", val)
      sub(/^["'\'']/, "", val); sub(/["'\'']$/, "", val)
      sub(/[[:space:]]*#.*$/, "", val); sub(/[[:space:]]+$/, "", val)
      if (val != "") print val
    }
    # Stop at the next top-level key (no leading whitespace).
    !/^[[:space:]]/ && !/^$/ { in_triggers = 0; in_paths = 0 }
  ' "$file"
}

# ---------------------------------------------------------------------------
# Glob-match: does $1 (a path) match $2 (a glob pattern with ** support)?
# ---------------------------------------------------------------------------
glob_matches() {
  local path="$1"; local pat="$2"
  # Convert ** → .* and * → [^/]*  (very small subset; sufficient for
  # the manifests we ship today).
  local re
  re=$(printf '%s' "$pat" \
    | sed -e 's/\./\\./g' \
          -e 's|\*\*|__GLOBSTAR__|g' \
          -e 's|\*|[^/]*|g' \
          -e 's|__GLOBSTAR__|.*|g')
  [[ "$path" =~ ^${re}$ ]]
}

# ---------------------------------------------------------------------------
# Diff handling
# ---------------------------------------------------------------------------

# get_changed_paths <base> <head>
#   Print one path per line that changed between base and head.
get_changed_paths() {
  local base="$1"; local head="$2"
  git -C "$REPO_ROOT" diff --name-only "$base" "$head"
}

# is_path_in_set <path> <newline-separated-set-of-globs>
#   Returns 0 if any glob in the set matches the path.
is_path_in_set() {
  local path="$1"; local set="$2"
  local pat
  while IFS= read -r pat; do
    [ -z "$pat" ] && continue
    if glob_matches "$path" "$pat"; then
      return 0
    fi
  done <<<"$set"
  return 1
}

# ---------------------------------------------------------------------------
# Main commands
# ---------------------------------------------------------------------------

cmd_list() {
  list_suites
}

cmd_foundational() {
  if [ -f "$FOUNDATIONAL_FILE" ]; then
    read_paths_block "$FOUNDATIONAL_FILE" foundational_paths
  fi
}

cmd_validate() {
  local rc=0
  # Foundational paths must exist.
  while IFS= read -r p; do
    [ -z "$p" ] && continue
    if [ ! -e "$REPO_ROOT/$p" ]; then
      echo "::error::foundational path missing: $p (in _foundational.yaml)" >&2
      rc=1
    fi
  done < <(cmd_foundational)

  # Each suite must have name + runner + triggers.paths.
  local suite f
  for suite in $(list_suites); do
    f="$TEST_SUITES_DIR/$suite.yaml"
    if ! grep -q '^name:' "$f"; then
      echo "::error::$f missing name:" >&2; rc=1
    fi
    if ! grep -q '^runner:' "$f"; then
      echo "::error::$f missing runner:" >&2; rc=1
    fi
    if ! read_paths_under_triggers "$f" | head -1 | grep -q .; then
      echo "::error::$f missing triggers.paths or empty" >&2; rc=1
    fi
  done
  if [ "$rc" -eq 0 ]; then
    echo "All manifests valid."
  fi
  return "$rc"
}

cmd_diff() {
  local base="$1"; local head="$2"; local verbose="${3:-0}"

  local changed; changed=$(get_changed_paths "$base" "$head")

  if [ -z "$changed" ]; then
    [ "$verbose" = "1" ] && echo "(no changes)" >&2
    return 0
  fi

  # Foundational paths: if any matched, ALL suites fire.
  local foundational; foundational=$(cmd_foundational)
  local hit_foundational=""
  while IFS= read -r path; do
    [ -z "$path" ] && continue
    if is_path_in_set "$path" "$foundational"; then
      hit_foundational+="$path"$'\n'
    fi
  done <<<"$changed"

  if [ -n "$hit_foundational" ]; then
    if [ "$verbose" = "1" ]; then
      echo "# Foundational change(s) — firing ALL suites:" >&2
      echo "$hit_foundational" | sed 's/^/#   /' >&2
    fi
    list_suites
    return 0
  fi

  # Otherwise, per-suite check.
  local suite f
  for suite in $(list_suites); do
    f="$TEST_SUITES_DIR/$suite.yaml"
    local suite_paths; suite_paths=$(read_paths_under_triggers "$f")
    local fired=""
    while IFS= read -r path; do
      [ -z "$path" ] && continue
      if is_path_in_set "$path" "$suite_paths"; then
        fired+="$path"$'\n'
      fi
    done <<<"$changed"
    if [ -n "$fired" ]; then
      echo "$suite"
      if [ "$verbose" = "1" ]; then
        echo "# $suite fires because of:" >&2
        echo "$fired" | sed 's/^/#   /' >&2
      fi
    fi
  done
}

# ---------------------------------------------------------------------------
# CLI dispatch
# ---------------------------------------------------------------------------

case "${1:-}" in
  --list)
    cmd_list
    ;;
  --foundational)
    cmd_foundational
    ;;
  --validate)
    cmd_validate
    ;;
  --diff)
    BASE="${2:-}"; HEAD="${3:-HEAD}"; VERBOSE=0
    if [ -z "$BASE" ]; then
      echo "Usage: $0 --diff <base-ref> <head-ref> [--verbose]" >&2
      exit 2
    fi
    if [ "${4:-}" = "--verbose" ]; then VERBOSE=1; fi
    cmd_diff "$BASE" "$HEAD" "$VERBOSE"
    ;;
  -h|--help|"")
    sed -n '2,25p' "$0"
    ;;
  *)
    echo "Unknown command: $1" >&2
    exit 2
    ;;
esac
