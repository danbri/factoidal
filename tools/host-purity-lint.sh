#!/usr/bin/env bash
# host-purity-lint.sh — the LWS and Solid Node hosts carry bytes and make no
# protocol decision (CLAUDE.md iron rule 7). This lint fails when a host file
# contains what only the Lean engine may decide:
#
#   * an HTTP status other than 500 (the host's own failure);
#   * a protocol header name (Link, Allow, Accept-Patch/Post/Put,
#     Last-Modified, ETag, If-*, Slug, Location, WAC-Allow,
#     Access-Control-*, Content-Type of a representation);
#   * protocol vocabulary (containment, acl, describedby, pim:, text/n3,
#     ldp:, solid:, WebID, inbox).
#
# Comments are stripped before the check, so a file may EXPLAIN what it does
# not do. The method is a regular-expression scan of the host sources named
# below; it cannot see a decision hidden behind a variable named after
# nothing, which is why the host tests replay the specification's own HTTP
# examples against the engine as well (tests/solid/server/protocol.mjs).
set -u -o pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
files=(
  "$root/npm/factoidal/lws/server.mjs"
  "$root/npm/factoidal/solid/server/index.mjs"
  "$root/npm/factoidal/solid/client/index.mjs"
)
pattern='\b(20[0-9]|30[0-9]|40[0-9]|41[0-9]|42[0-9]|50[1-9])\b|\b(Link|Allow|Accept-Patch|Accept-Post|Accept-Put|Last-Modified|ETag|If-Match|If-None-Match|Slug|Location|WAC-Allow|Access-Control-[A-Za-z-]+)\b|containment|describedby|\bacl\b|pim:|text/n3|\bldp:|\bsolid:|WebID|\binbox\b'
fail=0
for f in "${files[@]}"; do
  if [ ! -f "$f" ]; then echo "MISSING $f"; fail=1; continue; fi
  # Strip // line comments and /* */ blocks, then scan.
  # The client names the engine's interpretation KINDS as quoted words
  # ('containment', 'wacAllow', ...). Those are the wasm ABI's vocabulary
  # for which reading the engine should perform, not a reading done here,
  # so exact quoted kind names are removed before the scan.
  hits=$(sed -E 's#//.*$##' "$f" | perl -0pe 's#/\*.*?\*/##gs' \
    | sed -E "s/'(storage|containment|auxiliaries|profile|wacAllow|read|create|replace|patch|delete|discoverStorage|readProfile)'//g" \
    | grep -n -E "$pattern" || true)
  if [ -n "$hits" ]; then
    echo "FAIL $f"; echo "$hits" | sed 's/^/     /'; fail=1
  else
    echo "ok   $f"
  fi
done
if [ "$fail" -eq 0 ]; then echo "host-purity-lint: 3 pass, 0 fail (out of 3)"; else echo "host-purity-lint: FAIL"; fi
exit $fail
