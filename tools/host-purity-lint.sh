#!/usr/bin/env bash
# host-purity-lint.sh — a host carries bytes and makes no decision the
# specification reserves for the engine (CLAUDE.md iron rule 7). Two groups
# of host files, two rules, one method.
#
# GROUP 1, the LWS and Solid hosts: no PROTOCOL decision. This lint fails
# when one of those files contains
#
#   * an HTTP status other than 500 (the host's own failure);
#   * a protocol header name (Link, Allow, Accept-Patch/Post/Put,
#     Last-Modified, ETag, If-*, Slug, Location, WAC-Allow,
#     Access-Control-*, Content-Type of a representation);
#   * protocol vocabulary (containment, acl, describedby, pim:, text/n3,
#     ldp:, solid:, WebID, inbox).
#
# GROUP 2, the store hosts (filesystem and HTTP): no STORAGE FORMAT
# decision. The engine's plan names the artifacts a query needs; the host
# fetches exactly those and hands the bytes over. This lint fails when one
# of those files contains
#
#   * an artifact suffix or block-kind name (.ibk5, .sri2, IBK3, SBM2, …).
#     The two manifest FILE names are the documented exception: a host must
#     be able to open a file to hand its bytes over, and it opens whichever
#     of the two exists without looking inside either;
#   * a byte offset, a magic number, or a typed-array read of a field
#     (0x…, DataView, getUint*, readUInt*) — a host that reads a field has
#     decoded a format;
#   * a Merkle root or any other derived commitment of its own. Comparing a
#     whole artifact's SHA-256 against the digest the ENGINE read out of
#     the manifest is allowed, and is what the HTTP host does.
#
# Comments are stripped before the check, so a file may EXPLAIN what it
# does not do. The method is a regular-expression scan of the host sources
# named below; it cannot see a decision hidden behind a variable named
# after nothing, which is why the host tests replay the specification's own
# HTTP examples against the engine as well (tests/solid/server/protocol.mjs)
# and the store tests compare the rows the engine answers against the
# native tools (tests/store-host/cli.mjs, tests/store-http/over-http.mjs).
set -u -o pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

protocol_files=(
  "$root/npm/factoidal/lws/server.mjs"
  "$root/npm/factoidal/solid/server/index.mjs"
  "$root/npm/factoidal/solid/client/index.mjs"
)
store_files=(
  "$root/npm/factoidal/store-http/index.mjs"
  "$root/npm/factoidal/store-host/index.mjs"
  "$root/npm/factoidal/bin/store.mjs"
)

protocol_pattern='\b(20[0-9]|30[0-9]|40[0-9]|41[0-9]|42[0-9]|50[1-9])\b|\b(Link|Allow|Accept-Patch|Accept-Post|Accept-Put|Last-Modified|ETag|If-Match|If-None-Match|Slug|Location|WAC-Allow|Access-Control-[A-Za-z-]+)\b|containment|describedby|\bacl\b|pim:|text/n3|\bldp:|\bsolid:|WebID|\binbox\b'
store_pattern='\.(ibk|sri|oli|tli|lgi|gbi|ptd|sbm)[0-9]|\b(IBK|SBM|PTD|SRI|OLI|TLI|LGI|GBI)[0-9]|\.merkle|\.lit\b|merkleRoot|0[xX][0-9a-fA-F]+|DataView|getUint|readUInt|\bmagic\b'

fail=0
total=0

# Strip // line comments and /* */ blocks, then scan.
strip_comments () {
  sed -E 's#//.*$##' "$1" | perl -0pe 's#/\*.*?\*/##gs'
}

scan () {
  local f="$1" pattern="$2" allow="$3"
  total=$((total + 1))
  if [ ! -f "$f" ]; then echo "MISSING $f"; fail=1; return; fi
  local hits
  hits=$(strip_comments "$f" | sed -E "$allow" | grep -n -E "$pattern" || true)
  if [ -n "$hits" ]; then
    echo "FAIL $f"; echo "$hits" | sed 's/^/     /'; fail=1
  else
    echo "ok   $f"
  fi
}

# The Solid client names the engine's interpretation KINDS as quoted words
# ('containment', 'wacAllow', ...). Those are the wasm ABI's vocabulary for
# which reading the engine should perform, not a reading done here, so exact
# quoted kind names are removed before the scan.
protocol_allow="s/'(storage|containment|auxiliaries|profile|wacAllow|read|create|replace|patch|delete|discoverStorage|readProfile)'//g"
# The two manifest file names a store host may open by name.
store_allow="s/'manifest\.sbm[12]'//g"

for f in "${protocol_files[@]}"; do scan "$f" "$protocol_pattern" "$protocol_allow"; done
for f in "${store_files[@]}"; do scan "$f" "$store_pattern" "$store_allow"; done

if [ "$fail" -eq 0 ]; then
  echo "host-purity-lint: $total pass, 0 fail (out of $total)"
else
  echo "host-purity-lint: FAIL"
fi
exit $fail
