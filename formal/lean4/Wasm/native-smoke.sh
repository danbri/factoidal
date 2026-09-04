#!/usr/bin/env bash
#
# native-smoke.sh — exercise EVERY op of the dispatch ABI
# (Wasm/Dispatch.lean) once through the native CLI, so an ABI bug and a
# wasm-toolchain bug can never be confused for one another.
#
#   formal/lean4/Wasm/native-smoke.sh
#
# Builds l4wasm-cli, then drives `l4wasm-cli call <op> <argsJsonFile>`
# (and, for the dataset-handle ops whose state must survive across
# calls, `l4wasm-cli callseq <seqJsonFile>` — several ops in one
# process) with tiny inline fixtures and asserts the envelope keys the
# F* npm entry (bin/npm-entry/entry_jsoo.ml) pins. Includes one error
# path per family: bad Turtle (parse), DESCRIBE (query), unknown handle
# (handles), unknown op (dispatch). Exits non-zero on any mismatch.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
command -v lake >/dev/null || { echo "lake not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }

echo "=== build l4wasm-cli + IBK3 fixture publisher"
lake build l4wasm-cli l4block-shard-pack >/dev/null
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"
PACK="$LEAN_DIR/.lake/build/bin/l4block-shard-pack"
[ -x "$CLI" ] || { echo "FAIL: $CLI not built"; exit 1; }
[ -x "$PACK" ] || { echo "FAIL: $PACK not built"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0

# args <file> <arg>... — write a JSON array-of-strings args file.
args() {
  local out="$1"; shift
  python3 - "$out" "$@" <<'EOF'
import json, sys
with open(sys.argv[1], "w") as f:
    json.dump(sys.argv[2:], f)
EOF
}

# checkseq <label> <seqfile> <python-assert-expr>
# Runs `l4wasm-cli callseq <seqfile>` — several op/args pairs in ONE
# process, which is what dataset-handle state needs — and hands the
# expression the parsed envelopes as the list `rs`, in call order.
checkseq() {
  local label="$1" seqfile="$2" expr="$3"
  local out
  out="$("$CLI" callseq "$seqfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
rs = [json.loads(line) for line in sys.stdin if line.strip()]
assert ($expr), rs
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

# checkblob <label> <op> <argsfile> <blobfile> <python-assert-expr>
# Runs `l4wasm-cli callblob <op> <argsfile> <blobfile>` — the native form of
# the wasm module's `l4_call_blob_c`, which carries ONE contiguous byte region
# beside the string arguments. The expression sees the envelope as `r`.
checkblob() {
  local label="$1" op="$2" argsfile="$3" blobfile="$4" expr="$5"
  local out
  out="$("$CLI" callblob "$op" "$argsfile" "$blobfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

# check <label> <op> <argsfile> <python-assert-expr>
# The expression sees the parsed envelope as `r`.
check() {
  local label="$1" op="$2" argsfile="$3" expr="$4"
  local out
  out="$("$CLI" call "$op" "$argsfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

echo "=== dispatch smoke ($TMP)"

# --- Parse family -----------------------------------------------------
TTL='@prefix ex: <http://example.org/> . ex:alice ex:knows ex:bob .'
args "$TMP/parse.json" "$TTL" "turtle" ""
check "parseToDatasetJson turtle" parseToDatasetJson "$TMP/parse.json" \
  'r["ok"] is True and r["count"] == 1 and "example.org/alice" in r["nquads"]'

args "$TMP/parse-nt.json" '<http://e/a> <http://e/p> <http://e/b> .' "ntriples" ""
check "parseToDatasetJson ntriples" parseToDatasetJson "$TMP/parse-nt.json" \
  'r["ok"] is True and r["count"] == 1'

args "$TMP/parse-bad.json" 'this is not turtle @@@' "turtle" ""
check "parseToDatasetJson bad turtle -> error" parseToDatasetJson "$TMP/parse-bad.json" \
  'r["ok"] is False and isinstance(r["error"], str) and len(r["error"]) > 0'

args "$TMP/parse-jsonld.json" '{}' "jsonld" ""
check "parseToDatasetJson jsonld -> named gap" parseToDatasetJson "$TMP/parse-jsonld.json" \
  'r["ok"] is False and "JSON-LD" in r["error"]'

NQ='<http://e/a> <http://e/p> <http://e/b> .
<http://e/a> <http://e/p> <http://e/c> <http://e/g> .
'
args "$TMP/ser-nq.json" "$NQ"
check "serializeNQuads" serializeNQuads "$TMP/ser-nq.json" \
  'r["ok"] is True and "<http://e/g>" in r["nquads"] and r["nquads"].count(" .") == 2'

args "$TMP/ser-ttl.json" "$NQ"
check "serializeTurtle" serializeTurtle "$TMP/ser-ttl.json" \
  'r["ok"] is True and "@prefix" in r["turtle"] and "<http://e/>" in r["turtle"]'

# --- Query family -----------------------------------------------------
DATA='<http://e/a> <http://e/p> <http://e/b> .
'
args "$TMP/q-select.json" "$DATA" 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
check "queryDataset select" queryDataset "$TMP/q-select.json" \
  'r["ok"] is True and r["kind"] == "select" and isinstance(r["srj"], dict)
   and r["srj"]["head"]["vars"] == ["s"]
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'

args "$TMP/q-ask.json" "$DATA" 'ASK { <http://e/a> <http://e/p> <http://e/b> }'
check "queryDataset ask" queryDataset "$TMP/q-ask.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'

# §18.6 EXISTS / NOT EXISTS through the backend path: the data holds a p b
# only, so NOT EXISTS of the reversed pattern keeps the row and EXISTS drops
# it. Regression pin (2026-09-02): the backend environment carried no
# dataset and FILTER NOT EXISTS answered zero rows.
args "$TMP/q-not-exists.json" "$DATA" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER NOT EXISTS { ?o <http://e/p> ?s } }'
check "queryDataset FILTER NOT EXISTS keeps the row" queryDataset "$TMP/q-not-exists.json" \
  'r["ok"] is True and r["kind"] == "select"
   and len(r["srj"]["results"]["bindings"]) == 1
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'

args "$TMP/q-exists.json" "$DATA" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER EXISTS { ?o <http://e/p> ?s } }'
check "queryDataset FILTER EXISTS drops the row" queryDataset "$TMP/q-exists.json" \
  'r["ok"] is True and r["kind"] == "select" and len(r["srj"]["results"]["bindings"]) == 0'

args "$TMP/q-construct.json" "$DATA" \
  'CONSTRUCT { ?s <http://e/q> ?o } WHERE { ?s <http://e/p> ?o }'
check "queryDataset construct" queryDataset "$TMP/q-construct.json" \
  'r["ok"] is True and r["kind"] == "construct" and "<http://e/q>" in r["nquads"]'

args "$TMP/q-describe.json" "$DATA" 'DESCRIBE <http://e/a>'
check "queryDataset DESCRIBE -> error" queryDataset "$TMP/q-describe.json" \
  'r["ok"] is False and r["error"] == "DESCRIBE is not supported by the npm entry yet"'

args "$TMP/update.json" "$DATA" \
  'INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }'
check "updateDataset" updateDataset "$TMP/update.json" \
  'r["ok"] is True and "<http://e/x>" in r["nquads"] and "<http://e/a>" in r["nquads"]'

# --- Stateless block-worker family ----------------------------------
# Generate the fixture with the same Lean publisher used by native stores;
# the test therefore crosses the dispatch boundary with a real current-format
# artifact rather than a hand-authored byte string.
printf '%s\n' '<http://e/a> <http://e/p> <http://e/b> .' >"$TMP/block.ttl"
"$PACK" "$TMP/block.ttl" "$TMP/block-store" ibk3 >/dev/null
python3 - "$TMP/block-store/predicate-0.ibk3" "$TMP/block-ibk3.json" <<'EOF'
import json, pathlib, sys
block = pathlib.Path(sys.argv[1]).read_bytes().hex()
pathlib.Path(sys.argv[2]).write_text(json.dumps([block, "http://e/p", "source:native-smoke"]))
EOF
check "scanIBK3Predicate current artifact" scanIBK3Predicate "$TMP/block-ibk3.json" \
  'r["ok"] is True and r["format"] == "IBK3"
   and r["blankNodeScope"] == "source:native-smoke" and r["rows"] == 1
   and "<http://e/a> <http://e/p> <http://e/b> ." in r["ntriples"]'

args "$TMP/block-ibk3-bad.json" "00" "http://e/p" "source:native-smoke"
check "scanIBK3Predicate corrupt artifact -> error" scanIBK3Predicate "$TMP/block-ibk3-bad.json" \
  'r["ok"] is False and "invalid or corrupt canonical IBK3" in r["error"]'

args "$TMP/block-ibk3-noscope.json" "00" "http://e/p" ""
check "scanIBK3Predicate requires blank-node scope" scanIBK3Predicate "$TMP/block-ibk3-noscope.json" \
  'r["ok"] is False and "blankNodeScope must be non-empty" in r["error"]'

# Bounded block-set preview: blocks stay inside Lean, no N-Triples round trip.
python3 - "$TMP/block-store/predicate-0.ibk3" "$TMP/block-set.json" "$TMP/block-set-nolimit.json" <<'EOF'
import json, pathlib, sys
block = pathlib.Path(sys.argv[1]).read_bytes().hex()
blocks = json.dumps([["http://e/p", block]])
pathlib.Path(sys.argv[2]).write_text(json.dumps([blocks, "source:native-smoke",
  "SELECT ?s ?o WHERE { ?s <http://e/p> ?o } LIMIT 5"]))
pathlib.Path(sys.argv[3]).write_text(json.dumps([blocks, "source:native-smoke",
  "SELECT ?s ?o WHERE { ?s <http://e/p> ?o }"]))
EOF
check "queryIBK3BlockSetPreview bounded select" queryIBK3BlockSetPreview "$TMP/block-set.json" \
  'r["ok"] is True and r["kind"] == "select"
   and len(r["srj"]["results"]["bindings"]) == 1
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'
check "queryIBK3BlockSetPreview requires LIMIT" queryIBK3BlockSetPreview "$TMP/block-set-nolimit.json" \
  'r["ok"] is False and "require LIMIT" in r["error"]'

# --- Shardborough store family (manifest inspect / plan / query) ------
# The WASM module has no file system, so a JavaScript host reads the files.
# These three ops are what keep the host from having to understand any of
# them: it carries bytes by name, and every decision stays in Lean.
#
# Fixtures come from the same Lean publisher a native store uses, so the
# manifest bytes, the digests and the block bytes are the real ones.
REPO_ROOT="$(cd "$LEAN_DIR/../.." && pwd)"

printf '%s\n' \
  '<http://e/a> <http://e/p> <http://e/b> .' \
  '<http://e/a> <http://e/q> "one" .' \
  '<http://e/c> <http://e/p> <http://e/d> .' >"$TMP/store.ttl"
"$PACK" "$TMP/store.ttl" "$TMP/store-ibk3" ibk3 >/dev/null

# One predicate per line, 65 of them: enough entries that a full-manifest
# plan trips the 64-artifact cap without any large file.
python3 - "$TMP/wide.ttl" <<'EOF'
import sys
with open(sys.argv[1], "w") as f:
    for i in range(65):
        f.write(f"<http://e/s> <http://e/p{i}> <http://e/o{i}> .\n")
EOF
"$PACK" "$TMP/wide.ttl" "$TMP/store-wide" ibk3 >/dev/null

"$PACK" "$REPO_ROOT/tests/local/data/quad_sample.trig" "$TMP/store-ibk4" ibk4 >/dev/null

# The IBK4 N-Quads pack streams (PackStream.quadIngestFeed) on BOTH surfaces:
# the native CLI reads the file in chunks, the pack ops take the chunks from
# the host. Neither buffers the source. A routing change that made only one of
# them stream would still pass every other check here, so the gate is a byte
# comparison of the two generations, not a count.
printf '%s\n' \
  '<http://e/a> <http://e/p> "x" .' \
  '<http://e/a> <http://e/p> "y" <http://e/g1> .' \
  '<http://e/b> <http://e/q> "z"@en <http://e/g2> .' \
  '<http://e/c> <http://e/p> "w" <http://e/g1> .' \
  '_:b1 <http://e/q> <http://e/d> <http://e/g2> .' > "$TMP/quads.nq"
"$PACK" "$TMP/quads.nq" "$TMP/store-nq-cli" ibk4 >/dev/null
"$CLI" pack "$TMP/quads.nq" "$TMP/store-nq-ops" nquads ibk4 >/dev/null
if diff -r "$TMP/store-nq-cli" "$TMP/store-nq-ops" >/dev/null; then
  echo "ok   pack ops and the CLI commit the same IBK4 N-Quads generation"
  PASS=$((PASS + 1))
else
  echo "FAIL pack ops and the CLI commit the same IBK4 N-Quads generation"
  DIFF_RC=0; diff -r "$TMP/store-nq-cli" "$TMP/store-nq-ops" || DIFF_RC=$?
  printf '     diff exit %s\n' "$DIFF_RC"
  FAIL=$((FAIL + 1))
fi

# storeargs <out> <manifest-file> [extra json string]... — the manifest is
# hex, so only the host's file read crosses the boundary.
storeargs() {
  local out="$1" manifest="$2"; shift 2
  python3 - "$out" "$manifest" "$@" <<'EOF'
import json, pathlib, sys
out, manifest = sys.argv[1], sys.argv[2]
argv = [pathlib.Path(manifest).read_bytes().hex()] + sys.argv[3:]
pathlib.Path(out).write_text(json.dumps(argv))
EOF
}

# blobargs <argsout> <blobout> <manifest> <sparql> <generation-dir> <key>...
# The host path: the artifacts go into ONE contiguous region with no encoding,
# and the args document describes {"key","offset","len"} windows into it.
# `--tamper` as the last key flips one byte of the region.
blobargs() {
  local argsout="$1" blobout="$2" manifest="$3" sparql="$4" dir="$5"; shift 5
  python3 - "$argsout" "$blobout" "$manifest" "$sparql" "$dir" "$@" <<'EOF'
import json, pathlib, sys
argsout, blobout, manifest, sparql, directory = sys.argv[1:6]
keys = list(sys.argv[6:])
tamper = "--tamper" in keys
if tamper:
    keys.remove("--tamper")
blob = bytearray()
descriptors = []
for key in keys:
    data = (pathlib.Path(directory) / key).read_bytes()
    descriptors.append({"key": key, "offset": len(blob), "len": len(data)})
    blob += data
if tamper and blob:
    blob[len(blob) // 2] ^= 0xFF
pathlib.Path(blobout).write_bytes(bytes(blob))
pathlib.Path(argsout).write_text(json.dumps(
    [pathlib.Path(manifest).read_bytes().hex(), sparql, json.dumps(descriptors)]))
EOF
}

# hexargs <argsout> <manifest> <sparql> <generation-dir> <key>... — the
# diagnostic {"key","bytes":"<hex>"} form, reachable through the plain `call`
# entry that carries no region. A host must not use it: it doubles the bytes
# over the boundary and walks every character on the way in.
hexargs() {
  local argsout="$1" manifest="$2" sparql="$3" dir="$4"; shift 4
  python3 - "$argsout" "$manifest" "$sparql" "$dir" "$@" <<'EOF'
import json, pathlib, sys
argsout, manifest, sparql, directory = sys.argv[1:5]
payload = [{"key": key,
            "bytes": (pathlib.Path(directory) / key).read_bytes().hex()}
           for key in sys.argv[5:]]
pathlib.Path(argsout).write_text(json.dumps(
    [pathlib.Path(manifest).read_bytes().hex(), sparql, json.dumps(payload)]))
EOF
}

storeargs "$TMP/store-inspect.json" "$TMP/store-ibk3/manifest.sbm2"
check "storeManifestInspect reports an IBK3 generation" storeManifestInspect "$TMP/store-inspect.json" \
  'r["ok"] is True and r["wireVersion"] >= 1 and r["rangeCommitted"] is True
   and "ibk3" in r["layout"] and len(r["entries"]) == 2
   and r["entries"][0]["key"].endswith(".ibk3")
   and r["entries"][0]["blockKind"] == "IBK3"
   and len(r["entries"][0]["sha256"]) == 64
   and r["entries"][0]["rows"] >= 1
   and r["entries"][0]["chunkBytes"] > 0
   and len(r["entries"][0]["merkleRoot"]) == 64
   and r["totalBytes"] > 0 and r["totalRows"] == 3'

args "$TMP/store-inspect-bad.json" "00"
check "storeManifestInspect refuses bytes that do not decode" storeManifestInspect "$TMP/store-inspect-bad.json" \
  'r["ok"] is False and "do not decode" in r["error"]'

storeargs "$TMP/store-plan-bound.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s WHERE { ?s <http://e/p> ?o }'
check "storeQueryPlan selects one shard for a constant predicate" storeQueryPlan "$TMP/store-plan-bound.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle(1)"
   and r["shards"] == 1 and len(r["keys"]) == 1 and r["bytes"] > 0 and r["rows"] == 2'

storeargs "$TMP/store-plan-open.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }'
check "storeQueryPlan opens the whole manifest for an unbound predicate" storeQueryPlan "$TMP/store-plan-open.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)"
   and r["shards"] == 2 and len(r["keys"]) == 2'

# An EXISTS outside the pattern is evaluated against the active graph
# (section 18.6), so the plan must select every entry.
storeargs "$TMP/store-plan-exists.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s (EXISTS { ?s <http://e/q> ?v } AS ?e) WHERE { ?s <http://e/p> ?o }'
check "storeQueryPlan refuses predicate selection under EXISTS" storeQueryPlan "$TMP/store-plan-exists.json" \
  'r["ok"] is True and r["mode"] == "ibk3-paged-merkle-full-manifest(2)" and r["shards"] == 2'

# The HOST path: one contiguous region, no encoding, offset/len windows.
blobargs "$TMP/store-query.json" "$TMP/store-query.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' \
  "$TMP/store-ibk3" predicate-0.ibk3
checkblob "storeQuery answers over a supplied IBK3 block region" storeQuery \
  "$TMP/store-query.json" "$TMP/store-query.blob" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and r["mode"] == "ibk3-paged-merkle(1)"
   and len(r["srj"]["results"]["bindings"]) == 2'

# The diagnostic hexadecimal form must answer exactly the same envelope, so a
# fixture written either way pins the same behaviour.
hexargs "$TMP/store-query-hex.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' "$TMP/store-ibk3" predicate-0.ibk3
check "storeQuery hexadecimal diagnostic path answers the same rows" storeQuery "$TMP/store-query-hex.json" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and len(r["srj"]["results"]["bindings"]) == 2'

# A window that runs past the end of the region the call carried is an
# ordinary refusal, not a memory fault: Lean never receives a host pointer.
python3 - "$TMP/store-query.json" "$TMP/store-query-overrun.json" <<'EOF'
import json, pathlib, sys
argv = json.loads(pathlib.Path(sys.argv[1]).read_text())
artifacts = json.loads(argv[2])
artifacts[0]["offset"] += 1
argv[2] = json.dumps(artifacts)
pathlib.Path(sys.argv[2]).write_text(json.dumps(argv))
EOF
checkblob "storeQuery refuses a window past the end of the region" storeQuery \
  "$TMP/store-query-overrun.json" "$TMP/store-query.blob" \
  'r["ok"] is False and "names blob bytes" in r["error"]'

# A digest that does not match its manifest entry refuses the whole query
# and names the key; no partially trusted generation is answered from.
blobargs "$TMP/store-query-tampered.json" "$TMP/store-query-tampered.blob" \
  "$TMP/store-ibk3/manifest.sbm2" 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' \
  "$TMP/store-ibk3" predicate-0.ibk3 --tamper
checkblob "storeQuery refuses an artifact whose SHA-256 differs" storeQuery \
  "$TMP/store-query-tampered.json" "$TMP/store-query-tampered.blob" \
  'r["ok"] is False and "predicate-0.ibk3" in r["error"] and "SHA-256" in r["error"]'

storeargs "$TMP/store-query-missing.json" "$TMP/store-ibk3/manifest.sbm2" \
  'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }' '[]'
check "storeQuery refuses a plan whose bytes were not supplied" storeQuery "$TMP/store-query-missing.json" \
  'r["ok"] is False and "no bytes were supplied for artifact" in r["error"]'

# Cap trip: 65 predicates, so the full-manifest plan needs 65 artifacts and
# the cap is 64. The refusal names the cap and the value that exceeded it.
storeargs "$TMP/store-query-cap.json" "$TMP/store-wide/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }' '[]'
check "storeQuery refuses a plan over the artifact cap" storeQuery "$TMP/store-query-cap.json" \
  'r["ok"] is False and "selects 65 artifacts" in r["error"] and "cap is 64" in r["error"]'

# The same manifest still PLANS: the caps belong to storeQuery, so a host can
# see what a query would cost before it fetches anything.
storeargs "$TMP/store-plan-cap.json" "$TMP/store-wide/manifest.sbm2" \
  'SELECT ?s WHERE { ?s ?p ?o }'
check "storeQueryPlan reports a plan the query cap would refuse" storeQueryPlan "$TMP/store-plan-cap.json" \
  'r["ok"] is True and r["shards"] == 65'

# --- The same three ops over an SBM7 generation of IBK4 quad blocks ---
storeargs "$TMP/store-inspect-ibk4.json" "$TMP/store-ibk4/manifest.sbm2"
check "storeManifestInspect reports an IBK4 generation and its graph set" storeManifestInspect "$TMP/store-inspect-ibk4.json" \
  'r["ok"] is True and r["wireVersion"] == 7
   and r["layout"] == "quad-ibk4-ptd1-merkle-v0"
   and r["blankNodeProfile"] == "content-digest-shared"
   and len(r["entries"]) == 2
   and r["entries"][0]["blockKind"] == "IBK4"
   and len(r["entries"][0]["blankNodeScope"]) > 0
   and [g["kind"] for g in r["entries"][0]["graphs"]][0] == "default"
   and "http://example.org/g1" in [g["value"] for g in r["entries"][0]["graphs"]]'

storeargs "$TMP/store-plan-ibk4.json" "$TMP/store-ibk4/manifest.sbm2" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }'
check "storeQueryPlan selects IBK4 entries by graph set" storeQueryPlan "$TMP/store-plan-ibk4.json" \
  'r["ok"] is True and r["mode"] == "ibk4-full-manifest(1)" and r["shards"] == 1
   and r["keys"] == ["predicate-0.ibk4"]'

blobargs "$TMP/store-query-ibk4.json" "$TMP/store-query-ibk4.blob" \
  "$TMP/store-ibk4/manifest.sbm2" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }' \
  "$TMP/store-ibk4" predicate-0.ibk4
checkblob "storeQuery answers a GRAPH clause over a supplied IBK4 block region" storeQuery \
  "$TMP/store-query-ibk4.json" "$TMP/store-query-ibk4.blob" \
  'r["ok"] is True and r["kind"] == "select" and r["shards"] == 1
   and r["mode"] == "ibk4-full-manifest(1)"
   and len(r["srj"]["results"]["bindings"]) == 2'

args "$TMP/store-arity.json" "00"
check "storeQuery wrong arity -> error" storeQuery "$TMP/store-arity.json" \
  'r["ok"] is False and "expects 3 arguments" in r["error"]'

# --- Canon family -----------------------------------------------------
args "$TMP/canon.json" '_:b0 <http://e/p> "v" .
'
check "canonicalizeToNQuads" canonicalizeToNQuads "$TMP/canon.json" \
  'r["ok"] is True and "_:c14n0" in r["nquads"]'

# --- Reason family ----------------------------------------------------
SUBCLASS='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
'
args "$TMP/owl-rdfs.json" "$SUBCLASS" "RDFS"
check "owlClosure RDFS" owlClosure "$TMP/owl-rdfs.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-rl.json" "$SUBCLASS" "OWL-RL"
check "owlClosure OWL-RL" owlClosure "$TMP/owl-rl.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-badmode.json" "$SUBCLASS" "nonsense"
check "owlClosure unknown mode -> error" owlClosure "$TMP/owl-badmode.json" \
  'r["ok"] is False and "unknown mode" in r["error"]'

args "$TMP/rhodf.json" "$SUBCLASS"
check "rhoDfClosure" rhoDfClosure "$TMP/rhodf.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

args "$TMP/frag-yes.json" "$SUBCLASS"
check "rhoDfFragmentCheck true" rhoDfFragmentCheck "$TMP/frag-yes.json" \
  'r["ok"] is True and r["fragment"] is True'

args "$TMP/frag-no.json" '<http://e/a> <http://e/p> "a literal" .
'
check "rhoDfFragmentCheck false (literal object)" rhoDfFragmentCheck "$TMP/frag-no.json" \
  'r["ok"] is True and r["fragment"] is False'

SAMEAS='<http://e/a> <http://www.w3.org/2002/07/owl#sameAs> <http://e/b> .
<http://e/a> <http://e/p> <http://e/v> .
'
args "$TMP/rdfsplus.json" "$SAMEAS"
check "rdfsPlusClosure" rdfsPlusClosure "$TMP/rdfsplus.json" \
  'r["ok"] is True and "<http://e/b> <http://e/p> <http://e/v> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

# --- OWL DL consistency / entailment (issue 586) ----------------------
# Envelopes pinned against bin/npm-entry/entry_jsoo.ml's
# owl_is_consistent_json / owl_entails_json: three-valued, budget-out
# reported as null with a reason, never a silent false.
args "$TMP/owl-cons-yes.json" "$SUBCLASS" ""
check "owlIsConsistent consistent -> true, no reason" owlIsConsistent "$TMP/owl-cons-yes.json" \
  'r["ok"] is True and r["consistent"] is True and "reason" not in r'

NOTHING='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing> .
'
args "$TMP/owl-cons-no.json" "$NOTHING" ""
check "owlIsConsistent owl:Nothing member -> false + reason" owlIsConsistent "$TMP/owl-cons-no.json" \
  'r["ok"] is True and r["consistent"] is False and "contradiction" in r["reason"]'

# A cyclic TBox (A subClassOf someValuesFrom(p, A)) keeps the expansion
# changing, so fuel 1 runs out mid-search: the verdict is null.
CYCLIC='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/A> .
<http://e/A> <http://www.w3.org/2000/01/rdf-schema#subClassOf> _:r .
_:r <http://www.w3.org/2002/07/owl#onProperty> <http://e/p> .
_:r <http://www.w3.org/2002/07/owl#someValuesFrom> <http://e/A> .
'
args "$TMP/owl-cons-unk.json" "$CYCLIC" '{"fuel":"1"}'
check "owlIsConsistent fuel 1 -> null (budget-out, fuel named)" owlIsConsistent "$TMP/owl-cons-unk.json" \
  'r["ok"] is True and r["consistent"] is None and "budget-out" in r["reason"]
   and "fuel 1 " in r["reason"]'

# The same cyclic TBox at the default budget saturates under the
# witness-depth cap: consistent.
args "$TMP/owl-cons-cyc.json" "$CYCLIC" ""
check "owlIsConsistent cyclic TBox, default fuel -> true" owlIsConsistent "$TMP/owl-cons-cyc.json" \
  'r["ok"] is True and r["consistent"] is True'

# Entailment via the closure path: a type D . follows from
# a type C, C subClassOf D by cax-sco.
CONCL='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> .
'
args "$TMP/owl-ent-yes.json" "$SUBCLASS" "$CONCL" ""
check "owlEntails subclass typing -> true via closure" owlEntails "$TMP/owl-ent-yes.json" \
  'r["ok"] is True and r["entailed"] is True and r["via"] == "closure"'

# Not entailed: the negated conclusion is satisfiable beside the
# premise (a countermodel), reported via the refutation path.
UNRELATED='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Zebra> .
'
args "$TMP/owl-ent-no.json" "$SUBCLASS" "$UNRELATED" ""
check "owlEntails unrelated class -> false via refutation" owlEntails "$TMP/owl-ent-no.json" \
  'r["ok"] is True and r["entailed"] is False and r["via"] == "refutation"
   and "model" in r["reason"]'

# Budget-out on a refutation goal: null, never a silent false.
args "$TMP/owl-ent-unk.json" "$CYCLIC" "$UNRELATED" '{"fuel":"1"}'
check "owlEntails fuel 1 -> null (budget-out)" owlEntails "$TMP/owl-ent-unk.json" \
  'r["ok"] is True and r["entailed"] is None and r["via"] == "refutation"
   and "budget-out" in r["reason"]'

args "$TMP/owl-ent-badnq.json" 'not nquads @@@' "$CONCL" ""
check "owlEntails bad premise -> error" owlEntails "$TMP/owl-ent-badnq.json" \
  'r["ok"] is False and len(r["error"]) > 0'

# --- Common Logic / IKL family ----------------------------------------
IKL='(ist c (that (Dead OBL)))'
args "$TMP/cl-parse.json" "$IKL"
check "clParse ikl sentence" clParse "$TMP/cl-parse.json" \
  'r["ok"] is True and r["sentences"] == 1 and r["pureCL"] is False
   and r["normalized"] == "(ist c (that (Dead OBL)))"'

args "$TMP/cl-parse-pure.json" '(married Jack Jill) (forall (x) (if (Boy x) (Human x)))'
check "clParse pure CL text" clParse "$TMP/cl-parse-pure.json" \
  'r["ok"] is True and r["sentences"] == 2 and r["pureCL"] is True'

args "$TMP/cl-parse-bad.json" '(P a'
check "clParse unclosed paren -> error" clParse "$TMP/cl-parse-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clSerialize — the canonical writer, with the OPEN round-trip lemma
# reported rather than assumed (`clif_roundTrip`, CL/ClifAdequacy.lean).
args "$TMP/cl-ser.json" '(forall (x) (if (Boy x) (Person x)))'
check "clSerialize canonical text" clSerialize "$TMP/cl-ser.json" \
  'r["ok"] is True and r["sentences"] == 1
   and r["clif"] == "(forall (x) (if (Boy x) (Person x)))"
   and r["roundTripProved"] is False'

args "$TMP/cl-ser-bad.json" '(P a'
check "clSerialize unclosed paren -> error" clSerialize "$TMP/cl-ser-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clAlphaNorm — two alpha-variants must serialise byte-identically.
args "$TMP/cl-alpha-x.json" '(forall (x) (if (Boy x) (Person x)))'
check "clAlphaNorm canonical names" clAlphaNorm "$TMP/cl-alpha-x.json" \
  'r["ok"] is True and r["sentences"] == 1
   and r["clif"] == "(forall (v1) (if (Boy v1) (Person v1)))"'

args "$TMP/cl-alpha-z.json" '(forall (zz) (if (Boy zz) (Person zz)))'
check "clAlphaNorm collapses an alpha-variant" clAlphaNorm "$TMP/cl-alpha-z.json" \
  'r["ok"] is True
   and r["clif"] == "(forall (v1) (if (Boy v1) (Person v1)))"'

# clNormalize — Hayes's satisfiability-preserving IKL-to-CL reduction.
# `noIntrusion` is the PROOF HYPOTHESIS decided, so both verdicts are
# pinned: the head/tail pair, and the intrusion case the theorems do
# not cover.
args "$TMP/cl-norm.json" '(P (that (Q a)))'
check "clNormalize that-term -> head + tail" clNormalize "$TMP/cl-norm.json" \
  'r["ok"] is True and r["thatCount"] == 1 and r["noIntrusion"] is True
   and r["head"] == ["(P prop1)"] and r["tail"] == ["(iff (prop1) (Q a))"]
   and r["preserves"] == "satisfiability"'

args "$TMP/cl-norm-intr.json" '(forall (x) (P (that (Q x))))'
check "clNormalize intrusion -> noIntrusion false" clNormalize "$TMP/cl-norm-intr.json" \
  'r["ok"] is True and r["noIntrusion"] is False and r["thatCount"] == 1'

args "$TMP/cl-norm-bad.json" '(P a'
check "clNormalize unclosed paren -> error" clNormalize "$TMP/cl-norm-bad.json" \
  'r["ok"] is False and "unclosed" in r["error"]'

# clFiniteSat — CL.Examples' `tiny` as a wire interpretation: Boy holds
# of Bill alone. The refutations are pinned alongside the satisfactions,
# so a checker answering `true` to everything cannot pass.
CLI_FS='{"domain":["bill","boy"],"default":"bill","names":{"Bill":"bill","Boy":"boy","Sue":"boy"},"relations":[{"op":"boy","args":["bill"]}]}'

args "$TMP/cl-fs-yes.json" "$CLI_FS" '(Boy Bill)
(exists (x) (Boy x))'
check "clFiniteSat satisfied" clFiniteSat "$TMP/cl-fs-yes.json" \
  'r["ok"] is True and r["satisfied"] is True and r["domainSize"] == 2
   and [s["satisfied"] for s in r["sentences"]] == [True, True]
   and r["preconditions"]["domainComplete"]["holds"] is True
   and r["preconditions"]["noSeqQuant"]["holds"] is True'

args "$TMP/cl-fs-no.json" "$CLI_FS" '(Boy Sue)
(forall (x) (Boy x))'
check "clFiniteSat refutes where the tables have no row" clFiniteSat "$TMP/cl-fs-no.json" \
  'r["ok"] is True and r["satisfied"] is False
   and [s["satisfied"] for s in r["sentences"]] == [False, False]'

# The hypothesis `noSeqQuant` of `satisfiesFin_eq` is CHECKED, and a
# text outside it is refused by name rather than answered.
args "$TMP/cl-fs-seq.json" "$CLI_FS" '(forall (...m) (P ...m))'
check "clFiniteSat refuses a sequence-marker quantifier" clFiniteSat "$TMP/cl-fs-seq.json" \
  'r["ok"] is False and r["precondition"] == "noSeqQuant"
   and "noSeqQuant" in r["error"]'

args "$TMP/cl-fs-label.json" '{"domain":["bill"],"names":{"Boy":"nope"}}' '(Boy Bill)'
check "clFiniteSat unknown domain label -> error" clFiniteSat "$TMP/cl-fs-label.json" \
  'r["ok"] is False and "nope" in r["error"]'

args "$TMP/cl-fs-empty.json" '{"domain":[]}' '(Boy Bill)'
check "clFiniteSat empty domain -> error" clFiniteSat "$TMP/cl-fs-empty.json" \
  'r["ok"] is False and "at least one element" in r["error"]'

args "$TMP/cl-fs-nodom.json" '{}' '(Boy Bill)'
check "clFiniteSat missing domain -> error" clFiniteSat "$TMP/cl-fs-nodom.json" \
  "r['ok'] is False and 'domain' in r['error']"

args "$TMP/cl-fs-arity.json" "$CLI_FS"
check "clFiniteSat wrong arity -> error" clFiniteSat "$TMP/cl-fs-arity.json" \
  'r["ok"] is False and "expects 2 arguments" in r["error"]'

# --- Dataset handles (issue 585) --------------------------------------
# Handle state lives in the process, so the dependent sequence runs
# through `callseq`: open -> query -> update -> query -> serialize
# (both formats) -> close -> use-after-close error.
python3 - "$TMP/handles-seq.json" <<'EOF'
import json, sys
TTL = '@prefix ex: <http://e/> . ex:a ex:p ex:b .'
seq = [
  ["datasetOpen",      [TTL, "turtle", ""]],
  ["datasetQuery",     ["h1", "SELECT ?s WHERE { ?s <http://e/p> ?o }"]],
  ["datasetUpdate",    ["h1", "INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }"]],
  ["datasetQuery",     ["h1", "ASK { <http://e/x> <http://e/p> <http://e/y> }"]],
  ["datasetSerialize", ["h1", "nquads"]],
  ["datasetSerialize", ["h1", "turtle"]],
  ["datasetClose",     ["h1"]],
  ["datasetQuery",     ["h1", "ASK { ?s ?p ?o }"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handle lifecycle (open/query/update/serialize/close)" "$TMP/handles-seq.json" \
  'rs[0]["ok"] is True and rs[0]["handle"] == "h1" and rs[0]["count"] == 1
   and rs[1]["ok"] is True and rs[1]["kind"] == "select"
   and rs[1]["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"
   and rs[2]["ok"] is True and rs[2]["count"] == 2
   and rs[3]["ok"] is True and rs[3]["kind"] == "ask" and rs[3]["boolean"] is True
   and rs[4]["ok"] is True and "<http://e/x>" in rs[4]["nquads"] and "<http://e/a>" in rs[4]["nquads"]
   and rs[5]["ok"] is True and "@prefix" in rs[5]["turtle"]
   and rs[6] == {"ok": True}
   and rs[7]["ok"] is False and rs[7]["error"] == "unknown dataset handle: h1"'

# Two handles are independent: an update through h2 must not leak into
# h1, and closing h2 must leave h1 open. Also the per-family errors:
# an unknown serialize format, and closing an unknown handle.
python3 - "$TMP/handles-two.json" <<'EOF'
import json, sys
seq = [
  ["datasetOpen",      ["<http://e/a> <http://e/p> <http://e/b> .", "ntriples", ""]],
  ["datasetOpen",      ["<http://f/c> <http://f/q> <http://f/d> .", "ntriples", ""]],
  ["datasetUpdate",    ["h2", "INSERT DATA { <http://f/x> <http://f/q> <http://f/y> }"]],
  ["datasetSerialize", ["h1", "nquads"]],
  ["datasetSerialize", ["h1", "trig"]],
  ["datasetClose",     ["h2"]],
  ["datasetClose",     ["h2"]],
  ["datasetQuery",     ["h1", "ASK { <http://e/a> <http://e/p> <http://e/b> }"]],
]
json.dump(seq, open(sys.argv[1], "w"))
EOF
checkseq "dataset handles are independent + per-family errors" "$TMP/handles-two.json" \
  'rs[0]["handle"] == "h1" and rs[1]["handle"] == "h2"
   and rs[2]["ok"] is True and rs[2]["count"] == 2
   and rs[3]["ok"] is True and "<http://f/" not in rs[3]["nquads"]
   and rs[4]["ok"] is False and "unknown format tag" in rs[4]["error"]
   and rs[5] == {"ok": True}
   and rs[6]["ok"] is False and rs[6]["error"] == "unknown dataset handle: h2"
   and rs[7]["ok"] is True and rs[7]["boolean"] is True'

# One-shot error paths reachable without process state.
args "$TMP/h-open-bad.json" 'this is not turtle @@@' "turtle" ""
check "datasetOpen bad turtle -> error, no handle" datasetOpen "$TMP/h-open-bad.json" \
  'r["ok"] is False and "handle" not in r and len(r["error"]) > 0'

args "$TMP/h-query-unknown.json" "h999" 'ASK { ?s ?p ?o }'
check "datasetQuery unknown handle -> error" datasetQuery "$TMP/h-query-unknown.json" \
  'r["ok"] is False and r["error"] == "unknown dataset handle: h999"'

args "$TMP/h-open-arity.json" "just-one-arg"
check "datasetOpen wrong arity -> error" datasetOpen "$TMP/h-open-arity.json" \
  'r["ok"] is False and "expects 3 arguments" in r["error"]'

# --- FPP0 proof checker (issue 623 / M1) ------------------------------
# The degenerate bundle of the adoption doc's section 8a: the conclusion
# is itself a declared assumption. It is VALID and it proves nothing,
# and the three fields that say so travel with the verdict. No digests
# are needed for this shape, so the fixture is writable by hand.
PROOF_DEGEN='{"profile":"fpp0/1","artifacts":[],"assumptions":[{"id":"a1","subject":{"kind":"clif","proposition":"(P jim)"},"level":"attestation"}],"steps":[],"conclusion":{"kind":"clif","proposition":"(P jim)"}}'

args "$TMP/proof-degen.json" "$PROOF_DEGEN"
check "proofCheck reports the degenerate bundle, never as a proof" proofCheck "$TMP/proof-degen.json" \
  'r["ok"] is True and r["valid"] is True
   and r["conclusionIsAssumption"] is True
   and r["foundationalOnly"] is False
   and r["counts"]["foundational"] == 0
   and len(r["assumptions"]) == 1'

# An UNKNOWN level string is refused by name — never read as the weakest
# member, never dropped (theorem L4Wasm.Ops.decodeLevelName_inj).
args "$TMP/proof-badlevel.json" "${PROOF_DEGEN/\"level\":\"attestation\"/\"level\":\"A\"}"
check "proofCheck refuses an unknown evidence level" proofCheck "$TMP/proof-badlevel.json" \
  'r["ok"] is False and "unknown evidence level" in r["error"]'

# A decode failure is NOT an invalid bundle: the level below is a level
# the decoder knows, and the KERNEL is what refuses the bundle.
args "$TMP/proof-fnd-asm.json" "${PROOF_DEGEN/\"level\":\"attestation\"/\"level\":\"foundational\"}"
check "proofCheck: a foundational assumption is ok:true, valid:false" proofCheck "$TMP/proof-fnd-asm.json" \
  'r["ok"] is True and r["valid"] is False'

args "$TMP/proof-inspect.json" "$PROOF_DEGEN"
check "proofInspect reports shape and NO verdict" proofInspect "$TMP/proof-inspect.json" \
  'r["ok"] is True and "valid" not in r and r["steps"] == 0
   and r["conclusionDeclaredAsAssumption"] is True'

args "$TMP/proof-arity.json"
check "proofCheck wrong arity -> error" proofCheck "$TMP/proof-arity.json" \
  'r["ok"] is False and "expects 1 argument" in r["error"]'

# --- Dispatch reflection + unknown op ---------------------------------
args "$TMP/empty.json"
check "ops reflection (incl. handle ops via callIO)" ops "$TMP/empty.json" \
  'r["ok"] is True and isinstance(r["abiVersion"], str)
   and set(["parseToDatasetJson","queryDataset","updateDataset",
            "serializeNQuads","serializeTurtle","canonicalizeToNQuads",
            "scanIBK2Predicate","scanIBK3Predicate","queryIBK3BlockSetPreview",
            "storeManifestInspect","storeQueryPlan","storeQuery",
            "owlClosure","owlIsConsistent","owlEntails",
            "rhoDfClosure","rhoDfFragmentCheck",
            "rdfsPlusClosure","clParse","clSerialize",
            "clAlphaNorm","clNormalize","clFiniteSat",
            "proofCheck","proofInspect","ops",
            "datasetOpen","datasetQuery","datasetUpdate",
            "datasetSerialize","datasetClose",
            "activateVerify",
            "packBegin","packFeed","packEndPass",
            "packNext","packFinish","packClose"]) <= set(r["ops"])
   and r["blobOps"] == ["storeQuery","activateVerify"]
   and r["blobIoOps"] == ["blobEcho","packFeed","packNext"]'

check "unknown op -> error" definitelyNotAnOp "$TMP/empty.json" \
  'r["ok"] is False and "unknown op" in r["error"]'

echo "=== native-smoke: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
