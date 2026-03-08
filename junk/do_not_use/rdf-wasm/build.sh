#!/usr/bin/env bash
# Build the rdf-wasm library for WebAssembly and copy to docs/ for GitHub Pages.
# Requires: rustup, wasm-pack (cargo install wasm-pack)
set -euo pipefail

cd "$(dirname "$0")"

echo "Building rdf-wasm for wasm32 target..."
wasm-pack build --target web --out-dir pkg

echo "Copying WASM artifacts to docs/pkg/..."
mkdir -p ../docs/pkg
cp pkg/rdf_wasm_bg.wasm pkg/rdf_wasm.js pkg/rdf_wasm.d.ts pkg/rdf_wasm_bg.wasm.d.ts ../docs/pkg/

echo ""
echo "Done! WASM artifacts are in docs/pkg/"
echo "To run the demo:"
echo "  cd docs && python3 -m http.server 8080"
echo "  Open http://localhost:8080"
