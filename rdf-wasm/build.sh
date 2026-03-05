#!/usr/bin/env bash
# Build the rdf-wasm library for WebAssembly.
# Requires: rustup, wasm-pack (cargo install wasm-pack)
set -euo pipefail

echo "Building rdf-wasm for wasm32 target..."
wasm-pack build --target web --out-dir pkg

echo ""
echo "Done! To run the demo:"
echo "  cd demo && python3 -m http.server 8080"
echo "  Open http://localhost:8080"
