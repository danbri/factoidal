# Vendored: w3c/vc-di-eddsa-test-suite

- **Upstream:** https://github.com/w3c/vc-di-eddsa-test-suite
- **Commit:** `769275c968c608799939aa25bb32869ce76a8e10` (2026-01-14T15:55:48-05:00)
- **Retrieved:** 2026-07-10, `git clone --depth 1`
- **Licence:** BSD-3-Clause (`LICENSE.md`, Copyright (c) 2024 W3C, Inc.)

Vendored for task #88 (canivc.com community-compatibility integration)
so the official W3C Data Integrity `eddsa-rdfc-2022` / `eddsa-jcs-2022`
interoperability suite can run offline against
`bin/vc-api-shim/server.mjs`. `.git` metadata was stripped after clone
(this directory is a plain vendored copy, not a submodule, matching
the pattern of `third_party/contexts/`).

## What's here vs. what's not

- Suite source (`tests/`, `config/`, `package.json`, `w3c.json`,
  `localConfig.example.cjs`) is committed as-is.
- `node_modules/` is NOT committed (gitignored) — install with:

  ```sh
  cd third_party/testing/vc-di-eddsa
  npm install
  ```

  This pulls the suite's own dependency tree, including
  `data-integrity-test-suite-assertion` (github:w3c-ccg/...) and
  `vc-test-suite-implementations` (github:w3c/...) via npm's
  GitHub-dependency resolution — needs network access once, at install
  time. Suite execution itself (`npm test`) does not need network
  access beyond what `documentLoader.js` falls back to for context
  IRIs the suite's own `jsonld-document-loader` doesn't have bundled
  (the base VC/security contexts it depends on are bundled via its own
  `@digitalbazaar/*-context` packages).
- The suite's own `.localConfig.cjs` (implementation registration) is
  generated at test-run time by
  `tests/vc-di-eddsa/run.sh` (gitignored, not committed) — it points
  the suite's issuer/verifier tags at `bin/vc-api-shim/server.mjs`
  under `BASE_URL`, following the suite's own documented local-testing
  pattern (`localConfig.example.cjs`'s header comment).

## Scope run

Runner: `tests/vc-di-eddsa/run.sh` (task #88). Only the
`eddsa-rdfc-2022` tag is configured against the shim — the shim does
not implement `eddsa-jcs-2022` (JCS canonicalization of proof options
instead of RDFC; see
`docs/designissues/2026-07-10-canivc-community-compat.md` for the
scoping decision). `enableInteropTests` and `testAllImplementations`
are left at the suite's own defaults (`false`) so only our
implementation's own issuer/verifier round trip is exercised, not
cross-implementation interop against the other ~8 registered
implementations (those need live network + the
`w3c/vc-test-suite-implementations` registry's real endpoints, which
is explicitly out of scope for an offline-reproducible local run).
