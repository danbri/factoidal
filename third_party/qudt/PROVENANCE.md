# QUDT v3.4.0 — vendored distribution + SHACL rulesets

## Upstream

- Repository: [github.com/qudt/qudt-public-repo](https://github.com/qudt/qudt-public-repo)
- Release tag: `v3.4.0` (released 2026-06-25)
- Tag commit: `1137205617d03d3d5c8351ea58105b6719c5d6f0`
  (peeled from tag object `e3c999028fbf3f6b49430390112ea4be4cfaafff`,
  read via `git ls-remote refs/tags/v3.4.0` on 2026-07-10)
- Retrieved: 2026-07-10

## License

CC BY 4.0, attribution to QUDT.org. Upstream `LICENSE.md` (vendored
verbatim as [`LICENSE.md`](LICENSE.md) in this directory) reads, in
full:

> Creative Commons Attribution 4.0 International License (CC BY 4.0),
> available at https://creativecommons.org/licenses/by/4.0/.
> Attribution should be made to QUDT.org"

(The trailing quote character is upstream's own.)

## Files and retrieval channels

| File | Retrieved from | SHA-256 |
|---|---|---|
| `QUDT-all-in-one-SHACL.ttl` | `https://qudt.org/3.4.0/shacl/qudt-all` (versioned resolved-graph URI; `Accept: text/turtle`) | `fc7ab1041a382e18fccdda7a99bd2c2a5a3d27e2aaa407561d68c3cf089b562c` |
| `QUDT-all-in-one-OWL.ttl` | `https://qudt.org/3.4.0/qudt-all` (versioned resolved-graph URI; `Accept: text/turtle`) | `1b6276ef2c2f6f95aa96044e46dcec1421cfcaac7fec7953648dcd91d235c045` |
| `COLLECTION_QUDT_USER_TESTS.ttl` | `https://raw.githubusercontent.com/qudt/qudt-public-repo/v3.4.0/src/main/rdf/validation/COLLECTION_QUDT_USER_TESTS.ttl` | `a1e09442be76dfc97ba1f429031a20ecbb28ebeff0beec4feea07e2cbfb51437` |
| `COLLECTION_QUDT_QA_TESTS_ALL.ttl` | `https://raw.githubusercontent.com/qudt/qudt-public-repo/v3.4.0/src/main/rdf/validation/COLLECTION_QUDT_QA_TESTS_ALL.ttl` | `d45d7a8adf1d61fe7307f1a6d3b20190ee3ffc2bfdb7fdca273b8ca392e1c49b` |
| `LICENSE.md` | `https://raw.githubusercontent.com/qudt/qudt-public-repo/v3.4.0/LICENSE.md` | (167 bytes, quoted in full above) |

Retrieval-channel note: the two all-in-one files are GitHub *release
assets* built by upstream CI (`target/dist/QUDT-all-in-one-{SHACL,OWL}.ttl`
in upstream's `pom.xml`), not files in the git tree, and the sandbox
proxy blocks `github.com` release-asset downloads for repositories
outside this session. The qudt.org versioned resolved-graph URIs above
are upstream's own documented distribution channel for the same graphs
(README.md "Quick-Start Guide", option 2: "Use the resolved graph and
instance URIs ... You can also load a specific version by including
the semantic version number"), and the downloaded graphs self-identify
as `<http://qudt.org/3.4.0/shacl/qudt-all>` /
`<http://qudt.org/3.4.0/qudt-all>` — the 3.4.0 pin is preserved; only
the transport differs from the release-asset download.

The two SHACL rulesets are the *source* (template) forms from the git
tree at the tag: their ontology IRIs carry a literal `$$QUDT_VERSION$$`
placeholder that upstream's build substitutes at dist time. The shapes
themselves (targets, SPARQL constraint text, severities) are identical
to the dist forms; the placeholder only appears in the collection /
prefix-declaration node IRIs, which are internally consistent within
each file.

Which ruleset is which (upstream README.md, "SHACL Validation for QUDT
Users versus QUDT Developers"):

- `COLLECTION_QUDT_USER_TESTS.ttl` — user-facing: flags references to
  deprecated instances/properties and checks user quantity data
  (dimension-vector consistency, array homogeneity/dimensionality).
- `COLLECTION_QUDT_QA_TESTS_ALL.ttl` — contributor-facing: validates
  the integrity of the QUDT ontologies themselves.

## Pinned-version rationale

QUDT unit definitions carry published conversion multipliers/offsets
(`qudt:conversionMultiplier`, `qudt:conversionOffset`) that change
across releases as upstream corrects data. Exactness claims made by
later layers of the QUDT program (Layer B exact-rational conversion,
Layer C SPARQL functions — see
`docs/designissues/2026-07-10-qudt-scoping.md`) are relative to the
published multipliers of THIS release, not to physics and not to
whatever qudt.org serves as "latest". Do not re-vendor from an
unversioned URI; bump the pin deliberately and re-run the suite.
