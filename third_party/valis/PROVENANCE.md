# third_party/valis — the Valis vocabulary and example circuits (MIT)

[Valis](https://github.com/danja/valis) is Danny Ayers' description of
virtual analog synthesizer circuits in RDF: an LV2-style port vocabulary
for elements (oscillators, filters, envelopes, ...) and Turtle documents
that wire elements into a circuit with `val:Arc`/`val:ControlArc`. The
repository also ships a JUCE-based C++ plugin host, which is not part
of this vendoring — see "What is not vendored" below.

Nothing here is hand-written or modified. Each file is the upstream
byte stream at a named commit, recorded below with its SHA-256.
Provenance style follows
[`../vocabularies/PROVENANCE.md`](../vocabularies/PROVENANCE.md).

## Retrieval

- **Upstream:** <https://github.com/danja/valis>
- **Commit:** `0aeec1cfcf07f4068f124774ecb08470406c52ae` ("tweak",
  2026-09-16T18:24:16+02:00)
- **Retrieval date:** 2026-09-16
- **Method:** `git show <commit>:<path>` against a local clone of the
  upstream repository, redirected straight to the file below — no
  network fetch, no edit.

## Licence

The upstream `LICENSE` file is the GNU Affero General Public License
v3, covering the JUCE-based C++ plugin. The README's "Licence" section
at the pinned commit states the Turtle files are licensed apart from
that, verbatim:

> Any parts of this repository involving JUCE are AGPL - see LICENSE.
> Note that JUCE 9 is AGPLv3-or-commercial. A distributed binary that
> links JUCE under the AGPL obliges AGPL for the combined work. But
> the .ttl and other such descriptive files stand apart from this and
> are licensed as MIT. Derivative works that do not use the JUCE
> components may be considered under the latter license.

`LICENSE` in this directory is the MIT licence text, naming Danny
Ayers as the copyright holder, with that sentence quoted at its head —
the upstream repository has no separate `LICENSE-MIT` file to copy, so
the text here is the standard MIT template rather than an upstream
file. Nothing AGPL is vendored: no file under upstream's `src/`,
`include/`, `CMakeLists.txt` or the AGPL `LICENSE` itself is present in
this directory or anywhere else in this repository.

Background on why this vendoring is timed to this specific commit:
[danbri/factoidal#687](https://github.com/danbri/factoidal/issues/687)
(comments record the AGPL-at-first-check, the owner's request to Danny
Ayers to relicense the descriptive files, and the relicensing landing
as `0aeec1c`).

## Files and retrieval

| File | Bytes | SHA-256 | Triples (`factoidal count`) |
|---|---|---|---|
| `vocabs/valis.ttl` | 69,336 | `30aa9bdf9a66c5ca2dafdb83e7323e4a517d7a2c0fb3fe6d56aa11fc9ff9a13d` | 2,203 |
| `examples/909.ttl` | 40,892 | `224a7585c9d4192e52863e5b15fbe65c2fd6a85a3a643464d91074eb46204473` | 1,486 |
| `examples/808-bd.ttl` | 4,182 | `e1ceec1be3db72db4ae9cf92424a44a0c8b777d9aedf028681102537ebe4e184` | 137 |
| `examples/basic.ttl` | 1,646 | `29c6e5c5db18bb21ba71d6b3b71d946b76ec04ac34f0b7fe9de6dcc6bad02c91` | 57 |

Triple counts are `bin/linux-x86_64/factoidal count <file>`, no
`baseIRI` argument (the CLI's default relative-IRI base). Hub post 55
parses `vocabs/valis.ttl` and `examples/909.ttl` again through the npm
engine with the document's own `baseIRI` options
(`http://purl.org/stuff/valis/` and `urn:valis:909`); that run's own
triple counts are pinned separately in
[`tests/hub/post55_expected.json`](../../tests/hub/post55_expected.json)
and printed by the post itself, since a different base IRI can change
how many relative-IRI statements resolve. An earlier DAW session report
(quoted in issue #687) measured 2,132 and 1,486 triples against an
earlier revision of `vocabs/valis.ttl`; the count above is for the
file actually vendored here.

## What is vendored, and what is not

Only `vocabs/valis.ttl` and the three `examples/*.ttl` files listed
above are vendored. `vocabs/lv2/*.ttl` (the LV2 port vocabulary, ISC)
and `vocabs/w3c/owl.ttl` (W3C's own OWL vocabulary) are upstream files
too, but Valis's own Turtle documents reuse them by IRI reference
(`http://lv2plug.in/ns/lv2core#`, `http://lv2plug.in/ns/extensions/units#`)
rather than by import, so no copy of either is needed for the hub
notebook's SPARQL queries to run.

Nothing from upstream `src/`, `include/`, `CMakeLists.txt`, `cmake/`,
`build.sh`, `install.sh`, `valis` (the launcher script) or any other
C++/build file is included. The DAW engine JavaScript vendored
alongside this directory
(`docs/web/hub/assets/valis-daw/`) is not derived from that C++; see
its own `README.md` and the derivation review linked from
[danbri/factoidal#687](https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083).
