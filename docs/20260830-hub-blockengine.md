# Hub demos and the block-engine boundary

Date: 2026-08-30

## Hub consolidation follow-up

- The maintained public navigation now directs readers to the Hub rather than
  the ageing `/fstar-extracted/` gallery. Legacy assets remain fixtures and
  browser-engine inputs; they are no longer the advertised demo surface.
- Post 02 includes the original music corpus's `ex:by/ex:member` property
  path, making the two-hop album-to-performer example visible in the main
  SPARQL notebook.
- Post 48 is the editable JSON-LD playground: it performs `toRdf` and
  canonicalization locally, with an explicit unsupported-remote-context
  boundary. Post 47 contains the Hub/Observable-style authoring guide, leaving
  the Hub landing page as a short route into demonstrations.
- Hub output rendering is automatic. RDF datasets and binding rows use the
  existing responsive `pretty()` table renderer; DOM and chart values retain
  their native rendering. The reader-facing `Auto | Table` control was removed.
- Verified with the three focused Hub Node tests and a full Eleventy build from
  `docs/` into `/private/tmp/factoidal-hub-site`.

## Landed Hub notebooks

- `web/hub/45-life-sciences-named-graphs.md` is the concise Hub form of
  `fstar-extracted/demo-lifesci.html`.  It retains the three committed KGX
  Turtle files and the cross-graph chromosome/variant join, but makes loading
  an explicit click.  A documentation visit must not automatically parse its
  43,103 triples.
- `web/hub/46-browser-block-artifacts.md` accepts a local `IBK1` file through
  a user gesture, displays the public framing fields, computes SHA-256 with
  Web Crypto, and can persist an exact copy in OPFS.  It carefully does not
  claim that the browser already runs SPARQL over that block.

The older RIF page has already been superseded by the maintained and pinned
Hub notebook `web/hub/10-rules-rif-core.md`; no second RIF port is needed.

## Browser persistence direction

The file picker is portable.  `showOpenFilePicker()` is an optional ergonomic
path and the normal input is its fallback.  OPFS is an optional local cache,
not a trust source or upload destination.  When the Lean block-core WASM ABI
accepts canonical block bytes, it should consume the exact bytes from this
boundary after the same manifest/digest validation as native execution.

The likely performance shape is an OPFS-resident block file accessed in a
dedicated worker.  The File System API's synchronous access handle is worker-
only; that is compatible with a future range-reading `IBK2` directory but is
not required for the present IBK1 whole-artifact inspector.
