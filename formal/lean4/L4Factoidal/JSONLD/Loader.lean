/-
L4Factoidal.JSONLD.Loader — the JSON-LD document-loader ABSTRACTION.

Port of `formal/fstar/JSONLD.Loader.fst`, whose whole content is one
declaration:

    assume val jsonld_load_document : string -> option string

That is the F* tree's only JSON-LD `assume val`. It is an ambient,
globally-resolved call: `JSONLD.Context.context_process` invokes it
directly, and each consumer binary installs a realisation into a mutable
ref cell at start-up
(`minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh`).

**This port dissolves it by parameterisation** (the purity doctrine in
`skills/factoidal-lean-basics/SKILL.md`): a `Loader` is an ordinary
total function value, threaded explicitly through every context-
processing entry point. There is no global state, no `opaque`, no
`@[extern]`, and no ambient effect — `contextProcess` is a total
function of its inputs, the loader among them.

JSON-LD 1.1 API (https://www.w3.org/TR/json-ld11-api/):
  * §4.1 Context Processing, the "dereference" step — a context given
    as a string is an IRI to be fetched;
  * §4.1 Context Processing, the `@import` step — the named document is
    fetched and merged before the containing context's own entries;
  * the error conditions `loading remote context failed` and
    `invalid remote context` are what a `none` result (or a fetched
    document that is not JSON / carries no `@context`) must become.

## The banned fallback

`skills/jsonld-context-cache/SKILL.md` states the rule this module
obeys: **an empty-context fallback is banned.** A loader that cannot
resolve an IRI returns `none`, and the caller turns that into
`JsonLdError.loadingRemoteContextFailed`. It must never return
`{"@context": {}}`, because a silently-empty context produces a
document that expands with every term unmapped — a wrong answer that
looks like a right one.

## The cache-directory-backed default (for the probe)

`third_party/jsonld-context-cache/` is a URL-keyed, content-addressed,
versioned snapshot store. Its `index.json` has this shape:

    { "contexts": {
        "<requested URL>": {
          "domain": "<host dir>",
          "url_sha256": "<hex>",
          "versions": [ { "path": "<domain>/<url_sha256>/vN.jsonld",
                          "final_url": "...", "version": N, ... } ] } } }

`cacheTableOfIndex` below turns that JSON into the `(url, relative
path)` table a caller needs; the caller (`Harness/JsonLdProbe.lean`)
does the actual file reads in `IO` and hands the resulting
`(url, body)` table to `tableLoader`. The library never touches the
file system.

The W3C toRdf suite's own "remote" contexts are NOT in that cache —
they are ordinary files shipped beside the manifest, addressed by the
manifest's `baseIri` prefix (see `JSONLD.Loader.fst`'s banner). Those
are served by `prefixLoader`, which rewrites a URL under a known IRI
prefix into a suffix the caller has already read from disk.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-- A JSON-LD document loader: an absolute IRI to the raw bytes of the
document retrieved from it, or `none` when it cannot be retrieved.

This is the Lean form of `JSONLD.Loader.fst`'s single `assume val`. It
is a PARAMETER, never an ambient call: `contextProcess` and every entry
point above it take one explicitly, so the whole of context processing
stays a total function of explicit inputs. Real I/O (a file read, an
HTTP fetch) lives in the executable that builds the `Loader` value. -/
abbrev Loader := String → Option String

namespace Loader

/-- The loader that resolves nothing. Every remote context reference
becomes `loading remote context failed` — the honest failure a consumer
with no fetching capability must produce. NOT an empty-context
fallback: see this module's header. -/
def none : Loader := fun _ => Option.none

/-- Try `a` first, then `b`. -/
def orElse (a b : Loader) : Loader := fun url =>
  match a url with
  | some d => some d
  | Option.none => b url

end Loader

/-- A loader backed by an explicit `(absolute IRI, document body)`
table — the shape a probe builds after reading files in `IO`. First
match wins. -/
def tableLoader (table : List (String × String)) : Loader := fun url =>
  (table.find? (fun kv => kv.1 == url)).map Prod.snd

/-- True when `s` starts with `p`. -/
def hasPrefix (p s : String) : Bool :=
  s.toList.take p.toList.length == p.toList


/-- Drop `n` leading characters. -/
def dropPrefixChars (n : Nat) (s : String) : String := (s.toList.drop n) |> String.ofList

/-- A loader for a whole IRI PREFIX: a URL beginning with `pre` has that
prefix stripped, and the remaining SUFFIX is looked up in `files` (the
caller's already-read `(relative path, contents)` table). This is how
the W3C JSON-LD suite's "remote" contexts resolve offline — the
manifest's `baseIri` (`https://w3c.github.io/json-ld-api/tests/`) maps
onto `third_party/testing/json-ld/tests/` on disk. -/
def prefixLoader (pre : String) (files : List (String × String)) : Loader := fun url =>
  if hasPrefix pre url then
    let suffix := dropPrefixChars pre.toList.length url
    (files.find? (fun kv => kv.1 == suffix)).map Prod.snd
  else Option.none

/-- One row of the vendored context cache's index: the requested URL and
the store-relative path of its newest snapshot. -/
structure CacheEntry where
  url  : String
  path : String
  deriving Repr, DecidableEq

/-- The `path` of the highest-numbered `versions` entry of one context
record. The index's `versions` array is ordered oldest-first, so the
LAST entry carrying a `path` string is the newest snapshot. -/
def newestVersionPath (rec_ : Json) : Option String :=
  match rec_.getArray? "versions" with
  | some vs =>
    vs.foldl (fun acc v =>
      match v.getString? "path" with
      | some p => some p
      | Option.none => acc) Option.none
  | Option.none => Option.none

/-- Read `third_party/jsonld-context-cache/index.json` (already parsed)
into the `(url, store-relative path)` table a caller needs. Documented
shape in this module's header; a record with no usable `versions` entry
is skipped rather than guessed at. -/
def cacheTableOfIndex (index : Json) : List CacheEntry :=
  match index.field? "contexts" with
  | some (.object entries) =>
    entries.filterMap (fun kv =>
      match newestVersionPath kv.2 with
      | some p => some { url := kv.1, path := p }
      | Option.none => Option.none)
  | _ => []

end L4Factoidal.JSONLD
