# graphflow — verified RDF transform networks, described as RDF

A spike. It answers one question: **does flow-based programming actually buy
this project anything, or is it a vocabulary we would be importing for its own
sake?**

The answer it produces: the *runtime* half of FBP buys nothing here, and the
*composition* half buys something real. This directory is the evidence.

```bash
node bin/graphflow/run.mjs                          # run the network, emit certificates
node bin/graphflow/check.mjs tmp/graphflow.cert.json # check them with no engine in the room
node bin/graphflow/sabotage.mjs                     # break each guard, confirm it bites
node --test bin/graphflow/test/graphflow.test.js
```

## What it does

`networks/validate-and-sign.ttl` describes a transformation network **as RDF**:
processes, components, ports, connections, and Initial Information Packets, in
classical FBP's nomenclature. `run.mjs` reads that description **with the
engine itself** — the network is extracted by SPARQL queries — orders the
processes, runs each one as an `fn.*` call, and emits one **transform
certificate** per process in the shape `docs/designissues/graphflow.md`
specifies: input hash, output hash, the semantics the transform claims, and a
signature.

The network is a real DAG, not a chain:

```
   IIP(data turtle)              IIP(shapes turtle)
          │                              │
       [data] parse                 [shapes] parse
          │                              │
     [closure] rho-df ──────┬────────────┘
          │                 │
   [canon] RDFC-1.0    [validate] SHACL      ← fan-out at closure,
          │                 │                  fan-in at validate
    [sign] Ed25519    conforms + report
```

**The closure is load-bearing.** The shapes target `ex:Mammal`, and nothing in
the input is typed `ex:Mammal` — `rex` and `fido` are `ex:Dog`. Only after
core-RDFS closure does `rdfs:subClassOf` make them Mammals and the shape find
any target at all. Delete the closure process and validation passes vacuously.
A test asserts the resulting `conforms=false`.

## What the checker proves, and what it refuses to

`check.mjs` is the interesting file. It imports **nothing but node builtins** —
a test enforces that — and it never runs the engine, because a checker that
re-runs the thing it is checking has re-imported the trust it exists to remove.

It does not believe the certificate about anything it can re-derive:

* it re-hashes the embedded network bytes;
* it **re-derives the wiring from those bytes** with a ~40-line N-Quads reader,
  rather than trusting the runner's provenance claims. This is why the
  certificate embeds canonical N-Quads instead of Turtle: N-Quads is
  line-oriented, so reading it needs a tokenizer, not an RDF engine;
* it checks every wire: the hash a producer certified must be the hash its
  consumer certified;
* it anchors the chain at the **Initial Information Packets**, whose hashes it
  recomputes from the network description itself — so the whole dataflow is
  pinned to the RDF, not floating free;
* it verifies the two transforms whose correctness is *derivable* without the
  engine: `canonicalize` (its output hash must equal its input's canonical
  hash, because `hash(dataset)` IS sha256 of the canonical form) and any inline
  JSON value;
* it refuses an end-to-end streaming claim from a network containing a
  whole-graph component;
* it verifies the Ed25519 signature with `node:crypto` — **a different
  implementation from the HACL\* one that signed it.** Two implementations
  agreeing is worth more than a round trip through one.

And it prints what it does **not** establish, every run. Chiefly: it checks
that hashes *chain*, not that they are *earned*. Whether `rhoDfClosure` really
computed the core-RDFS closure is the engine's business, and this checker
deliberately cannot tell.

## What this says about FBP

Worth taking:

* **Network-as-data.** The pipeline is a queryable, validatable, signable RDF
  document. That is a position no FBP implementation in
  [awesome-fbp](https://github.com/flux-doctrine/awesome-fbp)'s showcase can
  take, because none of them have an RDF engine underneath. Here the network
  description goes through the same verified parser as the data.
* **Ports and typed packets** give the certificate its shape: `kind` decides
  how a value is hashed, which is what makes hashes comparable across a wire.
* **The streaming/whole-graph distinction.** FBP frameworks generally let you
  build a network that quietly buffers everything. Declaring `gf:WholeGraph`
  makes "can this run in bounded memory?" a checkable question. Note it is a
  necessary condition, not a sufficient one — none of today's `fn.*`
  implementations stream, so no network here may claim it yet.

Deliberately not taken:

* **IP ownership semantics.** Classical FBP gives Information Packets a single
  owner to get safe zero-copy in mutable languages. `FnDataset` is frozen and
  content-addressed; sharing is already free. Importing ownership would be
  ceremony.
* **A push-based scheduler, bounded buffers, NoFlo/Node-RED runtimes.**
  `fn.js`'s `derive` is pull-based memoization keyed by content hash — "did
  anything actually change?" answered in O(1). FBP has no such notion;
  everything flows every time. Converting would *lose* incrementality.

## Status and honest gaps

This is a spike, not a landed subsystem.

* The namespace is `factoidal.example` on purpose — it does not resolve, and
  should not be published under a real domain until the vocabulary settles.
* The signing key is a published demo key. The signature shows the certificate
  is unaltered since the run; it endorses nothing.
* No time attestation, no build provenance, no runtime attestation — three of
  the four assurance layers `graphflow.md` describes are absent.
* Certificates are JSON. `graphflow.md` also offers RDF and VC payloads; that
  conversion is unwritten.
* Nothing here is verified. The orchestration is a consumer tool under Iron
  Rule 11; every transform's *meaning* comes from the engine, but the
  composition logic in `check.mjs` is hand-written JavaScript.

## A parser defect this spike found (2026-08-23)

While writing the vocabulary I used an undeclared `rdf:` prefix. `fn.parse`
returned **success with those statements silently dropped**.

The F\* parser is not at fault — it rejects the input precisely
(`undefined prefix: nosuch (byte offset 41)`), and `bin/<platform>/factoidal
--dump-nq` prints that and exits 1. The defect is in the npm consumer path:
`bin/npm-entry/entry_jsoo.ml`'s `parse_text_to_dataset` (line ~380) calls the
total `Parser_*.parse_*` entry points and wraps the result in `Ok`, so
`parseToDatasetJson` reports `{"ok":true,"count":0,"nquads":""}` for input the
parser rejected. Its own doc comment promises an `{"ok":false,"error":...}`
branch that parse errors never reach. Every `fn.parse` caller — including the
hub notebooks — therefore cannot distinguish an empty document from a
malformed one. `<http://a/s> <http://a/p> .` (no object) parses as "success,
0 triples".

`run.mjs` works around it with a floor check on every parse
(`parseChecked`), because a typo in a network description would otherwise
become "a network with no processes" and certify nothing while reporting
success. **The workaround is not the fix** — the fix belongs in
`entry_jsoo.ml`, using the raising path the CLI already uses.
