# 2026-07-07 — Delta-log replication, forking, and erasure in regulated settings

Status: **design note, nothing built here.** Written in response to a
design question: can we replicate the database by streaming the delta
log elsewhere (XMPP, DNS, …), and can that log be forked, rewritten,
and signed in ways that survive the demands of regulated industries —
GDPR erasure, legal-discovery redaction, and removal of illegal or
minor-authored material without destroying the record that a removal
happened?

This note deliberately expands every acronym and defines every term on
first use. It separates two very different meanings of the word
"proof," because the question spans both and conflating them causes
confusion.

## 0. Vocabulary (plain definitions used throughout)

- **RDF** (Resource Description Framework): the W3C data model this
  engine implements. Data is a set of **triples** — `(subject,
  predicate, object)` statements, e.g. `(alice, knows, bob)`. A
  **quad** adds a fourth element, the named graph the triple lives in.
  A "database" here is a set of quads.
- **Delta log**: an append-only file of *changes*. Instead of
  overwriting the database, every change (add these quads / remove
  those quads) is written as a new, self-contained **entry** at the end
  of the log. "Append-only" means entries are only ever added, never
  edited or deleted in place. Factoidal already has this: framed
  entries with a magic marker (`DLE1`), length-prefixed fields, atomic
  append, checksum-detected torn-write recovery, and a **sequence
  number** (`seq`) per entry giving a total order.
- **Hash**: a fixed-size fingerprint of some bytes, produced by a
  one-way function (e.g. **SHA-256**, a 32-byte hash). Same input →
  same hash; changing one bit of input changes ~half the output bits;
  you cannot feasibly run it backwards to recover the input. Factoidal
  already computes canonical hashes of RDF graphs via **RDFC-1.0** (RDF
  Dataset Canonicalization 1.0), surfaced as `urn:rdfc:sha256:…`
  identifiers.
- **Signature / Ed25519**: a **digital signature** proves *who* created
  a message and that it wasn't altered. The signer holds a secret
  **private key**; anyone with the matching **public key** can verify.
  **Ed25519** is a specific, fast, widely-used signature algorithm.
  Factoidal now has Ed25519 sign/verify from **HACL\*** (the
  formally-verified crypto library Mozilla ships in Firefox), landed
  with the Verifiable Credentials work.
- **CRDT** (Conflict-free Replicated Data Type): a data structure
  designed so that independent replicas can each accept changes offline
  and later **merge** deterministically to the same state, with no
  central coordinator and no "merge conflict." Explained in §2.3.
- **Merkle tree**: a tree of hashes. Each leaf is the hash of one data
  item; each internal node is the hash of its children; the single
  **root hash** commits to the entire collection. Its value: you can
  prove one item belongs to the set by revealing only the ~log(N)
  hashes along its path to the root (a **Merkle proof** or **inclusion
  proof**), not the whole set — and you can *remove* an item's data
  while keeping its leaf hash, so the root still verifies. Named after
  Ralph Merkle.
- **Chain of custody**: the record, in law and forensics, of who held a
  piece of evidence, when, and what was done to it — an unbroken,
  auditable trail. In our setting: proving *that* a deletion happened,
  *who* authorized it, and *when*, even though the data itself is gone.

## 1. Replication: the delta log already *is* a replication log

The realization that makes everything else follow: **an append-only,
ordered log of changes is the exact primitive every replication system
is built on.** Database replication, event sourcing, message queues
like Apache Kafka, and CRDT delta-shipping are all "write changes to an
ordered log; ship the log; a replica replays it." Factoidal's delta log
already has the shape.

To replicate: ship each committed entry, in order, to another node;
that node replays the entries into *its own* delta log and rebuilds the
same quad-set. The **transport** — how bytes get from A to B — is
orthogonal to the model.

### 1.1 Transports (how the bytes travel)

- **XMPP** (Extensible Messaging and Presence Protocol): an open,
  federated messaging standard (the protocol behind Jabber; the "chat"
  lineage of the social/semantic web). Its **PubSub** extension
  (Publish-Subscribe, standardized as XEP-0060) is purpose-built for
  this: a publisher posts **items** to a **node** (a topic); every
  subscriber receives them in order. Publish each delta entry as a
  PubSub item; subscribers replay. You get ordered fan-out,
  subscription management, and cross-server **federation** (independent
  servers relaying to each other) for free. This is the strong,
  realistic transport, and it sits well with RDF's social-web history.
- **DNS** (Domain Name System): the internet's name-lookup system.
  Usable as a *cacheable, pull-only* data channel: publish entries as
  **TXT records** (free-text DNS records) under a zone you control
  (e.g. `42.mydb.deltas.example.org TXT "<base64-chunk>"`); replicas
  poll the sequence, and DNS's global caching distributes reads like a
  content-delivery network. Real but niche: TXT strings cap near 255
  bytes (so entries must be chunked), there is no push (replicas must
  poll), and writing needs control of a DNS zone. Best for a *small,
  slow, read-only* feed — a curiosity next to XMPP, though the caching
  and the fact that DNS names are a global namespace make a
  *content-addressed* delta feed (fetch entry by its hash) a genuinely
  interesting party trick.
- Others fit the same slot without changing the model: HTTP
  **SSE** (Server-Sent Events, a browser-native server-push stream),
  **WebRTC** (browser-to-browser peer connections), a shared file, an
  **IPFS** (InterPlanetary File System — content-addressed
  peer-to-peer storage) object, a Kafka topic. Pick per deployment.

The adapter that moves entries over any of these is **I/O glue** — in
this project's terms an `assume val` realization outside the
formally-verified core (Iron Rule #11), and it plugs into the existing
**store-capability seam** (`caps_of_backend`) the same way HDT, the
delta overlay, and the in-memory bytes store already do.

### 1.2 Ordering, gaps, idempotence

Because entries carry sequence numbers, a replica gets three things for
free: **ordered replay** (apply in `seq` order), **gap detection**
(missing `seq` ⇒ request a resend), and **idempotence** (replaying the
same entry twice is a no-op — critical when a transport may redeliver).

### 1.3 One writer vs. many (where CRDTs enter)

**Single-writer** replication — one node is the source of truth, others
are read replicas — is trivial: publish on append, replay on receive.
No conflicts are possible because only one node ever writes.

**Multi-writer** — several nodes each accept writes while offline, then
reconcile — needs a **merge** rule, and this is where RDF pays off
(next section).

## 2. Merging divergent replicas (the CRDT story, explained)

### 2.1 The problem

Two replicas go offline, each accepts different changes, then
reconnect. Whose change wins? A naive "last write overwrites" loses
data and depends on clocks agreeing. A **CRDT** avoids the question by
making merge **commutative, associative, and idempotent** — apply the
changes in any order, any number of times, and every replica lands on
the identical state. No central lock, no conflict dialog.

### 2.2 Why RDF is unusually friendly to this

An RDF database is a **set of quads**. Sets have a natural conflict-free
merge: **union**. If two replicas each added different quads, the merged
database is just the union of both — no conflict, by construction. The
hard part is *deletion* (below), not addition.

### 2.3 The set CRDTs, named

- **G-Set** (Grow-only Set): supports add only; merge = union. Perfect
  for an append-only knowledge base, useless if you ever delete.
- **2P-Set** (Two-Phase Set): an add-set plus a **tombstone** set (a
  *tombstone* is an explicit "this element is removed" marker). An
  element is present if it's in the add-set and not tombstoned.
  Simple, but once tombstoned an element can never be re-added.
- **OR-Set** (Observed-Remove Set): the practical choice. Each add is
  tagged with a unique id; a remove tombstones *the specific adds it
  observed*. This lets an element be removed and later legitimately
  re-added (a new add with a new id), which 2P-Set forbids.

Factoidal's delta log already records adds and removes as **distinct
framed operations**. Recording a unique tag per operation upgrades the
log to an OR-Set with **no new query algebra** — the SPARQL engine
still sees a plain quad-set; the merge logic lives at the log/overlay
layer. That is the whole multi-writer story: an OR-Set over the delta
log, merged by union-with-tombstones.

### 2.4 The catch that §3 is about

Tombstones delete *logically* — "treat this quad as gone." They do
**not** delete *physically*: the original add entry, with the data in
it, is still sitting in the log. For ordinary use that's fine. For
**erasure law and evidence handling it is not enough**, because the
personal data, the illegal content, or the withheld material is still
recoverable from the log. Resolving that is the rest of this note.

## 3. The core tension: immutability vs. the right (or duty) to erase

Everything that makes a signed, hash-chained, append-only log valuable
— tamper-evidence, replayability, provenance — is exactly what fights
against deletion. And several regimes *require* deletion:

- **GDPR Article 17** (the EU General Data Protection Regulation's
  "right to erasure," commonly "right to be forgotten"): a data subject
  can require a controller to delete their personal data.
- **Legal discovery**: in litigation, parties must produce relevant
  records — but often with privileged, irrelevant, or third-party
  personal material **redacted** (blacked out), and must attest the
  production is faithful.
- **Illegal or minor-authored content**: material that must be made
  unrecoverable (e.g. CSAM — child sexual abuse material — or content a
  minor authored and has a right to have removed), while law
  enforcement and custodians still need a provable record that an item
  existed and was removed, by whom and when.

A blockchain-style "you can never delete anything" log is
*incompatible* with all three. The good news: the cryptography
community solved this a decade ago, and the techniques compose cleanly
with what factoidal already has. The trick in every case is the same:
**separate the proof from the payload — keep the proof, destroy the
payload.**

### 3.1 Technique A — content/payload separation (hash-in-log, data-off-log)

Store in the log only a **hash** of each change, plus metadata (who,
when, `seq`). The actual quads live in a separate content store keyed
by that hash — factoidal already content-addresses graphs via RDFC-1.0
(`urn:rdfc:sha256:…`), which is precisely this key. To erase: delete the
content-store record; the log keeps the hash. A SHA-256 hash is a
fixed-size fingerprint, not the data, and — for high-entropy or
**salted** inputs (a random secret mixed in before hashing so the hash
can't be guessed by trying candidate values) — is generally treated as
de-identified. Result: the hash chain and ordering survive intact; the
personal data is gone. Caveat: hashing *low-entropy* data (a known
name, a boolean) is reversible by brute force, so this technique
requires salting or pairing with Technique B.

### 3.2 Technique B — crypto-shredding (encrypt per record, delete the key)

Encrypt each entry's payload under its **own** symmetric key. To erase
a subject's data, **destroy their key(s)**. The ciphertext (encrypted,
unreadable bytes) stays in the log — so the hash chain and every
signature over it remain valid — but the plaintext is permanently
unrecoverable. Deleting the key to render data permanently inaccessible
is an *accepted* GDPR erasure method: inaccessible-forever counts as
erased. This gives the strongest "keep the structure, lose the content"
guarantee, and it directly enables **partial obfuscation for
discovery**: release the keys for the discoverable records, withhold
the rest. Key management (per-subject or per-record keys, secure key
destruction) is the real engineering cost.

### 3.3 Technique C — redactable structures and signatures

- **Merkle pruning**: build a Merkle tree over the dataset (§0). To
  redact an item, drop its data but keep its **leaf hash** (or replace
  it with a "redacted here" placeholder). The **root hash** still
  verifies, so you retain a proof that "an item existed at this
  position and had this fingerprint" without its content — ideal for
  "we withheld N records, here's proof we didn't silently alter the
  rest."
- **Redactable signatures**: a real cryptographic primitive (a class of
  signature schemes) where the original signer signs a document such
  that *anyone* can later remove parts and produce a **still-valid
  signature over the redacted version**. The verifier learns that
  redaction occurred and that the remainder is authentic, but not what
  was removed. This is purpose-built for privacy-preserving disclosure
  and audit. (Note: HACL\* does not provide these; they'd be a separate
  vendored or verified primitive, or approximated with Merkle pruning +
  Ed25519 over the pruned tree. Flagged honestly as not-in-hand.)

### 3.4 Putting the techniques together per regulated case

- **GDPR erasure**: crypto-shred (B) the subject's records and/or redact
  (C); write a **signed tombstone** entry recording "erasure performed
  under Article 17 request #X at time T by controller Y." You end up
  *able to prove you complied* (the data is unrecoverable) *and able to
  prove what you did* (the signed removal record) — without retaining
  the personal data. The tombstone is the chain-of-custody, not the
  data.
- **Discovery with partial obfuscation**: produce a signed **fork**
  (§4) containing only the discoverable material, sensitive fields
  redacted via (C); hand the court a cryptographically-authentic subset
  with a proof it is a faithful redaction of the original — without
  exposing the withheld material.
- **Illegal / minor-authored material**: purge the content store (A) and
  crypto-shred (B) so the material is unrecoverable; keep the hash, a
  signed removal attestation, the authorizing order, and (for CSAM
  specifically) a perceptual-hash detection record — a **perceptual
  hash** (e.g. the PhotoDNA family) is a fingerprint robust to small
  image edits, letting you record "content matching known-bad
  fingerprint H was here and was removed" without ever storing the
  content. Content-addressing (A) is exactly the "keep the fingerprint,
  purge the content" primitive this needs.

## 4. Forking, "rewriting," and signing chains between nodes and forks

Yes — and the mental model is **Git** (the version-control system),
made cryptographic.

- **Hash-chaining the entries.** Give each delta entry a field holding
  the hash of the *previous* entry (like a Git commit's parent
  pointer). Now the log is a **hash-linked list** — literally a
  blockchain in the original sense — and it is **tamper-evident**:
  altering any past entry changes its hash, which changes every
  following entry's `prev-hash`, which breaks every subsequent
  signature. You cannot quietly rewrite history in place; that is the
  point.
- **Signing chains.** Sign each entry (or each **checkpoint** — a
  periodic signed commitment to the log state, like Certificate
  Transparency's "Signed Tree Head") with the node's Ed25519 key, over
  `(prev-hash, payload-hash, timestamp, node-id)`. When node B
  replicates node A's segment, B **counter-signs** it ("I, B, observed
  and accepted A's entries 1–100 at time T"). Chained counter-signatures
  give a **provenance chain**: a verifiable record of which node
  produced, and which nodes attested, every segment.
- **Forking.** A node forks the log at a point (a Git branch) — to
  produce a redacted variant for one jurisdiction, a discovery-response
  subset, or a divergent multi-writer branch. The fork's first entry
  records its **parent** (the fork-point hash) and is signed, so *the
  relationship between the canonical log and the fork is itself
  cryptographically provable*.
- **"Rewriting."** You never rewrite an append-only hash chain in
  place. Instead you produce a **new, re-signed fork** that
  omits/redacts entries, carrying a **signed derivation statement**:
  "this fork is derived from canonical log L at entry N by redaction
  operation R, authorized by order O, signed by custodian/DPO"
  (**DPO** = Data Protection Officer, the GDPR-mandated privacy role).
  Then crypto-shred the original payloads. The outcome is the important
  part for regulated work: **you do not hide that a deletion happened —
  you produce a tamper-evident, signed proof of who authorized it, when,
  and that everything else is unaltered.** That is chain-of-custody,
  built from forks + signatures + shredding rather than from never
  deleting.

The real-world precedent to point at is **Certificate Transparency
(CT)** — the system that makes the web's TLS certificate authorities
publicly auditable. CT logs are exactly this: append-only,
Merkle-tree-backed, publicly verifiable, with signed checkpoints and
**consistency proofs** that log version N is an append-only extension
of version M (i.e. no history was rewritten). CT proves the whole model
works at internet scale.

## 5. The two meanings of "proof" (the question spans both)

The question rightly notes the proofs here are "not necessarily F\*."
Keeping the two kinds distinct is essential:

- **F\* proofs (compile-time, about the *code*).** These prove the
  *software* is correct before it ever runs: that the delta-log
  serializer round-trips (`lemma_triple_roundtrip`), that a parser is
  total, that canonicalization is deterministic. They say nothing about
  any particular dataset's history. Static, about the program.
- **Cryptographic proofs (run-time, about the *data and its
  history*).** These prove facts about specific data as it flows
  between nodes:
  - **Integrity / tamper-evidence** — the hash chain proves no past
    entry was altered.
  - **Provenance / authenticity** — Ed25519 signatures prove which node
    produced or attested each entry.
  - **Inclusion (membership)** — a Merkle proof shows "this quad is in
    the committed dataset" by revealing only a short hash path, not the
    whole set.
  - **Exclusion (non-membership)** — over a sorted Merkle tree /
    authenticated dictionary, prove a quad is *not* present.
  - **Consistency** — CT-style, prove version N append-only-extends
    version M: no rewrite.
  - **Redaction** — redactable signatures prove "this is an authentic
    subset of a signed original, with parts removed," without revealing
    the removed parts.
  - **Zero-knowledge proofs (ZKPs)** — advanced but directly relevant
    to the hardest case: prove a *property* of erased/hidden data
    without revealing it, e.g. "the removed record matched a known-bad
    perceptual hash" or "the erased author was a minor, justifying
    removal," proven to an auditor who never sees the content.

The elegant part: **F\* proofs make the cryptographic-proof machinery
trustworthy.** The code that builds the Merkle tree, chains the hashes,
and verifies the signatures is itself extracted from verified F\* — so
the tamper-evidence rests on verified software, and the crypto
primitive (Ed25519) is already HACL\*-verified. The two kinds of proof
reinforce rather than compete.

## 6. What factoidal has vs. what this needs

Already in hand:

- Append-only framed delta log (`DLE1`), sequence numbers, atomic
  append, checksum torn-write recovery — the substrate.
- RDFC-1.0 content-addressing (`urn:rdfc:sha256`) — the hash primitive
  for content/payload separation and Merkle leaves.
- Ed25519 sign/verify via HACL\* — the signature primitive for signing
  chains and checkpoints.
- Canonical snapshots (compaction) — checkpoints a fork or fresh
  replica bootstraps from.
- The store-capability seam — where a transport/overlay adapter plugs
  in without touching the evaluator.

Not built (honestly scoped):

1. **Hash-chain field** on entries (each commits to `prev-hash`) — a
   small framing addition, specifiable and provable in F\* like the
   existing entry format.
2. **Merkle tree / authenticated dictionary** over the quad-set — for
   inclusion, exclusion, and CT-style consistency proofs.
3. **Per-record encryption + key lifecycle** — for crypto-shredding
   (the GDPR/illegal-content path). Key destruction is the hard part.
4. **Signed checkpoints + counter-signature/attestation format** — the
   provenance chain between nodes and forks.
5. **Fork / derivation record** — the signed "derived-from L at N by
   redaction R under order O" edge.
6. **Redactable signatures** — a vendored or newly-verified primitive
   (HACL\* lacks them); or approximate with Merkle pruning + Ed25519.
7. **Transport adapter(s)** — XMPP-PubSub as the reference; DNS-TXT as
   the cacheable read-only variant; both I/O glue.
8. **OR-Set merge tag** on operations — the multi-writer story (§2.3).

## 7. Suggested staging (smallest sound steps first)

1. **Hash-chain + signed checkpoints.** Add `prev-hash` to entries;
   emit a periodic Ed25519-signed checkpoint. Delivers tamper-evidence
   and provenance with existing primitives. Verifiable in F\*.
2. **Content/payload separation + signed tombstones.** Move payloads
   behind their RDFC-1.0 hash; make deletion = purge-content + signed
   removal record. Delivers GDPR erasure and the chain-of-custody
   record with no new crypto.
3. **Merkle tree + inclusion/consistency proofs.** Adds discovery-grade
   "faithful subset" and CT-style "no rewrite" proofs.
4. **Crypto-shredding + key lifecycle.** Adds strong erasure for
   illegal/minor-authored content and key-gated discovery disclosure.
5. **Fork/derivation records + counter-signatures.** Adds the
   full multi-node, multi-fork provenance graph.
6. **Transport adapter (XMPP-PubSub).** Turns all of the above into
   live replication.
7. **(Optional, advanced)** redactable signatures; zero-knowledge
   property proofs for the hardest content cases.

Steps 1–2 are cheap, mostly reuse landed primitives, and already
deliver "replicable, tamper-evident, GDPR-erasable with an audit
trail." The rest is additive and each step stands alone.

## 8. One honest caveat

None of this is a legal opinion. "Crypto-shredding satisfies Article
17" and "a signed tombstone is adequate chain-of-custody" are positions
with support in the literature and regulator guidance, but the
acceptable-erasure bar varies by jurisdiction, regulator, and case, and
CSAM handling in particular is governed by specific reporting-and-
destruction law that a system must be built *to*, not around. The
architecture here is designed to give a compliance/legal team the
*mechanisms* — provable deletion, provable non-alteration of the
remainder, provable authorization — not to decide on their behalf that
a given mechanism clears a given legal bar.
