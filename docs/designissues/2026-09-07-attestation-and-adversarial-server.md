# Attestation and the adversarial server: what theorems and what hardware can tie down

2026-09-07. Owner questions, verbatim, in order:

> "Considering possible misbehaviours of an XMPP server admin w.r.t. OMEMO and
> MIX, and potentially MUC, GC3 ... are there any theorems to seek that tie
> down different workflows, paths, activities within the server, so we can
> prove that a group hasn't been betrayed, or that certain unattractive
> activities are unreachable by admins, short of hardware meddling?"

> "(consider maybe this all runs on an attested platform too)"

> "I need to learn more about attestation options, what can be done so far and
> eg home vs office vs cloud/corp settings"

> "compromised client --- do we have enough in our library to be the client
> role's implementation too? can server and client each reasonably demand that
> the other prove it is running a specific attested build? Without locking us
> into Apple-esque walled gardens?"

> "we'd want to also know the client or server wasn't running in a VM /
> simulation where the owner of that universe can peek into its memory, etc?"

> "stick it all in a doc not issues, it is too speculative"

This record is that document. Nothing in it is scheduled; it states what is
provable, what hardware can and cannot establish, and the order in which the
pieces would be built if the work is taken up. The one non-speculative
dependency, reproducible builds of the Lean executables, is named in §7.

## 1. Three adversaries, three layers of theorem

The question "has the group been betrayed" splits by who the adversary is.

| layer | adversary | what can be proved | proved against what |
|---|---|---|---|
| 1 | nobody: the server is our binary, running as built | the server's code cannot read, fabricate or reroute what it carries | the Lean implementation, by theorem |
| 2 | the server operator, with full control of the server and the network | the members' protocol keeps confidentiality, authenticity, membership integrity and transcript agreement regardless of the server | the client-side protocol, over a symbolic cryptography model |
| 3 | whoever controls the machine below the software | that the software above is the proved software, and that memory is not readable from below | hardware attestation, with stated residues |

Layer 1 is provable today and cheap. Layer 2 is provable and is where the
real content sits. Layer 3 is not a theorem at all; it is measured evidence
signed by hardware, and it is what turns "the code we proved" into "the code
that is running".

## 2. Layer 1: theorems about our server's code

These are properties of `L4Factoidal/XMPP/Server.lean` and the modules under
it, provable in Lean without any cryptographic assumption.

- **Payload opacity by parametricity.** Route and store stanzas with the body
  as a type parameter the server code cannot inspect: `Stanza α` with routing
  polymorphic in `α`. "The server cannot read, log or branch on a body" is
  then a typing fact. This is the free theorem of the polymorphic type, and it
  costs nothing but discipline in the signatures.
- **No fabrication.** Every stanza delivered to a session is one a session
  emitted, with `from` stamped from the authenticated session that emitted it;
  stated as: the multiset of delivered stanzas is a sub-multiset of the emitted
  ones, `from` preserved. No path from the administrative interface mints a
  stanza attributed to a user.
- **Membership changes only by authenticated member commands.** For rooms
  (MUC, MIX, GC3) the membership transition relation is indexed by a
  client-authenticated command. An administrative transition can delete a room
  or refuse service; no transition adds a participant, changes a member's
  published key list, or rewrites a roster, because none exists. The "ghost
  user" attack on group chats is unreachable by construction, not by policy.
- **Non-interference.** What user A observes is a function of A's own sessions
  and the group transcript, and of administrative inputs only through
  availability (delay, drop).

These say: this binary, running as built, cannot do those things. They say
nothing once root replaces the binary. That is layer 3's job.

## 3. Layer 2: theorems about the client protocol against an arbitrary server

Here the operator is the adversary and may fire any server transition, drop,
reorder, delay, replay or forge anything on the wire. The properties are
stated over a symbolic cryptography model (the Dolev-Yao style; the
`ravst/SymbolicCryptographyLean` project is prior art for the modelling
style in Lean 4), with the HACL\* primitives entering as ideal functions.

| property | OMEMO (XEP-0384) | MLS (RFC 9420), and GC3 if specified on MLS |
|---|---|---|
| confidentiality of message bodies | provable: session keys never touch the server | provable |
| sender authenticity | provable per device | provable |
| no ghost member (the server cannot add a party able to decrypt) | provable only under a client policy of fingerprint verification; under blind trust of new devices the server CAN add a device, and the theorem says exactly that | provable: membership is the group's own signed transcript; the server is the untrusted Delivery Service of RFC 9420's threat model |
| no split view (the server cannot show different histories to different members without detection) | not provable: OMEMO binds no transcript | provable: the confirmation tag chains the epochs |
| forward secrecy and post-compromise security | provable per session | provable |

The sharp statement: with MLS underneath, "the group has not been betrayed"
is a theorem about the members' signed transcript, and the server is exactly
the untrusted delivery service the MLS specification assumes. With OMEMO
alone, the ghost-member and split-view properties depend on client key
verification, and a proof would say precisely that and no more. This argues
for specifying GC3 on MLS rather than on a new envelope; the modules under
`L4Factoidal/XMPP/Gc3.lean` are a scope stub today because the XSF
specification is unfinished.

What no theorem at layer 2 removes: metadata (who talks to whom, when, how
much), availability (the operator can always drop), and a compromised member
device. Stating those is part of the result.

## 4. Layer 3: attestation

### 4.1 What it is and what it proves

A hardware root of trust measures (hashes) everything that ran from reset
onward, chains the measurements, and signs a statement about them with a key
the hardware vendor certifies. A verifier compares the measurements with
expected values, for us the reproducible build of the Lean server plus its
carrier, kernel and configuration, and checks the signature chain to the
vendor. It proves which software booted on which class of hardware. It never
proves the software is correct; that is what layers 1 and 2 are for. The
vocabulary is RFC 9334 (RATS: Attester, Verifier, Relying Party); the evidence
format is EAT (COSE-signed claims), which the tree's ES256 and EdDSA
verification can already check.

### 4.2 Mechanisms that exist today

| mechanism | what it measures | who signs | where |
|---|---|---|---|
| TPM 2.0 measured boot (discrete or firmware TPM); Linux IMA for runtime files; Keylime as verifier | firmware, bootloader, kernel, initrd, optionally every executed file | the TPM's endorsement key, certified by the TPM maker | most PCs, mini PCs and servers; bare-metal hosting; a Raspberry Pi only with an add-on TPM |
| confidential VMs: AMD SEV-SNP, Intel TDX, Arm CCA | the VM's initial memory image and launch policy; memory encrypted against the host | the CPU (AMD VCEK, Intel PCK) | Azure Confidential VMs, GCP Confidential VMs and Confidential Space, some AWS instance types; bare metal with these CPUs |
| enclaves: AWS Nitro Enclaves, Intel SGX (server Xeons) | an isolated process image | AWS or Intel | any EC2 instance (Nitro); SGX servers |
| device attestation: Apple Secure Enclave and App Attest, Android Key Attestation, WebAuthn attestation | that a key lives in this device's hardware, plus boot state on Android | Apple, Google, the authenticator maker | client devices only |
| build provenance: reproducible builds, SLSA, Sigstore transparency logs | that a binary hash came from a named source commit and build | the build service | anywhere, no hardware needed |

### 4.3 By setting

- **Home.** An Intel or AMD mini PC with a firmware TPM gives measured boot of
  a unified kernel image, Keylime verifying from a second machine or a phone,
  and the server's identity key generated inside the TPM so no administrator
  can copy it. A Raspberry Pi needs a TPM board. Apple Silicon Macs have the
  hardware but expose no quote to third parties, so a Mac cannot attest a
  server workload. Runtime integrity after boot is the weak spot; IMA closes
  part of it.
- **Office or small organisation.** The same TPM story on a fleet, workload
  identity through SPIFFE/SPIRE with the TPM attestor, keys in an HSM
  (YubiHSM class), device attestation for members' machines through the
  management platform. This is where "an administrator cannot extract the
  group's keys" becomes a fact, because the administrator never holds them.
- **Cloud and corporate.** Confidential VMs are the strongest and simplest:
  the server runs inside a VM whose memory the host cannot read and whose
  launch measurement is signed by the CPU; GCP Confidential Space and Azure
  Attestation issue tokens a client can verify. Nitro Enclaves give a smaller
  signed isolated image on AWS. Trust moves from the cloud operator to the CPU
  vendor, a reduction, not an elimination. **Fly.io offers none of this**
  (Firecracker microVMs, no TPM or SEV quote), so the deployments of
  2026-09-07 (`factoidal-skosall`, the planned `factoidal-xmpp`) can publish
  build provenance but cannot attest what is running.

### 4.4 "Not in a VM whose owner can peek"

Plain attestation proves what booted; only confidential computing proves that
nobody below can read memory, and it has residues.

| running as | can the host or owner read memory? | what the evidence shows a verifier |
|---|---|---|
| ordinary VM with a virtual TPM | yes; the hypervisor sees all guest memory | the vTPM's quote proves what the host allowed it to measure; its endorsement certificate is the host's or the cloud's, not a chip maker's, and a policy can refuse it on that ground |
| bare metal, physical TPM, measured boot | no hypervisor if the measured chain has none: firmware, bootloader and kernel are recorded and a hypervisor stage would appear | the endorsement certificate chains to the TPM maker; residue: firmware below the first measurement, physical bus probing |
| confidential VM (SEV-SNP, TDX, CCA) | no: guest memory is encrypted with keys in the CPU; the hypervisor reads ciphertext | the report is signed by a key unique to the CPU, certified by the vendor, and carries the launch digest, firmware and microcode versions, and policy bits (debug, migration), so a verifier rejects debug mode and old firmware |
| enclave (Nitro, SGX) | no, for the enclave's memory | the same shape, signed by AWS or Intel |
| phone | the OS vendor, and anyone with an unlocked bootloader or root | key attestation reports verified boot, bootloader lock and patch level; a rooted or unlocked device is visible and a policy rejects it |
| browser tab | the browser and the OS | nothing about the software; only a hardware key |

Simulation is defeated by the signature, not by cleverness: a simulated CPU or
TPM cannot produce a report signed by AMD's, Intel's or a TPM maker's
certified key, so a verifier that checks the chain to a hardware root is not
fooled by a simulated universe. A verifier that checks only "a quote was
present" is.

Residues, so nobody over-claims: the chip vendor's keys and firmware;
published side-channel and physical attacks on confidential VMs (the class
BadRAM, CacheWarp and Heckler belong to; a policy that rejects old firmware and
requires the mitigations closes the known ones, never the next); physical
attacks on memory buses (encrypted memory turns these into ciphertext, which is
the reason confidential VMs exist beyond TPM-only boot); the client's own OS
vendor on phones; and metadata, visible to whoever runs the network.

## 5. Mutual attestation without a walled garden

The design that avoids lock-in treats attestation as evidence a group's
policy evaluates, not a gate a vendor imposes. Each side presents evidence
bound to its session key during the handshake; the other side's policy
decides; the roots of trust are plural.

| party | evidence available today | root of trust | vendor dependence |
|---|---|---|---|
| server on bare metal or a home box | TPM quote of measured boot, identity key TPM-resident | TPM maker | none beyond the chip |
| server in a cloud confidential VM | SEV-SNP or TDX report | AMD or Intel | the CPU vendor, not the cloud operator |
| Linux or Windows laptop client | TPM quote of the measured OS plus the reproducible open client build | TPM maker | none |
| Android phone | Key Attestation of a hardware key; app identity via the OS | Google's root | Google, and normally the Play build; F-Droid reproducible builds are the escape |
| iPhone | App Attest | Apple's service | Apple; no alternative root exists on that hardware |
| browser tab | WebAuthn device-bound key only | authenticator maker | proves a hardware key, not the software running |

A group policy then reads like a certificate policy: accept TPM-measured Linux
builds of the open client at these hashes; accept Play or F-Droid builds of the
open Android client at these hashes; accept App Attest for iOS; treat a browser
member as unattested and limit what an unattested member may do. The
open-hardware path (Linux, TPM, a reproducible build anyone can rebuild) is
first-class; Apple and Google are two roots among several; a group that
rejects them can. What cannot be escaped is physics: on an iPhone the only root
of trust is Apple's, so a member on one is Apple-attested or unattested, and
the policy makes that explicit. Symmetry falls out: a server demanding attested
clients and clients demanding an attested server are the same evaluator run in
both directions.

Verifier policy fields that make this concrete: endorsement chain to a
hardware root (refuse virtual TPMs unless the policy names a cloud's root
deliberately); for confidential VMs the chip identity, TCB versions above a
floor, debug and migration bits off, launch digest equal to the reproducible
build; for phones, verified boot and locked bootloader; a plural root list per
group.

## 6. The client role in this tree

The XMPP modules are protocol logic shared by both roles (JIDs, wire parsing,
the stream machine, SASL); the server landing of 2026-09-07 added the
server-side sequences; the client side needs the initiating half of the same
machine (stream open, SCRAM's client computation, bind request, roster and
presence requests), which is small and the same code base. In a browser a
client speaks XMPP over WebSocket (RFC 7395); on Node or native, TCP.

Cryptographic gaps for end-to-end encryption, all fillable from the pinned
HACL\* release: an AEAD (OMEMO 0.8 uses AES-128-GCM; ChaCha20-Poly1305 is the
alternative HACL\* ships), HKDF, and HPKE for MLS (HACL\* ships
`DHKEM(X25519) + HKDF-SHA256 + ChaCha20-Poly1305`, which is MLS ciphersuite
3). X25519, Ed25519, SHA-256, HMAC and PBKDF2 are already in. The owner asked
on 2026-09-07 for the AEADs and the other obvious pieces to be vendored; that
work is scheduled (not speculative) and is the one item from this record that
proceeds now.

## 7. The order, if taken up

1. **Reproducible builds** of the Lean executables and the deployment images,
   with provenance (source commit, toolchain, hashes) published and logged.
   Bit-for-bit reproducibility of the Lean-to-C-to-clang chain must be checked
   first, since attestation without a known-good hash proves nothing. Works on
   Fly today; costs nothing; everything else depends on it.
2. The layer-1 theorems for the server (payload parametricity, no fabrication,
   membership by authenticated command).
3. The server as a labelled transition system with the operator as an
   adversary who may fire any transition; executable red-team traces (ghost
   insertion, key substitution, drop and reorder, transcript fork) as
   expected-failure tests until proved.
4. An `Attestation` evidence type and verifier in Lean (TPM quote and SEV-SNP
   report parsing, EAT/COSE verification, the policy fields of §5), first on a
   home box with a firmware TPM, where the whole chain is checkable end to
   end.
5. The client half of the XMPP machine; the AEAD and HPKE primitives; MLS
   with attestation carried as a credential extension so membership and
   attestation decisions are one signed transcript; OMEMO's properties stated
   with their verification-policy dependence.
6. A confidential-VM deployment for the corporate case; GC3 or MIX clients
   treating a failed or missing attestation as a failed certificate.

## 8. Limits, restated in one place

Attestation covers boot and image, not every later state change (runtime
measurement or a confidential VM narrows that). Side channels remain. Vendor
roots are trusted. A member's own compromised device is outside all of it. The
theorems cover what the server and the protocol can do, never what a
compromised member does with what it legitimately receives. Metadata is
visible to whoever runs the network regardless of any of this.
