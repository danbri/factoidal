# Tav4 — EverParse research scratch (2026-04-25)

Reading log for `docs/designissues/everparse.md`. Sources visited, raw notes,
quotes, URLs.

## Sources visited

### Project pages

- https://project-everest.github.io/everparse/ — top-level project page
- https://project-everest.github.io/everparse/3d.html — 3D user manual
- https://project-everest.github.io/everparse/3d-lang.html — 3D language reference

### Repo

- https://github.com/project-everest/everparse — top-level
- https://raw.githubusercontent.com/project-everest/everparse/master/README.md — fetched OK
- `src/lowparse/` — listed via API; ~80 .fst files, includes `LowParse.BitFields.fst` (40KB), `LowParse.Low.*` family (validators), `LowParse.SLow.*` family (serializers), `LowParse.Low.DER.fst`, `LowParse.Low.VLData.fst` (variable-length-data), `LowParse.Repr.fst`. No README in subdir (404).
- `src/3d/` — listed via API; key files: `Ast.fst`, `Binding.fst`, `Main.fst`, `Target.fst`, `TranslateForInterpreter.fst`, `Z3TestGen.fst` (78KB, this is the 3DGen / symbolic test infrastructure), `BitFields.fst`, `RefineCStruct.fst`, `CoerceProbes.fst`, `GeneralizeProbes.fst`. No README.md (only a `README` plain file, 691 bytes — couldn't fetch directly).
- `src/cbor/`, `src/cddl/`, `src/cose/` — EverCBOR, EverCDDL, EverCOSign components. Confirms PulseParse paper claim of three integrated tools.
- `src/qd/` — QuackyDucky.
- `src/ASN1/` — there's a verified ASN.1 component too.

### Papers

- https://arxiv.org/abs/2505.17335 — PulseParse / EverCBOR / EverCDDL paper, 2025. Title: "Secure Parsing and Serializing with Separation Logic Applied to CBOR, CDDL, and COSE". Authors: Tahina Ramananandro, Gabriel Ebner, Guido Martínez, Nikhil Swamy. Distinguished Artifact Award at ACM CCS 2025.
- https://arxiv.org/abs/2404.10362 — 3DGen, 2024. Title: "3DGen: AI-Assisted Generation of Provably Correct Binary Format Parsers". Authors: Sarah Fakhoury, Markus Kuppe, Shuvendu K. Lahiri, Tahina Ramananandro, Nikhil Swamy.
- https://arxiv.org/html/2505.17335v2 — partial fetch of HTML version (truncated before related work)
- https://arxiv.org/html/2404.10362 — full evaluation details
- https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/ — PLDI 2022 paper on EverParse3D, deployed in Hyper-V network virtualization stack
- https://www.usenix.org/system/files/sec19-ramananandro_0.pdf — USENIX Security 2019 EverParse paper
- https://www.microsoft.com/en-us/research/publication/everparse/ — landing page for the 2019 paper

### Comparison points

- https://www.cs.purdue.edu/homes/bendy/Narcissus/narcissus.pdf — Narcissus paper, ICFP 2019
- https://arxiv.org/abs/1803.04870 — Narcissus arXiv version
- https://github.com/AdaCore/RecordFlux — RecordFlux repo
- https://blog.adacore.com/recordflux-from-message-specifications-to-spark-code — RecordFlux blog post
- https://www.adacore.com/papers/nvidia-using-recordflux-and-spark-to-implement-spdm-for-secure-computing — NVIDIA SPDM case study
- https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-bangert.pdf — Nail OSDI 2014 paper

### Pulse / PulseCore

- https://fstar-lang.org/papers/pulsecore.pdf — PulseCore PLDI 2025 paper, foundation that PulseParse builds on
- https://fstar-lang.org/tutorial/book/pulse/pulse.html — Pulse tutorial (in F* book)

## Key findings (raw)

### What 3D does and doesn't support

Bit-level support: yes, "Bitfields with configurable widths within UINT16/32/64 containers (MSVC packing rules)". Limitations:
- Actions cannot be associated with bitfields
- Enum values cannot be used in constraints (double-fetch prevention)
- Variable-length + alignment is fragile

Recursive support: 3D does support recursive types but PulseParse paper notes the stack-safety concern; recursion via `casetype` for tagged unions, parameterized types for re-use.

No native varint? The base types are fixed-width integers. Variable-length integer encoding (e.g. Thrift varint, Parquet's RLE/bit-packed integers) would need to be expressed via constraint+loop, or via parameterized types + actions.

### What's verified

From the 2019 USENIX paper (verbatim): "verified to be safe (no overflow, no use after free), correct (parsing is the inverse of serialization) and non-malleable (each message has a unique binary representation)."

From PLDI 2022: "memory safety, arithmetic safety, functional correctness, and even double-fetch freedom to prevent certain kinds of time-of check/time-of-use errors."

From PulseParse 2025: separation logic, full validation+parsing+serialization, recursive formats with constant-stack-space validation, non-malleability of deterministic CBOR.

### Format coverage to date

- TLS 1.0/1.1/1.2/1.3 (293 datatypes, integrated into miTLS)
- Bitcoin blocks + transactions (in-tree as `tests/bitcoin.rfc`)
- ASN.1 DER PKCS#1 RSA signatures
- QUIC
- Hyper-V network virtualization stack (~100 messages over 4 protocols, in production in Windows kernel)
- CBOR (deterministic + non-deterministic), CDDL, COSE (EverCBOR/EverCDDL/EverCOSign)
- DICE Protection Environment (secure boot)

### NOT seen

- No Parquet implementation in the EverParse repo or papers.
- No Thrift / Protocol Buffers / Avro / ORC implementation.
- No mention of columnar formats anywhere.
- The closest thing is Bitcoin (tag-length-value, somewhat structurally analogous to Thrift).

### Tool surface (what does extraction look like)

QuackyDucky: produces F* files, you then run F* + Karamel to get C.
3D: produces F*, then itself drives F* + Karamel to produce C and H files.
EverCBOR/CDDL/COSE: ship pre-extracted C and Rust. The Rust is via Karamel's Rust backend (a recent capability).

### Pulse / PulseCore positioning

Pulse is an F* DSL with concurrent separation logic. PulseCore is the underlying logic, published at PLDI 2025. PulseParse uses it because separation logic gives you (a) clean compositional reasoning about disjoint memory regions, useful for zero-copy where multiple slices of a buffer need permissions, and (b) ghost state for tracking abstract format invariants.

### 3DGen evaluation specifics

- 20 IETF protocols: UDP, TCP, IPv4, IPv6, ICMP, Ethernet, DHCP, ARP, NTP, GRE, VXLAN, DCCP, RTP, OSPF, PPP, TFTP, TPKT, NBNS, NSH, IGMPv2.
- pass@5 = 45% (9/20) against Wireshark; 100% after manual review where Wireshark was less strict than RFC.
- Uses Z3 (`Z3TestGen.fst` in repo, 78KB) to generate inputs satisfying the 3D spec, lets Wireshark label them, feeds back to LLM.
- LLM mistakes: bitfield syntax, ambiguous RFC ordering, missing constraints (TCP options, IPv4 IHL/TotalLength).

## Cross-references to factoidal code

- `formal/fstar/Parquet.Footer.fst` — 2545 lines of F*, hand-rolled Thrift compact decoder + zigzag varint + binary/list/map field walkers. Currently has `assume val parquet_zstd_decompress_hex` and `parquet_read_*_hex` for I/O. Operates entirely in hex string space (string of nibbles), which is unusual — extracted code does the binary work in hex strings rather than byte buffers.
- Today the spec proves: termination (`decreases`), Tot-functional purity. Does NOT prove: correctness against the Parquet binary spec (no formalization of "this is what TCompactProtocol means"); non-malleability; round-trip with a serializer (there is no serializer).
- Functions extracted: top-level `probe_parquet_*` API for COTTAS / parquet metadata reads.

## Plan for the doc

Sections per the prompt. Aim 800–1500 lines. Focus on:
1. Definitive component map.
2. What 3D specifically can/can't express, with examples.
3. Be precise about what PulseParse adds over LowParse.
4. Honest take on Parquet/Thrift for factoidal — likely needs a 3D pilot on a small piece (TCompactProtocol field walker) before committing.
5. Comparison table.
