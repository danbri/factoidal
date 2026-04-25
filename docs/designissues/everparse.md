# EverParse — research notes for factoidal

Status: research only, no recommendation. Compiled 2026-04-25.

Source list at the end. Reading log:
[`2026-04-25-tav4-everparse-research-scratch.md`](2026-04-25-tav4-everparse-research-scratch.md).

---

## 1. Headline — what is EverParse?

EverParse is a framework for generating verified parsers and serializers
from binary message-format descriptions, with the resulting code proven
safe, correct, and non-malleable. The 2019 USENIX Security paper states
the guarantees verbatim: "verified to be safe (no overflow, no use after
free), correct (parsing is the inverse of serialization) and
non-malleable (each message has a unique binary representation)." The
2022 PLDI paper added arithmetic safety, functional correctness, and
double-fetch freedom for the 3D-generated C path. The 2025 PulseParse
paper added separation-logic-based reasoning, full serialization, and a
class of constant-stack-space recursive formats.

The overall architecture has two halves:

1. **LowParse** — a verified library of parsing/formatting combinators
   implemented in F\* (and, in the Pulse extension, in F\*'s separation-
   logic DSL Pulse). Combinators are the small, composable building
   blocks: a parser for `UINT8`, a parser for "two parsers in sequence",
   a parser for "n-byte length prefix followed by that many bytes", etc.
2. **Front-end DSLs** that compile message-format descriptions down to
   uses of LowParse combinators, then through F\* to verified low-level
   F\* (Low\*) and finally to C via the Karamel backend (or Rust via
   Karamel's newer Rust backend).

The official self-description from the project page:

> "EverParse is a framework for generating verified secure parsers and
> formatters from domain-specific format specification languages. ...
> LowParse, a verified library of parsing and formatting combinators
> programmed and verified in F\* and Pulse."

Output targets:

- **C** (primary target; via Karamel)
- **Rust** (newer; via Karamel's Rust backend, used by EverCBOR-rust
  and EverCOSign-rust)
- **F\*** as an intermediate language; LowParse itself can be used
  directly from F\* without going through C.

There is no OCaml or JavaScript extraction story shipped from EverParse
specifically — those would need a separate Karamel-vs-`fstar.exe
--codegen` decision.

---

## 2. Component map

| Component | Role | Lives in | API style |
|-----------|------|----------|-----------|
| **LowParse** | verified combinator library | `src/lowparse/` (~80 .fst files) | F\* parser/serializer combinators; bit-level + byte-level |
| **PulseParse** | LowParse rewritten in Pulse / separation logic | parts of `src/cbor/pulse/` and library code | Pulse DSL; full parser+serializer with zero-copy |
| **3D** | byte-level dependent-type DSL → verified C parser | `src/3d/` | C-like syntax (`struct`, `casetype`, bitfields, dependent fields) |
| **QuackyDucky** | RFC-style format DSL → F\* | `src/qd/` | "RFC-style" message tables; older; produces F\*, you must finish the build manually |
| **EverCBOR** | shipped verified CBOR library (C + Rust) | `src/cbor/` | end-user library, two flavours (det / nondet) |
| **EverCDDL** | CDDL → verified parser/serializer | `src/cddl/` | front-end that emits C or Rust via PulseParse |
| **EverCOSign** | shipped verified COSE library | `src/cose/` | end-user library, signs and verifies COSE objects |
| **EverParse-ASN1** | verified ASN.1 / DER work | `src/ASN1/`, `LowParse.Low.DER.fst` | combinator-level, used in the original miTLS work |
| **3DGen** | LLM-driven RFC-to-3D generator | `src/3d/Z3TestGen.fst` (78KB) + research artefact | not a shipped tool; symbolic-test-driven repair loop |
| **Karamel** | F\* → C / Rust extractor (separate project) | external (`FStarLang/karamel`) | linked in via the EverParse build |

### LowParse — the core library

`src/lowparse/` is dense; some highlights from the file list:

- `LowParse.BitFields.fst` (40KB) and `.fsti` (13KB) — bit-level parsing
- `LowParse.Endianness.fst` (8KB) — explicit big-endian / little-endian
- `LowParse.Low.Base.fst` (64KB) — the validator core
- `LowParse.Low.Sum.fst` (76KB) — discriminated unions
- `LowParse.Low.VLData.fst` (28KB), `LowParse.Low.VLGen.fst` (39KB) —
  variable-length data and length-prefixed encodings
- `LowParse.Low.Writers.fst` (38KB) — serializer side
- `LowParse.Low.DER.fst` (12KB) — ASN.1 DER lengths
- `LowParse.SLow.*` family — "slow" reference implementations used as
  specs; the `Low.*` family is the extraction-ready high-performance one
- `LowParse.Repr.fsti` (31KB) — abstract data representation,
  the basis of zero-copy reads

LowParse's design is "specs as types": a parser is typed by what it
produces, and the combinators preserve key theorems (parse-after-serialize
is identity, the parser doesn't read past the buffer, etc.). The `SLow`
vs `Low` split is an EverParse idiom — `SLow` is for the specification,
`Low` is the implementation that extracts to performant C and is proven
to refine `SLow`.

The combinator inventory, by file-name prefix, gives a sense of the
expressivity:

- **Primitive parsers** — `Int.fst` (raw integer parsers),
  `BoundedInt.fst` (range-restricted integers), `ConstInt32.fst`
  (constants in headers), `Endianness.fst` (BE/LE handling).
- **Composition** — `Combinators.fst` (sequence, monadic bind, map),
  `IfThenElse.fst` (data-dependent branches), `Sum.fst` (tagged
  unions), `Enum.fst` (closed enumerations).
- **Collections** — `Array.fst` (fixed-size arrays), `List.fst`
  (homogeneous variable-length lists), `ListUpTo.fst` (lists with
  termination predicate), `VCList.fst` (validated collected lists).
- **Length-prefixed data** — `FLData.fst` (fixed-length data),
  `VLData.fst` (variable-length data with length prefix),
  `VLGen.fst` (generic variable-length).
- **Sub-byte / bit-level** — `BitSum.fst` (split a containing word
  into bit-typed sub-fields), `BitFields.fst` and
  `Endianness.BitFields.fst` (the heavy machinery for proven-correct
  bit packing).
- **Specialised number formats** — `BCVLI.fst` (a particular
  variable-length integer encoding), `DER.fst` (ASN.1 DER lengths),
  `DepLen.fst` (data-dependent length).
- **Output / serialization** — `Writers.fst` and
  `Writers.Instances.fst`, plus the `SLow.*` companion files.
- **Representation** — `Repr.fsti` (31KB), the type-level account of
  what an in-memory parsed object looks like and how its byte-level
  representation is tracked.

This is roughly the same surface as Hammer, Kaitai Struct, or
Construct (Python) — but every combinator carries its proof of
correctness against the spec it implements. The `Repr` module in
particular is what lets PulseParse later layer separation-logic
permissions on top.

### 3D — the byte-level DSL

3D ("Dependent Data Descriptions") is the front-end most analogous to
what factoidal would want for Parquet / Thrift work. It's a C-like syntax
with type-level constraints:

```
typedef struct _ETHERNET_HEADER {
    UINT8 destination_mac[6];
    UINT8 source_mac[6];
    UINT16BE ether_type;
} ETHERNET_HEADER;
```

The supported feature set (from the 3D language reference):

- Fixed-width integers `UINT8/16/32/64`, with explicit big-endian
  variants `UINT16BE/32BE/64BE/UINT8BE`. Little-endian default.
- **Bitfields** within UINT8/16/32/64 containers (MSVC packing rules).
- Nested structs.
- Tagged unions / discriminated unions via `casetype`:
  ```
  casetype NAME(PARAMS) {
    switch(tag_field) {
      case value: Type field_name;
      default:    Type default_name;
    }
  }
  ```
- Fixed-size arrays.
- **Variable-size arrays** sized in *bytes*, not element counts:
  `T f[:byte-size n]`.
- Enumerations.
- Parameterized data types (templates).
- Dependent fields: a later field's value or array length can reference
  earlier fields; constraints on field values use a small expression
  language (`+`, `-`, `*`, `/`, `<=`, `&&`, `||`, etc.).
- Pointer / probe support: `pointer?` plus `extern probe ProbeAndCopy(...)`
  callbacks that the generated validator calls before dereferencing.
- Alignment via explicit `aligned` attribute (no implicit padding).
- Modular cross-module type references.
- Imperative actions on success / on error.

Limitations called out explicitly by the 3D manual:

- Enum-typed fields cannot be used in subsequent constraints (because
  the double-fetch prevention machinery would have to re-read them).
- No actions on bitfields.
- Variable-length-data + alignment combined behaves differently from
  C compiler's flexible-array-member layout; care needed.
- Specialization (e.g. 64-bit→32-bit pointer down-conversion) cannot
  depend on constrained or enum-typed fields, and the specialization
  proof covers soundness but not completeness.

What 3D does **not** appear to support natively:

- Variable-length integer encodings (varint, ULEB128, zigzag, Thrift's
  varint). The base integer types are fixed-width. To express varint
  you would presumably reach for a parameterized type with a per-byte
  loop expressed via constraint, or step outside 3D into LowParse.
  This is a real gap for Parquet / Thrift work — see §5.
- True element-counted (rather than byte-counted) variable arrays
  whose count is a varint. Element-count works with fixed integer
  size headers; byte-count is the more general 3D primitive.
- Recursive types in 3D itself: 3D's compilation model is finite-depth.
  PulseParse adds a class of recursive formats with constant-stack
  validation, but those are written against the LowParse/Pulse API
  directly, not via 3D's syntax.

### QuackyDucky — the historical front-end

QuackyDucky ("qd") is the older RFC-style DSL. Its native input style
mirrors the message-table grammar found in IETF RFCs (TLS RFC 8446
in particular). Its claim to fame is the full TLS 1.3 implementation
in miTLS — 293 datatypes covering TLS 1.0–1.3.

QD accepts data formats in a style common to many RFCs and produces F\*
files (not C directly). You then run F\* and Karamel by hand. This makes
it less push-button than 3D but more direct for protocol designers
who already think in terms of `T msg = struct { ... };` definitions.

The repo's example files:
- TLS 1.3 — referenced from the miTLS project
- Bitcoin — `tests/bitcoin.rfc` lives in the repo

### How does 3D actually compile?

The `src/3d/` source layout reveals the pipeline:

- `Ast.fst` (60KB) — surface syntax AST.
- `Desugar.fst` (23KB) — surface→core lowering.
- `Binding.fst` (96KB) — name resolution + type checking.
- `Simplify.fst` — peephole simplifications.
- `BitFields.fst` — bit-level handling.
- `RefineCStruct.fst`, `InlineSingletonRecords.fst` — layout decisions
  to control the shape of generated C structs.
- `TranslateForInterpreter.fst` (53KB) — translate to a verified
  interpreter representation.
- `InterpreterTarget.fst` (39KB) — the target representation.
- `Target.fst` (53KB), `Generate32BitTypes.fst` — the C output backend.
- `Specialize.fst` — pointer-size specialization.
- `CoerceProbes.fst`, `GeneralizeProbes.fst` — the pointer-probe
  machinery.
- `Z3TestGen.fst` (78KB) — the symbolic test generation that
  3DGen builds on.
- `GenMakefile.fst` — emit a Makefile for the generated C/H files.
- `Main.fst` — driver.

The "verified interpreter representation" is the key idea — instead of
generating bespoke C for every spec, 3D compiles the spec down to a
data structure interpreted by a small, separately-verified interpreter.
This keeps the F\* trusted base small and means the verification effort
scales sublinearly in the number of formats you handle.

### PulseParse — the 2025 evolution

The PulseParse paper:

> "Towards this end, we present PulseParse, a library of verified parser
> and serializer combinators for non-malleable binary formats.
> Specifications and proofs in PulseParse are in separation logic,
> offering a more abstract and compositional interface, with full support
> for data validation, parsing, and serialization. PulseParse also
> supports a class of recursive formats — with a focus on security and
> handling adversarial inputs, we show how to parse such formats with
> only a constant amount of stack space."

Key technical contributions over the original LowParse:

- **Separation-logic specs.** Permissions over byte ranges are tracked
  in PulseCore (the impredicative concurrent separation logic underlying
  Pulse, PLDI 2025). This makes zero-copy more tractable: you can
  carve up a buffer's permission, give a sub-permission to a downstream
  parser, and recover the whole permission afterwards using the magic-
  wand connective `-*`.
- **Zero-copy by construction.** A "zero-copy reader is a Pulse function
  ... returning the value of the integer and a pointer to the byte
  array, which it will thus not copy." The verified callers can hand
  back the sub-permission to recover ownership of the original buffer
  — which is the critical move for being able to allocate the parse
  tree inside the input rather than alongside it. Concretely: the
  parse function for an array `[a]` returns `(value, ptr_into_a)`
  along with a separation-logic `wand` that, when applied with the
  permission to `ptr_into_a`, recovers the permission to the
  original buffer. This is the formal-methods analogue of "lifetime
  re-borrow" in Rust.
- **Recursive formats with constant stack.** Theorem 2.1 in the paper
  establishes a class: header-then-payload formats where the header
  alone determines child count, with constant-stack header validation,
  validate in constant total stack. The implementation maintains a
  counter (initial 1, decrement when validating, increment by expected
  child count on completion) and uses while-loops bounded by the
  function-definition count instead of recursion. This matters because
  adversarial inputs with deep nesting can blow the stack on naive
  recursive-descent parsers.
- **Full serialization.** The original LowParse had serializers, but
  PulseParse paper-frames the serializer→parser round-trip more
  cleanly under separation logic.
- **First formalization of CBOR + CDDL.** The deterministic fragment
  of CBOR is proven non-malleable. CDDL well-formedness conditions are
  identified that ensure the schemas yield unambiguous, non-malleable
  formats; EverCDDL checks them and emits verified parsers.

Real artefacts shipped from the PulseParse line:

- EverCBOR (C + Rust), two flavours (deterministic, non-deterministic).
- EverCDDL — CDDL → C/Rust parsers and serializers.
- EverCOSign — COSE signing (sign1 / verify1).
- DICE Protection Environment (secure boot protocol) was generated
  from CDDL in the evaluation.

### 3DGen — LLM lifting RFCs to 3D

3DGen (arXiv:2404.10362) is an LLM-driven workflow that takes an
informal RFC and example inputs and produces a 3D specification,
which then compiles via the regular EverParse path to verified C.

Mechanism:

1. LLM agent drafts a 3D spec from RFC text.
2. **3dTestGen** (the `Z3TestGen.fst` module, 78KB) symbolically
   encodes the candidate 3D spec into SMT-LIB and asks Z3 to find
   inputs that satisfy it.
3. An external oracle (Wireshark in the published evaluation) labels
   the generated inputs as accept/reject.
4. Discrepancies feed back to the LLM as repair targets.
5. Iterate until the spec passes the accumulated test suite.

Evaluation: 20 IETF protocols (UDP, TCP, IPv4, IPv6, ICMP, Ethernet,
DHCP, ARP, NTP, GRE, VXLAN, DCCP, RTP, OSPF, PPP, TFTP, TPKT, NBNS,
NSH, IGMPv2). pass@5 = 45% against Wireshark labels; manual review
brought it to 100% (with the caveat that 11 cases involved Wireshark
being more permissive than the RFC, so 3DGen was actually right and
Wireshark was wrong). Authors are explicit that "3dGen should not be
used to blindly match the behavior of a legacy tool" and that
specifications are "only as good as the tests on which it is evaluated".

Honest failure modes documented:
- LLMs struggle with 3D's bitfield syntax.
- LLMs misorder fields when RFC English is ambiguous (VXLAN was
  called out specifically).
- LLMs miss constraints that exist only in RFC text and aren't
  exercised by the test set (TCP options, IPv4 IHL/TotalLength).

This is a research artefact, not a shipped tool. The `Z3TestGen.fst`
infrastructure is in the repo; the LLM-agent harness is described in
the paper but not packaged for general use.

### Karamel — the C/Rust extractor

Karamel (formerly KreMLin) is the F\*-to-C translator used by the
whole Project Everest. It is a separate project
(`FStarLang/karamel`). For EverParse:

- F\* code in the **Low\*** subset (ML-style, but with monomorphic
  buffer-typed primitives) is fed to Karamel.
- Karamel produces idiomatic C and headers; the Pulse/PulseCore
  pipeline includes a Rust backend now too.
- Pure F\* code (no buffers, no mutable state) extracts to OCaml
  via `fstar.exe --codegen OCaml` (this is the path factoidal uses
  today).

In a hypothetical factoidal-on-EverParse story, one would:
1. Write the binary format in 3D (or in Pulse/LowParse directly).
2. Have EverParse drive F\* + Karamel to produce C.
3. Either bind to that C from OCaml/JS (FFI), or ship the C
   directly as the parser, or use Karamel's Rust output and bind
   to that.

Today factoidal's pipeline is `.fst → fstar.exe --codegen OCaml →
.ml → ocamlfind / js_of_ocaml`. Adopting EverParse would introduce
a second pipeline alongside the OCaml one, not replace it.

---

## 3. What is verified, what isn't

### What is verified

The five named theorem classes across EverParse generations:

1. **Memory safety** — no out-of-bounds reads, no use-after-free.
   Established for C output via Low\* + Karamel; for Pulse via the
   separation-logic permissions.
2. **Arithmetic safety** — additions and multiplications of length /
   offset values don't overflow the integer type they're stored in.
   Made explicit at the PLDI 2022 stage.
3. **Functional correctness** — the parser accepts a byte string iff
   the format spec accepts it, and the parsed value matches the spec.
4. **Non-malleability** (a.k.a. unique binary representation) — every
   value of the abstract type has at most one byte-string representation
   that the parser will accept. This is the security-critical property
   for signed messages. The PulseParse paper proves this for the
   deterministic CBOR fragment.
5. **Round-trip / parser–serializer inverse** — `parse ∘ serialize =
   id` and (under non-malleability) `serialize ∘ parse = id` on
   accepted inputs.
6. **Double-fetch freedom** (3D-specific) — the generated validator
   reads each input byte at most once, so a TOCTOU adversary
   modifying memory between two fetches cannot cause inconsistent
   parses. Important for kernel-mode validators where the input
   buffer may be in shared user/kernel memory.

### What is assumed / not verified

- **Allocator soundness.** Where the parser does allocate (most of the
  C output is zero-copy / on-stack, but some paths may need heap),
  the underlying `malloc`/`free` is taken on faith.
- **Cryptographic correctness** of any HMAC, signatures etc. — those
  are handled by HACL\* / EverCrypt, separate Project Everest pieces.
- **Side-channel resistance.** No claims about constant-time behaviour
  unless inherited from underlying crypto.
- **Compiler correctness.** F\* → C goes through Karamel (verified to
  preserve types but not the C compiler's translation to machine code);
  the C is then handed to a regular C compiler. This is the standard
  caveat: the proven artefact is the F\* code, not the binary.
- **Spec faithfulness to the standard.** Verifying a parser against a
  3D spec doesn't prove the 3D spec faithfully encodes (say) RFC 8446.
  3DGen is precisely the attempt to systematise that step, but it's
  oracle-based, not formal.
- **Floating-point semantics.** EverCBOR explicitly does not yet
  support float values; CBOR's float NaN-equivalence semantics for
  map keys aren't standardised yet.
- **Resource bounds.** Stack-space bounds are proven for the
  PulseParse recursive-format class (Theorem 2.1) but not in general
  for arbitrary 3D specs.

---

## 4. Format coverage to date

What has been parsed via EverParse, by component:

### Via QuackyDucky (RFC-style)
- **TLS 1.0 / 1.1 / 1.2 / 1.3** with extensions, 293 datatypes.
  Integrated into miTLS (the F\* TLS implementation). This is the
  flagship.
- **Bitcoin** block headers and transactions (`tests/bitcoin.rfc`).
- **ASN.1 DER** payload of PKCS#1 RSA signatures.
- **QUIC** message processing.

### Via 3D
- **Hyper-V network virtualization stack**, ~100 messages over four
  protocols, deployed in the Windows kernel since 2022 (PLDI paper).
- **DPE (DICE Protection Environment)** — secure boot.
- The 20 RFC protocols evaluated via 3DGen (UDP/TCP/IP family + a
  range of network protocols).

### Via PulseParse / EverCDDL
- **CBOR** (deterministic + non-deterministic).
- **CDDL** as a meta-format.
- **COSE** (sign1, verify1; encryption in progress).
- **DICE** secure boot protocol.

### NOT covered
None of the following appear in EverParse's published or in-tree work:
- **Apache Parquet** metadata or value pages.
- **Apache Thrift** TCompactProtocol or TBinaryProtocol.
- **Apache Avro** schema or container files.
- **Apache ORC**.
- **Protocol Buffers** wire format.
- **MessagePack** beyond the structurally-similar CBOR.
- **HDT** (the binary RDF format factoidal explores in `ballyhoo`).

In particular: the parquet-format spec is itself defined as a Thrift
IDL (`parquet.thrift`), and Thrift has its own published
TCompactProtocol binary spec. Neither has been the subject of an
EverParse case study to date.

---

## 5. Relevance to factoidal

This is the section that motivated the research, so it gets the most
detailed treatment.

### Today's situation in factoidal

`formal/fstar/Parquet.Footer.fst` is **2545 lines of F\*** that hand-rolls:

- Parquet's footer location convention (last 8 bytes: `<le_u32 footer_len><PAR1>`).
- Apache Thrift TCompactProtocol decoding: zigzag varints, field-id
  delta encoding, the type-tag table (1=bool-true, 2=bool-false, 3=byte,
  4=i16, 5=i32, 6=i64, 8=binary, 9=list, 10=set, 11=map, 12=struct).
- A field-walker: `nth_field_hex hex target_id pos prev_id fuel`.
- A list/set element walker: `nth_compact_list_element_start_hex`.
- Top-level `probe_*` functions that pull single fields out of the
  footer or out of a row-group's column metadata.

The work is genuinely careful F\* — `Tot` totality, `decreases` clauses,
fuel parameters to make recursion structurally terminating. But the
verified surface is "this F\* function terminates and returns an option"
not "this function correctly implements TCompactProtocol §X.Y as
specified by Apache". The Parquet binary spec itself is not formalised,
and there is no serializer to round-trip against.

There are also three `assume val`s for I/O and zstd:

```
assume val parquet_read_tail_hex      : string -> nat -> option string
assume val parquet_read_range_hex     : string -> nat -> nat -> option string
assume val parquet_zstd_decompress_hex: string -> nat -> option string
```

(Wired up in patch 69_runner_io_glue.sh and elsewhere — these are
acknowledged unverified gaps per CLAUDE.md rule #3.)

A separate piece of code, the column-page decoders (DELTA_LENGTH_BYTE_ARRAY,
RLE_DICTIONARY) extends this for column values, not just metadata.

### Quantifying what's "verified" today vs. what EverParse offers

Today's `Parquet.Footer.fst` proves:

- **Termination** — every recursive function has a `decreases` clause
  (mostly `fuel` parameters), so F\* admits them as `Tot` (totality).
- **No partiality** — return type is always `option T`; missing data
  surfaces as `None`, not as a runtime error.
- **Type-level structure** — the abstract type `parquet_footer`,
  `compact_field`, `compact_list_info` are populated through
  controlled constructor sites.
- **F\* erasure** — proofs and ghost code are erased on extraction,
  the .ml output is non-redundant.

It does **not** prove:

- That `parse_parquet_footer_tail_hex` accepts exactly the byte
  strings that valid Parquet footers serialize to.
- That `decode_varint_value_hex` correctly implements the Thrift
  zigzag varint decoding for arbitrary byte lengths.
- That the field-id-delta tracking in `nth_field_hex` correctly
  implements the TCompactProtocol "delta from previous field id"
  semantics in the presence of explicit field-id resets.
- That the implementation is non-malleable — different byte strings
  could be accepted as encoding the same parquet metadata, which is
  fine for read-only consumption but would break any
  signature-on-Parquet-footer scheme.
- That the implementation has any specific stack/space behaviour
  on adversarial inputs; the `fuel` parameter is the engineering
  countermeasure.

EverParse — both 3D and PulseParse — offers all of those properties as
end-to-end theorems. So the **verified surface** is genuinely larger
under EverParse, even allowing for the build-system cost.

### Could 3D have given us this for free?

Theoretical answer: yes, for the structure-walker portion. The
Parquet footer is a Thrift compact-encoded `FileMetaData` struct. A
`FileMetaData.3d` file would express:

```
casetype _ParquetFooter(...) {
  switch (...) { case ...: ThriftStruct(ROOT_TYPE_FILE_METADATA); }
}
```

with `ThriftStruct` itself a 3D type. EverParse would emit a verified
C parser; we would link to it from OCaml via FFI, or use Karamel's
Rust output and link to that.

Practical answer: this would be a **multi-week port** today, with a
real risk of finding a 3D expressivity gap mid-flight. Specific
hazards:

1. **TCompactProtocol uses varints everywhere.** Field-id deltas are
   varints; lengths are varints; values are zigzag varints. 3D's
   primitives are fixed-width integers. A varint would be expressed
   either:
   - as a parameterized "read a stream of bytes until the high bit
     clears" which 3D's `byte-size` arrays support indirectly but
     awkwardly (you don't know the byte size until you've read), or
   - by stepping out of 3D and into LowParse / Pulse directly.
   The PulseParse paper's CBOR work has solved similar (CBOR has its
   own variable-size length encoding via the "additional info" field),
   but that's coded against PulseParse, not via the 3D front-end.

2. **Thrift's field-id-delta-or-explicit-id encoding.** A short field
   header is one byte: high nibble is delta from previous field id,
   low nibble is type. If high nibble is zero, an explicit varint
   field id follows. This is dependent-field-on-prior-field-bits,
   which 3D handles structurally well, **except** that bitfields can't
   be used in constraints due to the double-fetch limitation. Workable
   but ugly.

3. **Recursion.** `FileMetaData` contains lists of `RowGroup`, each
   `RowGroup` contains a list of `ColumnChunk`, each `ColumnChunk`
   contains a `ColumnMetaData` containing `Statistics` and so on,
   roughly four levels. PulseParse's constant-stack-space recursive
   format support (Theorem 2.1) covers this kind of header-then-children
   pattern, but is in the library, not in 3D.

4. **`assume val parquet_zstd_decompress_hex`.** EverParse has nothing
   to say about zstd. That gap stays. (One could imagine plumbing a
   verified-zstd from Microsoft Research's zstd verification work, but
   that's a separate dependency entirely.)

5. **Column-page integer encodings.** DELTA_LENGTH_BYTE_ARRAY and
   RLE_DICTIONARY are bit-packed. 3D supports bitfields *inside* a
   container word (UINT8/16/32/64). Parquet RLE/bit-packing is more
   like "stream of N-bit values, N may not divide 8, the stream
   continues until a count is reached". This is closer to the kind
   of arithmetic-bit-pump LowParse has in `LowParse.BitFields.fst`
   than what 3D exposes. So this part is probably best done by
   dropping to LowParse / Pulse, not via 3D.

   Concretely, RLE_DICTIONARY page header has:
   - varint header (run-length or bit-packed-run header)
   - if RLE: a varint count, then a single value
   - if bit-packed: an N-byte sequence containing 8\*M values
     bit-packed at width W
   The W (bit-width) is read from the page header byte; the count
   is from the varint; alignment doesn't survive page boundaries.
   This is well-typed Pulse/LowParse code, but it isn't a 3D spec.

6. **String-of-hex encoding.** Today's code lives in hex-nibble strings
   end-to-end. EverParse expects byte buffers (`UINT8 *` in C, `array
   uint8_t` in Pulse). The current string-of-hex idiom is a useful
   workaround for js_of_ocaml's missing native bytes support — but
   migrating to EverParse means dropping that and binding Karamel's
   buffer C ABI from JavaScript directly (or via a small wrapper).
   Workable, but it's a non-trivial deployment story for the
   in-browser demo.

So: 3D could plausibly do the **footer structure walk** with some
work; PulseParse could probably do the **whole thing** including page
decoders, but as a bespoke library, not via a 3D-style declarative
front-end. The deliverable would be a verified parser **and** a
verified serializer, plus C/WASM extraction quality wins via Karamel.

### Could PulseParse help with COTTAS write-side (issue #100 Phase 5)?

If factoidal ever writes parquet files (issue #100 Phase 5 candidate
per the cottas-parquet-wiring-plan doc), PulseParse's serializer
support and round-trip theorems are directly relevant. The
parser-serializer inverse property is what you want for "we wrote
metadata X, we can re-read it and get X back" — which is something
factoidal's current code can't claim for itself (no serializer
exists). For a write path that signs the parquet footer (or a
Parquet-Lake / Iceberg-style scenario), non-malleability matters.

### 3DGen and the LLM angle

Factoidal's user is doing AI-assisted F\* development. 3DGen is
adjacent: it's an LLM-agent harness with a symbolic test loop,
specifically tuned for binary-format spec-writing. Useful prior art
for thinking about how factoidal might use LLMs to lift the SPARQL
1.1 grammar (already tried in this codebase) or the SRX/SRJ result
formats. Concretely:

- Symbolic-test-driven feedback (use Z3 to generate inputs from a
  candidate 3D spec, label with an oracle, feed back) is something
  factoidal could mimic for SPARQL grammar work, modulo the lack
  of an obvious symbolic encoding for grammars.
- The 3DGen evaluation honestly distinguishes "spec is correct, oracle
  is permissive" from "spec is wrong" — that habit is exactly the
  honesty-discipline factoidal's CLAUDE.md asks for (rules #2, #3).

### Honest assessment — would adopting EverParse shrink or grow
factoidal's verified surface?

**Both**, in different time horizons:

- **Short term, it grows.** Adopting EverParse adds Karamel as a
  build dependency (heavy), introduces a second extraction pipeline,
  and forces a port of the parquet code from idiomatic
  string-of-hex-nibbles F\* to LowParse-or-Pulse-style buffer-typed
  F\*. The build matrix grows. The current minimal-glue pattern (an
  `assume val`, a sed patch) doesn't apply cleanly because EverParse
  expects buffer-typed inputs all the way down.

- **Long term, it shrinks.** A verified parser+serializer pair for
  Parquet's footer would replace ~2500 lines of carefully-fenced F\*
  with a 3D / Pulse spec that's much smaller and proves more. The
  column-page decoders (DLBA, RLE_DICT) would still need bespoke
  Pulse code, but it'd be Pulse code with separation-logic permissions
  in place — better than today's option-typed string traversals.

- **Quality wins.** C and Rust extraction targets become available,
  which today factoidal lacks. The work in
  `docs/designissues/2026-04-24-c-extraction-plan.md` — about getting
  C/WASM out of factoidal F\* — is ostensibly easier with Karamel
  than with bespoke `--codegen OCaml` post-processing.

- **Risk.** EverParse is a research-grade codebase with a
  high-cardinality build chain (F\*, Karamel, Pulse, opam stack).
  Last published artefact of widely-deployed binary parsers via 3D
  is the Hyper-V case study from 2022; outside Microsoft, public
  3D usage is thin. Adopting it puts factoidal one step further
  from upstream stability.

The sane factoidal move would be a **scoped pilot**, not a full
adoption — see §6.

---

## 6. Concrete next-steps factoidal could take

- **Smallest possible 3D pilot.** Pick the Thrift compact field walker
  (~150 lines of `Parquet.Footer.fst`: `nth_field_hex` and
  `decode_compact_list_info_hex`). Try expressing it as a 3D spec.
  See whether 3D's varint story is workable; see how the hex-vs-byte
  buffer mismatch shakes out. Time-box one week. Outcome: a written-up
  report, not necessarily merged code.
- **Survey factoidal's `assume val`s for EverParse-blessed alternatives.**
  Most are I/O glue (`parquet_read_*`, file read, `regex_match`, hash,
  uuid, base IRI resolution) which EverParse doesn't address.
  `parquet_zstd_decompress_hex` is the one that has a possible
  EverParse-adjacent answer — Microsoft Research has published verified
  zstd work, though not under EverParse explicitly. Worth one hour of
  search.
- **Consider 3DGen-style LLM-RFC-to-spec for clear-spec text formats.**
  N-Triples (RFC 9482), N-Quads (RFC 9482), and SPARQL Result XML
  (W3C Rec) all have crisp specs and structured outputs — closer to
  what 3DGen targets than free-form RDF. The win wouldn't be "verified
  C parser" (factoidal already has these in F\*), but rather
  "AI-assisted spec lifting" as a prior-art reference point if
  factoidal wants to systematise its own spec-from-RFC work.
- **Read the EverCDDL implementation in detail** before any port.
  CDDL → verified parser is the closest analogue of what a Thrift IDL
  → verified parser would look like. The PulseParse paper claims
  "table extensibility patterns such as `(? 18 => int, * int => any)`"
  which is structurally similar to Thrift's optional-field model.
  Reading `src/cddl/` would reveal whether PulseParse-flavoured
  extensibility lines up with Thrift compact's "skip unknown fields"
  semantics.

None of these are commitments to adopt EverParse. They are
investigations that would let a future decision be informed.

---

## 7. Comparison with related verified-parser work

| Tool | Platform | Verification framework | Output target | DSL | Real-world use | Last activity |
|------|----------|------------------------|---------------|-----|----------------|---------------|
| **EverParse / 3D** | F\* + Pulse + Karamel | F\* + Z3 SMT, Pulse separation logic | C, Rust, F\* | 3D (C-like, byte+bit), QuackyDucky (RFC-table), CDDL | TLS 1.0–1.3 (miTLS, 293 datatypes), QUIC, Bitcoin, ASN.1 DER, Hyper-V kernel parsers (~100 messages, prod since 2022), DICE secure boot, COSE, CBOR | active 2026 (CCS 2025 award, PLDI 2025 PulseCore) |
| **Narcissus** | Coq | Coq tactics, correct-by-construction | OCaml (extracted) | Coq combinators (no separate DSL) | Internet protocol stack in MirageOS unikernel; packet formats (TCP/UDP/IP/ICMP/ARP/Ethernet/DNS) | research-grade, last paper 2019 ICFP, repo updates sporadic |
| **RecordFlux** | SPARK / Ada | GNATprove (SPARK Pro) | SPARK Ada source | RecordFlux DSL (.rflx files) — message specs + state machines | NVIDIA SPDM (Security Protocol and Data Model) implementation; SPDM 1.2; commercial SPARK customers via AdaCore | active 2026, AdaCore commercial product, regular GitHub releases |
| **Nail** | C (with custom C codegen) | Bidirectional grammar guarantees (semantic bijection); not a proof system per se | C source | Nail grammar | DNS server (300 LoC), unzip (220 LoC); demonstrated outperforming BIND on auth workload | dormant — last published OSDI 2014; the work continued under different banners (LangSec community) |
| **Vest** | F\* + Karamel | F\* + Z3, similar to LowParse but TLS-record-layer-focused | C | combinators | TLS 1.3 record layer, integrated into miTLS | published 2018, subsumed by EverParse |

A few cross-cutting observations:

- **EverParse is the most-deployed.** The Windows kernel use is a
  unique data point: production-grade, externally adversarial
  inputs, kernel privilege boundary. Narcissus has MirageOS but
  unikernel deployment is academic. RecordFlux has commercial
  customers (NVIDIA) but on a single protocol family (SPDM).
  Nail has the smallest deployment surface today.
- **EverParse and Narcissus are the only ones that go all the way to
  formal verification of memory safety.** RecordFlux's SPARK Pro
  proves run-time-error freedom, which is closer in spirit to
  EverParse's memory-safety guarantee, but does not currently prove
  full functional correctness against the spec by default. Nail
  enforces grammar-level invariants at compile time but does not
  produce a proof in a recognised proof assistant.
- **DSL ergonomics differ.** 3D is the most C-programmer-friendly.
  RecordFlux's DSL is the most domain-specific (built around
  message types + state machines). Narcissus has no separate DSL
  (everything is Coq). Nail's grammar is intermediate.
- **Serializer support.** EverParse, Narcissus, and Nail all have
  bidirectional support (parser + serializer / generator). RecordFlux
  has it for messages but the state-machine side is parser-focused.
- **Recursion + adversarial-input resistance.** PulseParse's
  constant-stack recursive-format result is unique to EverParse.
  Narcissus does support recursion but doesn't make stack-space
  guarantees about it. RecordFlux generally does not encourage
  unbounded recursion in messages. Nail has stream transforms but
  not formal stack-bound proofs.
- **Activity level.** EverParse and RecordFlux are the two clearly
  alive and well in 2026. Narcissus is in maintenance. Nail is
  effectively dormant.

For factoidal specifically:
- EverParse's F\* lineage is the **only** one of the four where the
  underlying language matches what factoidal already uses.
  Narcissus would mean adopting Coq. RecordFlux would mean adopting
  SPARK/Ada. Nail would mean adopting an unmaintained tool.
- This makes EverParse the **only** practically considerable option
  for factoidal — but it's still a multi-week investment, and the
  "you wrote it in F\*, but you wrote it in vanilla F\*, not LowParse"
  gap is real.

---

## 8. Sources

### EverParse — official

- Project page: https://project-everest.github.io/everparse/
- 3D user manual: https://project-everest.github.io/everparse/3d.html
- 3D language reference: https://project-everest.github.io/everparse/3d-lang.html
- GitHub: https://github.com/project-everest/everparse
- Top-level README (raw): https://raw.githubusercontent.com/project-everest/everparse/master/README.md
- Microsoft Research blog post:
  https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/
- Tahina Ramananandro's project page:
  http://www.normalesup.org/~ramanana/research/everparse/

### Papers

- USENIX Security 2019 — "EverParse: Verified Secure Zero-Copy Parsers
  for Authenticated Message Formats" — Ramananandro,
  Delignat-Lavaud, Fournet, Swamy, Chajed, Kobeissi, Protzenko.
  https://www.usenix.org/system/files/sec19-ramananandro_0.pdf
- PLDI 2022 — "Hardening Attack Surfaces with Formally Proven Binary
  Format Parsers" — Swamy, Ramananandro, Rastogi, Spiridonova, Ni,
  Malloy, Vazquez, Tang, Cardona, Gupta.
  https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/
- 3DGen 2024 — "3DGen: AI-Assisted Generation of Provably Correct
  Binary Format Parsers" — Fakhoury, Kuppe, Lahiri, Ramananandro,
  Swamy. https://arxiv.org/abs/2404.10362
- PulseParse 2025 — "Secure Parsing and Serializing with Separation
  Logic Applied to CBOR, CDDL, and COSE" — Ramananandro, Ebner,
  Martínez, Swamy. https://arxiv.org/abs/2505.17335
- PulseCore PLDI 2025 — "PulseCore: An Impredicative Concurrent
  Separation Logic for Dependently Typed Programs". DOI:
  https://dl.acm.org/doi/10.1145/3729311

### Related work (for the comparison table)

- Narcissus, ICFP 2019 — Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala.
  https://www.cs.purdue.edu/homes/bendy/Narcissus/narcissus.pdf
  arXiv: https://arxiv.org/abs/1803.04870
- RecordFlux — AdaCore + Componolit.
  Repo: https://github.com/AdaCore/RecordFlux
  AdaCore intro post: https://blog.adacore.com/recordflux-from-message-specifications-to-spark-code
  NVIDIA SPDM case study: https://www.adacore.com/papers/nvidia-using-recordflux-and-spark-to-implement-spdm-for-secure-computing
- Nail, OSDI 2014 — Bangert, Zeldovich.
  https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-bangert.pdf

### F\* / Pulse

- F\* tutorial (Pulse chapter): https://fstar-lang.org/tutorial/book/pulse/pulse.html
- PulseCore paper PDF: https://fstar-lang.org/papers/pulsecore.pdf

### Apache Parquet (for context)

- Parquet format spec: https://github.com/apache/parquet-format
- Parquet Thrift IDL: https://github.com/apache/parquet-format/blob/master/src/main/thrift/parquet.thrift
- Thrift compact protocol spec:
  https://github.com/apache/thrift/blob/master/doc/specs/thrift-binary-protocol.md
  (see also `BinaryProtocolExtensions.md` in the parquet-format repo)

### Factoidal cross-references

- Existing Parquet hand-written F\* code: `formal/fstar/Parquet.Footer.fst` (2545 lines)
- COTTAS plan: `docs/designissues/2026-04-19-cottas-parquet-wiring-plan.md`
- C extraction plan: `docs/designissues/2026-04-24-c-extraction-plan.md`
- Reading log for this doc: `docs/designissues/2026-04-25-tav4-everparse-research-scratch.md`
