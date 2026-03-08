# KaRaMeL-Extracted C from Verified F*

This directory contains C code extracted from `RDF.Graph.Executable.fst` via KaRaMeL.

## What this is

The C code is **mechanically extracted** from F* source that has been verified by the F* typechecker with zero `admit()` calls. The logical correctness of the algorithms is machine-checked. This is the same pipeline used by HACL* (Firefox, Linux kernel) and EverParse (Windows Hyper-V).

## What this is NOT (yet)

The current F* source uses high-level features that are **not in the Low\* subset**. KaRaMeL extracts them with compatibility shims, which means:

### Warning 9 — Static initializers
`empty_graph` requires runtime initialization. Callers must invoke `krmlinit_globals()` before use.

### Warning 11 — Closures
Functions like `graph_remove` use anonymous lambdas. KaRaMeL translates these to function pointers, which works but is fragile for closures that capture variables.

### Warning 15 — Not Low\* (the significant one)
| Feature used | C consequence | Fix |
|-------------|--------------|-----|
| `list triple` (GC linked list) | **Leaks memory** — no GC to reclaim nodes | Rewrite to `Buffer.t triple` (Low\* stack/heap buffer) |
| `Prims_string` (GC string) | **Leaks memory** — same issue | Rewrite to `C.String.t` or fixed-size `uint8_t*` |
| `krml_checked_int_t` (math int) | Runtime overflow checks, not native `int` | Rewrite to `UInt32.t` or `UInt64.t` |
| Closures in filters | Function pointer translation | Rewrite to explicit loops |

## Practical status

- **Short-lived programs / test harnesses**: the C will produce **correct results**
- **Long-running services**: will **leak memory** on every graph operation
- **The logic is verified; the memory management is not**

## Path to standalone C

The standard F* approach (HACL*, EverParse) is Spec + Impl modules:

```
RDF.Graph.Executable.fst     ← Spec (current — readable, proved, high-level)
RDF.Graph.Impl.fst           ← Impl (planned — Low*, extractable to standalone C)
  - imports Spec
  - proves: impl_graph_add ≡ Spec.graph_add
  - uses: Buffer.t, UInt32.t, C.String.t
```

The Spec is never deleted. The Impl proves equivalence, then KaRaMeL extracts only the Impl to self-contained C with no GC dependency.

## Regenerating

```bash
eval $(opam env --switch=fstar)
cd formal/fstar
make extract-c
```

Requires KaRaMeL (built from source at `/tmp/karamel`).
