/*
l4_stubs.c — placeholder definitions for the host facilities the wasm
build deliberately leaves out.

The exported ABI is a pure computation (JSON in, JSON out), but Lean's
runtime initialiser (`runtime/init_module.cpp`) unconditionally calls
into the libuv-backed event loop, which is not built for wasm32.

Measured, not assumed: after excluding runtime/libuv.cpp, runtime/uv/*
and runtime/openssl.cpp from the build, `wasm-ld` reported exactly ONE
undefined symbol — `initialize_libuv`. Everything else Lean's `Init`
initialisers reach is either satisfied by the compiled runtime or never
pulled in by the linker. So this file has exactly one stub, and its
smallness is the evidence that the exported surface really is pure.

If a future export needs real IO, the fix is to build libuv for wasm
(Lean's own CMake does this with an ExternalProject) or to move the
capability into Lean — never to make this stub do work.
*/

/* Lean's event loop is never started: no export reaches Lean's IO,
   task, socket or DNS layers. */
void initialize_libuv(void) {}
