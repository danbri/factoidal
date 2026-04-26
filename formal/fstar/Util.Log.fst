module Util.Log

(* F*-first logging primitive.

   Spec view: each emit_* is a no-op (returns unit, no observable
   effect on the spec). Pure code that calls them remains pure.
   Removing all log calls doesn't change correctness.

   OCaml realisation (Util_Log_runtime in
   experimental_ocaml_glue/util_log_runtime.sh): writes structured lines
   to stderr or to a file based on level + sink configured at process
   start.

   IMPORTANT: each level has its own `assume val` rather than a
   convenience-alias dispatching through a single `emit`. F* extraction
   inlines small `let` definitions like `let debug = emit LL_Debug`,
   then sees the unit-typed result as dead code in `_ = debug "..." "..."`
   contexts and erases the whole call. By making each level a standalone
   `assume val`, F* can't inline them away — the calls survive extraction
   intact. (Verified empirically 2026-04-26.)

   Industry-conventional levels (RFC 5424-ish):
     error  : something is wrong; user-visible
     warn   : recoverable anomaly worth surfacing
     info   : milestone events (request start/end, plan chosen)
     debug  : per-decision detail (e.g. each tp considered by planner)
     trace  : per-step detail (e.g. each rg walked)

   Default level is warn (matches Unix tool norms). Set
   FACTOIDAL_LOG_LEVEL=info|debug|trace (env var) or
   --log-level=NAME (CLI, future) to lower the threshold.

   Callers format their own messages. We can add structured-record
   helpers later without breaking the spec view (these signatures are
   stable).
*)

(* Each level is a separate assume val. F* won't fold them through a
   common dispatcher and can't erase them as unit-discarded `let _`
   expressions. *)

assume val error : string -> string -> Tot unit
//                 module    message

assume val warn : string -> string -> Tot unit

assume val info : string -> string -> Tot unit

assume val debug : string -> string -> Tot unit

assume val trace : string -> string -> Tot unit
