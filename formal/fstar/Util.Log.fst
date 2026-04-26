module Util.Log

(* F*-first logging primitive.

   Spec view: emit is a no-op (returns unit, no observable effect on the
   spec). Pure code that calls it remains pure. Removing all log calls
   doesn't change correctness.

   OCaml realisation (Util_Log_runtime in
   experimental_ocaml_glue/util_log_runtime.sh): writes structured lines
   to stderr or to a file based on level + sink configured at process
   start.

   Industry-conventional levels (RFC 5424-ish):
     LL_Error  : something is wrong; user-visible
     LL_Warn   : recoverable anomaly worth surfacing
     LL_Info   : milestone events (request start/end, plan chosen)
     LL_Debug  : per-decision detail (e.g. each tp considered by planner)
     LL_Trace  : per-step detail (e.g. each rg walked)

   Default level is LL_Warn (matches Unix tool norms). --log-level=info,
   --log-level=debug, --log-level=trace lower the threshold; -v / -vv /
   -vvv on the CLI map to info/debug/trace respectively.

   This module deliberately keeps the API tiny. Callers format their
   own messages. We can add structured-record helpers later without
   breaking the spec view (the assume val signature is stable).
*)

type level =
  | LL_Error
  | LL_Warn
  | LL_Info
  | LL_Debug
  | LL_Trace

(* The realisation in OCaml is impure. The spec sees it as Tot unit
   because removing it preserves correctness. *)
assume val emit : level -> string -> string -> Tot unit
//                level    module   message

(* Convenience aliases. Pure spec-side; same underlying assume val. *)

let error (modname : string) (msg : string) : Tot unit =
  emit LL_Error modname msg

let warn (modname : string) (msg : string) : Tot unit =
  emit LL_Warn modname msg

let info (modname : string) (msg : string) : Tot unit =
  emit LL_Info modname msg

let debug (modname : string) (msg : string) : Tot unit =
  emit LL_Debug modname msg

let trace (modname : string) (msg : string) : Tot unit =
  emit LL_Trace modname msg
