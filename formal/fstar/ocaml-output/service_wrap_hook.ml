(* service_wrap_hook.ml -- a single mutable ref cell, hand-written (no
   corresponding .fst source, same footing as fstar_pure_hashes.ml),
   breaking an OCaml link-order cycle that has no F*-side counterpart.

   Virtual sources, Part A Stages 1-2
   (docs/designissues/2026-07-06-virtual-sources-design.md), issue #57
   family. `SPARQL11_Algebra.ml`'s patched `service_endpoint_lookup`
   (minimal_regrettable_glue_code_each_with_an_open_issue/
   57_service_client_bind.sh) wants to fall back, on a static-table
   miss, to resolving a `wrap+http(s):` SERVICE endpoint by fetching it
   -- but that fetch logic needs RML_Eval/RML_Mapping/RML_Sources
   (Stage 2's `rml=` override) and SPARQL_HTTP_Client, all of which are
   extracted from .fst modules that structurally depend on
   SPARQL11.Algebra (RML.Eval.fst itself opens SPARQL11.Algebra) and
   therefore MUST be compiled after SPARQL11_Algebra.ml in every
   ocamlopt/ocamlfind invocation. `SPARQL11_Algebra.ml` cannot reference
   a not-yet-compiled module directly.

   This file is the standard OCaml fix for that shape: a tiny, self-
   contained ref cell compiled EARLY (right before SPARQL11_Algebra.ml
   in build-ocaml.sh's module lists, in both the native and JS/WASM
   builds), defaulting to "always None" -- i.e. today's exact "wrap+
   resolver not installed" behaviour, per the design doc's own security
   posture (§2.6: "no code path exists to differentiate 'wrap+ IRI,
   resolver not installed' from 'any other unknown scheme'"). A LATER-
   compiled module (`service_wrap_http.ml`, native builds only -- see
   its own banner for why it is deliberately absent from the JS/WASM
   module list) sets this ref, once, at program start, after every
   module it needs is already linked.

   No RDF/SPARQL semantic logic here at all -- not even format
   detection or IRI parsing (that's 100% in SPARQL.Service.Wrap.fst).
   This file is exactly one mutable binding.
*)

let resolver : (string -> RDF_Graph_Executable.rdf_graph option) ref =
  ref (fun (_ : string) -> None)
