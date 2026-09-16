(* entry_lite_jsoo — js_of_ocaml / wasm_of_ocaml LITE entry point for
   the npm package (`factoidal-npm-entry-lite.js` / `.wasm.js`,
   https://github.com/danbri/factoidal/issues/684).

   This is a CONSUMER (rule #11): it links ONLY entry_core.ml (parse,
   query, update, serialize, dataset handles, the SPARQL 1.1 s17.6
   extension-function bridge, SERVICE endpoint snapshots) and exports
   that surface under the SAME JS global `factoidalNpmEntry` the full
   bundle (entry_jsoo.ml) uses — so npm/factoidal/lib/api.js, browser.js
   and createApi work unchanged against either bundle (open decision 5
   in docs/designissues/2026-07-05-bundle-modularity.md). It does NOT
   link entry_extras.ml, so the OCaml linker (build-ocaml.sh's lite
   build step runs without -linkall) never pulls SHACL/ShEx/OWL/RIF/
   JSON-LD/XML/XPath/CSVW/RML/VC/DID/COTTAS/delta-log/XSLT/MathML/
   XForms/JSON Schema/Schematron/TOAN/matrix/sigmoid into
   npm_entry_lite.byte — that is the size lever this bundle exists for.

   A request for a format this bundle does not parse (RDF/XML,
   JSON-LD) answers the routing error entry_core.ml's parse_document
   produces when its `extra_parsers` hook is None ("format '...' is
   not in the lite bundle; load factoidal-npm-entry.js") rather than a
   missing-function TypeError, so a caller can detect and fall back
   without a try/catch around a property access. `shaclValidate` and
   every entry_extras-only function are simply absent from this
   bundle's export object (`typeof e.shaclValidate === "undefined"`).

   ABI contract: the "Strict parsing", "Dataset handles" and "SPARQL
   1.2 opt-in variants" sections of entry_jsoo.ml's header comment
   apply verbatim to this bundle; everything under that file's
   "FULL-BUNDLE ONLY" heading is absent here. *)

module Js = Js_of_ocaml.Js

let () =
  Js.export "factoidalNpmEntry"
    (Js.Unsafe.obj
       [| ("abiVersion", Js.Unsafe.inject (Js.string Entry_core.abi_version));
          ("profile", Js.Unsafe.inject (Js.string "lite"));
          ("parseToDatasetJson", Entry_core.s3 Entry_core.parse_to_dataset_json);
          ("parseDocument", Entry_core.s4 Entry_core.parse_document_json);
          ("queryDataset", Entry_core.s2 Entry_core.query_dataset);
          ("askDataset", Entry_core.s2 Entry_core.ask_dataset);
          ("updateDataset", Entry_core.s2 Entry_core.update_dataset);
          ("queryDataset12", Entry_core.s2 Entry_core.query_dataset_12);
          ("askDataset12", Entry_core.s2 Entry_core.ask_dataset_12);
          ("updateDataset12", Entry_core.s2 Entry_core.update_dataset_12);
          ("serializeNQuads", Entry_core.s1 Entry_core.serialize_nquads);
          ("canonicalizeToNQuads", Entry_core.s1 Entry_core.canonicalize_to_nquads);
          ("serializeTurtle", Entry_core.s1 Entry_core.serialize_turtle);
          ("serializeTurtleWith", Entry_core.s2 Entry_core.serialize_turtle_with);
          ("datasetOpen", Entry_core.s3 Entry_core.dataset_open);
          ("datasetQuery", Entry_core.s2 Entry_core.dataset_query);
          ("datasetQuery12", Entry_core.s2 Entry_core.dataset_query_12);
          ("datasetUpdate", Entry_core.s2 Entry_core.dataset_update);
          ("datasetSerialize", Entry_core.s2 Entry_core.dataset_serialize);
          ("datasetSerializeWith", Entry_core.s3 Entry_core.dataset_serialize_with);
          ("datasetClose", Entry_core.s1 Entry_core.dataset_close);
          ("registerExtensionFunction",
             Js.Unsafe.inject (Js.wrap_callback Entry_core.ext_register));
          ("unregisterExtensionFunction", Entry_core.s1 Entry_core.ext_unregister);
          ("clearExtensionFunctions", Entry_core.s0 Entry_core.ext_clear);
          ("registerServiceEndpoint", Entry_core.s2 Entry_core.register_service_endpoint);
          ("clearServiceEndpoints", Entry_core.s0 Entry_core.clear_service_endpoints)
       |])
