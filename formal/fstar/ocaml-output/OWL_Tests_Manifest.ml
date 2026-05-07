open Prims
let (test_ns : Prims.string) = "http://www.w3.org/2007/OWL/testOntology#"
let (is_test_type_iri : Prims.string -> Prims.bool) =
  fun iri ->
    let prefix = test_ns in
    let pl = FStar_String.strlen prefix in
    let il = FStar_String.strlen iri in
    if il < pl
    then false
    else
      if (FStar_String.sub iri Prims.int_zero pl) <> prefix
      then false
      else
        (let suffix = FStar_String.sub iri pl (il - pl) in
         ((((suffix = "PositiveEntailmentTest") ||
              (suffix = "NegativeEntailmentTest"))
             || (suffix = "ConsistencyTest"))
            || (suffix = "InconsistencyTest"))
           || (suffix = "ProfileIdentificationTest"))
