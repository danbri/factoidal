module OWL.Tests.Manifest

// Test-type-IRI classifier for the W3C OWL test suite. Migrated
// from owl_runner.ml. Per CLAUDE.md rule #11 OCaml glue may not
// classify test type IRIs.

module S = FStar.String

let test_ns : string = "http://www.w3.org/2007/OWL/testOntology#"

// FStar.String.sub : s:string -> i:nat -> l:nat{i + l <= length s} -> Tot (r:string {length r = l})
// FStar.String.substring is in the Ex (exception) effect; we use sub
// to stay in Tot. The proof obligations on i+l<=length s are
// discharged by the il<pl / pl<=il guards.

let is_test_type_iri (iri : string) : Tot bool =
  let prefix = test_ns in
  let pl = S.length prefix in
  let il = S.length iri in
  if il < pl then false
  else if S.sub iri 0 pl <> prefix then false
  else
    let suffix = S.sub iri pl (il - pl) in
    suffix = "PositiveEntailmentTest" ||
    suffix = "NegativeEntailmentTest" ||
    suffix = "ConsistencyTest" ||
    suffix = "InconsistencyTest" ||
    suffix = "ProfileIdentificationTest"
