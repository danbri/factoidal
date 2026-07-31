(* tests/local/rdfs_entailment_regime_probe.ml -- throwaway test glue
   (not registered in build-ocaml.sh; same ad-hoc-harness-compiled-by-
   its-own-shell-script convention as tests/local/rml_virtual_pushdown_
   probe.ml and tests/local/delta_log_crash_harness.sh's probe.ml).

   Pins finding RS-4 of docs/designissues/2026-07-30-rdf-rdfs-entailment-
   refinement.md, issue #335. RDF.Entailment.Regime.fst used to define a
   one-argument `rdfs_closure` that SHADOWED RDFS.Closure's two-argument
   RDFS rule driver, so the rdf12 manifests' "RDFS" entailment regime ran
   exactly one rule (the RDF 1.2 rdf:reifies range step) and none of
   rdfs1-rdfs13.

   The W3C rdf-semantics manifest cannot detect that: it carries only two
   "RDFS" tests (reifies-range, triple-terms-propositions) and two
   "RDFS-Plus" tests (opaque-iri, opaque-iri-control), and NONE of the
   four uses rdfs:subClassOf / rdfs:domain / rdfs:range /
   rdfs:subPropertyOf. This probe supplies the missing coverage.

   Every function called here is Tot. Verdicts are deterministic values.

   Usage: rdfs_entailment_regime_probe        (no arguments) *)

let base = "http://example.com/probe"

let g s = Parser_Turtle.parse_turtle_with_base_12 s base

let prefixes =
  "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
   PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n\
   PREFIX owl:  <http://www.w3.org/2002/07/owl#>\n\
   PREFIX :     <http://example.com/ns#>\n"

let failures = ref 0

(* name, entailment relation, antecedent Turtle, consequent Turtle,
   expected verdict *)
let check name efn antecedent consequent expected =
  let a = g (prefixes ^ antecedent) in
  let b = g (prefixes ^ consequent) in
  let got = efn a b in
  let verdict = if got = expected then "ok  " else (incr failures; "FAIL") in
  Printf.printf "%s %-34s expected=%b got=%b (antecedent %d triples, consequent %d triples)\n"
    verdict name expected got (List.length a) (List.length b)

let rdfs = RDF_Entailment_Regime.entails_rdfs
let rdfs_plus = RDF_Entailment_Regime.entails_rdfs_plus
let rdf = RDF_Entailment_Regime.entails_rdf

let () =
  (* ---- the six rdfs rule rows the shipping driver implements ---- *)
  check "rdfs9-subClassOf" rdfs
    ":a rdf:type :C . :C rdfs:subClassOf :D .\n"
    ":a rdf:type :D .\n" true;

  check "rdfs2-domain" rdfs
    ":a :p :b . :p rdfs:domain :C .\n"
    ":a rdf:type :C .\n" true;

  check "rdfs3-range" rdfs
    ":a :p :b . :p rdfs:range :C .\n"
    ":b rdf:type :C .\n" true;

  check "rdfs7-subPropertyOf" rdfs
    ":a :p :b . :p rdfs:subPropertyOf :q .\n"
    ":a :q :b .\n" true;

  check "rdfs11-subClassOf-trans" rdfs
    ":C rdfs:subClassOf :D . :D rdfs:subClassOf :E .\n"
    ":C rdfs:subClassOf :E .\n" true;

  check "rdfs5-subPropertyOf-trans" rdfs
    ":p rdfs:subPropertyOf :q . :q rdfs:subPropertyOf :r .\n"
    ":p rdfs:subPropertyOf :r .\n" true;

  (* Two rows chained: rdfs3 feeds rdfs9 inside the fixed-point loop.
     A single rule pass cannot derive this. *)
  check "rdfs3-then-rdfs9-chained" rdfs
    ":a :p :b . :p rdfs:range :C . :C rdfs:subClassOf :D .\n"
    ":b rdf:type :D .\n" true;

  (* ---- the RDF 1.2 reifies-range step must survive the rename ---- *)
  check "rdf12-reifies-range" rdfs
    ":a rdf:reifies :b .\n"
    ":b rdf:type rdfs:Proposition .\n" true;

  (* The reifies step now runs BEFORE the rule driver, so its conclusion
     is visible to rdfs9. *)
  check "reifies-then-rdfs9" rdfs
    ":a rdf:reifies :b . rdfs:Proposition rdfs:subClassOf :Statement .\n"
    ":b rdf:type :Statement .\n" true;

  (* ---- negative controls: the closure must not be vacuously wide ---- *)
  check "neg-unrelated-class" rdfs
    ":a rdf:type :C . :C rdfs:subClassOf :D .\n"
    ":a rdf:type :E .\n" false;

  check "neg-subClassOf-not-symmetric" rdfs
    ":C rdfs:subClassOf :D .\n"
    ":D rdfs:subClassOf :C .\n" false;

  (* RS-1 guard. The regime deliberately uses the bare RDFS.Closure
     rdfs_closure, NOT rdfs_closure_with_reflexivity, whose class harvest
     reads owl:Class typing and emits `C rdfs:subClassOf C` that no RDFS
     rule licenses. If someone swaps the driver, this flips to true. *)
  check "neg-no-reflexivity-harvest" rdfs
    ":C rdf:type owl:Class .\n"
    ":C rdfs:subClassOf :C .\n" false;

  (* ---- RDFS-Plus keeps owl:sameAs AND gains the RDFS rules ---- *)
  check "plus-sameas-still-works" rdfs_plus
    ":superman :can :fly . :clark owl:sameAs :superman .\n"
    ":clark :can :fly .\n" true;

  check "plus-rdfs9-now-works" rdfs_plus
    ":a rdf:type :C . :C rdfs:subClassOf :D .\n"
    ":a rdf:type :D .\n" true;

  (* ---- the RDF regime must NOT have gained the RDFS rules ----
     Finding RS-5 of the same note records that OTHER code paths run the
     RDFS rule set under the "RDF" regime, which is unsound at that rung.
     This path does not, and must not start. *)
  check "rdf-regime-has-no-rdfs9" rdf
    ":a rdf:type :C . :C rdfs:subClassOf :D .\n"
    ":a rdf:type :D .\n" false;

  check "rdf-regime-has-no-reifies" rdf
    ":a rdf:reifies :b .\n"
    ":b rdf:type rdfs:Proposition .\n" false;

  Printf.printf "\nrdfs_entailment_regime_probe: %d failing checks\n" !failures;
  if !failures > 0 then exit 1
