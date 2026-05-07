module RIF.Core.Tests

// Phase 4 of the RIF Core F* engine, per
// docs/designissues/2026-05-07-rif-fstar-investigation.md.
//
// Runner shim that ties the four earlier phases together for the W3C
// SPARQL 1.1 entailment tests rif01 / rif03 / rif04 / rif06:
//
//   - Parser.RIFXML.parse_rif_program  : string -> option rif_program
//   - RIF.Core.Eval.fixpoint           : rdf_graph -> rif_program -> nat -> rdf_graph
//   - RDF.Graph.Executable.mem_triple  : triple -> rdf_graph -> bool
//
// The W3C SPARQL entailment tests come in two shapes:
//
//   (a) ASK-style: the .srx contains a single boolean. The test passes
//       iff the saturated graph entails the ASK pattern. Two of the
//       four targets (rif04 "Modeling Brain Anatomy", rif06 "RDF
//       Combination Blank Node") are this shape, with the expected
//       boolean being true. We expose `run_ask_entails_triple` which
//       checks whether a specific concrete triple appears in the
//       saturated graph -- the .rq file's WHERE pattern is degenerate
//       (a single triple pattern with all positions ground or a
//       single bnode in subject), so triple-membership is the right
//       primitive.
//
//   (b) SELECT-style: the .srx contains a list of result rows over a
//       set of named variables. rif01 ("Logical Entailment") and
//       rif03 ("Frames") are this shape. We expose `run_select_check`
//       which takes a list of (variable name, expected RDF term) row
//       expectations and confirms each row appears as a triple in the
//       saturated graph under the WHERE pattern's projection.
//
// The runner shim does NOT re-implement SPARQL evaluation -- it
// invokes the F* SPARQL stack indirectly via RIF.Core.Eval, which
// uses SPARQL11.Algebra.eval_bgp internally for body matching, and
// then the consumer-side OCaml glue feeds the saturated graph back
// into the standard SPARQL evaluator that w3c_runner already uses
// for the SELECT/ASK execution proper. The F* surface here is
// limited to "fixpoint, then membership check" so the OCaml glue
// can compose with `parse_sparql_query` + `eval_query` without
// duplicating semantic logic (per iron rule #15).
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10, rule #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.
//   - Inside the verified library, OCaml glue may only realise
//     assume val (rule #11). The w3c_runner.ml dispatch that calls
//     this module is one of the consumer-side runners exempted in
//     rule #11; this module exposes pure F* surface to it.

open RDF.Graph.Executable
module Syn = RIF.Core.Syntax
module Ev  = RIF.Core.Eval
module Pr  = Parser.RIFXML

// ------------------------------------------------------------------
// 1. Default fuel.
//
// The four W3C target tests reach saturation after a small number of
// rounds (parent/brother/uncle in rif01: one round; transitive frame
// reasoning in rif04: bounded by the number of brain regions in the
// imported ontology; the others are even shallower). We pick a
// generous default of 100 rounds so degenerate inputs still terminate
// in well under a second; the public surface accepts an explicit
// fuel for the caller that wants tighter control.
// ------------------------------------------------------------------

let default_fuel : nat = 100

// ------------------------------------------------------------------
// 2. The core composite: parse + saturate.
//
// `saturate_with_program` is the single F* function that drives a
// RIF Core test from raw RIF-XML rules + a premise graph to a
// saturated graph. Returns None if the RIF-XML failed to parse;
// that case is the only failure mode F* can report -- semantic
// failures (the saturated graph not entailing the conclusion) are
// the caller's pass/fail to decide.
// ------------------------------------------------------------------

let saturate_with_program
  (rif_xml : string) (premise : rdf_graph) (fuel : nat)
  : option rdf_graph
  =
  match Pr.parse_rif_program rif_xml with
  | None -> None
  | Some program -> Some (Ev.fixpoint premise program fuel)

// ------------------------------------------------------------------
// 3. ASK-style runner: triple membership in the saturated graph.
//
// W3C SPARQL ASK queries with a fully-ground triple pattern (or a
// single bnode in subject -- which exists-checks any ground binding)
// reduce to triple membership against the saturated graph. The
// rif04/rif06 tests are exactly this shape. We expose the simpler
// "is this concrete triple in the closure?" primitive; the OCaml
// glue can pre-resolve the bnode-existential by walking the graph.
// ------------------------------------------------------------------

let run_rif_ask_triple
  (rif_xml : string) (premise : rdf_graph) (conclusion : triple)
  : bool
  =
  match saturate_with_program rif_xml premise default_fuel with
  | None     -> false
  | Some sat -> mem_triple conclusion sat

// Parametric variant -- explicit fuel + arbitrary membership
// predicate. Used for the bnode-existential rif06 case where the
// caller wants to scan for "any triple with predicate rdf:type and
// object ex:named".
let run_rif_ask_with
  (rif_xml : string) (premise : rdf_graph) (fuel : nat)
  (check : rdf_graph -> bool)
  : bool
  =
  match saturate_with_program rif_xml premise fuel with
  | None     -> false
  | Some sat -> check sat

// ------------------------------------------------------------------
// 4. SELECT-style runner: row-by-row entailment check.
//
// A SELECT row is a list of (variable name, expected RDF term)
// pairs. We do NOT here re-implement projection: the w3c_runner
// glue parses the .srx with the existing F*-extracted Parser.SRX
// and feeds the rows in. For each row, we ask whether the
// saturated graph contains the triples that the WHERE BGP would
// have read to bind those variables. The single-pattern case is
// the only one the four W3C targets exercise (rif01: one triple
// pattern; rif03: one triple pattern). We surface the
// membership-of-a-fully-resolved-triple primitive again --
// `run_rif_ask_triple` -- and add a small "all rows pass"
// combinator for clarity.
// ------------------------------------------------------------------

let rec run_rif_select_rows
  (rif_xml : string) (premise : rdf_graph) (fuel : nat)
  (rows : list triple)
  : Tot bool (decreases rows)
  =
  match rows with
  | [] -> true
  | row :: rest ->
    if run_rif_ask_with rif_xml premise fuel (fun g -> mem_triple row g)
    then run_rif_select_rows rif_xml premise fuel rest
    else false

// ------------------------------------------------------------------
// 5. Convenience: SPARQL-test entrypoint.
//
// `run_rif_entailment_check` is the named entry the w3c_runner
// dispatch in formal/fstar/ocaml-output/w3c_runner.ml calls. It
// composes the parse + saturate + membership check into a single
// boolean, matching the dispatch shape the design doc specifies:
//
//   match RIF_Core_Tests.run_rif_entailment_check rif_xml premise rows with
//   | true  -> Pass
//   | false -> Fail "RIF entailment check failed"
//
// `rows` is the list of fully-resolved triples that the SPARQL
// SELECT result asserts must be entailed. For ASK-true tests, pass
// the single asked triple; for ASK-false tests, pass the empty
// list and confirm via run_rif_ask_with that the asked triple is
// NOT in the saturated graph (the OCaml glue is responsible for
// the polarity flip).
// ------------------------------------------------------------------

let run_rif_entailment_check
  (rif_xml : string) (premise : rdf_graph) (rows : list triple)
  : bool
  =
  run_rif_select_rows rif_xml premise default_fuel rows

// ------------------------------------------------------------------
// 6. Saturation soundness re-export.
//
// Re-export the saturation-extends lemma from RIF.Core.Eval so
// downstream proofs can refer to it without an extra `open`. The
// lemma states that fixpoint preserves every input triple; this
// is the soundness side of "entailment under forward chaining
// never loses information from the premise graph".
// ------------------------------------------------------------------

let lemma_saturate_extends
  (rif_xml : string) (premise : rdf_graph) (fuel : nat)
  : Lemma
      (match saturate_with_program rif_xml premise fuel with
       | None     -> True
       | Some sat -> Ev.graph_subset premise sat)
  =
  match Pr.parse_rif_program rif_xml with
  | None         -> ()
  | Some program -> Ev.lemma_fixpoint_extends premise program fuel

// ------------------------------------------------------------------
// 7. Parse-failure short-circuit lemma.
//
// Feeding a non-XML string to run_rif_entailment_check has to flow
// through saturate_with_program's None branch. We capture that
// case-split as a structural lemma rather than an `assert_norm`:
// the latter would force the SMT solver to reduce
// Parser.RIFXML.parse_rif_program over the full Parser.XML scanner,
// which is a multi-thousand-line tower of recursive matches; the
// reduction times out without aiding the proof. The structural
// case-split below is one line of F* and SMT-free.
// ------------------------------------------------------------------

let lemma_parse_none_yields_false
  (rif_xml : string) (premise : rdf_graph) (rows : list triple) (fuel : nat)
  : Lemma
      (requires Pr.parse_rif_program rif_xml == None)
      (ensures  run_rif_select_rows rif_xml premise fuel rows
                  == (match rows with | [] -> true | _ -> false))
  =
  match rows with
  | []        -> ()
  | _ :: _    -> ()
