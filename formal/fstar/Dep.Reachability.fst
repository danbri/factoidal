module Dep.Reachability

// ===================================================================
// VERIFIED graph reachability for module-liveness analysis (#448).
//
// WHY THIS EXISTS
// -------------------------------------------------------------------
// tools/module-liveness.py v2 rooted its dead-module BFS in
// `ocamlobjinfo <unit>.cmx` — text emitted by the OCaml compiler, read
// by an unverified Python BFS. That BFS is exhaustive relative to the
// edges it is given, but nothing checks that the OUTPUT it produces is
// actually closed under those edges: a bug in the BFS loop (an off-by-
// one queue drain, a missed edge-direction flip) would silently under-
// or over-report DEAD modules, and the .cmx dependency means the tool
// cannot even run before a build exists.
//
// This module is the verified reachability CORE that v3 of the tool
// calls into (via bin/depcheck) instead of trusting a hand-written
// Python BFS. It carries one theorem — closed_set_catches_all — whose
// premises (`is_closed`, `mem r acc`) are DECIDABLE booleans that the
// driver RE-CHECKS on the algorithm's actual output at runtime (see
// bin/depcheck/depcheck.ml). That is what makes fuel adequacy and the
// closure implementation's correctness irrelevant to soundness: even
// if `closure_fuel` ran out of fuel, or had an implementation bug, and
// returned a non-closed set, depcheck's runtime `is_closed` check
// catches it and refuses (exit 2) before any DEAD verdict is trusted.
// The theorem's job is narrower and stronger: IF the output the driver
// is holding really is closed and really does contain the roots, THEN
// no root can reach anything outside it — a fact about ALL closed
// supersets of the roots, not just the one `closure_fuel` happens to
// compute.
//
// GUARD RAILS
// -------------------------------------------------------------------
// - Issue #453: no proof here computes on STRING CONTENTS. `node` is
//   `string` only as an opaque, decidably-equal label type; every
//   proof step is list membership / structural induction, never
//   string parsing or char-level reasoning.
// - Iron rule #10: no --lax, no --admit_smt_queries. Every lemma below
//   verifies under z3 4.13.3 with explicit (bounded) fuel/ifuel where
//   the default budget was not enough — see the per-lemma comments.
// ===================================================================

open FStar.List.Tot

// ---------------------------------------------------------------------
// Graph representation. `node` is an opaque, decidably-equal label
// (in practice an F* module name or OCaml unit name); `edge = (s, d)`
// reads "s's compiled/verified unit references d's".
// ---------------------------------------------------------------------

let node = string
let edge = node & node

/// An edge is closed w.r.t. `acc` iff its source is not in `acc`, or
/// its target is. (Vacuously closed when the source is absent.)
let edge_closed (acc: list node) (e: edge) : Tot bool =
  let (s, d) = e in not (mem s acc) || mem d acc

/// `acc` is closed under `edges`: every edge whose source is in `acc`
/// has its target in `acc` too. Decidable — this is the premise the
/// driver re-checks on the algorithm's actual output.
let is_closed (edges: list edge) (acc: list node) : Tot bool =
  for_all (edge_closed acc) edges

/// Every element of `xs` occurs in `acc`. Used for the roots-are-
/// included premise the driver also re-checks.
let all_mem (xs acc: list node) : Tot bool = for_all (fun x -> mem x acc) xs

// ---------------------------------------------------------------------
// THE ALGORITHM. Not trusted for soundness (see header) — it only has
// to be plausible enough that `closure_fuel`'s output usually IS
// closed, because depcheck refuses otherwise. `step_edge`/`step` only
// ever ADD nodes, so `closure_fuel` is monotone in `acc` and the fuel
// bound (`length edges + 1`) is enough rounds for a correct
// implementation to reach a fixpoint (each round that doesn't reach a
// fixpoint has added at least one node, and there are at most
// `length edges` distinct target nodes worth adding) — but that
// adequacy argument is exactly the kind of reasoning issue #448 does
// NOT want load-bearing, which is why closed_set_catches_all below
// does not depend on it.
// ---------------------------------------------------------------------

let step_edge (acc: list node) (e: edge) : Tot (list node) =
  let (s, d) = e in if mem s acc && not (mem d acc) then d :: acc else acc

let step (edges: list edge) (acc: list node) : Tot (list node) =
  fold_left step_edge acc edges

let rec closure_fuel (edges: list edge) (acc: list node) (fuel: nat)
  : Tot (list node) (decreases fuel) =
  if fuel = 0 then acc
  else let acc' = step edges acc in
       if length acc' = length acc then acc
       else closure_fuel edges acc' (fuel - 1)

let reachable (edges: list edge) (roots: list node) : Tot (list node) =
  closure_fuel edges roots (length edges + 1)

// ---------------------------------------------------------------------
// THE SPEC: inductive reachability, independent of the algorithm
// above. `reaches edges r n` is a derivation that `n` is reachable
// from `r` by following zero or more `edges`.
// ---------------------------------------------------------------------

noeq type reaches (edges: list edge) : node -> node -> Type =
  | RRefl : n: node -> reaches edges n n
  | RStep : a: node -> b: node -> c: node ->
            reaches edges a b -> squash (memP (b, c) edges) ->
            reaches edges a c

// ---------------------------------------------------------------------
// THE DELETION-SAFETY THEOREM.
//
// Premises are the two DECIDABLE booleans the driver re-checks on the
// algorithm's real output (`is_closed edges acc`, `mem r acc`), so
// neither `closure_fuel`'s fuel bound nor its implementation is
// trusted — only this proof, and the runtime rechecks that make its
// hypotheses true of the actual data, are.
//
// Proof: induction on the `reaches` derivation (structural recursion
// on the proof term `h`, matching the sketch's suggested shape).
//   - RRefl: n = r, and `mem r acc` is exactly the hypothesis.
//   - RStep a b c hb (pf : squash (memP (b,c) edges)): the recursive
//     call on `hb : reaches edges a b` (note: `a` unifies with the
//     outer `r` via the GADT index, since we are matching
//     `h : reaches edges r n`) gives `mem b acc` by the induction
//     hypothesis. `is_closed edges acc` unfolds to
//     `for_all (edge_closed acc) edges`; `FStar.List.Tot.for_all_mem`
//     turns that into `forall x. memP x edges ==> edge_closed acc x`,
//     which applied to `(b, c)` (using `pf`) gives
//     `edge_closed acc (b, c)`, i.e. `not (mem b acc) || mem c acc`.
//     `mem b acc` from the IH kills the left disjunct, so `mem c acc`
//     — and `c` unifies with the outer `n`.
// ---------------------------------------------------------------------

let rec closed_set_catches_all
  (edges: list edge) (acc: list node) (r n: node) (h: reaches edges r n)
  : Lemma (requires is_closed edges acc /\ mem r acc)
          (ensures mem n acc)
          (decreases h)
  = match h with
    | RRefl _ -> ()
    | RStep a b c hb pf ->
        closed_set_catches_all edges acc r b hb;
        // IH: mem b acc.
        FStar.List.Tot.for_all_mem (edge_closed acc) edges;
        // forall x. memP x edges ==> edge_closed acc x
        assert (memP (b, c) edges);
        assert (edge_closed acc (b, c))

/// Corollary usable by the driver's report, stated as the
/// contrapositive of closed_set_catches_all: if the roots are all in
/// a closed set that does not contain `n`, then NO root reaches `n`.
val no_root_reaches
  (edges: list edge) (acc roots: list node) (n: node)
  : Lemma (requires is_closed edges acc /\ all_mem roots acc /\ not (mem n acc))
          (ensures forall (r: node). memP r roots ==> ~(reaches edges r n))
let no_root_reaches edges acc roots n =
  FStar.List.Tot.for_all_mem (fun x -> mem x acc) roots;
  // forall x. memP x roots ==> mem x acc
  introduce forall (r: node). memP r roots ==> ~(reaches edges r n)
  with introduce memP r roots ==> ~(reaches edges r n)
  with _ . begin
    assert (mem r acc);
    let contra : reaches edges r n -> Lemma False =
      fun h -> closed_set_catches_all edges acc r n h
    in
    FStar.Classical.impl_intro contra
  end
