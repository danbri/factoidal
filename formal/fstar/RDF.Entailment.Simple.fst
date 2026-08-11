module RDF.Entailment.Simple

// Simple entailment for RDF 1.2 (W3C RDF 1.2 Semantics, "simple" regime).
//
// Graph A simply-entails graph B iff there is a mapping from B's blank
// node labels to terms occurring in A such that the instance of B under
// that mapping is a subset of A. Equivalently: B homomorphically maps
// into A, with blank nodes acting as the existential variables and IRIs
// / literals matched exactly.
//
// RDF 1.2 adds triple terms (`T_TripleTerm`): a blank node inside a
// triple term is still an ordinary graph-scoped existential, so the
// homomorphism must recurse INTO triple terms and share one binding map
// across every position (subject, object, and every depth of nesting).
// That shared scope is exactly what the W3C `constrained-bnodes-*` and
// `*-no-spurious` tests pin down.
//
// This is the "simple" regime only: literals are matched by literal TERM
// equality (`literal_term_eq` -- RDF 1.1 Concepts §3.3, case-sensitive
// language tags, no rdf:XMLLiteral canonicalization), no datatype value
// canonicalization and no RDF/RDFS axiomatic closure. Those are the
// RDF / RDFS regimes, layered on top of this engine separately, and they
// pass the coarser `literal_eq` instead (issue #324 / SE-1). Per Iron
// Rule #1 this logic is
// F*-native (it previously lived, un-triple-term-aware, in the OCaml
// w3c_runner — a rule #15 boundary violation this module retires for the
// rdf12 suite).

open RDF.Graph.Executable
open RDF.Term
open FStar.List.Tot

// A binding maps a blank-node label from B to the ground term of A it was
// unified with. One flat, graph-scoped map (blank nodes are shared across
// subject / object / triple-term-interior positions).
let binding = list (string * rdf_term)

// A subject viewed as a term, so subjects and objects share one matcher.
let subj_as_term (s : subject) : rdf_term =
  match s with
  | S_IRI i   -> T_IRI i
  | S_BNode b -> T_BNode b

// Match a subject-position pattern against a ground subject. Subjects
// never nest, so this is non-recursive; keeping it separate lets the
// term matcher below carry a clean `decreases pat`.
let match_subj (b : binding) (ps : subject) (gs : subject) : option binding =
  match ps with
  | S_BNode lbl ->
    (match assoc lbl b with
     | Some t -> if rdf_term_eq t (subj_as_term gs) then Some b else None
     | None   -> Some ((lbl, subj_as_term gs) :: b))
  | S_IRI i ->
    (match gs with
     | S_IRI j   -> if i = j then Some b else None
     | S_BNode _ -> None)

// Match a pattern term (from B) against a ground term (from A), threading
// the shared binding. A pattern blank node binds on first sight and must
// agree on every later sight; IRIs and literals match exactly; triple
// terms recurse structurally, matching predicate exactly and recursing
// through subject then object. `decreases pat`: the only recursive call
// is on `po`, a strict sub-term of `T_TripleTerm ps pp po` (the subject
// side goes through the non-recursive `match_subj`).
// The engine is parameterized by a literal-equality predicate `leq`
// (`literal -> literal -> bool`). Simple entailment passes strict
// `literal_term_eq` (issue #324 / SE-1); the RDF/RDFS (D-)entailment
// layer in RDF.Entailment.Regime passes a value-aware predicate for
// recognized datatypes. `leq` is a plain value argument — it is threaded
// through the matchers untouched and does NOT participate in the
// termination measures, so the Phase A proof is unchanged. Bnode-bound
// consistency still uses structural `rdf_term_eq` (a bnode re-seen must
// denote the same ground term) -- NOTE this is `rdf_term_eq`, not `leq`,
// so it still routes literal comparison through the coarser
// `literal_eq` even under the simple regime. Benign for every fixture
// this engine runs today (no test reuses a blank node across two
// literals that differ only by language-tag case or XMLLiteral
// canonical form) but it is the same root cause as SE-1 reachable
// through a second path; not closed by this fix. Tracked as a residual
// note against issue #324, not a separate issue, until it has a
// witness.
// The engine is parameterized by TWO predicates:
//   * `leq : inside_tt -> literal -> literal -> bool` — literal match,
//     given whether the literals sit INSIDE a triple term (opaque
//     position). Simple entailment ignores the flag; the D-entailment
//     layer uses it (e.g. directional language strings are opaque —
//     case-sensitive — only inside a triple term).
//   * `bnd : rdf_term -> bool` — may a pattern blank node RANGE OVER this
//     ground term? Simple entailment: always. D-entailment: NOT over a
//     malformed recognized-datatype literal (it denotes nothing).
// Both are plain value arguments — threaded untouched, not in the
// termination measure, so the Phase A proof is unchanged. Bnode re-see
// consistency stays structural (`rdf_term_eq`).
let rec match_term (leq : bool -> literal -> literal -> bool)
                   (bnd : rdf_term -> bool)
                   (inside_tt : bool)
                   (b : binding) (pat : rdf_term) (g : rdf_term)
  : Tot (option binding) (decreases pat) =
  match pat with
  | T_BNode lbl ->
    (match assoc lbl b with
     | Some t -> if rdf_term_eq t g then Some b else None
     | None   -> if bnd g then Some ((lbl, g) :: b) else None)
  | T_IRI i ->
    (match g with T_IRI j -> if i = j then Some b else None | _ -> None)
  | T_Literal l ->
    (match g with T_Literal m -> if leq inside_tt l m then Some b else None | _ -> None)
  | T_TripleTerm ps pp po ->
    (match g with
     | T_TripleTerm gs gp go ->
       if pp = gp then
         (match match_subj b ps gs with
          | Some b1 -> match_term leq bnd true b1 po go
          | None    -> None)
       else None
     | _ -> None)

// Match a whole B-triple against a candidate A-triple, threading the
// binding: predicate exact, then subject, then object (top level, so the
// object matcher starts with inside_tt = false).
let match_triple (leq : bool -> literal -> literal -> bool)
                 (bnd : rdf_term -> bool)
                 (b : binding) (tb : triple) (ta : triple) : option binding =
  if tb.p = ta.p then
    (match match_subj b tb.s ta.s with
     | Some b1 -> match_term leq bnd false b1 tb.o ta.o
     | None    -> None)
  else None

// Backtracking search: bind each remaining B-triple `bs` against some
// A-triple, trying alternatives (`try_alts`) and backtracking when a
// local match cannot be completed downstream. Lexicographic termination
// %[remaining B-triples; remaining A-candidates]:
//   try_match(tb::rest)  -> try_alts(cand=a)   : same B-level, cand shrinks
//                                                 vs try_match's `1+len a`.
//   try_alts(ta::more)   -> try_match(rest)    : B-level strictly shrinks.
//   try_alts(ta::more)   -> try_alts(more)     : same B-level, cand shrinks.
let rec try_match (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
                  (bs : list triple) (b : binding) (a : list triple)
  : Tot bool (decreases %[length bs; 1 + length a]) =
  match bs with
  | [] -> true
  | tb :: rest -> try_alts leq bnd bs tb rest b a a
and try_alts (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
             (bs : list triple) (tb : triple)
             (rest : list triple { length rest < length bs }) (b : binding)
             (a : list triple) (cand : list triple)
  : Tot bool (decreases %[length bs; length cand]) =
  // Invariant: bs = tb :: rest, so `length bs` = the B-level try_match
  // was at, and `length rest` < `length bs`. Passing `bs` explicitly
  // keeps the measure a plain variable (not `1 + length rest`), which is
  // what the well-founded comparison needs to see across the mutual
  // recursion.
  match cand with
  | [] -> false
  | ta :: more ->
    (match match_triple leq bnd b tb ta with
     | Some b1 -> if try_match leq bnd rest b1 a then true else try_alts leq bnd bs tb rest b a more
     | None    -> try_alts leq bnd bs tb rest b a more)

// Graph `a` entails graph `b` under literal-match `leq` (position-aware)
// and bnode-range predicate `bnd`.
let entails_with (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
                 (a b : list triple) : bool =
  try_match leq bnd b [] a

// Graph `a` simply-entails graph `b`: literal TERM equality (RDF 1.1
// Semantics §5 / RDF 1.1 Concepts §3.3 -- position ignored, case
// SENSITIVE on language tags, no rdf:XMLLiteral value canonicalization),
// and blank nodes may range over any ground term.
//
// Issue #324 (SE-1): this used to pass `literal_eq`, which is
// deliberately COARSER than literal term equality (it folds language-tag
// case and canonicalizes rdf:XMLLiteral pairs -- both D-entailment
// behaviours, RDF.Entailment.Regime's job, not simple entailment's). That
// let `simple_entails` accept pairs that do not stand in the simple
// entailment relation -- see the machine-checked witness
// `simple_entails_not_sound_unconditionally` in
// RDF.Entailment.Simple.Refinement.fst. `literal_term_eq` is the strict
// per-field test the spec actually calls for.
let simple_entails (a b : list triple) : bool =
  entails_with (fun _ l m -> literal_term_eq l m) (fun _ -> true) a b
