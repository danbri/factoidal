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
// This is the "simple" regime only: literals are matched by STRUCTURAL
// equality (`literal_eq`), no datatype value canonicalization and no
// RDF/RDFS axiomatic closure. Those are the RDF / RDFS regimes, layered
// on top of this engine separately. Per Iron Rule #1 this logic is
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
let rec match_term (b : binding) (pat : rdf_term) (g : rdf_term)
  : Tot (option binding) (decreases pat) =
  match pat with
  | T_BNode lbl ->
    (match assoc lbl b with
     | Some t -> if rdf_term_eq t g then Some b else None
     | None   -> Some ((lbl, g) :: b))
  | T_IRI i ->
    (match g with T_IRI j -> if i = j then Some b else None | _ -> None)
  | T_Literal l ->
    (match g with T_Literal m -> if literal_eq l m then Some b else None | _ -> None)
  | T_TripleTerm ps pp po ->
    (match g with
     | T_TripleTerm gs gp go ->
       if pp = gp then
         (match match_subj b ps gs with
          | Some b1 -> match_term b1 po go
          | None    -> None)
       else None
     | _ -> None)

// Match a whole B-triple against a candidate A-triple, threading the
// binding: predicate exact, then subject, then object.
let match_triple (b : binding) (tb : triple) (ta : triple) : option binding =
  if tb.p = ta.p then
    (match match_subj b tb.s ta.s with
     | Some b1 -> match_term b1 tb.o ta.o
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
let rec try_match (bs : list triple) (b : binding) (a : list triple)
  : Tot bool (decreases %[length bs; 1 + length a]) =
  match bs with
  | [] -> true
  | tb :: rest -> try_alts bs tb rest b a a
and try_alts (bs : list triple) (tb : triple)
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
    (match match_triple b tb ta with
     | Some b1 -> if try_match rest b1 a then true else try_alts bs tb rest b a more
     | None    -> try_alts bs tb rest b a more)

// Graph `a` simply-entails graph `b`.
let simple_entails (a b : list triple) : bool =
  try_match b [] a
