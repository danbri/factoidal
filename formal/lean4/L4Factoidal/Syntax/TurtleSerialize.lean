/-
L4Factoidal.Syntax.TurtleSerialize — the Turtle pretty-printer.

Port of `formal/fstar/RDF.Turtle.Serialize.fst` (502 lines).

The wire-correct serialisers exist for round-trip and hashing fidelity;
this one targets a HUMAN-FACING rendering of the same graph — a
`@prefix` header, `;`-joined predicate lists, `,`-joined object lists,
one block per subject. The owner's brief for it was "ensure serializers
are not gratuitously ugly".

## The correctness anchor, and what it forbids

`parseTurtle (turtleOfGraph table g)` must give back `g`. So an
abbreviation may be emitted only when the parser would accept it, which
is why `tsAbbreviateIri` calls the SAME `Syntax.validatePnLocal` the
parser uses rather than approximating the Turtle grammar a second time.
An IRI whose remainder is not `PN_LOCAL`-safe falls back to `<iri>`.

Two abbreviations are used, both round-trip safe: a prefixed name when
the local part validates, and the `a` keyword for `rdf:type`, which
Turtle defines as its shorthand and the parser accepts unconditionally.

Numeric and boolean literals are NOT sugared to bare `42` / `true` —
correctness over sugar, as in F\*. The datatype IRI itself is
abbreviated, since that is pure compaction with no ambiguity.

## Auto prefix derivation

Split each IRI at its last `#` or `/`, count the namespaces whose
remainder is `PN_LOCAL`-safe, prefer the eight well-known prefixes when
they occur, and fill the rest with `ns1:`…`ns8:`. A namespace whose
IRIs never compact cleanly earns no header line, because the per-term
fallback already covers it.

## What the F\* module proves, and what it does not

It carries `lemma_ts_abbreviate_iri_pname_safe`, a structural fact
about the abbreviator, and its banner is explicit that the term-level
round trip is out of reach there: the literal path goes through byte
primitives that stay opaque to the solver, so even
`nq_escape_literal "a" == "a"` fails to reduce. Wire correctness of the
literal path is pinned at the CLI level instead.

Lean has the opposite situation. `Syntax.escapeLiteral` is an ordinary
computable function, so the round trip is CHECKABLE by `#guard` on
concrete graphs, through the real `parseTurtle` — which is what the
checks at the end do. That is evidence at the checked shapes, not a
theorem for all graphs, and this note says which it is.
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Joins

One reverse-accumulate then one concat, so a graph whose triples all
share a subject and predicate stays linear rather than quadratic. -/

def joinWithAcc (sep : String) : List String → List String → List String
  | [], acc => acc
  | [x], acc => x :: acc
  | x :: rest, acc => joinWithAcc sep rest (sep :: x :: acc)

def joinWith (sep : String) (xs : List String) : String :=
  String.join (joinWithAcc sep xs []).reverse

/-! ## The prefix table

`(namespace IRI, "label:")` pairs — the label already carries its
colon. -/

abbrev PrefixTable := List (String × String)

def tsStartsWithStrict (s pfx : String) : Bool :=
  s.length > pfx.length && s.startsWith pfx

def tsFindPrefix (table : PrefixTable) (iri : String) : Option (String × String) :=
  table.find? (fun p => tsStartsWithStrict iri p.1)

/-- `PN_LOCAL` may legally be empty (a bare `ex:`); anything non-empty
    must satisfy the parser's own validator. -/
def tsLocalOk (loc : String) : Bool :=
  loc.isEmpty || validatePnLocal loc.toList true

/-- Compact to a prefixed name only when the parser would read it back;
    otherwise emit the full `<iri>`. -/
def tsAbbreviateIri (table : PrefixTable) (iri : String) : String :=
  match tsFindPrefix table iri with
  | some (ns, abbr) =>
      let loc := String.ofList (iri.toList.drop ns.length)
      if tsLocalOk loc then abbr ++ loc else "<" ++ iri ++ ">"
  | none => "<" ++ iri ++ ">"

/-! ## Terms -/

def tsTermToTurtle (table : PrefixTable) : Term → String
  | .iri i => tsAbbreviateIri table i.val
  | .bnode b => "_:" ++ b
  | .literal l =>
      let esc := escapeLiteral l.val.lexicalForm
      match l.val.langTag with
      | some tag =>
          let ds := match l.val.direction with
                    | some .ltr => "--ltr"
                    | some .rtl => "--rtl"
                    | none => ""
          "\"" ++ esc ++ "\"@" ++ tag ++ ds
      | none =>
          if l.val.datatype == xsdString then "\"" ++ esc ++ "\""
          else "\"" ++ esc ++ "\"^^" ++ tsAbbreviateIri table l.val.datatype.val
  | .tripleTerm s p o =>
      let subjStr := match s with
                     | .iri i => tsAbbreviateIri table i.val
                     | .bnode b => "_:" ++ b
      let predStr := if p == rdfType then "a" else tsAbbreviateIri table p.val
      "<<( " ++ subjStr ++ " " ++ predStr ++ " " ++ tsTermToTurtle table o ++ " )>>"

def tsSubjectToTurtle (table : PrefixTable) : Subject → String
  | .iri i => tsAbbreviateIri table i.val
  | .bnode b => "_:" ++ b

/-- `a` is Turtle's own shorthand for `rdf:type`, accepted back by the
    parser, and needs no prefix-table entry. -/
def tsPredicateToTurtle (table : PrefixTable) (p : WfIri) : String :=
  if p == rdfType then "a" else tsAbbreviateIri table p.val

/-! ## Sorting and subject grouping

The sort key is subject, separator, predicate, separator, object — the
same discipline the closure path's dedup uses. The separator is U+001F,
which the F\* source documents as forbidden inside an IRI, so the join
is unambiguous. -/

def unitSep : String := String.singleton (Char.ofNat 31)

def tsTermKey : Term → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b
  | .literal l => "2" ++ l.val.lexicalForm ++ unitSep ++ l.val.datatype.val ++
      unitSep ++ l.val.langTag.getD ""
  | .tripleTerm _ _ _ => "3"

def tsSubjKey : Subject → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b

def tsTripleKey (t : Triple) : String :=
  tsSubjKey t.s ++ unitSep ++ t.p.val ++ unitSep ++ tsTermKey t.o

/-- Lean's own merge sort, keyed by `tsTripleKey`. The F\* module uses
    `List.Tot.sortWith triple_cmp`; this is the same O(n log n) sort
    with the comparator expressed as a `≤` on the key string. -/
def sortTriples (g : List Triple) : List Triple :=
  g.mergeSort (fun a b => tsTripleKey a ≤ tsTripleKey b)

structure SubjState where
  subj        : Subject
  subjText    : String
  curPred     : WfIri
  curPredText : String
  curObjs     : List String
  predChunks  : List String

def finishPred (st : SubjState) : List String :=
  (st.curPredText ++ " " ++ joinWith " , " st.curObjs.reverse) :: st.predChunks

def finishSubj (st : SubjState) : String :=
  st.subjText ++ " " ++ joinWith " ;\n    " (finishPred st).reverse ++ " .\n\n"

def walkTriples (table : PrefixTable) : List Triple → Option SubjState →
    List String → List String
  | [], none, acc => acc
  | [], some s, acc => finishSubj s :: acc
  | t :: rest, none, acc =>
      walkTriples table rest (some
        { subj := t.s, subjText := tsSubjectToTurtle table t.s,
          curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
          curObjs := [tsTermToTurtle table t.o], predChunks := [] }) acc
  | t :: rest, some s, acc =>
      let objText := tsTermToTurtle table t.o
      if s.subj == t.s then
        if s.curPred == t.p then
          walkTriples table rest (some { s with curObjs := objText :: s.curObjs }) acc
        else
          walkTriples table rest (some
            { s with curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
                     curObjs := [objText], predChunks := finishPred s }) acc
      else
        walkTriples table rest (some
          { subj := t.s, subjText := tsSubjectToTurtle table t.s,
            curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
            curObjs := [objText], predChunks := [] }) (finishSubj s :: acc)

def renderTriples (table : PrefixTable) (g : Graph) : String :=
  String.join (walkTriples table (sortTriples g) none []).reverse

/-! ## The header and the entry point -/

def renderPrefixHeader (table : PrefixTable) : List String :=
  table.map (fun (ns, abbr) => "@prefix " ++ abbr ++ " <" ++ ns ++ "> .\n")

def turtleOfGraph (table : PrefixTable) (g : Graph) : String :=
  let headerLines := renderPrefixHeader table
  String.join headerLines ++ (if headerLines.isEmpty then "" else "\n") ++
    renderTriples table g

/-! ## Auto prefix derivation -/

/-- The last `#` or `/`, as a split into `(namespace-with-delimiter,
    local)`. `none` when the IRI has neither and so cannot be
    compacted. -/
def nsSplit (iri : String) : Option (String × String) :=
  let cs := iri.toList
  let idx := cs.zipIdx.foldl (fun best (ci : Char × Nat) =>
    if ci.1 == '#' || ci.1 == '/' then some ci.2 else best) none
  match idx with
  | none => none
  | some i => some (String.ofList (cs.take (i + 1)), String.ofList (cs.drop (i + 1)))

/-- Every IRI in the graph: subjects, predicates, object IRIs, and
    literal datatypes other than the implicit `xsd:string` and language
    cases, which never print with a suffix. The IRIs nested inside a
    triple term are skipped, as in F\* — they print un-abbreviated,
    which is correct if less pretty. -/
def collectIris (g : Graph) : List String :=
  g.flatMap (fun t =>
    [t.p.val] ++
    (match t.s with | .iri i => [i.val] | _ => []) ++
    (match t.o with
     | .iri i => [i.val]
     | .literal l => match l.val.langTag with
                     | some _ => []
                     | none => if l.val.datatype == xsdString then []
                               else [l.val.datatype.val]
     | _ => []))

def candidateNamespaces (iris : List String) : List String :=
  iris.filterMap (fun i =>
    match nsSplit i with
    | none => none
    | some (ns, loc) =>
        if !loc.isEmpty && validatePnLocal loc.toList true then some ns else none)

def countRuns : List String → List (String × Nat)
  | [] => []
  | [x] => [(x, 1)]
  | x :: y :: rest =>
      if x == y then
        match countRuns (y :: rest) with
        | (y2, n) :: more => (y2, n + 1) :: more
        | [] => [(x, 1)]
      else (x, 1) :: countRuns (y :: rest)

def insertByCountDesc (x : String × Nat) : List (String × Nat) → List (String × Nat)
  | [] => [x]
  | y :: ys => if x.2 > y.2 then x :: y :: ys else y :: insertByCountDesc x ys

def sortByCountDesc : List (String × Nat) → List (String × Nat)
  | [] => []
  | x :: xs => insertByCountDesc x (sortByCountDesc xs)

def insertStr (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertStr x ys

def sortStrs : List String → List String
  | [] => []
  | x :: xs => insertStr x (sortStrs xs)

def assignLabels : Nat → List (String × Nat) → List (String × String)
  | _, [] => []
  | idx, (ns, _) :: rest =>
      if idx < 9 then (ns, "ns" ++ toString idx ++ ":") :: assignLabels (idx + 1) rest
      else []

/-- Preferred over auto-numbered labels when the graph uses them: real
    graphs are dominated by `rdf:type` and `xsd:` datatypes, and a
    numbered prefix for those would be needless ugliness. -/
def wellKnownPrefixes : PrefixTable :=
  [ ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:")
  , ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:")
  , ("http://www.w3.org/2001/XMLSchema#",           "xsd:")
  , ("http://www.w3.org/2002/07/owl#",              "owl:")
  , ("http://xmlns.com/foaf/0.1/",                  "foaf:")
  , ("http://purl.org/dc/terms/",                   "dcterms:")
  , ("http://purl.org/dc/elements/1.1/",            "dc:")
  , ("http://schema.org/",                          "schema:") ]

def turtleOfGraphAuto (g : Graph) : String :=
  let counted := countRuns (sortStrs (candidateNamespaces (collectIris g)))
  let presentNs := counted.map (·.1)
  let known := wellKnownPrefixes.filter (fun p => presentNs.contains p.1)
  let knownNs := known.map (·.1)
  let fresh := (sortByCountDesc counted).filter (fun p => !knownNs.contains p.1)
  let budget := if known.length ≥ 8 then 0 else 8 - known.length
  turtleOfGraph (known ++ assignLabels 1 (fresh.take budget)) g

/-! ## Build-time checks

### Abbreviation happens only when the parser would read it back -/

private def wi (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩

private def exTable : PrefixTable := [("http://example.org/", "ex:")]

#guard tsAbbreviateIri exTable "http://example.org/a" == "ex:a"
#guard tsAbbreviateIri exTable "http://other.org/a" == "<http://other.org/a>"

/-! A local part the parser would reject is NOT compacted: a space
    cannot appear in `PN_LOCAL`, so the full form is emitted. -/

#guard tsAbbreviateIri exTable "http://example.org/a b"
       == "<http://example.org/a b>"

/-! The strict prefix test needs the IRI to be LONGER than the
    namespace, so an IRI equal to it does not compact. -/

#guard tsAbbreviateIri exTable "http://example.org/" == "<http://example.org/>"

/-! ### `rdf:type` renders as `a`, in PREDICATE position only -/

#guard tsPredicateToTurtle [] rdfType == "a"
#guard tsPredicateToTurtle exTable (wi "http://example.org/p") == "ex:p"
#guard tsTermToTurtle [] (.iri rdfType) ==
       "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

/-! ### Literals -/

private def litT (lex : String) (dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := wi dt,
                       langTag := none, direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .bnode "bad"

#guard tsTermToTurtle [] (litT "x" "http://www.w3.org/2001/XMLSchema#string")
       == "\"x\""
#guard tsTermToTurtle [("http://www.w3.org/2001/XMLSchema#", "xsd:")]
         (litT "1" "http://www.w3.org/2001/XMLSchema#integer") == "\"1\"^^xsd:integer"
#guard tsTermToTurtle [] (litT "a\"b" "http://www.w3.org/2001/XMLSchema#string")
       == "\"a\\\"b\""

/-! ### The round trip, through the real parser

The F\* banner records that this could not be proved OR
`assert_norm`-witnessed there, because the literal path goes through
byte primitives that stay opaque to the solver. In Lean these are
ordinary computable functions, so the round trip is checkable — at
these shapes, which is evidence and not a theorem. -/

private def g1 : Graph :=
  [ ⟨.iri (wi "http://example.org/a"), rdfType, .iri (wi "http://example.org/C")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     .iri (wi "http://example.org/b")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     litT "hello" "http://www.w3.org/2001/XMLSchema#string"⟩
  , ⟨.bnode "b0", wi "http://example.org/q",
     litT "a\"b\\c" "http://www.w3.org/2001/XMLSchema#string"⟩ ]

private def roundTrips (g : Graph) : Bool :=
  match parseTurtle (turtleOfGraphAuto g) none .rdf12 with
  | .error _ => false
  | .ok g2 => sortTriples g2 == sortTriples g

#guard roundTrips g1
#guard roundTrips []
#guard roundTrips [⟨.iri (wi "http://x/y"), wi "http://x/p", .iri (wi "http://x/z")⟩]

/-! An IRI that cannot be compacted round-trips through the `<…>`
    fallback. -/

#guard roundTrips [⟨.iri (wi "http://x/a"), wi "http://x/p",
                    litT "1" "http://www.w3.org/2001/XMLSchema#integer"⟩]

/-! ### Grouping: `;` between predicates, `,` between objects -/

#guard ((turtleOfGraphAuto g1).splitOn " ;\n    ").length == 2
#guard ((turtleOfGraphAuto g1).splitOn " , ").length == 2

/-! ### The auto table prefers a well-known label over a numbered one -/

#guard ((turtleOfGraphAuto
  [⟨.iri (wi "http://example.org/a"), rdfType,
    .iri (wi "http://www.w3.org/2000/01/rdf-schema#Class")⟩]).splitOn
  "@prefix rdfs:").length == 2

end L4Factoidal.Syntax
