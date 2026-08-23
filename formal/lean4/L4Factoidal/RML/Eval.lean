/-
L4Factoidal.RML.Eval — run a mapping over its sources.

Spec: RML-Core §"Generating RDF terms" and §"Generating triples".

## What a record is, and why it is not a string map

A record is the JSON value one iteration of the logical source yields.
A reference is evaluated against it as a JSONPath, and the value that
comes back CARRIES ITS TYPE — `10` is an `xsd:integer`, not the string
`"10"`. Flattening a record to `String → Option String` at the door
throws that away before the term is built, and the corpus measures it
(`RMLTC0002a-JSON` expects `"10"^^xsd:integer`).

## Sources are supplied, not read

`evalMapping` takes the source documents as a list of
`(path, Json)` pairs. Reading a file needs I/O; deciding what a
mapping means does not, and keeping the second a total function of
explicit inputs is the purity doctrine this port follows everywhere.
-/
import L4Factoidal.RML.FromGraph
import L4Factoidal.RML.JsonPath
import L4Factoidal.RML.Value
import L4Factoidal.JSON.Parser

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- The records one logical source yields. With NO iterator the whole
    document is one record. -/
def recordsOf (src : LogicalSource) (doc : Json) : List Json :=
  match src.iterator with
  | none     => [doc]
  | some itr => evalPath itr doc

/-- Look a reference up in one record. A reference selecting SEVERAL
    values is not an error — RML says a term map generates one term
    per value — so the caller gets the list and decides. -/
def refValues (rec' : Json) (r : String) : List RVal :=
  (evalPath r rec').filterMap rvalOf

/-- The single-value lookup `generateTerm` takes. The FIRST value
    wins; `termsOf` below is what handles the multi-valued case, and
    the two are kept apart so a single-valued position cannot silently
    take one of several. -/
def lookup1 (rec' : Json) : String → Option String := fun r =>
  (refValues rec' r).head?.map (·.lexical)

/-- Every term a map generates from one record.

    A REFERENCE map is multi-valued: `$.amounts[*]` selects three
    values and generates three terms, and taking only the first loses
    two triples that the corpus expects. A TEMPLATE map is
    single-valued here, which is the corpus's own shape — a template
    over a multi-valued reference is a cross product this slice does
    not build, and it says so rather than producing one arm of it. -/
def termsOf (base : Option String) (tm : TermMap) (rec' : Json) (naturalTypes : Bool)
    : List Term :=
  match tm.form with
  | .reference r =>
      let tt := tm.termType.getD (defaultTermType tm.form)
      (refValues rec' r).filterMap (fun v =>
        match tt with
        | .literal =>
            -- The SOURCE's datatype applies only when the map states
            -- neither a datatype nor a language: `rml:datatype` and
            -- `rml:language` both override it.
            let tm' := if naturalTypes && tm.datatype.isNone && tm.language.isNone
                       then { tm with datatype := v.natural } else tm
            generateTerm base tm' (fun f => if f == r then some v.lexical else none)
        | _ => generateTerm base tm (fun f => if f == r then some v.lexical else none))
  | .template raw =>
      -- A TEMPLATE over a multi-valued reference produces one term
      -- per COMBINATION. `$.Student[*].Name` selecting two names in
      -- `http://example.com/Student/{$.Student[*].Name}` means two
      -- subjects, and taking only the first lost half of
      -- `RMLTC0025c`'s output -- with the right predicate and the
      -- right objects on the half that survived, which is why the
      -- count was the only sign.
      let segs := parseTemplate raw
      let names := segs.foldl (fun acc seg => match seg with
        | .reference f => if acc.contains f then acc else acc ++ [f]
        | _            => acc) ([] : List String)
      let valueLists := names.map (fun f => (refValues rec' f).map (·.lexical))
      let combos := valueLists.foldl (fun acc vs =>
        acc.flatMap (fun a => vs.map (fun v => a ++ [v]))) [([] : List String)]
      combos.filterMap (fun combo =>
        generateTerm base tm (fun f =>
          ((names.zip combo).find? (fun (n, _) => n == f)).map (·.2)))
  | _ => (generateTerm base tm (lookup1 rec')).toList

/-- A term map whose value is a DATATYPE or a LANGUAGE: the lexical
    form of the first term it generates. -/
def stringOf (base : Option String) (tm : TermMap) (rec' : Json) : Option String :=
  (termsOf base tm rec' false).head?.bind (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | _          => none)

/-- One quad, before the dataset is assembled. -/
structure QuadOut where
  s : Subject
  p : WfIri
  o : Term
  g : Option Term
deriving Repr

private def toSubject? (t : Term) : Option Subject :=
  match t with
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

private def toPred? (t : Term) : Option WfIri :=
  match t with | .iri i => some i | _ => none

/-- A term map in an IRI POSITION — a subject, a predicate, a graph.
    The default term type there is `iri`, not `literal`:
    `defaultTermType` reads only the FORM, and a subject map written
    `rml:subjectMap [ rml:reference "$.FirstName" ]` is a reference,
    so it defaulted to a literal and produced no subject at all
    (`RMLTC0019a`). Position decides this, and only the caller knows
    the position. -/
def asIri (tm : TermMap) : TermMap :=
  match tm.termType with
  | some _ => tm
  | none   => { tm with termType := some .iri }

/-- A term map whose value is a plain STRING — a `rml:languageMap`.
    A language tag is not an IRI, and `defaultTermType` sends a
    template to `iri`, so `rml:languageMap [ rml:template
    "{$.language}-{$.region}" ]` produced the IRI
    `http://example.com/en-GB` where the tag `en-GB` was meant
    (`RMLTC0031c`). A `rml:datatypeMap` is the opposite case and keeps
    `asIri`: a datatype IS an IRI. -/
def asLiteral (tm : TermMap) : TermMap :=
  match tm.termType with
  | some _ => tm
  | none   => { tm with termType := some .literal }

/-- A blank-node label built from a triples map's id and a record's
    position. Non-name characters are dropped: an id is an IRI, and
    `:` and `/` are not blank-node label characters. -/
def anonLabel (id : String) (i : Nat) : String :=
  String.ofList (id.toList.filter (fun c => c.isAlphanum)) ++ "r" ++ toString i

/-- The subjects one triples map generates from one record. `i` is the
    record's position, which an ANONYMOUS blank-node subject needs.

    `rml:subjectMap [ rml:termType rml:BlankNode ]` states a term type
    and no form at all, and means "a fresh blank node for each
    record". `generateTerm` has no form to work from and returns
    nothing, so `RMLTC0012e` produced an empty graph from a mapping
    that describes four triples. -/
def subjectsOf (tm : TriplesMap) (rec' : Json) (i : Nat) : List Subject :=
  match tm.subject.form, tm.subject.termType with
  | .unknown, some .blankNode => [.bnode (anonLabel tm.id i)]
  | _, _ => (termsOf tm.base (asIri tm.subject) rec' false).filterMap toSubject?

/-- The graph terms a list of graph maps produces. An EMPTY list is
    not "the default graph" -- it is "this level states no graph", and
    the caller unions the levels before deciding. -/
def graphTermsOf (base : Option String) (gs : List TermMap) (rec' : Json)
    : List Term :=
  gs.flatMap (fun gm => termsOf base (asIri gm) rec' false)

/-- The graphs one triple goes into: the UNION of the subject map's
    graph maps and the predicate-object map's, and the default graph
    when that union is empty.

    Union, not override. R2RML and RML both say the graphs of a
    triple are the union of the two levels, and treating a
    predicate-object map's graph as a replacement put
    `student_10 practises sport_100` in the predicate-object map's
    graph only, where `RMLTC0009b` expects it in the subject map's as
    well -- one quad short, with every other quad right. -/
def graphsFor (sgraphs pgraphs : List Term) : List (Option Term) :=
  let u := sgraphs ++ pgraphs.filter (fun g => !(sgraphs.contains g))
  match u with
  | [] => [none]
  | _  => u.map some

def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-- The STRINGS one side of a join produces from a record. Both sides
    go through term generation, so a template side is expanded before
    the comparison rather than compared as a template. -/
def joinValues (tm : TermMap) (rec' : Json) : List String :=
  (termsOf none tm rec' false).filterMap (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | .bnode b   => some b
    | _          => none)

/-- Does a join hold between a child record and a parent record? -/
def joinHolds (js : List JoinCondition) (child parent : Json) : Bool :=
  js.all (fun j =>
    let cs := joinValues j.child child
    let ps := joinValues j.parent parent
    cs.any (fun c => ps.contains c))

/-- The quads one triples map generates. `docFor` supplies a source
    document by path, and `parents` the other triples maps a
    `rml:parentTriplesMap` can name. -/
def quadsOfMap (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    : List QuadOut :=
  match docFor tm.source.path with
  | none => []
  | some doc =>
      ((recordsOf tm.source doc).zipIdx).flatMap (fun (rec', i) =>
        let subjs := subjectsOf tm rec' i
        let sgraphs := graphTermsOf tm.base tm.graphs rec'
        subjs.flatMap (fun s =>
          let typeQuads : List QuadOut :=
            tm.classes.flatMap (fun c =>
              match (if h : isIri c then some (⟨c, h⟩ : WfIri) else none) with
              | none    => []
              | some ci => (graphsFor sgraphs []).map (fun g =>
                  ({ s := s, p := rdfTypeIri, o := .iri ci, g := g } : QuadOut)))
          let pomQuads : List QuadOut :=
            tm.poms.flatMap (fun pom =>
              let preds := pom.predicates.flatMap (fun pm =>
                (termsOf tm.base (asIri pm) rec' false).filterMap toPred?)
              let graphs := graphsFor sgraphs (graphTermsOf tm.base pom.graphs rec')
              let objs : List Term := pom.objects.flatMap (fun om =>
                match om with
                | .term base dtm lm =>
                    let base := match dtm.bind (fun m => stringOf tm.base (asIri m) rec') with
                      | some d => { base with datatype := some d }
                      | none   => base
                    let base := match lm.bind (fun m => stringOf tm.base (asLiteral m) rec') with
                      | some l => { base with language := some l }
                      | none   => base
                    termsOf tm.base base rec' true
                | .ref parentId joins =>
                    match all.find? (fun p => p.id == parentId) with
                    | none => []
                    | some parentMap =>
                        match docFor parentMap.source.path with
                        | none => []
                        | some pdoc =>
                            (((recordsOf parentMap.source pdoc).zipIdx).filter
                               (fun (prec, _) => joinHolds joins rec' prec)).flatMap
                              (fun (prec, pi) =>
                                (subjectsOf parentMap prec pi).map Subject.toTerm))
              preds.flatMap (fun p => objs.flatMap (fun o =>
                graphs.map (fun g => ({ s := s, p := p, o := o, g := g } : QuadOut)))))
          typeQuads ++ pomQuads))

/-- `rml:defaultGraph` names the default graph, so a graph map that
    produces it is the same as producing none. -/
def defaultGraphIri : String := rmlNs ++ "defaultGraph"

/-- Run a whole mapping. `defaultBase` is the base IRI in force where
    a triples map states none — the test corpus gives one per case
    (`rml:defaultBaseIRI`, `base_iri` in its own metadata), and
    without it a template that produces `Carlos` yields no term at all
    instead of `http://example.com/Carlos` (`RMLTC0019a`). -/
def evalMapping (defaultBase : Option String) (m : Mapping)
    (docFor : String → Option Json) : List QuadOut :=
  let m := m.map (fun t => { t with base := t.base.orElse (fun _ => defaultBase) })
  (m.flatMap (quadsOfMap m docFor)).map (fun q =>
    match q.g with
    | some (.iri i) => if i.val == defaultGraphIri then { q with g := none } else q
    | _             => q)

end L4Factoidal.RML
