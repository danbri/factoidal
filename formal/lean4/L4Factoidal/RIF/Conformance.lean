/-
L4Factoidal.RIF.Conformance — the RIF Core conformance conditions.

Port of `formal/fstar/RIF.Core.Conformance.fst` (801 lines).

Two families of decision, both STRUCTURAL over the XML tree rather than
over the evaluable AST:

* **Safeness** — W3C RIF Core §6.1 "Well-formed Terms, Formulas, and
  Rules": rule argument-safeness, and the no-free-variables condition.
* **Import rejection** — the RIF-RDF/OWL combination spec's per-import
  validity conditions.

## Why this works on XML and not on `RIF.Syntax`

It reasons about constructs the evaluator does not give semantics to
(`External`, `Equal`, `Or`, `Exists`) and only needs to know THAT they
are present and how they interact with bound-ness. It also has to keep
working on documents `RIF.Xml` REFUSES: the `Multiple_Context_Error`
fixture's imported document carries a multi-slot frame in HEAD position,
which the single-atom-head rule rejects, and a conformance verdict must
not depend on the rule being evaluable.

The one exception is the last section, the OWL-Direct
vocabulary-separation check, which reads parsed `Atom`s because it is
about the CONTENT of ground frame facts rather than the document's
shape.

## Narrowness, stated rather than implied

Three checks here are deliberately narrower than the specification
condition they are named after, and the F\* module says so for each:

* `importedGraphIsEmpty` is not an OWL 2 DL well-formedness checker. It
  catches the one criterion its fixture names — an empty graph is not
  recognisable as an OWL 2 DL ontology.
* `owlDirectSeparationInconsistent` is not an OWL 2 DL consistency
  checker. It detects the two vocabulary-separation violations the
  Approved corpus exercises.
* `noFreeVariables` compares the used and declared variable sets
  GLOBALLY over a document, not per-`Forall`-scope. That is enough for
  the fixture that exercises it and avoids a nested-scoping analysis
  nothing needs. A document that declares `?x` in one rule and uses a
  DIFFERENT `?x` free in another would pass; no fixture has that shape,
  and the limit is recorded here rather than left to be discovered.

## Fuel

Shared, and decremented at every call including the ones that start a
fresh sub-walk. The F\* module explains why: a fresh constant at those
points leaves no single well-founded measure across the mutual group,
so an arbitrarily deep `And`-of-`And` would not terminate provably. The
same reasoning holds in Lean, and the same budget is carried.
-/
import L4Factoidal.RIF.Xml
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RIF.Conformance

open L4Factoidal.RIF.Xml (tagIs firstChildWithLocalName childElementsOnly
  collectLeafText trimWs findAttr elementChildren isAtomTag isBodyWrapperTag
  findFirstNamed parseTermHost isIriTypeMarker rifNs)

def conformanceFuel : Nat := 1000

/-! ## 1. Free variables

`collectVarsExclDeclare` gathers every `Var` name reached WITHOUT
descending into a `declare` wrapper, so a quantifier's own declarations
do not count as uses. `collectDeclaredVars` gathers the names inside
`declare` wrappers, continuing to recurse afterwards so nested
quantifiers are all picked up. -/

mutual

def collectVarsExclDeclare (n : XML.Node) : Nat → List String
  | 0 => []
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "declare" tag then []
          else if tagIs "Var" tag then
            let raw := trimWs (collectLeafText children)
            if raw.isEmpty then [] else [raw]
          else collectVarsExclDeclareList children fuel
      | _ => []

def collectVarsExclDeclareList : List XML.Node → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, fuel + 1 =>
      collectVarsExclDeclare c fuel ++ collectVarsExclDeclareList rest fuel

end

mutual

def collectDeclaredVars (n : XML.Node) : Nat → List String
  | 0 => []
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "declare" tag then
            collectVarsExclDeclareList children fuel
              ++ collectDeclaredVarsList children fuel
          else collectDeclaredVarsList children fuel
      | _ => []

def collectDeclaredVarsList : List XML.Node → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, fuel + 1 =>
      collectDeclaredVars c fuel ++ collectDeclaredVarsList rest fuel

end

def listSubset (a b : List String) : Bool := a.all (b.contains ·)

/-- Every variable used outside a `declare` must be declared by SOME
`declare` in the document. Global rather than per-scope; see the header
for what that admits. -/
def noFreeVariables (root : XML.Node) : Bool :=
  listSubset (collectVarsExclDeclare root conformanceFuel)
             (collectDeclaredVars root conformanceFuel)

/-! ## 2. Builtin binding patterns

Most RIF-DTB builtins require every argument bound and contribute no new
binding. `pred:iri-string` and `pred:list-contains` are the two with an
alternate pattern that lets them PRODUCE one. -/

inductive BPat where
  | b
  | u
deriving DecidableEq, Repr

def iriStringLocal : String := "iri-string"
def listContainsLocal : String := "list-contains"

/-- The part of a builtin IRI after the last `#`. Kept local rather than
taking a dependency edge onto `RIF.Builtins`: this module works purely
on the XML tree and has no other reason to reach into the evaluator. -/
def localNameOfIri (iri : String) : String :=
  match (iri.toList.reverse.takeWhile (· != '#')).reverse with
  | []  => if iri.contains '#' then "" else iri
  | cs  => String.ofList cs

/-- Allowed patterns for a builtin. `[]` means no pattern with an
unbound position is allowed. -/
def builtinBindingPatterns (localNm : String) : List (List BPat) :=
  if localNm == iriStringLocal then [[.b, .u], [.u, .b]]
  else if localNm == listContainsLocal then [[.b, .u]]
  else []

/-! ## 3. Argument safeness, as a fixpoint over a body condition -/

def varNameOf : XML.Node → Option String
  | .element tag _ children =>
      if tagIs "Var" tag then
        let raw := trimWs (collectLeafText children)
        if raw.isEmpty then none else some raw
      else none
  | _ => none

mutual

def collectAllVars (n : XML.Node) : Nat → List String
  | 0 => []
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Var" tag then
            let raw := trimWs (collectLeafText children)
            if raw.isEmpty then [] else [raw]
          else collectAllVarsList children fuel
      | _ => []

def collectAllVarsList : List XML.Node → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, fuel + 1 => collectAllVars c fuel ++ collectAllVarsList rest fuel

end

def dedupStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- An argument is AVAILABLE when it is a constant, or a variable
already bound. Only direct `Var`/`Const` shapes are analysed; a nested
`External`-as-term argument does not occur in any fixture. -/
def argAvailability (bound : List String) (arg : XML.Node) : BPat :=
  match varNameOf arg with
  | some name => if bound.contains name then .b else .u
  | none      => .b

def argsAvailability (bound : List String) (args : List XML.Node) : List BPat :=
  args.map (argAvailability bound)

/-- Does an allowed pattern apply? Every position it marks `b` must be
available; a `u` position may be either — an already-bound argument
there is fine, it is just not exploited for a new binding. -/
def patternApplicable : List BPat → List BPat → Bool
  | [], [] => true
  | .b :: arest, .b :: brest => patternApplicable arest brest
  | .b :: _, .u :: _ => false
  | .u :: arest, _ :: brest => patternApplicable arest brest
  | _, _ => false

/-- The names this application binds: positions the pattern marks `u`
where the argument really was unbound. -/
def newlyBoundFromPattern : List BPat → List XML.Node → List BPat → List String
  | .u :: arest, a :: argsRest, .u :: brest =>
      match varNameOf a with
      | some name => name :: newlyBoundFromPattern arest argsRest brest
      | none      => newlyBoundFromPattern arest argsRest brest
  | _ :: arest, _ :: argsRest, _ :: brest =>
      newlyBoundFromPattern arest argsRest brest
  | _, _, _ => []

/-- The first applicable pattern decides. A RIF-DTB builtin with more
than one pattern is deterministic about which argument is the output
once availability is known, so the order does not change the answer. -/
def tryPatterns : List (List BPat) → List XML.Node → List BPat → List String
  | [], _, _ => []
  | p :: rest, args, actual =>
      if p.length == actual.length && patternApplicable p actual then
        newlyBoundFromPattern p args actual
      else tryPatterns rest args actual

/-- `(builtin local name, argument nodes)` from an `External`'s
`content`, whichever of `Expr` / `Atom` it wraps: safeness does not care
which, both are op-and-args shapes. -/
def externalOpAndArgs (externalNode : XML.Node) : Option (String × List XML.Node) :=
  match firstChildWithLocalName "content" (elementChildren externalNode) with
  | none => none
  | some contentNode =>
      match childElementsOnly (elementChildren contentNode) with
      | [inner] =>
          match firstChildWithLocalName "op" (elementChildren inner) with
          | none => none
          | some opNode =>
              match parseTermHost opNode with
              | some (.const pi sp) =>
                  if sp != iriSpace then none
                  else
                    let args := match firstChildWithLocalName "args"
                                        (elementChildren inner) with
                      | none => []
                      | some an => childElementsOnly (elementChildren an)
                    some (localNameOfIri pi, args)
              | _ => none
      | _ => none

def boundAfterExternal (bound : List String) (externalNode : XML.Node) : List String :=
  match externalOpAndArgs externalNode with
  | none => []
  | some (localNm, args) =>
      tryPatterns (builtinBindingPatterns localNm) args (argsAvailability bound args)

/-- `Equal(l, r)`: when one side is bound or constant, the other side's
variable becomes bound. -/
def boundAfterEqual (bound : List String) (equalNode : XML.Node) : List String :=
  match firstChildWithLocalName "left" (elementChildren equalNode),
        firstChildWithLocalName "right" (elementChildren equalNode) with
  | some lHost, some rHost =>
      match childElementsOnly (elementChildren lHost),
            childElementsOnly (elementChildren rHost) with
      | [l], [r] =>
          match argAvailability bound l, argAvailability bound r with
          | .b, .u => (varNameOf r).toList
          | .u, .b => (varNameOf l).toList
          | _, _   => []
      | _, _ => []
  | _, _ => []

/-! ### The closure

`boundClosure n bound` is the variables bound AFTER formula `n`, given
those already bound. Per §6.1:

* an ordinary atomic formula binds every variable occurring in it;
* `And` binds a variable safe in AT LEAST ONE conjunct — computed as a
  fixpoint, because an `Equal` chain such as `?x=?y, ?y=?z` needs
  several passes;
* `Or` binds a variable only when it is safe in EVERY disjunct, given
  the SAME incoming set for each: disjuncts do not accumulate into one
  another;
* `Exists` does not itself restrict propagation, and its own declared
  variables are not exported outward;
* `Equal` and `External` are the two productive cases above. -/

mutual

def boundClosure (n : XML.Node) (bound : List String) : Nat → List String
  | 0 => bound
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if isBodyWrapperTag tag then
            match childElementsOnly children with
            | [] => bound
            | first :: _ => boundClosure first bound fuel
          else if isAtomTag tag then
            dedupStrings (bound ++ collectAllVars n conformanceFuel)
          else if tagIs "And" tag then
            andFixpoint (childElementsOnly children) bound fuel
          else if tagIs "Or" tag then
            orIntersection (childElementsOnly children) bound fuel
          else if tagIs "Exists" tag then
            match firstChildWithLocalName "formula" children with
            | some f => boundClosure f bound fuel
            | none =>
                match (childElementsOnly children).filter
                        (fun c => match c with
                                  | .element t _ _ => !(tagIs "declare" t)
                                  | _ => false) with
                | f :: _ => boundClosure f bound fuel
                | []     => bound
          else if tagIs "External" tag then
            dedupStrings (bound ++ boundAfterExternal bound n)
          else if tagIs "Equal" tag then
            dedupStrings (bound ++ boundAfterEqual bound n)
          else bound
      | _ => bound

/-- Rounds over the conjuncts until the bound set stops growing. -/
def andFixpoint (conjuncts : List XML.Node) (bound : List String) : Nat → List String
  | 0 => bound
  | fuel + 1 =>
      let bound' := oneAndRound conjuncts bound fuel
      if bound'.length == bound.length then bound
      else andFixpoint conjuncts bound' fuel

def oneAndRound (conjuncts : List XML.Node) (bound : List String) : Nat → List String
  | 0 => bound
  | fuel + 1 =>
      match conjuncts with
      | [] => bound
      | c :: rest => oneAndRound rest (boundClosure c bound fuel) fuel

def orIntersection (branches : List XML.Node) (bound : List String) : Nat → List String
  | 0 => bound
  | fuel + 1 =>
      match branches with
      | [] => bound
      | b0 :: rest => intersectRest bound rest (boundClosure b0 bound fuel) fuel

def intersectRest (bound : List String) (bs : List XML.Node) (acc : List String) :
    Nat → List String
  | 0 => acc
  | fuel + 1 =>
      match bs with
      | [] => acc
      | b :: more =>
          let br := boundClosure b bound fuel
          intersectRest bound more (acc.filter (br.contains ·)) fuel

end

/-! ## 4. Rule-level safety

A rule is safe when it is a variable-free fact, or when every variable
of its HEAD and every variable of its BODY are in the body's bound
closure. The second condition is the one that catches a variable used
only inside an `External` call with no way to bind it, even when it
never reaches the head. -/

def checkSentence (n : XML.Node) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "sentence" tag || tagIs "formula" tag then
            match childElementsOnly children with
            | [] => true
            | first :: _ => checkSentence first fuel
          else if tagIs "Forall" tag then
            match firstChildWithLocalName "formula" children with
            | some f => checkSentence f fuel
            | none =>
                match firstChildWithLocalName "Implies" children with
                | some imp => checkSentence imp fuel
                | none     => true
          else if tagIs "Implies" tag then
            match findFirstNamed ["if", "body"] children,
                  findFirstNamed ["then", "head"] children with
            | some bodyNode, some headNode =>
                let bound := boundClosure bodyNode [] conformanceFuel
                let headVars := dedupStrings (collectAllVars headNode conformanceFuel)
                let bodyVars := dedupStrings (collectAllVars bodyNode conformanceFuel)
                listSubset headVars bound && listSubset bodyVars bound
            | _, _ => false
          else if isAtomTag tag then
            (collectAllVars n conformanceFuel).isEmpty
          else true
      | _ => true

mutual

def allSentencesSafe (n : XML.Node) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          if tagIs "Group" tag || tagIs "payload" tag || tagIs "Document" tag then
            allSentencesSafeList (childElementsOnly children) fuel
          else if tagIs "sentence" tag then checkSentence n conformanceFuel
          else true
      | _ => true

def allSentencesSafeList : List XML.Node → Nat → Bool
  | _, 0 => true
  | [], _ => true
  | c :: rest, fuel + 1 => allSentencesSafe c fuel && allSentencesSafeList rest fuel

end

/-- The safeness verdict for a whole document. -/
def checkDocumentSafe (root : XML.Node) : Bool :=
  noFreeVariables root && allSentencesSafe root conformanceFuel

/-- The same from source text. A document that is not well-formed XML is
not conformant, which is a verdict rather than an error. -/
def checkDocumentSafeText (input : String) : Bool :=
  match XML.parseXML input with
  | .error _ => false
  | .ok doc  => checkDocumentSafe doc.root

/-! ## 5. Import rejection -/

/-! Under an OWL-Direct import profile every `Frame` must be a DL-Frame
formula: its slot KEY has to be a constant. A `<slot><Var>x</Var>…`
violates that. -/

mutual

def hasVariableFrameProperty (n : XML.Node) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          let here :=
            if tagIs "slot" tag then
              match childElementsOnly children with
              | (.element kt _ _) :: _ => tagIs "Var" kt
              | _ => false
            else false
          here || hasVariableFramePropertyList children fuel
      | _ => false

def hasVariableFramePropertyList : List XML.Node → Nat → Bool
  | _, 0 => false
  | [], _ => false
  | c :: rest, fuel + 1 =>
      hasVariableFrameProperty c fuel || hasVariableFramePropertyList rest fuel

end

def rifIriDatatype : String := rifNs ++ "iri"
def rdfPlainLiteralDatatype : String := rdfNs ++ "PlainLiteral"

/-- `rif:iri` and `rdf:PlainLiteral` typed literals are not permitted in
an RDF graph a RIF document imports (RIF-RDF combination, "Well-formed
RDF Graphs"). -/
def tripleHasForbiddenDatatype (t : RDF.Triple) : Bool :=
  match t.o with
  | .literal l => l.val.datatype.val == rifIriDatatype
                    || l.val.datatype.val == rdfPlainLiteralDatatype
  | _ => false

def graphHasForbiddenRifDatatype (g : RDF.Graph) : Bool :=
  g.any tripleHasForbiddenDatatype

/-- Simple < RDF < RDFS is one comparable chain; OWL-Direct sits on a
separate branch with no ordering against them. -/
def profileRank (p : String) : Option Nat :=
  if p == "http://www.w3.org/ns/entailment/Simple" then some 0
  else if p == "http://www.w3.org/ns/entailment/RDF" then some 1
  else if p == "http://www.w3.org/ns/entailment/RDFS" then some 2
  else none

def profilesComparable (p1 p2 : String) : Bool :=
  if p1 == p2 then true
  else match profileRank p1, profileRank p2 with
       | some _, some _ => true
       | _, _ => false

/-- A document's imports must have a single highest profile. -/
def hasIncomparableProfilePair : List String → Bool
  | [] => false
  | p :: rest =>
      rest.any (fun q => !(profilesComparable p q)) || hasIncomparableProfilePair rest

/-- Under OWL-Direct an EMPTY imported graph cannot be recognised as an
OWL 2 DL ontology. Narrow by design: this is the one criterion the
fixture names, not a well-formedness checker. -/
def importedGraphIsEmpty (g : RDF.Graph) : Bool := g.isEmpty

/-! ### Multiple contexts

A non-`rif:local` constant must not occur in more than one ROLE — a
positional-atom predicate and a frame slot property — across a
document's imports closure. `rif:local` constants are excluded
automatically: their `Const` type marker is `rif:local`, not `rif:iri`,
and a local is document-scoped, so two documents' same-lexical locals
are different constants by construction.

XML-level rather than AST-level, deliberately: the imported document in
the fixture carries a multi-slot frame in HEAD position, which
`RIF.Xml`'s single-atom-head rule rejects, and the role analysis must
not depend on the rule being evaluable. Builtin `External` `Atom` ops
are collected too, harmlessly — a builtin IRI never appears as a frame
slot property, so it can never contribute a clash. -/

def constIriText : XML.Node → Option String
  | .element tag attrs children =>
      if tagIs "Const" tag then
        match findAttr "type" attrs with
        | some ty => if isIriTypeMarker ty then some (trimWs (collectLeafText children))
                     else none
        | none => none
      else none
  | _ => none

def hostFirstConstIri (host : XML.Node) : List String :=
  match childElementsOnly (elementChildren host) with
  | first :: _ => (constIriText first).toList
  | [] => []

mutual

def collectAtomOpIris (n : XML.Node) : Nat → List String
  | 0 => []
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          let here :=
            if tagIs "Atom" tag then
              match firstChildWithLocalName "op" children with
              | some opNode => hostFirstConstIri opNode
              | none => []
            else []
          here ++ collectAtomOpIrisList children fuel
      | _ => []

def collectAtomOpIrisList : List XML.Node → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, fuel + 1 => collectAtomOpIris c fuel ++ collectAtomOpIrisList rest fuel

end

mutual

def collectFramePropertyIris (n : XML.Node) : Nat → List String
  | 0 => []
  | fuel + 1 =>
      match n with
      | .element tag _ children =>
          (if tagIs "slot" tag then hostFirstConstIri n else [])
            ++ collectFramePropertyIrisList children fuel
      | _ => []

def collectFramePropertyIrisList : List XML.Node → Nat → List String
  | _, 0 => []
  | [], _ => []
  | c :: rest, fuel + 1 =>
      collectFramePropertyIris c fuel ++ collectFramePropertyIrisList rest fuel

end

/-- True when some `rif:iri` constant is used BOTH as a positional-atom
predicate and as a frame slot property across the given trees. The
caller supplies every document in the imports closure. -/
def multipleContextViolation (roots : List XML.Node) : Bool :=
  let preds := roots.flatMap (collectAtomOpIris · conformanceFuel)
  let props := roots.flatMap (collectFramePropertyIris · conformanceFuel)
  preds.any (props.contains ·)

/-! ## 6. OWL-Direct vocabulary separation

OWL 2 Direct Semantics separates the individual, class and data-value
vocabularies. Two violations are detected, in the two directions the
Approved corpus exercises:

* a ground frame TYPES an individual as an XSD datatype — a datatype is
  not a class, and an individual is not a data value;
* a ground frame asserts a declared `owl:ObjectProperty` with a LITERAL
  value — an object property's range is the individual domain, disjoint
  from data values.

Narrow by design, same as §5: not a general OWL 2 DL consistency
checker. -/

def bodyAtomsOf : Formula → List Atom
  | .atom a => [a]
  | .and fs => fs.flatMap bodyAtomsOf
  | .or fs  => fs.flatMap bodyAtomsOf
  | .exists _ f => bodyAtomsOf f

def ruleAtoms (r : Rule) : List Atom :=
  r.head :: (match r.body with | none => [] | some b => bodyAtomsOf b)

def owlObjectPropertyIri : String := "http://www.w3.org/2002/07/owl#ObjectProperty"
def rdfTypeIri : String := rdfNs ++ "type"

def iriHasXsdPrefix (i : String) : Bool := i.startsWith xsdNs && i.length > xsdNs.length

def graphDeclaresObjectProperty (g : RDF.Graph) (p : String) : Bool :=
  g.any (fun t =>
    (match t.s with | .iri si => si.val == p | _ => false)
      && t.p.val == rdfTypeIri
      && (match t.o with | .iri oi => oi.val == owlObjectPropertyIri | _ => false))

def frameFactSeparationViolation (imported : RDF.Graph) : Atom → Bool
  | .frame (.const _ osp) (.const p psp) v =>
      if osp != iriSpace || psp != iriSpace then false
      else
        match v with
        | .const vi vsp =>
            if vsp == iriSpace then p == rdfTypeIri && iriHasXsdPrefix vi
            else graphDeclaresObjectProperty imported p
        | _ => false
  | _ => false

def owlDirectSeparationInconsistent (rules : List Rule) (imported : RDF.Graph) : Bool :=
  (rules.flatMap ruleAtoms).any (frameFactSeparationViolation imported)

/-! ## Pinned behaviour

A conformance checker that answered `true` for everything would pass
every positive fixture, so each check below is pinned in BOTH
directions. -/

section Pins

private def wrapGroup (body : String) : String :=
  "<Document xmlns=\"http://www.w3.org/2007/rif#\"><payload><Group>" ++ body ++
  "</Group></payload></Document>"

private def atomStr (pred : String) (args : String) : String :=
  "<Atom><op><Const type=\"rif:iri\">http://example.org/" ++ pred ++
  "</Const></op><args>" ++ args ++ "</args></Atom>"

private def vv (name : String) : String := "<Var>" ++ name ++ "</Var>"
private def cc (name : String) : String :=
  "<Const type=\"rif:iri\">http://example.org/" ++ name ++ "</Const>"

/-! A safe rule: the head's variable is bound by the body atom. -/
private def safeRule : String :=
  wrapGroup ("<sentence><Forall><declare>" ++ vv "x" ++ "</declare><formula><Implies>" ++
    "<if>" ++ atomStr "q" (vv "x" ++ cc "b") ++ "</if>" ++
    "<then>" ++ atomStr "p" (vv "x" ++ cc "c") ++ "</then>" ++
    "</Implies></formula></Forall></sentence>")

#guard checkDocumentSafeText safeRule

/-! An UNSAFE rule: the head names a variable the body never binds.
Without this pin the checker could be answering `true` always. -/
private def unsafeRule : String :=
  wrapGroup ("<sentence><Forall><declare>" ++ vv "x" ++ "</declare><declare>" ++
    vv "y" ++ "</declare><formula><Implies>" ++
    "<if>" ++ atomStr "q" (vv "x" ++ cc "b") ++ "</if>" ++
    "<then>" ++ atomStr "p" (vv "y" ++ cc "c") ++ "</then>" ++
    "</Implies></formula></Forall></sentence>")

#guard !(checkDocumentSafeText unsafeRule)

/-! A free variable — used but never declared. -/
private def freeVarDoc : String :=
  wrapGroup ("<sentence><Forall><formula><Implies>" ++
    "<if>" ++ atomStr "q" (vv "x" ++ cc "b") ++ "</if>" ++
    "<then>" ++ atomStr "p" (vv "x" ++ cc "c") ++ "</then>" ++
    "</Implies></formula></Forall></sentence>")

#guard !(checkDocumentSafeText freeVarDoc)

/-! A variable-free fact is safe; a fact carrying a variable is not. -/
#guard checkDocumentSafeText (wrapGroup ("<sentence>" ++ atomStr "p" (cc "a" ++ cc "b") ++
                                         "</sentence>"))
#guard !(checkDocumentSafeText (wrapGroup ("<sentence>" ++ atomStr "p" (vv "x" ++ cc "b") ++
                                           "</sentence>")))

/-! An `Equal` chain settles: `?x` is bound by the atom, `?y` by
`?x = ?y`, and `?z` by `?y = ?z` — which needs more than one pass, and
is what makes the `And` case a fixpoint rather than a single fold. -/
private def equalChain : String :=
  wrapGroup ("<sentence><Forall><declare>" ++ vv "x" ++ "</declare><declare>" ++
    vv "y" ++ "</declare><declare>" ++ vv "z" ++ "</declare><formula><Implies>" ++
    "<if><And>" ++
      "<formula>" ++ atomStr "q" (vv "x" ++ cc "b") ++ "</formula>" ++
      "<formula><Equal><left>" ++ vv "y" ++ "</left><right>" ++ vv "x" ++
        "</right></Equal></formula>" ++
      "<formula><Equal><left>" ++ vv "z" ++ "</left><right>" ++ vv "y" ++
        "</right></Equal></formula>" ++
    "</And></if>" ++
    "<then>" ++ atomStr "p" (vv "z" ++ cc "c") ++ "</then>" ++
    "</Implies></formula></Forall></sentence>")

#guard checkDocumentSafeText equalChain

/-! Local-name extraction, both directions. -/
#guard localNameOfIri "http://www.w3.org/2007/rif-builtin-predicate#iri-string"
        == "iri-string"
#guard localNameOfIri "urn:no-hash" == "urn:no-hash"

/-! Binding patterns: `pred:iri-string` has two, an ordinary builtin has
none. -/
#guard (builtinBindingPatterns iriStringLocal).length == 2
#guard (builtinBindingPatterns "numeric-add").isEmpty

/-! Pattern matching: a `b` position demands availability, a `u`
position accepts either. -/
#guard patternApplicable [.b, .u] [.b, .u]
#guard patternApplicable [.b, .u] [.b, .b]
#guard !(patternApplicable [.b, .u] [.u, .b])
#guard !(patternApplicable [.b] [.b, .b])

/-! Profile ordering: the Simple/RDF/RDFS chain is comparable
throughout, and OWL-Direct is comparable only with itself. -/
#guard !(hasIncomparableProfilePair
          ["http://www.w3.org/ns/entailment/Simple",
           "http://www.w3.org/ns/entailment/RDFS"])
#guard hasIncomparableProfilePair
        ["http://www.w3.org/ns/entailment/Simple",
         "http://www.w3.org/ns/entailment/OWL-Direct"]
#guard !(hasIncomparableProfilePair
          ["http://www.w3.org/ns/entailment/OWL-Direct",
           "http://www.w3.org/ns/entailment/OWL-Direct"])
#guard !(hasIncomparableProfilePair [])

end Pins

end L4Factoidal.RIF.Conformance
