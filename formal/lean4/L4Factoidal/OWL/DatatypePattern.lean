/-
L4Factoidal.OWL.DatatypePattern — finite XSD pattern languages used by
the OWL datatype refuter.

XSD pattern facets match the whole lexical form. A finite pattern
language can therefore be exhausted by explicit negative assertions
or values asserted through a disjoint data property. This module
recognises only a structural, finite subset of the existing XSD regex
AST. Unsupported and oversized expressions return `none`, so they
cannot create a clash.
-/
import L4Factoidal.OWL.ClassExpr
import L4Factoidal.Regex.XSDPattern

namespace L4Factoidal.OWL

open L4Factoidal.RDF
open L4Factoidal.Regex

/-- Maximum number of lexical forms materialised for one pattern
    restriction. Checks happen before Cartesian products are built. -/
def maxFinitePatternValues : Nat := 256

/-- The finite-language path also bounds every materialised lexical
    form. Brace quantifiers are declined before invoking the shared
    parser because a very large exact repetition expands its AST. -/
def finitePatternTextSupported (s : String) : Bool :=
  let cs := s.toList
  cs.length ≤ maxFinitePatternValues &&
    !(cs.contains '{') && !(cs.contains '}')

/-- Enumerate the complete language of the finite regex fragment.
    `star`, complement, non-singleton ranges, and oversized results
    decline with `none`. -/
def finiteRegexLanguage (cap : Nat) : Re → Option (List (List Nat))
  | .empty => some []
  | .eps => some [[]]
  | .ranges rs =>
      if rs.all (fun (lo, hi) => lo == hi) && rs.length ≤ cap then
        some ((rs.map fun (lo, _) => [lo]).eraseDups)
      else none
  | .cat a b => do
      let xs ← finiteRegexLanguage cap a
      let ys ← finiteRegexLanguage cap b
      if xs.length * ys.length ≤ cap &&
          xs.all (fun x => ys.all (fun y => x.length + y.length ≤ cap)) then
        some ((xs.flatMap fun x => ys.map (x ++ ·)).eraseDups)
      else none
  | .alt a b => do
      let xs ← finiteRegexLanguage cap a
      let ys ← finiteRegexLanguage cap b
      if xs.length + ys.length ≤ cap then
        some ((xs ++ ys).eraseDups)
      else none
  | .inter a b => do
      let xs ← finiteRegexLanguage cap a
      let ys ← finiteRegexLanguage cap b
      some (xs.filter ys.contains)
  | .compl _ | .star _ => none

/-- Tail-recursive parser for every pattern facet. A malformed pattern
    facet makes the restriction unsupported rather than silently
    dropping a conjunct. -/
def parsedPatternFacets (facets : List (WfIri × Term)) : Option (List Re) :=
  let rec go : List (WfIri × Term) → List Re → Option (List Re)
  | [], acc => some acc.reverse
  | (f, v) :: rest, acc =>
      if f == facetPattern then
        match v with
        | .literal l =>
            if l.val.datatype == xsdString &&
                finitePatternTextSupported l.val.lexicalForm then
              match XSDPattern.parseXsdPattern l.val.lexicalForm with
              | some r => go rest (r :: acc)
              | none => none
            else none
        | _ => none
      else go rest acc
  go facets []

/-- The complete lexical language of a supported finite conjunction
    of XSD pattern facets. No pattern facet returns `none`. -/
def finitePatternLanguage (facets : List (WfIri × Term)) : Option (List (List Nat)) := do
  let rs ← parsedPatternFacets facets
  match rs with
  | [] => none
  | r :: rest =>
      let first ← finiteRegexLanguage maxFinitePatternValues r
      let rec intersectAll : List Re → List (List Nat) → Option (List (List Nat))
        | [], acc => some acc
        | next :: tail, acc => do
            let nextWords ← finiteRegexLanguage maxFinitePatternValues next
            intersectAll tail (acc.filter nextWords.contains)
      intersectAll rest first

/-- XSD string lexical forms denoted by explicit forbidden terms.
    The `xsd:string` lexical-to-value mapping is the identity. -/
def forbiddenStringWords (excluded : List Term) : List (List Nat) :=
  excluded.filterMap (fun t => match t with
    | .literal l =>
        if l.val.datatype == xsdString then
          some (cpsOfString l.val.lexicalForm)
        else none
    | _ => none) |>.eraseDups

/-- Is a finite string-pattern restriction exhausted by forbidden
    values? Every language member must occur in the forbidden value
    set; unknown regex constructs withhold the verdict. -/
def stringPatternExcluded (d : ClassExpr) (excluded : List Term) : Bool :=
  match d with
  | .dataRestriction dt facets =>
      if dt == xsdString then
        match finitePatternLanguage facets with
        | some words => words.all (forbiddenStringWords excluded).contains
        | none => false
      else false
  | _ => false

end L4Factoidal.OWL
