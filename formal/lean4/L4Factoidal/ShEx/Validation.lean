/-
L4Factoidal.ShEx.Validation — node-constraint satisfaction, ported
from `formal/fstar/ShEx.Validation.fst`.

Spec: ShEx 2.1 Semantics §5.4 `satisfies2` for node constraints.

This slice covers NODE constraints — nodeKind, datatype, string
facets, value sets and numeric facets — over an RDF term. Shape
satisfaction (triple expressions, cardinality matching, EXTRA and
CLOSED) builds on it and is the next increment.
-/
import L4Factoidal.ShEx.Schema
import L4Factoidal.RDF.Core
import L4Factoidal.ShEx.XsdLexical

namespace L4Factoidal.ShEx

open L4Factoidal.RDF

/-! ## Semantic actions

ShEx 2.1 §5.10: a semantic action is code in an extension language,
and an implementation that does not know the language cannot evaluate
it — an unknown extension's action neither passes nor fails, so it is
ignored. The ONE extension the validation corpus relies on is the Test
extension, whose whole language is `print(...)` and `fail(...)`:
`fail` makes the containing expression not match, `print` does
nothing an implementation can observe.

Reading `semActs` at all is new. `FromJson.lean` was passing `[]` for
every `semActs` slot, so `%<...Test/>{ fail(s) %}` was invisible and
four `*fail_abort* ` entries of the suite reported conformance for
schemas that abort. -/

/-- The one extension whose language this implementation knows. -/
def testExtension : String := "http://shex.io/extensions/Test/"

private def dropLeadingSpace (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n'))

/-- Does this action ABORT? Only a Test-extension `fail(...)` does. -/
def semActFails (a : SemAct) : Bool :=
  a.name == testExtension && (dropLeadingSpace (a.code.getD "")).startsWith "fail"

def anySemActFails (as : List SemAct) : Bool := as.any semActFails

/-- §5.4.1 nodeKind. `nonLiteral` admits IRIs and blank nodes. -/
def matchesNodeKind (k : NodeKind) (t : Term) : Bool :=
  match k, t with
  | .iri,        .iri _     => true
  | .bnode,      .bnode _   => true
  | .literal,    .literal _ => true
  | .nonLiteral, .iri _     => true
  | .nonLiteral, .bnode _   => true
  | _, _ => false

/-- The lexical form a facet applies to. -/
def lexicalOf (t : Term) : String :=
  match t with
  | .literal l => l.val.lexicalForm
  | .iri i     => i.val
  | .bnode b   => b
  | _          => ""

/-- §5.4.3 datatype: only literals can match. -/
def matchesDatatype (dt : String) (t : Term) : Bool :=
  match t with
  | .literal l => l.val.datatype.val == dt
  | _          => false

/-- §5.4.4 string facets, measured in CHARACTERS not bytes — a length
    facet over a multi-byte lexical form would otherwise be silently
    wrong. -/
def matchesLengthFacets (nc : NodeConstraint) (t : Term) : Bool :=
  let n : Int := (lexicalOf t).toList.length
  (match nc.length with    | some l => n == l | none => true) &&
  (match nc.minLength with | some l => n ≥ l  | none => true) &&
  (match nc.maxLength with | some l => n ≤ l  | none => true)

/-- Exact object-value match. An ABSENT language or datatype in the
    constraint means "unconstrained", not "must be absent". -/
def matchesObjectValue (ov : ObjectValue) (t : Term) : Bool :=
  match ov, t with
  | .iri v, .iri i => i.val == v
  | .literal v lang dt, .literal l =>
      l.val.lexicalForm == v &&
      (match lang with | some g => l.val.langTag == some g | none => true) &&
      (match dt with   | some d => l.val.datatype.val == d | none => true)
  | _, _ => false

/-- A LANGUAGE stem matches on SUBTAG boundaries, not on characters.

    BCP 47 / RFC 4647 basic filtering: the range `fr` matches the tag
    `fr` and every tag that extends it with a further subtag — `fr-be`,
    `fr-CA` — and matches `frc` (Cajun French) not at all, because
    `frc` is a DIFFERENT primary subtag rather than a refinement of
    `fr`. A character prefix test admitted it, so `[@fr~]` accepted
    `"septante"@frc` (`1val1languageStem_failLAtfrc`), and the
    exclusion `- @fr-be~` removed `"septante"@fr-bel`, which it does
    not cover either.

    The empty range matches every language tag, which is how ShEx
    writes `@~`. -/
def langRangeMatches (range tag : String) : Bool :=
  let r := range.toLower
  let g := tag.toLower
  r.isEmpty || g == r || g.startsWith (r ++ "-")

/-- Stem matching: wildcard matches anything; an IRI or literal stem
    is a character PREFIX, and a language stem is a subtag range. -/
def matchesStem (kind : VsvKind) (s : Stem) (t : Term) : Bool :=
  let target := match kind, t with
    | .iri,      .iri i     => some i.val
    | .literal,  .literal l => some l.val.lexicalForm
    | .language, .literal l => l.val.langTag
    | _, _ => none
  match target, s with
  | none,   _         => false
  | some _, .wildcard => true
  | some v, .plain p  =>
      match kind with
      | .language => langRangeMatches p v
      | _         => v.startsWith p

/-- Does an exclusion remove this term? A nested STEM excludes a whole
    prefix, not one value — `IriStemRange` with an `IriStem` exclusion
    is how ShEx writes "everything under `…/v` except everything under
    `…/v1`". -/
def matchesExclusion (k : VsvKind) (e : Exclusion) (t : Term) : Bool :=
  match e with
  | .value ov => matchesObjectValue ov t
  | .lang tag => (match t with
                  | .literal l => l.val.langTag == some tag
                  | _          => false)
  | .stem p   => matchesStem k (.plain p) t

/-- §5.4.5 value set membership. An EXCLUSION removes a term the stem
    would otherwise have admitted. -/
def matchesValueSetValue (v : ValueSetValue) (t : Term) : Bool :=
  match v with
  | .object ov => matchesObjectValue ov t
  | .stem k s  => matchesStem k s t
  | .stemRange k s excl =>
      matchesStem k s t && !(excl.any (fun e => matchesExclusion k e t))
  | .language tag =>
      match t with
      | .literal l => l.val.langTag == some tag
      | _          => false

def matchesValues (vs : List ValueSetValue) (t : Term) : Bool :=
  vs.isEmpty || vs.any (fun v => matchesValueSetValue v t)

/-- Split a char list on the first '.', or return it whole. -/
private def splitOnDot (l : List Char) : List (List Char) :=
  match l.findIdx? (· == '.') with
  | some i => [l.take i, l.drop (i + 1)]
  | none   => [l]

/-- Compare two decimal lexemes EXACTLY, without a float. `none` when
    either side is not a plain decimal — the caller then treats the
    facet as unsatisfied rather than guessing an ordering. -/
def compareDecimal (a0 b0 : String) : Option Ordering :=
  -- An `xsd:double` writes its value in E-notation, and the facet it
  -- is compared against may not. Folding the exponent into the digits
  -- FIRST is what lets `1.0E2` be compared with `100`; without it the
  -- parse below failed, the comparison returned `none`, and the facet
  -- was reported unsatisfied — twelve entries of the suite, every one
  -- a POSITIVE test that a correct value was rejected.
  let a := L4Factoidal.CSVW.resolveExponent a0
  let b := L4Factoidal.CSVW.resolveExponent b0
  let parse (s : String) : Option (Bool × List Char × List Char) :=
    let neg := s.startsWith "-"
    let body := if neg || s.startsWith "+" then s.toList.drop 1 else s.toList
    let isD := fun (c : Char) => '0' ≤ c && c ≤ '9'
    match splitOnDot body with
    | [ip]     => if !ip.isEmpty && ip.all isD then some (neg, ip, []) else none
    | [ip, fp] => if (!ip.isEmpty || !fp.isEmpty) && ip.all isD && fp.all isD
                  then some (neg, ip, fp) else none
    | _        => none
  match parse a, parse b with
  | some (na, ia, fa), some (nb, ib, fb) =>
      let iw := max ia.length ib.length
      let fw := max fa.length fb.length
      let ka := List.replicate (iw - ia.length) '0' ++ ia ++ fa ++ List.replicate (fw - fa.length) '0'
      let kb := List.replicate (iw - ib.length) '0' ++ ib ++ fb ++ List.replicate (fw - fb.length) '0'
      let magnitude := compare (String.ofList ka) (String.ofList kb)
      some (match na, nb with
        | false, false => magnitude
        | true,  true  => magnitude.swap
        | true,  false => .lt
        | false, true  => .gt)
  | _, _ => none

private def cmpOk (facet : Option String) (lex : String) (ok : Ordering → Bool) : Bool :=
  match facet with
  | none   => true
  | some f => match compareDecimal lex f with
              | some o => ok o
              | none   => false

/-- §5.4.6 numeric facets. Only literals carry them, and a
    non-numeric lexical form FAILS rather than being coerced. -/
def matchesNumericFacets (nc : NodeConstraint) (t : Term) : Bool :=
  let anySet := nc.minInclusive.isSome || nc.maxInclusive.isSome ||
                nc.minExclusive.isSome || nc.maxExclusive.isSome
  if !anySet then true
  else match t with
    | .literal l =>
        let lex := l.val.lexicalForm
        cmpOk nc.minInclusive lex (fun o => o != .lt) &&
        cmpOk nc.maxInclusive lex (fun o => o != .gt) &&
        cmpOk nc.minExclusive lex (fun o => o == .gt) &&
        cmpOk nc.maxExclusive lex (fun o => o == .lt)
    | _ => false

/-- §5.4.3, second half: a `datatype` constraint requires the literal's
    LEXICAL FORM to be in that datatype's lexical space, not merely
    that the datatype IRI matches.

    Checking only the IRI accepted `"1.0"^^xsd:integer`,
    `"NaN"^^xsd:decimal` and `"+1"^^xsd:negativeInteger` — 144 entries
    of the validation suite, every one of them a node the schema says
    must NOT satisfy the shape. A validator that accepts everything
    passes every positive test, which is why the negative half of a
    suite is where a gap like this shows.

    A datatype whose lexical space `inXsdLexicalSpace` does not decide
    imposes no check, and that stays visible as a `none` rather than
    becoming a silent `true`. -/
def matchesDatatypeLexical (dt : String) (t : Term) : Bool :=
  match t with
  | .literal l =>
      (match inXsdLexicalSpace dt l.val.lexicalForm with
       | some ok => ok
       | none    => true)
  | _ => false

/-- §5.4.5 `pattern`: an XPath regular expression, matched the way
    `fn:matches` matches — a search, with `^` and `$` as anchors and
    the `flags` string passed through. A node that is not a literal or
    an IRI has no string to match. -/
def matchesPattern (nc : NodeConstraint) (t : Term) : Bool :=
  match nc.pattern with
  | none     => true
  | some pat =>
      let flags := nc.flags.getD ""
      match t with
      | .literal l => L4Factoidal.Regex.regexMatch l.val.lexicalForm pat flags
      | .iri i     => L4Factoidal.Regex.regexMatch i.val pat flags
      -- A BLANK NODE matches on its label. That is not obvious — a
      -- label is not part of the graph's meaning — but the suite
      -- states it: `1nonliteralPattern` gives a `pattern` under a
      -- `nonliteral` node kind and expects a blank node to match.
      | .bnode b   => L4Factoidal.Regex.regexMatch b pat flags
      | _          => false

/-- §5.4.6 `totalDigits` / `fractionDigits`. A literal whose lexical
    form is not a decimal FAILS the facet rather than being coerced,
    which is the rule the ordering facets already follow.

    The facets are defined on `xsd:decimal` and the types derived from
    it, and on nothing else, so the literal's DATATYPE decides whether
    they can apply at all — counting digits in the lexical form was
    not enough. `"1.23456"^^xsd:float` has no digit count (its value
    space is the IEEE binary floats), and `"1.2345"^^xsd:integer` is
    not in `xsd:integer`'s lexical space, so it has no value to count
    the digits of. Both were being accepted by reading the characters
    and ignoring the datatype. -/
def matchesDigitFacets (nc : NodeConstraint) (t : Term) : Bool :=
  if nc.totalDigits.isNone && nc.fractionDigits.isNone then true
  else match t with
    | .literal l =>
        let lex := l.val.lexicalForm
        if !(digitFacetsApply l.val.datatype.val lex) then false else
        (match nc.totalDigits with
         | none   => true
         | some d => match totalDigitsOf lex with
                     | some n => (n : Int) ≤ d
                     | none   => false) &&
        (match nc.fractionDigits with
         | none   => true
         | some d => match fractionDigitsOf lex with
                     | some n => (n : Int) ≤ d
                     | none   => false)
    | _ => false

/-- §5.4 node-constraint satisfaction: every present facet must hold.
    An EMPTY constraint is satisfied by any node. -/
def satisfiesNodeConstraint (nc : NodeConstraint) (t : Term) : Bool :=
  (match nc.nodeKind with | some k => matchesNodeKind k t | none => true) &&
  (match nc.datatype with
   | some d => matchesDatatype d t && matchesDatatypeLexical d t
   | none   => true) &&
  matchesLengthFacets nc t &&
  matchesValues nc.values t &&
  matchesNumericFacets nc t &&
  matchesPattern nc t &&
  matchesDigitFacets nc t

end L4Factoidal.ShEx
