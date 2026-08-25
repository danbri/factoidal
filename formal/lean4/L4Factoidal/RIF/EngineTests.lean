/-
L4Factoidal.RIF.EngineTests — build-time checks for the RIF Core
slice.
-/
import L4Factoidal.RIF.Engine
import L4Factoidal.RIF.Ps

namespace L4Factoidal.RIF

/-! ## The presentation syntax -/

private def okDoc : String :=
  "Document( Prefix(ex <http://example.org/#>) Group( " ++
  "Forall ?x ( ex:q(?x) :- ex:p(?x) ) ex:p(ex:a) ) )"

#guard (parseDocument okDoc).toOption.isSome
#guard (match parseDocument okDoc with | .ok d => d.rules.length | _ => 0) == 2

-- `(* … *)` is an ANNOTATION, not a comment, and it carries no truth
-- (`Non-Annotation_Entailment`). Skipping it is right; treating `(`
-- as an open paren made every annotated document unparsable.
#guard (parseDocument
  "Document( (* <http://ex/a> *) Group( <http://ex/p>(<http://ex/a>) ) )").toOption.isSome

-- A frame written without spaces is ordinary RIF: `-` is a name
-- character, so `ex:a->1` scanned as the name `ex:a-` before the
-- name scanner learned to stop at an arrow.
#guard (parseFormulaText { prefixes := [("ex", "http://ex/")] } "ex:o[ex:a->1]").toOption.isSome

-- A conclusion is a BARE FORMULA with no prologue.
#guard (parseFormulaText { prefixes := [("ex", "http://ex/")] } "ex:a # ex:D").toOption.isSome

/-! ## Safeness (RIF Core)

A head variable the body never binds makes the document ill-formed,
and a parser cannot see it. Boundness PROPAGATES: `?x = ?y` binds
`?y` once `?x` is, and `pred:iri-string` binds either side from the
other. -/

private def safeOf (src : String) : Bool :=
  match parseDocument src with
  | .ok d    => documentSafe d.rules
  | .error _ => false

#guard safeOf ("Document( Prefix(ex <http://ex/>) Group( " ++
  "Forall ?x ( ex:p(?x) :- ex:q(?x) ) ) )")
-- `?y` is in the head and nothing binds it.
#guard !(safeOf ("Document( Prefix(ex <http://ex/>) Group( " ++
  "Forall ?x ?y ( ex:p(?y) :- ex:q(?x) ) ) )"))
-- ...but an equality chain does bind it (Core_Safeness_2).
#guard safeOf ("Document( Prefix(ex <http://ex/>) Group( " ++
  "Forall ?x ?y ?z (ex:p(?z) :- And(ex:q(?x) ?x=?y ?y=?z)) ) )")
-- ...and so does a BINDING built-in (Core_Safeness_3).
#guard safeOf ("Document( Prefix(ex <http://ex/>) Prefix(pred " ++
  "<http://www.w3.org/2007/rif-builtin-predicate#>) Group( " ++
  "Forall ?x ?z (ex:p(?x) :- And( ex:q(?z) External(pred:iri-string(?x ?z)))) ) )")
-- A variable outside the `Forall` is free, and a free variable is
-- not RIF Core (No_free_variables).
#guard !(safeOf ("Document( Prefix(ex <http://ex/>) Group( " ++
  "Forall ?x ( ex:p(?x) :- ex:q(?y) ) ) )"))

/-! ## Built-ins: three answers

`unknown` is not `no`. A rule whose body needs a built-in this port
does not decide cannot fire, and the entailment is then UNDECIDED. -/

private def xsI (l : String) : String := xsdNs ++ l

-- RIF-DTB asks about the VALUE SPACE, not the datatype IRI:
-- `"1"^^xs:integer` IS a literal of `xs:decimal`.
#guard evalPred "is-literal-decimal" [gLit "1" (xsI "integer")] == .yes
#guard evalPred "is-literal-integer" [gLit "1" (xsI "integer")] == .yes
-- ...but the families do not overlap.
#guard evalPred "is-literal-double" [gLit "1" (xsI "integer")] == .no
#guard evalPred "is-literal-not-boolean" [gStr "foo"] == .yes
-- A plain literal with an EMPTY language tag is in `xs:string`.
#guard evalPred "is-literal-string" [.const "Hello world@" (rdfNs ++ "PlainLiteral")] == .yes
#guard evalPred "is-literal-string" [.const "Hello world@en" (rdfNs ++ "PlainLiteral")] == .no

-- `1` and `true` are the SAME boolean value.
#guard evalPred "boolean-less-than" [gLit "0" (xsI "boolean"), gLit "1" (xsI "boolean")] == .yes
#guard evalPred "boolean-equal" [gLit "1" (xsI "boolean"), gLit "true" (xsI "boolean")] == .yes

-- `pred:literal-not-identical` compares the PAIR, so the same lexical
-- form in two symbol spaces is two constants.
#guard evalPred "literal-not-identical" [gLit "1" (xsI "integer"), gLit "1" (xsI "string")] == .yes
#guard evalPred "literal-not-identical" [gLit "1" (xsI "integer"), gLit "1" (xsI "integer")] == .no

-- A built-in outside the slice is `unknown`, and the engine must not
-- read that as `no`.
#guard evalPred "add-dayTimeDuration-to-date" [gStr "x", gStr "y"] == .unknown

/-! ## Local constants are DOCUMENT-scoped

`_p` in a premise and `_p` in a conclusion are different symbols
(`Local_Predicate`, `Local_Constant`). -/

#guard (match qualifyTm "a" (.const "p" localSpace) with
        | .const l s => l == "a#p" && s == localSpace | _ => false)
#guard (match qualifyTm "a" (.const "p" iriSpace) with
        | .const l s => l == "p" && s == iriSpace | _ => false)

end L4Factoidal.RIF
