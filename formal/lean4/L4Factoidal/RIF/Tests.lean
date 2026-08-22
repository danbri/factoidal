/-
L4Factoidal.RIF.Tests — build-time checks for RIF Core forward
chaining.
-/
import L4Factoidal.RIF.Core

namespace L4Factoidal.RIF
open L4Factoidal.RDF

private def iri! (s : String) : WfIri := if h : isIri s then ⟨s, h⟩ else ⟨"http://x", by decide⟩
private def I (s : String) : Term := .iri (iri! s)
private def S (s : String) : Subject := .iri (iri! s)

private def parent : String := "http://ex/parent"
private def ancestor : String := "http://ex/ancestor"

private def facts : List Triple :=
  [ ⟨S "http://ex/a", iri! parent, I "http://ex/b"⟩,
    ⟨S "http://ex/b", iri! parent, I "http://ex/c"⟩ ]

-- Rule 1: parent(?x,?y) → ancestor(?x,?y)
private def r1 : Rule :=
  { head := .triple (.var ⟨"x"⟩) (.const (I ancestor)) (.var ⟨"y"⟩)
    body := .atom (.triple (.var ⟨"x"⟩) (.const (I parent)) (.var ⟨"y"⟩)) }

-- Rule 2: ancestor(?x,?y) ∧ parent(?y,?z) → ancestor(?x,?z)
private def r2 : Rule :=
  { head := .triple (.var ⟨"x"⟩) (.const (I ancestor)) (.var ⟨"z"⟩)
    body := .and [ .atom (.triple (.var ⟨"x"⟩) (.const (I ancestor)) (.var ⟨"y"⟩)),
                   .atom (.triple (.var ⟨"y"⟩) (.const (I parent)) (.var ⟨"z"⟩)) ] }

private def prog : Program := { rules := [r1, r2] }

-- Direct consequence.
#guard entails prog facts ⟨S "http://ex/a", iri! ancestor, I "http://ex/b"⟩ 10

-- TRANSITIVE consequence: requires the second rule to consume the
-- first rule's own output, which is what makes this a fixed point
-- rather than one pass.
#guard entails prog facts ⟨S "http://ex/a", iri! ancestor, I "http://ex/c"⟩ 10

-- A non-consequence is not entailed.
#guard !(entails prog facts ⟨S "http://ex/c", iri! ancestor, I "http://ex/a"⟩ 10)

-- The closure terminates BEFORE the bound and reports that it did.
#guard (closure prog facts 10).2 == false

-- With too few rounds the bound IS reached, and the flag says so —
-- a caller must not read entailment off a truncated closure without
-- seeing this.
#guard (closure prog facts 1).2 == true

-- A repeated variable across body atoms acts as a JOIN, not as two
-- independent matches: `y` must be the same term in both.
#guard (Subst.extend [("y", I "http://ex/b")] "y" (I "http://ex/b")).isSome
#guard (Subst.extend [("y", I "http://ex/b")] "y" (I "http://ex/c")).isNone

-- An `equal` body succeeds only on identical ground terms.
private def eqRule : Rule :=
  { head := .triple (.const (I "http://ex/s")) (.const (I "http://ex/p")) (.const (I "http://ex/o"))
    body := .equal (.const (I "http://ex/a")) (.const (I "http://ex/a")) }
#guard entails { rules := [eqRule] } [] ⟨S "http://ex/s", iri! "http://ex/p", I "http://ex/o"⟩ 5
private def neqRule : Rule := { eqRule with body := .equal (.const (I "http://ex/a")) (.const (I "http://ex/b")) }
#guard !(entails { rules := [neqRule] } [] ⟨S "http://ex/s", iri! "http://ex/p", I "http://ex/o"⟩ 5)

-- A head whose predicate does not ground to an IRI produces no
-- triple rather than a malformed one.
#guard instantiateHead [] (.triple (.const (I "http://ex/s")) (.var ⟨"unbound"⟩) (.const (I "http://ex/o"))) == none
-- A literal subject is not a triple.
#guard instantiateHead [] (.triple (.const (.literal (Literal.string "lit")))
         (.const (I "http://ex/p")) (.const (I "http://ex/o"))) == none

-- An unevaluated external grounds to NOTHING rather than a
-- placeholder.
#guard groundTm [] (.external "http://ex/f" []) == none

end L4Factoidal.RIF
