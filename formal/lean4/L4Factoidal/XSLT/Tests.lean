/-
L4Factoidal.XSLT.Tests — build-time checks for template priorities and
conflict resolution.
-/
import L4Factoidal.XSLT.Templates

namespace L4Factoidal.XSLT

-- The four default-priority levels, x10-scaled so comparisons are
-- exact integers rather than float ties.
#guard altPriority "*" == -5
#guard altPriority "node()" == -5
#guard altPriority "text()" == -5
#guard altPriority "pfx:*" == -2        -- namespace wildcard
#guard altPriority "@pfx:*" == -2
#guard altPriority "foo" == 0           -- QName
#guard altPriority "foo/bar" == 5       -- compound
#guard altPriority "foo[@x]" == 5       -- predicate

-- ORDER OF CHECKS: the compound test comes BEFORE the wildcard test,
-- so `foo/*` scores 5, not -5. Reversing them makes compound patterns
-- lose to bare ones.
#guard altPriority "foo/*" == 5

-- A `|` alternation takes the HIGHEST alternative.
#guard defaultPriority "foo|*" == 0
#guard defaultPriority "*|node()" == -5
#guard defaultPriority "a/b|*" == 5

-- An explicit priority overrides the default.
#guard templatePriority { matchPattern := "*", priority := some 90 } == 90
#guard templatePriority { matchPattern := "*" } == -5

-- CONFLICT RESOLUTION. Import precedence wins OUTRIGHT, whatever the
-- priority — checking priority first is the classic bug, because an
-- imported specific pattern would then beat the importing
-- stylesheet's override and defeat xsl:import entirely.
private def imported : Template :=
  { matchPattern := "foo/bar", importPrec := 0 }    -- priority 5
private def importing : Template :=
  { matchPattern := "*", importPrec := 1 }          -- priority -5
#guard better importing imported
#guard !(better imported importing)

-- At equal precedence, priority decides.
private def specific : Template := { matchPattern := "foo/bar", importPrec := 1 }
private def general  : Template := { matchPattern := "*", importPrec := 1 }
#guard better specific general

-- At equal precedence AND priority, the LAST declared wins.
private def firstDecl : Template := { matchPattern := "foo", docOrder := 0 }
private def lastDecl  : Template := { matchPattern := "foo", docOrder := 1 }
#guard better lastDecl firstDecl
#guard !(better firstDecl lastDecl)

-- Selection picks the winner among matching templates in the mode.
private def alwaysMatch (_ : String) : Bool := true
#guard (pickTemplate [general, specific] "" alwaysMatch) == some specific
-- A template in a DIFFERENT mode is not a candidate at all.
private def otherMode : Template := { matchPattern := "foo/bar", mode := "m" }
#guard (pickTemplate [general, otherMode] "" alwaysMatch) == some general
#guard (pickTemplate [otherMode] "m" alwaysMatch) == some otherMode
-- A name-only template never matches by pattern.
#guard (pickTemplate [{ name := "n" }] "" alwaysMatch) == none
#guard (pickTemplate [] "" alwaysMatch) == none

-- Named lookup resolves by IMPORT PRECEDENCE, not document order.
private def namedLow  : Template := { name := "t", importPrec := 0, docOrder := 9 }
private def namedHigh : Template := { name := "t", importPrec := 5, docOrder := 0 }
#guard findNamed [namedLow, namedHigh] "t" == some namedHigh
#guard findNamed [namedLow] "missing" == none

-- Pattern steps: `//x` is RELATIVE descendant, `/x` is ROOT-anchored.
-- The two differ by one slash and mean different things.
#guard (parseSteps "/foo").1 == true
#guard (parseSteps "//foo").1 == false
#guard (parseSteps "foo").1 == false
#guard (parseSteps "//foo").2 == [(.descendant, "foo")]
#guard (parseSteps "/foo/bar").2 == [(.child, "foo"), (.child, "bar")]
-- `child::` is normalised away, since it is the default axis.
#guard (parseSteps "child::foo").2 == [(.child, "foo")]

end L4Factoidal.XSLT
