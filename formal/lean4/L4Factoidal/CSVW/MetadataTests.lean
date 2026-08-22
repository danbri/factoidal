/-
L4Factoidal.CSVW.MetadataTests — build-time checks for the metadata
model and the §5.1.1 inheritance rules.
-/
import L4Factoidal.CSVW.Metadata

namespace L4Factoidal.CSVW

-- §5.1.1: a value on the CHILD wins; otherwise the parent shows through.
private def parent : Inherited := { lang := some "en", null := some "NA" }
private def child  : Inherited := { lang := some "fr" }
#guard (Inherited.override parent child).lang == some "fr"   -- child wins
#guard (Inherited.override parent child).null == some "NA"   -- inherited
#guard (Inherited.override parent {}).lang == some "en"

-- The whole chain: group → table → schema → column.
private def grp : TableGroup :=
  { inherited := { lang := some "en", aboutUrl := some "G", null := some "NA" } }
private def tbl : TableDesc :=
  { url := "t.csv", inherited := { aboutUrl := some "T" } }
private def sch : TableSchema := { inherited := { propertyUrl := some "S" } }
private def col : Column := { inherited := { aboutUrl := some "C" } }

#guard (effectiveInherited grp tbl (some sch) col).aboutUrl == some "C"  -- column wins
#guard (effectiveInherited grp tbl (some sch) col).propertyUrl == some "S"
#guard (effectiveInherited grp tbl (some sch) col).lang == some "en"
#guard (effectiveInherited grp tbl (some sch) col).null == some "NA"
-- With no column override, the table's value reaches the column.
#guard (effectiveInherited grp tbl (some sch) {}).aboutUrl == some "T"
-- With no table override either, the group's does.
#guard (effectiveInherited grp { url := "t.csv" } none {}).aboutUrl == some "G"

-- §5.9: a table's dialect falls back to the group's.
#guard (effectiveDialect { dialect := some { delimiter := some "\t" } }
          { url := "t.csv" }).delimiter == some "\t"
#guard (effectiveDialect { dialect := some { delimiter := some "\t" } }
          { url := "t.csv", dialect := some { delimiter := some ";" } }).delimiter
       == some ";"

-- §5.6 column-name derivation: explicit name, then a language-matched
-- title, then an untagged title, then the positional `_col.N`.
#guard columnName { name := some "explicit", titles := ["T"] } 1 none == "explicit"
#guard columnName { titles := ["T"], titlesLang := [("T", none)] } 1 none == "T"
#guard columnName { titlesLang := [("Titre", some "fr"), ("Title", none)] } 1 (some "fr")
       == "Titre"
#guard columnName { titlesLang := [("Titre", some "fr"), ("Title", none)] } 1 (some "de")
       == "Title"
#guard columnName {} 3 none == "_col.3"

-- Datatype: both forms expose a base name.
#guard (Datatype.named "string").baseName == some "string"
#guard (Datatype.object (some "integer") none none none none none
          none none none none none none none none none).baseName == some "integer"

end L4Factoidal.CSVW
