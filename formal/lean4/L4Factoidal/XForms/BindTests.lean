/-
L4Factoidal.XForms.BindTests — build-time checks for the XForms model
layer.
-/
import L4Factoidal.XForms.Bind

namespace L4Factoidal.XForms

open L4Factoidal.XML

private def inst : Node :=
  .element "data" []
    [ .element "a" [] [.text "2"],
      .element "b" [] [.text "3"],
      .element "sum" [] [.text "0"],
      .element "twice" [] [.text "0"] ]

/-! ## Recalculation runs in DEPENDENCY order

`twice` reads `sum`, which reads `a` and `b`. Running the binds in
declaration order would compute `twice` from the STALE `sum`. -/

private def bindsOk : List Bind :=
  [ { target := "twice", calculate := some "../sum + ../sum" },
    { target := "sum",   calculate := some "../a + ../b" } ]

private def recalcText (bs : List Bind) (name : String) : String :=
  match recalculate bs inst with
  | some (x, _) => getLeafText x name
  | none        => "<document error>"

#guard recalcText bindsOk "sum" == "5"
#guard recalcText bindsOk "twice" == "10"

/-! ## A `calculate` CYCLE is a document error (§7.6.1)

It is rejected by the shape of the recursion, not by a counter: a
cyclic graph has no ready node, so `topoPass` returns `none` without
recursing. -/

private def bindsCycle : List Bind :=
  [ { target := "a", calculate := some "../b" },
    { target := "b", calculate := some "../a" } ]

#guard (topoSort bindsCycle).isNone
#guard recalcText bindsCycle "a" == "<document error>"

/-! A bind whose `calculate` reads its OWN target is a self-cycle. -/
#guard (topoSort [{ target := "a", calculate := some "../a + 1" }]).isNone

/-! ## Dependency edges come from the parsed AST, not from the text

`sum` is a NAME TEST in `../sum`; it is not one inside the string
literal `'sum'`, and a scan of the expression text could not tell
them apart. -/

#guard predsOf bindsOk { target := "x", calculate := some "../sum" } == ["sum"]
#guard predsOf bindsOk { target := "x", calculate := some "'sum'" } == []

/-! ## The `type` MIP — §6.2.1 -/

#guard typeWellformed .integer "-12"
#guard !(typeWellformed .integer "1.5")
#guard typeWellformed .decimal "1.5"
#guard typeWellformed .double "1.5e3"
/-! `NaN`, `INF` and `-INF` are VALUES of the double type, not error
    states. A lexical check that rejected them would reject a legal
    document. -/
#guard typeWellformed .double "NaN"
#guard typeWellformed .boolean "1"
#guard !(typeWellformed .boolean "yes")
/-! An unrecognised QName validates as INVALID: an explicit "we do not
    know", never a silent pass. -/
#guard !(typeWellformed .unsupported "anything")
#guard mipTypeOfQName "xs:date" == MipType.unsupported
#guard mipTypeOfQName "" == MipType.absent

/-! ## Validity — §7.4 exempts a non-relevant node -/

private def instBad : Node :=
  .element "data" [] [ .element "n" [] [.text "not a number"] ]

private def validityOf (bs : List Bind) (x : Node) : List Bool :=
  match recalculate bs x with
  | some (_, vs) => vs.map (·.valid)
  | none         => []

#guard validityOf [{ target := "n", mipType := .integer }] instBad == [false]
#guard validityOf [{ target := "n", mipType := .integer,
                     relevant := some "false()" }] instBad == [true]

/-! ## A `required` node with an empty value is invalid (§7.5) -/

private def instEmpty : Node := .element "data" [] [ .element "n" [] [] ]

#guard validityOf [{ target := "n", required := some "true()" }] instEmpty == [false]
#guard validityOf [{ target := "n" }] instEmpty == [true]

/-! ## Reading a bind sheet -/

private def sheet : Node :=
  .element "binds" []
    [ .element "bind" [⟨"nodeset", "sum"⟩, ⟨"calculate", "../a + ../b"⟩,
                       ⟨"type", "xsd:integer"⟩] [],
      .element "bind" [⟨"ref", "a"⟩] [],
      .element "bind" [⟨"id", "no-target"⟩] [] ]

#guard (decodeBinds sheet).length == 2
#guard ((decodeBinds sheet).map (·.target)) == ["sum", "a"]
#guard ((decodeBinds sheet).head?.map (·.mipType)) == some MipType.integer

end L4Factoidal.XForms
