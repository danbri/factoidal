/-
L4Factoidal.SPARQL.Diagnostics — human-readable trace strings.

Port of `formal/fstar/SPARQL.Diagnostics.fst` (78 lines).

## What these strings are, and what they are not

They are stderr trace lines for a person reading a run. They are NOT a
wire format, NOT a result serialisation, and nothing parses them back.
The F\* module's reason for keeping them beside the types they describe
is the totality check: when the described type grows a case, the
renderer stops compiling instead of silently printing nothing for the
new case. Lean's exhaustiveness check does the same job, so the reason
carries over unchanged.

## Where this port DIVERGES, and why

The F\* module's first renderer is `graph_backend_kind_string`, which
prints a `graph_backend` constructor name — `GB_List`, `GB_HDT`,
`GB_COTTAS`, and `GB_Union[...]` with its children spelled out inside
brackets. Its stated purpose is to let a person correlate a trace line
with the `--data` / `--data-cottas` / `--data-hdt` flags that produced
it.

There is no such constructor here. `RDF.StoreCapabilities` replaced the
backend tag with a record of functions, precisely so that no caller has
to ask which kind of store it holds — that is the change the seam
exists to make. So a constructor-name renderer has nothing to read.

What a person still needs from a trace line is the same information the
tag used to carry: can this store answer for named graphs, can it be
written to, is its estimate exact, can it report a decode failure. Those
are `StoreCapsFlags`, and they are on the record. `storeCapsKindString`
renders them, and `datasetCapsKindString` renders a whole dataset the
way `dataset_backend_kind_string` did — the default's description plus
the named-graph count.

This trades a name for the properties the name stood for. A trace line
now says what the store CAN DO rather than what it IS, which is the
question the planner asks. What it loses is the ability to distinguish
two stores with identical flags — an HDT file and a COTTAS base both
read `-named -update +stream +exact -decodefail`. A caller that needs to
tell those apart needs a label the seam does not carry, and this module
will not invent one.

`queryFormString` is a direct port with no divergence.
-/
import L4Factoidal.RDF.StoreCapabilities
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Store capability flags as a trace line -/

/-- One flag, rendered as `+name` or `-name`. -/
def flagString (name : String) (on : Bool) : String :=
  (if on then "+" else "-") ++ name

/-- The five policy answers a `StoreCaps` advertises, in the order they
appear on `StoreCapsFlags`. This replaces the F\* backend-constructor
name; the header says what that trade costs. -/
def storeCapsFlagsString (f : StoreCapsFlags) : String :=
  String.intercalate " "
    [ flagString "named" f.supportsNamedGraphs
    , flagString "update" f.supportsUpdate
    , flagString "stream" f.streamingShapes
    , flagString "exact" f.estimateIsExact
    , flagString "decodefail" f.canReportDecodeFail ]

/-- A read seam, rendered as `Store[<flags>]`. -/
def storeCapsKindString (c : StoreCaps) : String :=
  "Store[" ++ storeCapsFlagsString c.flags ++ "]"

/-- A whole dataset, in the shape the F\* `dataset_backend_kind_string`
used: the default graph's description, then how many named graphs. -/
def datasetCapsKindString (d : DatasetCaps) : String :=
  "{default=" ++ storeCapsKindString d.default
    ++ "; named=" ++ toString d.named.length ++ " graph(s)}"

/-- The named graphs by IRI, for a trace that has to say WHICH graphs a
dataset carries rather than how many. The F\* module had no counterpart;
`datasetCapsListGraphs` made it one line. -/
def datasetCapsGraphsString (d : DatasetCaps) : String :=
  "[" ++ String.intercalate "," (datasetCapsListGraphs d.named) ++ "]"

/-! ## Query form -/

/-- `ASK` / `SELECT` / `CONSTRUCT` / `DESCRIBE`. -/
def queryFormString (q : Query) : String :=
  match q.form with
  | .ask         => "ASK"
  | .select _    => "SELECT"
  | .construct _ => "CONSTRUCT"
  | .describe _  => "DESCRIBE"

/-! ## Pinned behaviour -/

section Pins

private def capsMem : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [])

/-! The in-memory store: update yes, estimate exact, decode failure not
reportable. Reading the flags off the record is the whole renderer, so a
wrong line here is a wrong record. -/
#guard storeCapsKindString capsMem
      == "Store[+named +update +stream +exact -decodefail]"

/-! A union differs from the in-memory store on exactly two flags: its
summed estimate is not claimed exact, and it has no write path. It does
gain the ability to report a member's decode failure. -/
#guard storeCapsKindString (unionCaps [capsMem, capsMem])
      == "Store[+named -update +stream -exact +decodefail]"

/-! Two stores with the same flags render the same. This is the loss the
header names, pinned so it cannot be mistaken for a defect later. -/
#guard storeCapsKindString capsMem
      == storeCapsKindString (capsOfIndexed (OWL.RL.Index.ofGraph []))

private def dsOne : DatasetCaps :=
  { default := capsMem
  , named := [("http://example/g", capsMem), ("http://example/h", capsMem)] }

#guard datasetCapsKindString dsOne
      == "{default=Store[+named +update +stream +exact -decodefail]; named=2 graph(s)}"

#guard datasetCapsGraphsString dsOne == "[http://example/g,http://example/h]"

#guard queryFormString (mkQuery .ask (.bgp [])) == "ASK"
#guard queryFormString (mkQuery (.construct []) (.bgp [])) == "CONSTRUCT"
#guard queryFormString (mkQuery (.describe []) (.bgp [])) == "DESCRIBE"

end Pins

end L4Factoidal.SPARQL
