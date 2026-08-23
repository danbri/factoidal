/-
L4Factoidal.SPARQL.Explain — the `--explain` dump's types and renderers.

Port of `formal/fstar/SPARQL.Explain.fst` (104 lines). Migrated in the
F\* tree out of `factoidal_explain.ml`, because iron rule #11 keeps
rendering logic out of glue.

What the module owns: the `BoundStatus` classification of a
triple-pattern position, its textual and JSON renderers, the per-pattern
explain row, and that row's JSON renderer.

What it does NOT own: the estimator loop that builds rows from a store.
The F\* header records that as still in OCaml, blocked on time-budget
infrastructure. `L4Factoidal.SPARQL.TimeBudget` is now ported, so the
Lean tree's version of that block is lifted — but the estimator needs a
store, and `SPARQL11.Store` is not ported, so the loop stays absent here
for a different reason than in the F\* tree. Worth stating rather than
leaving as a silent shortfall.
-/
import L4Factoidal.SPARQL.JsonEscape
import L4Factoidal.RDF.Pretty

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- How a triple-pattern position stands relative to the store's
    dictionary. -/
inductive BoundStatus where
  /-- `?varname` — unbound. -/
  | var (name : String)
  /-- Concrete, present in the dictionary. -/
  | hit (term : String)
  /-- Concrete and ABSENT from the dictionary. This is the diagnostic
      one: the result set is definitely empty for any join through this
      pattern. -/
  | miss (term : String)
  /-- Concrete but there is no dictionary for this column — a literal in
      predicate position, a blank node where the column expects an
      IRI. -/
  | other (term : String)
  deriving Repr, DecidableEq, Inhabited

def bsString : BoundStatus → String
  | .var v   => "?" ++ v ++ " (free)"
  | .hit s   => s ++ " [hit]"
  | .miss s  => s ++ " [MISS — term not in dictionary; result definitely empty]"
  | .other s => s ++ " [non-encodable]"

def bsJson : BoundStatus → String
  | .var v   => "{\"kind\":\"var\",\"name\":\"" ++ jsonEscape v ++ "\"}"
  | .hit s   => "{\"kind\":\"hit\",\"term\":\"" ++ jsonEscape s ++ "\"}"
  | .miss s  => "{\"kind\":\"miss\",\"term\":\"" ++ jsonEscape s ++ "\"}"
  | .other s => "{\"kind\":\"other\",\"term\":\"" ++ jsonEscape s ++ "\"}"

/-- One explain row. Data only. -/
structure TpExplain where
  label        : String
  tp           : TriplePattern
  sStatus      : BoundStatus
  pStatus      : BoundStatus
  oStatus      : BoundStatus
  boundBuilt   : Bool
  predPresent  : Option Bool
  estimate     : Int
  deriving Repr

/-- `Option Bool` as the JSON literals `null` / `true` / `false`. -/
def optBoolJson : Option Bool → String
  | none       => "null"
  | some true  => "true"
  | some false => "false"

def tpxJson (tpx : TpExplain) : String :=
  "{\"label\":\"" ++ jsonEscape tpx.label
  ++ "\",\"pattern\":\"" ++ jsonEscape (triplePatternShortExplain tpx.tp)
  ++ "\",\"s\":" ++ bsJson tpx.sStatus
  ++ ",\"p\":" ++ bsJson tpx.pStatus
  ++ ",\"o\":" ++ bsJson tpx.oStatus
  ++ ",\"bound_built\":" ++ (if tpx.boundBuilt then "true" else "false")
  ++ ",\"predicate_present\":" ++ optBoolJson tpx.predPresent
  ++ ",\"estimate\":" ++ toString tpx.estimate
  ++ "}"

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def ei (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

#guard bsString (.var "s") == "?s (free)"
#guard bsString (.hit "rdf:type") == "rdf:type [hit]"
#guard bsString (.other "\"x\"") == "\"x\" [non-encodable]"

/-! `miss` is the row a person reads the dump FOR, so its text says what
    it means rather than just naming the state. -/

#guard (bsString (.miss "ex:absent")).endsWith "result definitely empty]"

/-! ### The JSON renderer escapes its payload

A term holding a quote must not break the surrounding JSON. This is what
routing through `jsonEscape` is for, and a renderer that concatenated
raw would pass every other check here. -/

#guard bsJson (.hit "a\"b") == "{\"kind\":\"hit\",\"term\":\"a\\\"b\"}"
#guard bsJson (.var "v") == "{\"kind\":\"var\",\"name\":\"v\"}"

/-! The four kinds use four distinct tags, and `var` uses `name` where
    the other three use `term`. -/

#guard ([BoundStatus.var "x", .hit "x", .miss "x", .other "x"].map bsJson).eraseDups.length == 4
#guard ((bsJson (.var "x")).splitOn "\"name\"").length == 2
#guard ((bsJson (.hit "x")).splitOn "\"term\"").length == 2

/-! ### `null` is a JSON literal, not the string "null" -/

#guard optBoolJson none == "null"
#guard optBoolJson (some true) == "true"
#guard optBoolJson (some false) == "false"

/-! ### A whole row -/

private def row : TpExplain :=
  { label := "tp1",
    tp := { s := .var "s", p := .iri (ei "p"), o := .var "o" },
    sStatus := .var "s", pStatus := .hit "<http://e/p>", oStatus := .var "o",
    boundBuilt := true, predPresent := some true, estimate := 42 }

#guard (tpxJson row).startsWith "{\"label\":\"tp1\""
#guard (tpxJson row).endsWith "\"estimate\":42}"
#guard ((tpxJson row).splitOn "\"predicate_present\":true").length == 2
#guard ((tpxJson { row with predPresent := none }).splitOn
          "\"predicate_present\":null").length == 2

/-! A negative estimate renders with its sign — `estimate` is `Int`, and
    the F\* source uses `string_of_int`, not a natural. -/

#guard ((tpxJson { row with estimate := -1 }).splitOn "\"estimate\":-1").length == 2

end L4Factoidal.SPARQL
