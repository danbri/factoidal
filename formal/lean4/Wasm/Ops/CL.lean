/-
Wasm.Ops.CL — the Common Logic / IKL ops.

The Common Logic / IKL op family (L4Factoidal/CL/, issue 580):

  clParse(cliftext)
    -> {"ok":true,"sentences":N,"pureCL":true|false,"normalized":"…"}
  clSerialize(cliftext)
    -> {"ok":true,"clif":"…","sentences":N,"roundTripProved":false}
  clAlphaNorm(cliftext)
    -> {"ok":true,"clif":"…","sentences":N}
  clNormalize(cliftext)
    -> {"ok":true,"head":[…],"tail":[…],"clif":"…","thatCount":N,
        "noIntrusion":true|false,"preserves":"satisfiability",…}
  clFiniteSat(interpJson, cliftext)
    -> {"ok":true,"satisfied":B,"sentences":[…],"preconditions":{…}}
     | {"ok":false,"error":"refused: …","precondition":"…"}
  every op       | {"ok":false,"error":"…"}

The `clToDataset` and `queryWithIklService` ops are REMOVED
(https://github.com/danbri/factoidal/issues/626). They served the
IKL-to-RDF projection built on content-addressed proposition graph
names, which is deleted.

## What each op's answer is worth

`clParse` and `clSerialize` rest on the CLIF reader/writer pair. The
round-trip lemma `clif_roundTrip` (`CL/ClifAdequacy.lean`) is OPEN: the
fragment boundary `marksLexable` is MEASURED, not proved. `clSerialize`
reports this as `roundTripProved: false` rather than leaving the caller
to assume it.

`clNormalize` exposes Hayes's reduction of IKL to Common Logic
(https://github.com/danbri/factoidal/issues/625). Two limits, both
real, both in the answer:

* It preserves SATISFIABILITY, not equivalence. It suits entailment and
  consistency testing; it is not a transformation to apply to data you
  intend to keep. Reported as `preserves: "satisfiability"`.
* The INTRUSION case is outside what is proved. `tails_satisfiable` and
  `normalize_preserves` carry `noIntrS [] [] E = true`. The op runs the
  transformation either way and reports `noIntrusion` — which is the
  hypothesis itself, decided by `CL.noIntrSs`, not a paraphrase of it.

`clFiniteSat` decides satisfaction against a caller-supplied finite
interpretation. Its answer is worth what `satisfiesFin_eq`
(`CL/FiniteSatTheorems.lean`) says, and that theorem carries three
hypotheses. All three are DISCHARGED OR CHECKED here, never assumed:

* `[LawfulBEq α]` — the domain type is `Fin m`, whose core `BEq` is
  lawful.
* `hdom` (domain completeness, `∀ x : α, x ∈ fi.domain`) — discharged
  BY CONSTRUCTION. The ABI never lets the caller name the domain type:
  it supplies `m` element LABELS, the op takes the domain type to be
  `Fin m` and the domain list to be `List.finRange m`, and
  `finSatDomComplete` below proves completeness from
  `List.mem_finRange`. A caller cannot express a domain that omits an
  element of its own type.
* `hns` (`noSeqQuant s = true`) — CHECKED at runtime by
  `CL.noSeqQuantList`, the same function the theorem's hypothesis
  names. A text that quantifies a sequence marker is REFUSED, naming
  the condition, rather than answered outside the hypothesis.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.CL.Clif
import L4Factoidal.CL.Alpha
import L4Factoidal.CL.Normalize
import L4Factoidal.CL.FiniteSatTheorems

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.CL

/-! ## The text-shaped ops -/

/-- `clParse(cliftext)`. -/
def clParse (cliftext : String) : String :=
  match parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      okWith
        [ ("sentences", .number (toString ss.length))
        , ("pureCL", .bool (sentencesPureCL ss))
        , ("normalized", .string (String.intercalate "\n"
            (ss.map Sentence.toClif))) ]

/-- `clSerialize(cliftext)` — read a CLIF text and write it back in the
canonical spacing of `Sentence.toClif`.

`roundTripProved` is `false` because it is: `clif_roundTrip`
(`CL/ClifAdequacy.lean`) is an OPEN lemma and the fragment boundary
`marksLexable` is measured rather than proved. The field is in the
envelope so a caller does not have to go and find that out. -/
def clSerialize (cliftext : String) : String :=
  match parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      okWith
        [ ("clif", .string (String.intercalate "\n" (ss.map Sentence.toClif)))
        , ("sentences", .number (toString ss.length))
        , ("roundTripProved", .bool false) ]

/-- `clAlphaNorm(cliftext)` — the canonical representative of each
sentence's alpha-equivalence class (`Sentence.alphaNorm`), serialised.
Bound names become `v1`, `v2`, … in traversal order, so two sentences
that differ only in bound names produce byte-identical output. -/
def clAlphaNorm (cliftext : String) : String :=
  match parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      okWith
        [ ("clif", .string (String.intercalate "\n"
            (ss.map (fun s => s.alphaNorm.toClif))))
        , ("sentences", .number (toString ss.length)) ]

/-- `clNormalize(cliftext)` — Hayes's satisfiability-preserving
reduction of IKL to Common Logic, over a whole text: one head text and
one shared tail, with the proposition-name counter running across the
text (`CL.normalizeText`).

`noIntrusion` is the PROOF HYPOTHESIS, decided (`CL.noIntrSs [] []`),
not a paraphrase. When it is `false` the output is still the
transformation's output, but `tails_satisfiable` and
`normalize_preserves` do not cover it. -/
def clNormalize (cliftext : String) : String :=
  match parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      let r := normalizeText ss
      let head := r.1
      let tail := r.2
      okWith
        [ ("head", .array (head.map (fun s => Json.string s.toClif)))
        , ("tail", .array (tail.map (fun s => Json.string s.toClif)))
        , ("clif", .string (String.intercalate "\n"
            ((head ++ tail).map Sentence.toClif)))
        , ("sentences", .number (toString ss.length))
        , ("thatCount", .number (toString (sentsThatCount ss)))
        , ("noIntrusion", .bool (noIntrSs [] [] ss))
        , ("preserves", .string "satisfiability")
        , ("provedUnder", .string "noIntrS [] [] = true") ]

/-! ## `clFiniteSat`

### The interpretation wire format

Argument 1 is a JSON object. `domain` is the only required member.

```json
{ "domain":    ["bill", "boy"],
  "default":   "bill",
  "names":     { "Bill": "bill", "Boy": "boy", "Sue": "boy" },
  "strings":   { "a string": "bill" },
  "functions": [ { "op": "boy", "args": ["bill"], "value": "bill" } ],
  "relations": [ { "op": "boy", "args": ["bill"] } ],
  "props":     { "(P x)": "bill" } }
```

`domain` lists the element LABELS — arbitrary strings, distinct, at
least one. Every other member refers to elements by label; an unknown
label is an error naming the label, never a silent default.

The labels are the caller's names for elements, NOT the domain type.
The domain type is `Fin m` for `m` the number of labels, which is what
makes `hdom` hold by construction (see the module header).

`default` is the element the totalisations fall back on — an unlisted
name's denotation, a function application with no `functions` row. It
defaults to the FIRST label.

`props` keys are canonical CLIF texts of `that`-bodies, matching
`FiniteInterp.propD`'s keying by `Sentence.toClif`.

`maxSeq` is not accepted. It bounds sequence-marker quantification,
and a text containing one is refused before the interpretation is
read. -/

/-- The label-to-index resolution of one JSON object member. Written
here rather than reached for from `List`, so a core rename cannot
change the op's behaviour silently. -/
private def labelIndex : List String → String → Nat → Option Nat
  | [], _, _ => none
  | l :: rest, target, k => if l == target then some k else labelIndex rest target (k + 1)

/-- One JSON object member by key. -/
private def objField (fs : List (String × Json)) (k : String) : Option Json :=
  (fs.find? (·.1 == k)).map (·.2)

/-- A JSON string, or a caller error naming what was found instead. -/
private def asString (what : String) : Json → Except String String
  | .string s => .ok s
  | _ => .error s!"{what} must be a JSON string"

/-- A label resolved against the domain, or an error naming it. -/
private def asElem (labels : List String) (what : String) (j : Json) :
    Except String Nat := do
  let s ← asString what j
  match labelIndex labels s 0 with
  | some i => .ok i
  | none => .error s!"{what}: '{s}' is not a domain label"

/-- A JSON array of element labels. -/
private def asElems (labels : List String) (what : String) : Json → Except String (List Nat)
  | .array items => items.mapM (asElem labels what)
  | _ => .error s!"{what} must be a JSON array of domain labels"

/-- A JSON object read as string-keyed element rows (`names`,
`strings`, `props`). Absent reads as empty. -/
private def elemMap (labels : List String) (fs : List (String × Json)) (key : String) :
    Except String (List (String × Nat)) :=
  match objField fs key with
  | none => .ok []
  | some (.object rows) =>
      rows.mapM (fun kv => (asElem labels key kv.2).map (fun i => (kv.1, i)))
  | some _ => .error s!"{key} must be a JSON object"

/-- One `{"op":…,"args":[…]}` pair, shared by `functions` and
`relations`. -/
private def opArgs (labels : List String) (key : String) (fs : List (String × Json)) :
    Except String (Nat × List Nat) := do
  let opJ ← (objField fs "op").elim (.error s!"{key}: a row needs an 'op'") Except.ok
  let argsJ ← (objField fs "args").elim (.error s!"{key}: a row needs 'args'") Except.ok
  let o ← asElem labels s!"{key}.op" opJ
  let a ← asElems labels s!"{key}.args" argsJ
  .ok (o, a)

/-- `relations`: the pairs that hold. Absent reads as empty. -/
private def relRows (labels : List String) (fs : List (String × Json)) :
    Except String (List (Nat × List Nat)) :=
  match objField fs "relations" with
  | none => .ok []
  | some (.array items) =>
      items.mapM (fun it =>
        match it with
        | .object rowFs => opArgs labels "relations" rowFs
        | _ => .error "relations: each row must be a JSON object")
  | some _ => .error "relations must be a JSON array"

/-- `functions`: the graph rows. Absent reads as empty. -/
private def fnRows (labels : List String) (fs : List (String × Json)) :
    Except String (List ((Nat × List Nat) × Nat)) :=
  match objField fs "functions" with
  | none => .ok []
  | some (.array items) =>
      items.mapM (fun it =>
        match it with
        | .object rowFs => do
            let oa ← opArgs labels "functions" rowFs
            let vJ ← (objField rowFs "value").elim
              (.error "functions: a row needs a 'value'") Except.ok
            let v ← asElem labels "functions.value" vJ
            .ok (oa, v)
        | _ => .error "functions: each row must be a JSON object")
  | some _ => .error "functions must be a JSON array"

/-- The decoded interpretation, still index-based: every `Nat` here has
been checked against `labels`. -/
private structure FinSatSpec where
  labels : List String
  deflt : Nat
  names : List (String × Nat)
  strs : List (String × Nat)
  fns : List ((Nat × List Nat) × Nat)
  rels : List (Nat × List Nat)
  props : List (String × Nat)

/-- Decode argument 1. -/
private def decodeSpec (interpJson : String) : Except String FinSatSpec := do
  let j ← match parseJson interpJson with
    | .error e => .error s!"interpJson: {toString e}"
    | .ok v => .ok v
  let fs ← match j with
    | .object fs => .ok fs
    | _ => .error "interpJson must be a JSON object"
  let labels ← match objField fs "domain" with
    | none => .error "interpJson needs a 'domain'"
    | some (.array items) => items.mapM (asString "domain")
    | some _ => .error "domain must be a JSON array of labels"
  if labels.isEmpty then
    .error "domain must list at least one element"
  else do
    let deflt ← match objField fs "default" with
      | none => .ok 0
      | some v => asElem labels "default" v
    let names ← elemMap labels fs "names"
    let strs ← elemMap labels fs "strings"
    let props ← elemMap labels fs "props"
    let rels ← relRows labels fs
    let fns ← fnRows labels fs
    .ok { labels, deflt, names, strs, fns, rels, props }

/-- Build the interpretation over `Fin m`. `mkFin` is total: every
index reaching it was checked against a `labels` list of length `m`
during decoding, so the fallback arm is unreachable, and taking it
would only mean the first element rather than an unsound answer. -/
private def specInterp (m : Nat) (hm : 0 < m) (sp : FinSatSpec) : FiniteInterp (Fin m) :=
  let mkFin : Nat → Fin m := fun i => if h : i < m then ⟨i, h⟩ else ⟨0, hm⟩
  { domain := List.finRange m
    deflt := mkFin sp.deflt
    names := sp.names.map (fun p => (p.1, mkFin p.2))
    strs := sp.strs.map (fun p => (p.1, mkFin p.2))
    fns := sp.fns.map (fun p => ((mkFin p.1.1, p.1.2.map mkFin), mkFin p.2))
    rels := sp.rels.map (fun p => (mkFin p.1, p.2.map mkFin))
    props := sp.props.map (fun p => (p.1, mkFin p.2))
    maxSeq := 0 }

/-- **`hdom` for every interpretation this op can build.** The
`satisfiesFin_eq` hypothesis `∀ x : α, x ∈ fi.domain` holds for
`specInterp` whatever the caller sent, because the ABI fixes the domain
type to `Fin m` and the domain list to `List.finRange m`. This is what
lets `clFiniteSat` report domain completeness as discharged rather than
checked. -/
theorem finSatDomComplete (m : Nat) (hm : 0 < m) (sp : FinSatSpec) :
    ∀ x : Fin m, x ∈ (specInterp m hm sp).domain :=
  fun x => List.mem_finRange x

/-- The precondition block every `clFiniteSat` answer carries. -/
private def preconditionsJson : Json :=
  .object
    [ ("domainComplete", .object
        [ ("holds", .bool true)
        , ("how", .string ("discharged by construction: the domain type is Fin m "
            ++ "and the domain is List.finRange m (theorem finSatDomComplete, "
            ++ "from List.mem_finRange)")) ])
    , ("noSeqQuant", .object
        [ ("holds", .bool true)
        , ("how", .string ("checked by L4Factoidal.CL.noSeqQuantList, the function "
            ++ "the hypothesis names; a text that fails it is refused")) ]) ]

/-- `clFiniteSat(interpJson, cliftext)` — decide satisfaction of every
sentence of the text against the supplied finite interpretation.

`satisfied` is the conjunction over the text: `true` iff the
interpretation satisfies every sentence. Per-sentence verdicts are in
`sentences`.

A text quantifying a sequence marker is REFUSED (`ok: false`, with
`precondition: "noSeqQuant"`) rather than answered, because
`satisfiesFin_eq` says nothing about that case. -/
def clFiniteSat (interpJson cliftext : String) : String :=
  match parseClifText cliftext with
  | .error e => errJson (fmtParseError e)
  | .ok ss =>
      if noSeqQuantList ss = false then
        (Json.object
          [ ("ok", .bool false)
          , ("error", .string ("refused: the text quantifies a sequence marker, "
              ++ "which is outside the noSeqQuant hypothesis of "
              ++ "L4Factoidal.CL.satisfiesFin_eq"))
          , ("precondition", .string "noSeqQuant") ]).toString
      else
        match decodeSpec interpJson with
        | .error e => errJson e
        | .ok sp =>
          match sp.labels.length with
          | 0 => errJson "domain must list at least one element"
          | m + 1 =>
            let fi := specInterp (m + 1) (Nat.succ_pos m) sp
            let verdicts := ss.map (fun s => (s.toClif, fi.satisfies s))
            okWith
              [ ("satisfied", .bool (verdicts.all (·.2)))
              , ("sentences", .array (verdicts.map (fun v =>
                  Json.object
                    [ ("clif", .string v.1)
                    , ("satisfied", .bool v.2) ])))
              , ("domainSize", .number (toString (m + 1)))
              , ("preconditions", preconditionsJson)
              , ("agreementTheorem", .string "L4Factoidal.CL.satisfiesFin_eq") ]

/-! ## Build-time pins

`lake build` is this project's test run (`skills/factoidal-lean-basics`,
Build/test/demo), and until 2026-08-26 these ops had no build-time
coverage at all: they were gated only by `Wasm/native-smoke.sh` and
`Wasm/cli-smoke.sh`, which need a built binary and an explicit run.
Measured that day by sabotage — replacing `clFiniteSat`'s
`noSeqQuantList` test with `false`, so the op answered outside its own
hypothesis — `lake build` COMPLETED SUCCESSFULLY and only the smoke
script caught it. A session that ran the build and not the scripts
would have shipped a checker that answers where it should refuse.

So the safety-relevant behaviours are pinned here as well. Each is a
`#guard`, which evaluates during elaboration; a wrong answer is a build
error. They pin REFUSALS and REFUTATIONS, not only the affirmative
cases: an op that answered `true` to everything would satisfy the
affirmative pins alone. -/

/-- Substring test, written here rather than reached for from `String`,
so a core rename cannot change what these pins mean. -/
private def hasSub (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def guardInterp : String :=
  "{\"domain\":[\"bill\",\"boy\"],\"default\":\"bill\"," ++
  "\"names\":{\"Bill\":\"bill\",\"Boy\":\"boy\",\"Sue\":\"boy\"}," ++
  "\"relations\":[{\"op\":\"boy\",\"args\":[\"bill\"]}]}"

private def guardSeqMark : String := "(forall (...m) (P ...m))"

-- `clSerialize` reports the OPEN round-trip lemma rather than implying one.
#guard hasSub (clSerialize "(Boy Bill)") "\"roundTripProved\":false"

-- `clAlphaNorm` collapses alpha-variants to byte-identical text.
#guard clAlphaNorm "(forall (x) (Boy x))" == clAlphaNorm "(forall (zz) (Boy zz))"

-- `clNormalize` names an IKL `that`-term and emits the biconditional tail.
#guard hasSub (clNormalize "(P (that (Q a)))") "\"tail\":[\"(iff (prop1) (Q a))\"]"

-- ...and reports `noIntrusion` truthfully in BOTH directions: true where
-- the theorems reach, false where they do not.
#guard hasSub (clNormalize "(P (that (Q a)))") "\"noIntrusion\":true"
#guard hasSub (clNormalize "(forall (x) (P (that (Q x))))") "\"noIntrusion\":false"

-- `clFiniteSat` satisfies where the relation table has a row...
#guard hasSub (clFiniteSat guardInterp "(Boy Bill)") "\"satisfied\":true"
-- ...and REFUTES where it has none. Without this pin an op that answered
-- `true` unconditionally would pass every guard above.
#guard hasSub (clFiniteSat guardInterp "(Boy Sue)") "\"satisfied\":false"

-- The `noSeqQuant` hypothesis is CHECKED: a sequence-marker quantifier is
-- refused, by name. This is the guard the sabotage above defeated.
#guard hasSub (clFiniteSat guardInterp guardSeqMark) "\"precondition\":\"noSeqQuant\""
#guard hasSub (clFiniteSat guardInterp guardSeqMark) "\"ok\":false"

-- An unknown domain label is an error naming the label, never a silent
-- fallback to the default element.
#guard hasSub (clFiniteSat "{\"domain\":[\"bill\"],\"names\":{\"Boy\":\"nope\"}}" "(Boy Bill)")
              "'nope' is not a domain label"

-- The `hdom` hypothesis of `satisfiesFin_eq`, discharged for every
-- interpretation this ABI can build. The audit line keeps its axiom base
-- in every build log, per the proof policy in `skills/factoidal-lean-basics`.
#print axioms finSatDomComplete

end L4Wasm.Ops
