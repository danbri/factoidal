/-
Wasm.Ops.Proof — the FPP0 proof-checker ops.

  proofCheck(bundleJson)
    -> {"ok":true,"valid":B,"conclusion":"…","assumptions":[…],
        "counts":{"foundational":N,"verifiedReplay":N,"replay":N,
                  "attestation":N},"countsOver":"…",
        "foundationalOnly":B,"conclusionIsAssumption":B,
        "checkedSteps":N,"soundness":"…","validMeans":"…"}
     | {"ok":false,"error":"…"}
  proofInspect(bundleJson)
    -> {"ok":true,"profile":"…","artifacts":N,"artifactsWithBody":N,
        "assumptions":[…],"steps":N,"declaredStepLevels":{…},
        "countedOver":"…","rules":[…],"adapters":[…],
        "conclusion":{…},"conclusionDeclaredAsAssumption":B,
        "verdict":"none — …"}
     | {"ok":false,"error":"…"}

Milestone M1 of
`docs/designissues/2026-08-26-proof-profile-fpp0-adoption.md`: the
kernel over the dispatch ABI. The kernel itself is
`L4Factoidal/Proof/Checker.lean` and this module adds no checking to
it — `proofCheck` DECODES, calls `FPP0.checkBundle`, and ENCODES. Every
verdict field is copied out of the `CheckResult` the kernel returned.

## What each op's answer is worth

`proofCheck`'s answer is worth exactly what
`L4Factoidal.FPP0.checkBundle_sound` says, and no more:

    (checkBundle b).valid = true ->
      Derives (checkBundle b).assumptions (checkBundle b).conclusion

That is a statement about the FRONTIER, not a verdict that something
was proved. Adoption-doc section 8a: a bundle that declares its own
conclusion as an assumption satisfies it and proves nothing. The
envelope therefore never reports `valid` alone — `assumptions`,
`counts.foundational`, `foundationalOnly` and `conclusionIsAssumption`
travel with it in every answer, and `validMeans` states in the answer
what `valid` does and does not say.

`counts` is taken over the SUPPORT of the conclusion, not over the
whole bundle (padding a degenerate bundle with unused foundational
steps must not raise its foundational count). The envelope labels that
with `countsOver` rather than leaving a bare number to be misread.

`proofInspect` reports STRUCTURE and NEVER calls the kernel. Its
`declaredStepLevels` are the levels the producer WROTE, over every
step, which is a different number from `proofCheck`'s `counts` — so it
is named differently and carries its own `countedOver` label. Its
`verdict` member says in words that nothing was checked.

## The decoder is the new attack surface

Iron rule #11 puts the JSON assembly and parsing in the formal source,
so the decoder below is Lean and is part of what has to be right. A
lenient decoder would undo the design's guarantees without touching
the kernel, so it is strict in four specific ways:

1. TOTAL. Every function here is structurally recursive over a finite
   list. The FPP0 grammar is FIXED-DEPTH — bundle, table, row, claim —
   so no decoder function recurses on JSON nesting and none needs a
   fuel parameter. The only unbounded input is the JSON text itself,
   and `L4Factoidal.JSON.parseJson` already bounds that by its
   character count.
2. REJECT, NEVER DEFAULT. A missing `level`, `kind`, `profile`,
   `premises`, `assumptions` — every absent required member is an
   error naming the member. Absent is not benign: an absent
   `assumptions` array read as empty would report an EMPTY FRONTIER
   for a bundle that has one, which is the one direction of error that
   makes a bundle look stronger than it is.
3. AN UNKNOWN ENUM VALUE IS NOT THE WEAKEST MEMBER. An unrecognised
   `level` is refused by name; it is never mapped onto `attestation`,
   and never dropped. `decodeLevelName_inj` and `decodeRuleRow_name`
   below state that as theorems: nothing but the four level names
   decodes to a level, and nothing but the sixteen row names decodes
   to a row.
4. A DECODE FAILURE IS NOT AN INVALID BUNDLE. `{"ok":false,"error":…}`
   says the document did not parse; `{"ok":true,"valid":false}` says
   the kernel read a bundle and REFUSED it. Collapsing the two would
   lose the distinction a caller needs to tell a broken producer from
   a rejected proof.

Two grammar conditions are level-dependent or document-level, and are
the decoder's own rather than the kernel's:

* `citation` is REQUIRED at `verifiedReplay` (adoption doc section
  8b). The kernel enforces the same condition
  (`FPP0.levelEvidenceOk`, pinned in `Proof/Tests.lean` negative 13);
  neither side depends on the other, and a V step with no citation
  never reaches a reader as a `replay` step.
* `profile` at the top of the document must be `fpp0/1` (certificate
  v1 section 5's last rejection row). The `Bundle` type has no
  top-level profile field, so this one has nowhere else to live.

Duplicate ids in the three tables are refused at decode, naming the
id: a table with a repeated key does not denote a bundle. The kernel
refuses the same shapes independently (`artifactsOk`, `assumptionsOk`,
and `stepValid`'s new-id test), and its own pins for them stay in
`Proof/Tests.lean` where this decoder cannot mask them.

## The wire format

```json
{ "profile": "fpp0/1",
  "artifacts":   [ {"id":"G","kind":"graph","digest":"…","body":"…nt…"} ],
  "assumptions": [ {"id":"a1","subject":<claim>,"level":"replay"} ],
  "steps":       [ {"id":"s1","justification":<just>,"premises":["a1"],
                    "conclusion":<claim>,"level":"foundational",
                    "profile":"fpp0/1",
                    "citation":{"theoremName":"…","module":"…"}} ],
  "conclusion": <claim> }
```

`<claim>` is `{"kind":"rdfDerivable","graph":D,"axioms":D,"triple":NT}`
or `{"kind":"clif","proposition":P}`. `<just>` is
`{"kind":"rule","row":"rdfs7","graphArtifact":"G","axiomArtifact":"AX"}`
or `{"kind":"adapterEvidence","adapter":"…","detail":"…"}`.

Triples and inline graph bodies are N-Triples text, read and written
by the engine's own parser and serialiser (`Syntax/NTriples.lean`) in
RDF 1.2 mode. `body` is optional; every other member is required.
`citation` is optional except at `verifiedReplay`.

⚠️ The whole-bundle round trip `decodeBundle (encodeBundle b) = .ok b`
is PINNED BY `#guard` on the fixtures below, NOT proved. The obstacle
is named: the general N-Triples round trip
(`Syntax.SyntaxTheorems.graph_roundtrip`) is STATED AND NOT PROVED in
this tree, so a bundle-level theorem would rest on it. What IS proved
here is the enum layer — the three decoders where a lenient reading
would silently weaken a bundle.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.Proof.Checker
import L4Factoidal.Syntax.NTriples

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.FPP0

/-! ## JSON shape helpers

Written here rather than reached for from a shared module so that a
change elsewhere cannot silently relax what this decoder accepts. -/

/-- One object member by key, or `none`. -/
private def pfField (fs : List (String × Json)) (k : String) : Option Json :=
  (fs.find? (·.1 == k)).map (·.2)

private def pfObject (path : String) : Json → Except String (List (String × Json))
  | .object fs => .ok fs
  | _ => .error s!"{path}: must be a JSON object"

private def pfArray (path : String) : Json → Except String (List Json)
  | .array items => .ok items
  | _ => .error s!"{path}: must be a JSON array"

private def pfString (path : String) : Json → Except String String
  | .string s => .ok s
  | _ => .error s!"{path}: must be a JSON string"

/-- A REQUIRED member. Absent is an error naming the member — never a
default. -/
private def pfReq (path : String) (fs : List (String × Json)) (k : String) :
    Except String Json :=
  match pfField fs k with
  | some v => .ok v
  | none => .error s!"{path}.{k}: missing required field"

private def pfReqString (path : String) (fs : List (String × Json)) (k : String) :
    Except String String := do
  pfString s!"{path}.{k}" (← pfReq path fs k)

/-- The first id that occurs twice, if any. -/
private def firstDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDup xs

private def noDupIds (what : String) (ids : List String) : Except String Unit :=
  match firstDup ids with
  | some d => .error s!"{what}: duplicate id '{d}'"
  | none => .ok ()

/-! ## The enum layer, and the theorems that say it is not lenient -/

/-- The four evidence-level names. One spelling each: an abbreviation
would be a second name for a level and a chance to mis-read one. -/
def encodeLevel : EvidenceLevel → String
  | .foundational => "foundational"
  | .verifiedReplay => "verifiedReplay"
  | .replay => "replay"
  | .attestation => "attestation"

/-- Read a level name. An unrecognised name is `none` — NOT the
weakest member, and not silently dropped. -/
def decodeLevelName : String → Option EvidenceLevel
  | "foundational" => some .foundational
  | "verifiedReplay" => some .verifiedReplay
  | "replay" => some .replay
  | "attestation" => some .attestation
  | _ => none

/-- **Nothing but a level name decodes to a level.** This is the
statement that rules out the failure the design names: an unknown
`level` string mapped onto `attestation`, or a missing one defaulted
to `replay`. Both would make the decoder answer where it must
refuse. -/
theorem decodeLevelName_inj {s : String} {l : EvidenceLevel}
    (h : decodeLevelName s = some l) : s = encodeLevel l := by
  unfold decodeLevelName at h
  split at h <;> first | (cases h; rfl) | exact absurd h (by simp)

/-- ...and every level name decodes back to its own level. -/
theorem decodeLevelName_encodeLevel (l : EvidenceLevel) :
    decodeLevelName (encodeLevel l) = some l := by
  cases l <;> rfl

private def decodeLevel (path : String) (s : String) : Except String EvidenceLevel :=
  match decodeLevelName s with
  | some l => .ok l
  | none => .error s!"{path}: unknown evidence level '{s}' (expected one of \
      foundational, verifiedReplay, replay, attestation)"

def encodeKind : ArtifactKind → String
  | .graph => "graph"
  | .bytes => "bytes"
  | .claim => "claim"
  | .solutions => "solutions"

def decodeKindName : String → Option ArtifactKind
  | "graph" => some .graph
  | "bytes" => some .bytes
  | "claim" => some .claim
  | "solutions" => some .solutions
  | _ => none

theorem decodeKindName_inj {s : String} {k : ArtifactKind}
    (h : decodeKindName s = some k) : s = encodeKind k := by
  unfold decodeKindName at h
  split at h <;> first | (cases h; rfl) | exact absurd h (by simp)

theorem decodeKindName_encodeKind (k : ArtifactKind) :
    decodeKindName (encodeKind k) = some k := by
  cases k <;> rfl

private def decodeKind (path : String) (s : String) : Except String ArtifactKind :=
  match decodeKindName s with
  | some k => .ok k
  | none => .error s!"{path}: unknown artifact kind '{s}' (expected one of \
      graph, bytes, claim, solutions)"

/-- Read one RDF 1.1 Semantics row name. `RuleId.name`
(`RDFS/Derivation.lean`) is the spec's own name for the row and is the
inverse of this function. An unknown row name is refused; `RuleId` is
a closed inductive, so there is no member to fall back to. -/
def decodeRowName : String → Option RuleId
  | "base" => some .base
  | "axiomatic" => some .axiomatic
  | "rdfD2" => some .rdfD2
  | "rdfs2" => some .rdfs2
  | "rdfs3" => some .rdfs3
  | "rdfs4a" => some .rdfs4a
  | "rdfs4b" => some .rdfs4b
  | "rdfs5" => some .rdfs5
  | "rdfs6" => some .rdfs6
  | "rdfs7" => some .rdfs7
  | "rdfs8" => some .rdfs8
  | "rdfs9" => some .rdfs9
  | "rdfs10" => some .rdfs10
  | "rdfs11" => some .rdfs11
  | "rdfs12" => some .rdfs12
  | "rdfs13" => some .rdfs13
  | _ => none

/-- **Nothing but a row name decodes to a row**, so a made-up
inference row (certificate v1 section 5, row 3) cannot enter the
kernel wearing a real row's constructor. -/
theorem decodeRowName_inj {s : String} {r : RuleId}
    (h : decodeRowName s = some r) : s = r.name := by
  unfold decodeRowName at h
  split at h <;> first | (cases h; rfl) | exact absurd h (by simp)

theorem decodeRowName_name (r : RuleId) : decodeRowName r.name = some r := by
  cases r <;> rfl

private def decodeRow (path : String) (s : String) : Except String RuleId :=
  match decodeRowName s with
  | some r => .ok r
  | none => .error s!"{path}: unknown rule row '{s}'"

/-! ## Triples and graphs on the wire

N-Triples text, read and written by the engine's own parser and
serialiser in RDF 1.2 mode. RDF 1.2 rather than 1.1 so that a triple
term or a directional literal in a claim is carried rather than
refused at the wire. -/

private def ntMode : L4Factoidal.Syntax.Mode := .rdf12

private def decodeTripleText (path : String) (nt : String) : Except String Triple :=
  match L4Factoidal.Syntax.parseNTriples nt ntMode with
  | .error e => .error s!"{path}: not an N-Triples statement ({e.msg} at offset {e.pos})"
  | .ok [t] => .ok t
  | .ok g => .error s!"{path}: expected exactly one N-Triples statement, got {g.length}"

private def decodeGraphText (path : String) (nt : String) : Except String Graph :=
  match L4Factoidal.Syntax.parseNTriples nt ntMode with
  | .error e => .error s!"{path}: not an N-Triples document ({e.msg} at offset {e.pos})"
  | .ok g => .ok g

private def encodeTripleText (what : String) (t : Triple) : Except String String :=
  (L4Factoidal.Syntax.Triple.toNTriples ntMode t).mapError
    (fun e => s!"{what}: {e}")

private def encodeGraphText (what : String) (g : Graph) : Except String String :=
  (L4Factoidal.Syntax.Graph.toNTriples g ntMode).mapError (fun e => s!"{what}: {e}")

/-! ## Claims -/

/-- The tag a claim is filed under on the wire. -/
def claimKindName : Claim → String
  | .rdfDerivable _ _ _ => "rdfDerivable"
  | .clif _ => "clif"

def decodeClaim (path : String) (j : Json) : Except String Claim := do
  let fs ← pfObject path j
  let kind ← pfReqString path fs "kind"
  match kind with
  | "rdfDerivable" => do
      let gd ← pfReqString path fs "graph"
      let ad ← pfReqString path fs "axioms"
      let nt ← pfReqString path fs "triple"
      let t ← decodeTripleText s!"{path}.triple" nt
      .ok (.rdfDerivable gd ad t)
  | "clif" => do
      let p ← pfReqString path fs "proposition"
      .ok (.clif p)
  | other => .error s!"{path}.kind: unknown claim kind '{other}' \
      (expected rdfDerivable or clif)"

def encodeClaim (what : String) : Claim → Except String Json
  | .rdfDerivable gd ad t => do
      let nt ← encodeTripleText what t
      .ok (.object [ ("kind", .string "rdfDerivable")
                   , ("graph", .string gd)
                   , ("axioms", .string ad)
                   , ("triple", .string nt) ])
  | .clif p =>
      .ok (.object [ ("kind", .string "clif"), ("proposition", .string p) ])

/-! ## Justifications, citations, artifacts, assumptions, steps -/

def decodeJustification (path : String) (j : Json) : Except String Justification := do
  let fs ← pfObject path j
  let kind ← pfReqString path fs "kind"
  match kind with
  | "rule" => do
      let row ← decodeRow s!"{path}.row" (← pfReqString path fs "row")
      let ga ← pfReqString path fs "graphArtifact"
      let aa ← pfReqString path fs "axiomArtifact"
      .ok (.rule row ga aa)
  | "adapterEvidence" => do
      let adapter ← pfReqString path fs "adapter"
      let detail ← pfReqString path fs "detail"
      .ok (.adapterEvidence adapter detail)
  | other => .error s!"{path}.kind: unknown justification kind '{other}' \
      (expected rule or adapterEvidence)"

def encodeJustification : Justification → Json
  | .rule row ga aa =>
      .object [ ("kind", .string "rule")
              , ("row", .string row.name)
              , ("graphArtifact", .string ga)
              , ("axiomArtifact", .string aa) ]
  | .adapterEvidence adapter detail =>
      .object [ ("kind", .string "adapterEvidence")
              , ("adapter", .string adapter)
              , ("detail", .string detail) ]

def decodeCitation (path : String) (j : Json) : Except String Citation := do
  let fs ← pfObject path j
  let nm ← pfReqString path fs "theoremName"
  let md ← pfReqString path fs "module"
  .ok { theoremName := nm, module := md }

def encodeCitation (c : Citation) : Json :=
  .object [ ("theoremName", .string c.theoremName), ("module", .string c.module) ]

def decodeArtifact (path : String) (j : Json) : Except String Artifact := do
  let fs ← pfObject path j
  let id ← pfReqString path fs "id"
  let kind ← decodeKind s!"{path}.kind" (← pfReqString path fs "kind")
  let digest ← pfReqString path fs "digest"
  let body ← match pfField fs "body" with
    | none => pure none
    | some bj => do
        let txt ← pfString s!"{path}.body" bj
        let g ← decodeGraphText s!"{path}.body" txt
        pure (some g)
  .ok { id := id, kind := kind, digest := digest, body := body }

def encodeArtifact (what : String) (a : Artifact) : Except String Json := do
  let head : List (String × Json) :=
    [ ("id", .string a.id)
    , ("kind", .string (encodeKind a.kind))
    , ("digest", .string a.digest) ]
  match a.body with
  | none => .ok (.object head)
  | some g => do
      let nt ← encodeGraphText s!"{what}.body" g
      .ok (.object (head ++ [("body", .string nt)]))

def decodeAssumption (path : String) (j : Json) : Except String Assumption := do
  let fs ← pfObject path j
  let id ← pfReqString path fs "id"
  let subject ← decodeClaim s!"{path}.subject" (← pfReq path fs "subject")
  let level ← decodeLevel s!"{path}.level" (← pfReqString path fs "level")
  .ok { id := id, subject := subject, level := level }

def encodeAssumption (what : String) (a : Assumption) : Except String Json := do
  let subj ← encodeClaim s!"{what}.subject" a.subject
  .ok (.object [ ("id", .string a.id)
               , ("subject", subj)
               , ("level", .string (encodeLevel a.level)) ])

def decodeStep (path : String) (j : Json) : Except String BundleStep := do
  let fs ← pfObject path j
  let id ← pfReqString path fs "id"
  let just ← decodeJustification s!"{path}.justification" (← pfReq path fs "justification")
  let premJson ← pfArray s!"{path}.premises" (← pfReq path fs "premises")
  let premises ← premJson.zipIdx.mapM
    (fun (p, i) => pfString s!"{path}.premises[{i}]" p)
  let conclusion ← decodeClaim s!"{path}.conclusion" (← pfReq path fs "conclusion")
  let level ← decodeLevel s!"{path}.level" (← pfReqString path fs "level")
  let profile ← pfReqString path fs "profile"
  let citation ← match pfField fs "citation" with
    | none => pure none
    | some cj => do
        let c ← decodeCitation s!"{path}.citation" cj
        pure (some c)
  -- Adoption doc section 8b, as a grammar condition: at
  -- `verifiedReplay` the citation is a REQUIRED member. Accepting the
  -- step at `replay` instead would rewrite the producer's own claim.
  if level == EvidenceLevel.verifiedReplay && citation.isNone then
    .error s!"{path}.citation: missing required field — a verifiedReplay step \
      must cite a theorem by name and module (adoption doc section 8b)"
  else
    .ok { id := id, justification := just, premises := premises,
          conclusion := conclusion, level := level, profile := profile,
          citation := citation }

def encodeStep (what : String) (st : BundleStep) : Except String Json := do
  let concl ← encodeClaim s!"{what}.conclusion" st.conclusion
  let head : List (String × Json) :=
    [ ("id", .string st.id)
    , ("justification", encodeJustification st.justification)
    , ("premises", .array (st.premises.map Json.string))
    , ("conclusion", concl)
    , ("level", .string (encodeLevel st.level))
    , ("profile", .string st.profile) ]
  match st.citation with
  | none => .ok (.object head)
  | some c => .ok (.object (head ++ [("citation", encodeCitation c)]))

/-! ## The document -/

/-- Decode a whole FPP0 document. Total: three `mapM`s over finite
lists and a fixed set of member reads; nothing recurses on JSON
nesting. -/
def decodeBundle (bundleJson : String) : Except String Bundle := do
  let j ← match parseJson bundleJson with
    | .error e => .error s!"bundle: {toString e}"
    | .ok v => .ok v
  let fs ← pfObject "bundle" j
  let profile ← pfReqString "bundle" fs "profile"
  let _ ← if profile == fpp0Profile then Except.ok ()
          else Except.error s!"bundle.profile: unknown profile '{profile}' \
            (this kernel reads '{fpp0Profile}')"
  let artJson ← pfArray "bundle.artifacts" (← pfReq "bundle" fs "artifacts")
  let artifacts ← artJson.zipIdx.mapM
    (fun (a, i) => decodeArtifact s!"bundle.artifacts[{i}]" a)
  let _ ← noDupIds "bundle.artifacts" (artifacts.map (·.id))
  let asmJson ← pfArray "bundle.assumptions" (← pfReq "bundle" fs "assumptions")
  let assumptions ← asmJson.zipIdx.mapM
    (fun (a, i) => decodeAssumption s!"bundle.assumptions[{i}]" a)
  let _ ← noDupIds "bundle.assumptions" (assumptions.map (·.id))
  let stJson ← pfArray "bundle.steps" (← pfReq "bundle" fs "steps")
  let steps ← stJson.zipIdx.mapM (fun (s, i) => decodeStep s!"bundle.steps[{i}]" s)
  let _ ← noDupIds "bundle.steps" (steps.map (·.id))
  let conclusion ← decodeClaim "bundle.conclusion" (← pfReq "bundle" fs "conclusion")
  .ok { artifacts := artifacts.toArray, assumptions := assumptions.toArray,
        steps := steps.toArray, conclusion := conclusion }

/-- Write a bundle out in the same document shape `decodeBundle`
reads. Fails only where the N-Triples serialiser fails. -/
def encodeBundle (b : Bundle) : Except String String := do
  let artifacts ← b.artifacts.toList.zipIdx.mapM
    (fun (a, i) => encodeArtifact s!"bundle.artifacts[{i}]" a)
  let assumptions ← b.assumptions.toList.zipIdx.mapM
    (fun (a, i) => encodeAssumption s!"bundle.assumptions[{i}]" a)
  let steps ← b.steps.toList.zipIdx.mapM
    (fun (s, i) => encodeStep s!"bundle.steps[{i}]" s)
  let conclusion ← encodeClaim "bundle.conclusion" b.conclusion
  .ok (Json.object
    [ ("profile", .string fpp0Profile)
    , ("artifacts", .array artifacts)
    , ("assumptions", .array assumptions)
    , ("steps", .array steps)
    , ("conclusion", conclusion) ]).toString

/-! ## `proofCheck` -/

private def countsJson (c : LevelCounts) : Json :=
  .object [ ("foundational", .number (toString c.foundational))
          , ("verifiedReplay", .number (toString c.verifiedReplay))
          , ("replay", .number (toString c.replay))
          , ("attestation", .number (toString c.attestation)) ]

/-- One frontier entry. `claim` is `Claim.render` — PRESENTATION, as
the type's own doc says; `claimKind` carries the structural tag so a
reader does not have to parse the rendering. -/
private def assumptionJson (a : Assumption) : Json :=
  .object [ ("id", .string a.id)
          , ("level", .string (encodeLevel a.level))
          , ("claimKind", .string (claimKindName a.subject))
          , ("claim", .string a.subject.render) ]

/-- `proofCheck(bundleJson)` — decode an FPP0 document, run
`FPP0.checkBundle` on it, and report the result the kernel returned.

This op checks NOTHING itself. Every field below is read out of the
`CheckResult`; the answer is worth what `checkBundle_sound` says. -/
def proofCheck (bundleJson : String) : String :=
  match decodeBundle bundleJson with
  | .error e => errJson e
  | .ok b =>
      let r := checkBundle b
      okWith
        [ ("valid", .bool r.valid)
        , ("conclusion", .string r.conclusion.render)
        , ("conclusionKind", .string (claimKindName r.conclusion))
        , ("assumptions", .array (r.assumptions.toList.map assumptionJson))
        , ("counts", countsJson r.counts)
        , ("countsOver", .string ("the SUPPORT of the conclusion — the steps it "
            ++ "depends on, not every step of the bundle"))
        , ("foundationalOnly", .bool r.foundationalOnly)
        , ("conclusionIsAssumption", .bool r.conclusionIsAssumption)
        , ("checkedSteps", .number (toString b.steps.size))
        , ("soundness", .string "L4Factoidal.FPP0.checkBundle_sound")
        , ("validMeans", .string ("the conclusion is Derives-derivable from the "
            ++ "assumptions reported here; it is NOT a claim that the conclusion "
            ++ "was proved — read counts.foundational, foundationalOnly and "
            ++ "conclusionIsAssumption with it")) ]

/-! ## `proofInspect` -/

private def levelTally (levels : List EvidenceLevel) : LevelCounts :=
  levels.foldl (fun c l => c.bump l) LevelCounts.zero

/-- Distinct adapter names, in order of LAST occurrence. -/
private def adapterNames : List BundleStep → List String
  | [] => []
  | st :: rest =>
      let tail := adapterNames rest
      match st.justification with
      | .adapterEvidence a _ => if tail.contains a then tail else a :: tail
      | .rule _ _ _ => tail

/-- Distinct rule rows used, in order of LAST occurrence. -/
private def rowNames : List BundleStep → List String
  | [] => []
  | st :: rest =>
      let tail := rowNames rest
      match st.justification with
      | .rule r _ _ => if tail.contains r.name then tail else r.name :: tail
      | .adapterEvidence _ _ => tail

/-- `proofInspect(bundleJson)` — the SHAPE of a document, with no
verdict.

It does not call `checkBundle` and reports no `valid` member. Its
`declaredStepLevels` are the levels the PRODUCER WROTE, over every
step of the bundle; `proofCheck`'s `counts` are a different number
over a different set (the support of the conclusion), which is why the
two fields have different names and both carry a label. -/
def proofInspect (bundleJson : String) : String :=
  match decodeBundle bundleJson with
  | .error e => errJson e
  | .ok b =>
      let steps := b.steps.toList
      let asms := b.assumptions.toList
      okWith
        [ ("profile", .string fpp0Profile)
        , ("artifacts", .number (toString b.artifacts.size))
        , ("artifactsWithBody", .number (toString
            (b.artifacts.toList.filter (fun a => a.body.isSome)).length))
        , ("assumptions", .array (asms.map assumptionJson))
        , ("steps", .number (toString b.steps.size))
        , ("declaredStepLevels", countsJson (levelTally (steps.map (·.level))))
        , ("countedOver", .string ("every step of the bundle, at the level its "
            ++ "producer declared — NOT the support of the conclusion, and NOT "
            ++ "checked"))
        , ("rules", .array ((rowNames steps).map Json.string))
        , ("adapters", .array ((adapterNames steps).map Json.string))
        , ("conclusionKind", .string (claimKindName b.conclusion))
        , ("conclusion", .string b.conclusion.render)
        , ("conclusionDeclaredAsAssumption", .bool
            (asms.any (fun a => a.subject == b.conclusion)))
        , ("verdict", .string ("none — proofInspect reads the document and "
            ++ "reports its shape; it runs no check. Call proofCheck for a "
            ++ "verdict.")) ]

/-! ## Build-time pins

`lake build` is this project's test run, and `Wasm/Ops/*.lean` was
outside that net until the CL ops of
https://github.com/danbri/factoidal/issues/623 got `#guard`s: the
dispatch ops were gated only by `Wasm/native-smoke.sh` and
`Wasm/cli-smoke.sh`, which need a built binary and an explicit run. So
the pins live here, where a wrong answer is a build error.

They are a MATCHED PAIR (`skills/measuring-inference` sections 3 and
4). An op that errored on every input would trivially never return a
wrong verdict, so the ACCEPTED half is mandatory: the three real
bundles of `L4Factoidal/Proof/Tests.lean` — the 147-step RDFS witness,
the mixed one-assumption bundle and the R-level adapter bundle —
encoded to JSON, fed to `proofCheck`, and pinned BOTH against literal
expected values AND against the kernel's own `checkBundle` answer for
the same bundle. If the op and the kernel ever disagree,
`envelopeMatchesKernel` is the guard that finds it.

The REJECTED half mutates ONE thing in a document the op accepts, so
the defect is the only difference. Every rejection is
`{"ok":false,...}` — a document that did not parse — and the last pin
of the section is the one that keeps that distinction honest: an
assumption declared `foundational` DECODES fine and comes back
`{"ok":true,"valid":false}`, because the kernel refused a bundle it
could read.

⚠️ The fixtures below are FUNCTIONS of `Unit`, not constants. A
top-level `def` is computed by the module INITIALIZER, and this module
initializes inside the wasm instance — a 147-step RDFS closure and two
RDFC-1.0 digests would then be paid for on every load, by every
caller, whether or not they ever call a proof op. -/

/-- Substring test, written here rather than reached for from
`String`, so a core rename cannot change what these pins mean. -/
private def subOf (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def pfExA : WfIri := ⟨"http://example.org/a", by rfl⟩
private def pfExB : WfIri := ⟨"http://example.org/b", by rfl⟩
private def pfExP : WfIri := ⟨"http://example.org/p", by rfl⟩

private def pfDataTriple : Triple := ⟨.iri pfExA, pfExP, .iri pfExB⟩
private def pfDataGraph : Graph := [pfDataTriple]

/-- POSITIVE 1 — the 147-step RDFS witness wrapped as an FPP0 bundle,
the fixture `Proof/Tests.lean` pins as accepted with an EMPTY
frontier. -/
private def pfRdfsBundle : Unit → Bundle := fun _ =>
  let w := fullClosureWithProof [] [] pfDataGraph
  let ax := axiomaticTriples [] []
  bundleOfRdfsDerivation pfDataGraph ax w.2 (w.2[w.2.size - 1]!).conclusion

/-- POSITIVE 2 — one `replay` assumption feeding one foundational
rdfs4a row, over graph artifacts with NO inline body. -/
private def pfMixedBundle : Unit → Bundle := fun _ =>
  let gd := graphDigest pfDataGraph
  let ad := graphDigest (axiomaticTriples [] [])
  let concl : Triple := ⟨.iri pfExA, rdfType, .iri rdfsResource⟩
  { artifacts :=
      #[ { id := "G",  kind := .graph, digest := gd, body := none },
         { id := "AX", kind := .graph, digest := ad, body := none } ]
    assumptions :=
      #[{ id := "a1", subject := .rdfDerivable gd ad pfDataTriple, level := .replay }]
    steps :=
      #[{ id := "s1"
          justification := .rule .rdfs4a "G" "AX"
          premises := ["a1"]
          conclusion := .rdfDerivable gd ad concl
          level := .foundational
          profile := fpp0Profile
          citation := none }]
    conclusion := .rdfDerivable gd ad concl }

private def pfAdapterStep : BundleStep :=
  { id := "x1"
    justification := .adapterEvidence "sparql" "SELECT ?s WHERE { ?s ?p ?o }"
    premises := ["a1"]
    conclusion := .clif "(exists (v1) (answered v1))"
    level := .replay
    profile := fpp0Profile
    citation := none }

/-- POSITIVE 3 — an R-level adapter step, promoted into the frontier. -/
private def pfAdapterBundle : Unit → Bundle := fun _ =>
  { pfMixedBundle () with
    steps := #[(pfMixedBundle ()).steps[0]!, pfAdapterStep]
    conclusion := .clif "(exists (v1) (answered v1))" }

/-- The same adapter step at `verifiedReplay` WITH the citation
section 8b requires — the control for the missing-citation
rejection. -/
private def pfCitedBundle : Unit → Bundle := fun _ =>
  { pfAdapterBundle () with
    steps := #[(pfMixedBundle ()).steps[0]!,
               { pfAdapterStep with
                 level := .verifiedReplay
                 citation := some { theoremName := "L4Factoidal.SPARQL.eval_sound"
                                    module := "L4Factoidal.SPARQL.Invariants" } }] }

/-- The degenerate bundle of adoption-doc section 8a: the conclusion
is itself a declared assumption. -/
private def pfDegenerateBundle : Unit → Bundle := fun _ =>
  { artifacts := #[]
    assumptions := #[{ id := "a1", subject := .clif "(P jim)", level := .attestation }]
    steps := #[]
    conclusion := .clif "(P jim)" }

/-- A bundle as the document the ops read. `"ENCODE-FAILED"` is not a
document, so every guard below fails loudly if encoding ever does. -/
private def pfJson (b : Bundle) : String :=
  match encodeBundle b with
  | .ok j => j
  | .error _ => "ENCODE-FAILED"

/-- **The round trip**, as a Bool a `#guard` can pin: encode, decode,
and recover the very same bundle. NOT a theorem — the general
N-Triples round trip (`Syntax.SyntaxTheorems.graph_roundtrip`) is
stated and not proved in this tree, so a bundle-level theorem would
rest on an open lemma. The enum layer IS proved, above. -/
private def roundTrips (b : Bundle) : Bool :=
  match decodeBundle (pfJson b) with
  | .error _ => false
  | .ok b' => b' == b

/-- **The op agrees with the kernel.** Every verdict-bearing member of
the envelope, rebuilt from `checkBundle b` and required to be present
in what `proofCheck` returned for the encoded `b`. This is the guard
that fires if the op ever starts computing its own answer. -/
private def envelopeMatchesKernel (b : Bundle) : Bool :=
  let out := proofCheck (pfJson b)
  let r := checkBundle b
  subOf out s!"\"valid\":{r.valid}"
    && subOf out s!"\"foundationalOnly\":{r.foundationalOnly}"
    && subOf out s!"\"conclusionIsAssumption\":{r.conclusionIsAssumption}"
    && subOf out s!"\"counts\":{(countsJson r.counts).toString}"
    && subOf out s!"\"assumptions\":{(Json.array (r.assumptions.toList.map assumptionJson)).toString}"
    && subOf out s!"\"checkedSteps\":{b.steps.size}"

/-! ### ACCEPTED — the three real bundles

Literal pins first. `envelopeMatchesKernel` alone would still pass if
`checkBundle` itself changed its answer, so the numbers the RDFS layer
already pins are restated here against the ABI. -/

-- The 147-step witness: accepted, all foundational, EMPTY frontier,
-- and 4 foundational steps in the SUPPORT of its conclusion out of 147
-- steps in the bundle.
#guard subOf (proofCheck (pfJson (pfRdfsBundle ()))) "\"valid\":true"
#guard subOf (proofCheck (pfJson (pfRdfsBundle ()))) "\"assumptions\":[]"
#guard subOf (proofCheck (pfJson (pfRdfsBundle ()))) "\"foundationalOnly\":true"
#guard subOf (proofCheck (pfJson (pfRdfsBundle ())))
  "\"counts\":{\"foundational\":4,\"verifiedReplay\":0,\"replay\":0,\"attestation\":0}"
#guard subOf (proofCheck (pfJson (pfRdfsBundle ()))) "\"checkedSteps\":147"
#guard roundTrips (pfRdfsBundle ())
#guard envelopeMatchesKernel (pfRdfsBundle ())

-- The mixed bundle: one replay assumption survives in the frontier,
-- one foundational step in the support.
#guard subOf (proofCheck (pfJson (pfMixedBundle ()))) "\"valid\":true"
#guard subOf (proofCheck (pfJson (pfMixedBundle ()))) "\"foundationalOnly\":false"
#guard subOf (proofCheck (pfJson (pfMixedBundle ())))
  "\"id\":\"a1\",\"level\":\"replay\""
#guard subOf (proofCheck (pfJson (pfMixedBundle ())))
  "\"counts\":{\"foundational\":1,\"verifiedReplay\":0,\"replay\":0,\"attestation\":0}"
#guard roundTrips (pfMixedBundle ())
#guard envelopeMatchesKernel (pfMixedBundle ())

-- The adapter bundle: TWO frontier entries, no foundational step in
-- the support, one R.
#guard subOf (proofCheck (pfJson (pfAdapterBundle ()))) "\"valid\":true"
#guard subOf (proofCheck (pfJson (pfAdapterBundle ())))
  "\"counts\":{\"foundational\":0,\"verifiedReplay\":0,\"replay\":1,\"attestation\":0}"
#guard subOf (proofCheck (pfJson (pfAdapterBundle ()))) "\"id\":\"x1\",\"level\":\"replay\""
#guard roundTrips (pfAdapterBundle ())
#guard envelopeMatchesKernel (pfAdapterBundle ())

-- Adoption doc section 8a, SURFACED and not suppressed: a bundle whose
-- conclusion is an assumption comes back valid, with the three fields
-- that say it proves nothing.
#guard subOf (proofCheck (pfJson (pfDegenerateBundle ()))) "\"valid\":true"
#guard subOf (proofCheck (pfJson (pfDegenerateBundle ()))) "\"conclusionIsAssumption\":true"
#guard subOf (proofCheck (pfJson (pfDegenerateBundle ()))) "\"foundationalOnly\":false"
#guard subOf (proofCheck (pfJson (pfDegenerateBundle ()))) "\"foundational\":0"
#guard roundTrips (pfDegenerateBundle ())
#guard envelopeMatchesKernel (pfDegenerateBundle ())

-- `proofInspect` reads the same document and reports NO verdict.
#guard subOf (proofInspect (pfJson (pfRdfsBundle ()))) "\"steps\":147"
#guard subOf (proofInspect (pfJson (pfRdfsBundle ())))
  "\"declaredStepLevels\":{\"foundational\":147,\"verifiedReplay\":0,\"replay\":0,\"attestation\":0}"
#guard !(subOf (proofInspect (pfJson (pfRdfsBundle ()))) "\"valid\"")
#guard subOf (proofInspect (pfJson (pfAdapterBundle ()))) "\"adapters\":[\"sparql\"]"

/-! ### REJECTED — one mutation of an accepted document at a time

Each mutation edits the JSON `pfMixedBundle` (or `pfAdapterBundle`)
encodes to, so the named defect is the only difference between a
document the op accepts and one it refuses. -/

private def pfMixedJson : Unit → String := fun _ => pfJson (pfMixedBundle ())
private def pfAdapterJson : Unit → String := fun _ => pfJson (pfAdapterBundle ())

-- CONTROL: unmutated, both accepted. Every `"ok":false` below is
-- caused by its mutation and by nothing else.
#guard subOf (proofCheck (pfMixedJson ())) "\"ok\":true"
#guard subOf (proofCheck (pfAdapterJson ())) "\"ok\":true"

-- 1. Malformed JSON — the comma after the top-level `profile` member
-- is removed, so the document no longer parses at all.
#guard subOf (proofCheck ((pfMixedJson ()).replace
    "\"profile\":\"fpp0/1\"," "\"profile\":\"fpp0/1\"")) "\"ok\":false"

-- 2. An UNKNOWN level string. Not mapped onto the weakest member, not
-- dropped: refused by name. `decodeLevelName_inj` is the theorem.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"level\":\"replay\"" "\"level\":\"R\""))
  "unknown evidence level 'R'"
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"level\":\"replay\"" "\"level\":\"R\""))
  "\"ok\":false"

-- 3. A MISSING level on the assumption.
#guard subOf (proofCheck ((pfMixedJson ()).replace ",\"level\":\"replay\"}" "}"))
  "bundle.assumptions[0].level: missing required field"

-- 4. A `verifiedReplay` step with no citation (adoption doc section 8b).
#guard subOf (proofCheck ((pfAdapterJson ()).replace
    "\"level\":\"replay\",\"profile\"" "\"level\":\"verifiedReplay\",\"profile\""))
  "bundle.steps[1].citation: missing required field"
-- ...and the SAME step with a citation is accepted, so the rejection is
-- attributable to the missing citation and to nothing else.
#guard subOf (proofCheck (pfJson (pfCitedBundle ()))) "\"valid\":true"

-- 5. An unknown artifact kind, an unknown claim kind, an unknown
-- justification kind and an unknown rule row — four closed vocabularies,
-- four refusals by name.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"kind\":\"graph\"" "\"kind\":\"Graph\""))
  "unknown artifact kind 'Graph'"
#guard subOf (proofCheck ((pfMixedJson ()).replace
    "\"kind\":\"rdfDerivable\"" "\"kind\":\"rdfEntails\"")) "unknown claim kind 'rdfEntails'"
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"kind\":\"rule\"" "\"kind\":\"axiom\""))
  "unknown justification kind 'axiom'"
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"row\":\"rdfs4a\"" "\"row\":\"rdfs99\""))
  "unknown rule row 'rdfs99'"

-- 6. A missing required field — the artifact's digest.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"digest\":" "\"dgest\":"))
  "bundle.artifacts[0].digest: missing required field"

-- 7. A wrong type — a number where a string is expected.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"premises\":[\"a1\"]" "\"premises\":[1]"))
  "bundle.steps[0].premises[0]: must be a JSON string"

-- 8. A duplicate artifact id.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"id\":\"AX\"" "\"id\":\"G\""))
  "bundle.artifacts: duplicate id 'G'"

-- 9. A document written in another profile.
#guard subOf (proofCheck ((pfMixedJson ()).replace "\"profile\":\"fpp0/1\",\"artifacts\""
    "\"profile\":\"fpp0/2\",\"artifacts\"")) "unknown profile 'fpp0/2'"

/-! ### The distinction requirement 4 is about

A DECODE failure is not an INVALID bundle. Every pin above answers
`{"ok":false,…}`. The mutation below is a document the decoder reads
perfectly well and the KERNEL refuses — an assumption declared
`foundational`, which `FPP0.assumptionsOk` rejects — and it comes back
`{"ok":true,"valid":false}`. Without this pin a decoder that refused
everything would satisfy the rejection half above. -/

#guard subOf (proofCheck ((pfMixedJson ()).replace
    "\"level\":\"replay\"}" "\"level\":\"foundational\"}")) "\"ok\":true"
#guard subOf (proofCheck ((pfMixedJson ()).replace
    "\"level\":\"replay\"}" "\"level\":\"foundational\"}")) "\"valid\":false"

/-! ### The enum layer refuses aliases

`decodeLevelName_inj` says no string but a level name decodes to a
level. These pin the near-misses a caller is most likely to send. -/

#guard decodeLevelName "F" = none
#guard decodeLevelName "V" = none
#guard decodeLevelName "R" = none
#guard decodeLevelName "A" = none
#guard decodeLevelName "Replay" = none
#guard decodeLevelName "" = none
#guard decodeRowName "rdfs1" = none
#guard decodeKindName "Graph" = none

/-! ### Axiom audit — expect propext / Classical.choice / Quot.sound only -/

#print axioms L4Wasm.Ops.decodeLevelName_inj
#print axioms L4Wasm.Ops.decodeKindName_inj
#print axioms L4Wasm.Ops.decodeRowName_inj

end L4Wasm.Ops
