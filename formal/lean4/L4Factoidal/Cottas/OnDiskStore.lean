/-
L4Factoidal.Cottas.OnDiskStore — layer 1 of the port of
`RDF.CottasStore`.

The F\* module is the query-time face of a COTTAS file on disk: 2,825
lines, 108 definitions, and ten `assume val`s. This layer covers the
part that needs no file at all — the handle record, the dictionary key
strings, the term/token conversions in both directions, and the
predicate-presence and named-graph answers the handle can give from its
own fields.

## The ten assumptions, and what each becomes here

Two are `cottas_ondisk_open` and `cottas_ondisk_close` — real I/O, and
the F\* banner says so. The other eight are NOT I/O. They are the eight
directions of one dictionary:

    ondisk_id_to_{subj,pred,obj,graph}_token_global   id    → token
    ondisk_lookup_{subj,pred,obj,graph}_id_global     token → id

They are assumed in F\* for a performance reason the source states
plainly: the handle's `coh_*_raw_revmap` assoc-lists are EMPTY on a
lazily-opened handle, so the OCaml runtime answers from a hash table
instead. The F\* source then writes the correctness requirement as a
comment:

> "Soundness: the assume-val outcome must be observably equivalent to
> `revmap_lookup h.coh_*_raw_revmap tok` on a fully-populated handle."

That sentence is the whole contract, and in F\* nothing can check it —
an `assume val` has no body to compare against. Here it is
`TokenTables.AgreesWith`, a proposition; `tablesOfHandle` is the
instance that satisfies it (`tablesOfHandle_agrees`); and
`buildQpRow_agrees` is the consequence the source wanted: under
agreement, the fast path and the assoc-list path return the same row.
An assumption became an argument, and a comment became a theorem.

## The default-graph bound

`graphBoundToRawToken` is where <https://github.com/danbri/factoidal/issues/267>
landed in the F\* tree: `CGB_Default` yields `Some "DEFAULT"`, so a
default-graph query stops matching named-graph rows.
`graphCellMatch_default` states that as an iff rather than leaving it to
the reader of a comment, because the bug it fixed was a `None` that read
as "no constraint".

## What the out-of-range fallbacks mean

Four functions here answer a lookup that cannot be answered:
`idToRawToken` on an id past the end of the list, and the three
`tokenTo*` decoders on a cell that does not parse or does not parse
WHOLE. The F\* source returns a sentinel in each case and says why —
totality, and a value that cannot collide with well-formed data. The
sentinels are transcribed exactly, `oorSentinel` carries the `\x00`
prefix that makes it unreachable as a column token, and
`idToRawToken_outOfRange` pins the branch so a later edit cannot turn
the fallback into a silent `none`.

The decoders require the parser to consume the WHOLE cell — a COTTAS
cell carries a term and nothing else, no trailing dot or whitespace.
`tokenToSubject_partial_falls_back` pins that a trailing byte is a
rejection, not a truncation.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.Ballyhoo
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Cottas.OnDiskStore

open L4Factoidal.RDF
open L4Factoidal.Cottas.Ballyhoo
open L4Factoidal.Syntax

/-! ## 1. The handle

Port of `cottas_ondisk_handle`. Every field is a list the F\* record
holds, in the F\* order, with the `coh_` prefix dropped because the
namespace supplies it. -/

structure Handle where
  /-- Path the handle came from. -/
  path : String
  summary : Option ArtifactSummary := none
  /-- Per-column distinct-term inventories. The INDEX in the list is
  the term-id stored in the per-row int columns. -/
  subjects : List Subject := []
  predicates : List WfIri := []
  objects : List Term := []
  graphs : List Iri := []
  /-- Canonical key string → term-id. -/
  subjRevmap : List (String × Nat) := []
  predRevmap : List (String × Nat) := []
  objRevmap : List (String × Nat) := []
  graphRevmap : List (String × Nat) := []
  /-- Raw column tokens, indexed by term-id. `graphsRaw` does NOT carry
  the `"DEFAULT"` sentinel — only named-graph IRIs in `<iri>` form. -/
  subjectsRaw : List String := []
  predicatesRaw : List String := []
  objectsRaw : List String := []
  graphsRaw : List String := []
  /-- Raw-token-keyed reverse maps. Same shape as the canonical-key
  maps above; both are built at open time. -/
  subjRawRevmap : List (String × Nat) := []
  predRawRevmap : List (String × Nat) := []
  objRawRevmap : List (String × Nat) := []
  graphRawRevmap : List (String × Nat) := []

structure Store where
  artifactPath : String
  summary : Option ArtifactSummary := none
  handle : Handle

/-! ## 2. Pure helpers

`revmapLookup` and `listNth` are transcribed in the F\* shape — the
`if i = 0 then … else listNth tl (i - 1)` form rather than Lean's
pattern match on `i + 1` — so the two trees carry the same recursion.
`listNth_eq_getElem?` proves it is the standard indexing operation, so
everything downstream can reason with `List` lemmas instead of with
this function. -/

def revmapLookup : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (k', v) :: rest, k => if k == k' then some v else revmapLookup rest k

def listNth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | hd :: tl, i => if i = 0 then some hd else listNth tl (i - 1)

theorem listNth_eq_getElem? {α : Type} :
    ∀ (xs : List α) (i : Nat), listNth xs i = xs[i]?
  | [], i => by simp [listNth]
  | _ :: _, 0 => by simp [listNth]
  | _ :: tl, i + 1 => by
      simp only [listNth, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [listNth_eq_getElem? tl i]
      simp

theorem revmapLookup_mem : ∀ (m : List (String × Nat)) (k : String) (v : Nat),
    revmapLookup m k = some v → (k, v) ∈ m
  | [], _, _, h => by simp [revmapLookup] at h
  | (k', v') :: rest, k, v, h => by
      simp only [revmapLookup] at h
      by_cases hk : k == k'
      · rw [if_pos hk] at h
        have : k = k' := by simpa using hk
        subst this
        simp_all
      · rw [if_neg hk] at h
        exact List.mem_cons_of_mem _ (revmapLookup_mem rest k v h)

/-! ## 3. Canonical dictionary keys

Port of `revmap_unit_sep` and the three `*_to_revmap_key` functions.
The separator is U+001F, which RFC 3987 forbids in an IRI and which our
blank-node and lexical-form pipeline does not produce, so the segments
are unambiguous. The tag prefixes (`I_`, `B_`, `L_`, `T_`) keep the four
term families apart. -/

def revmapUnitSep : String := "\x1f"

def subjectToRevmapKey : Subject → String
  | .iri i => "I_" ++ i.val
  | .bnode b => "B_" ++ b

def iriToRevmapKey (i : Iri) : String := "I_" ++ i

/-- Literal keys carry datatype, language tag and lexical form, in that
order. The RDF 1.2 base direction is appended ONLY when present, so
every RDF 1.1 literal keeps its exact pre-1.2 key and the on-disk
dictionary encoding is byte-identical for 1.1 data. -/
def objectToRevmapKey : Term → String
  | .iri i => "I_" ++ i.val
  | .bnode b => "B_" ++ b
  | .literal wl =>
      let l := wl.val
      let tag := match l.langTag with | some t => t | none => ""
      let base := "L_" ++ l.datatype.val ++ revmapUnitSep ++ tag
                    ++ revmapUnitSep ++ l.lexicalForm
      match l.direction with
      | none => base
      | some .ltr => base ++ revmapUnitSep ++ "ltr"
      | some .rtl => base ++ revmapUnitSep ++ "rtl"
  | .tripleTerm s p o =>
      let subj := match s with
        | .iri i => "I_" ++ i.val
        | .bnode b => "B_" ++ b
      "T_" ++ subj ++ revmapUnitSep ++ p.val ++ revmapUnitSep
        ++ objectToRevmapKey o

/-! ## 4. What the handle can answer on its own -/

def Store.summaryOf (ds : Store) : Option ArtifactSummary :=
  ds.handle.summary

/-- A predicate absent from the dictionary cannot appear in any row.
The F\* source notes that this replaced a separate `predicates_seen`
cache: the reverse map already encodes membership. -/
def predicatePresent (ds : Store) (pred : WfIri) : Bool :=
  (revmapLookup ds.handle.predRevmap (iriToRevmapKey pred.val)).isSome

def namedGraphsAux : List Iri → Nat → List (Iri × GraphRef)
  | [], _ => []
  | g :: rest, idx => (g, idx) :: namedGraphsAux rest (idx + 1)

def namedGraphs (ds : Store) : List (Iri × GraphRef) :=
  namedGraphsAux ds.handle.graphs 0

/-- The graph-ref attached to each entry IS its position in the
dictionary list — which is what makes `listNth h.graphs r` the inverse
of this walk. -/
theorem namedGraphsAux_nth : ∀ (gs : List Iri) (base i : Nat),
    listNth (namedGraphsAux gs base) i
      = (listNth gs i).map (fun g => (g, base + i))
  | [], _, _ => by simp [namedGraphsAux, listNth]
  | _ :: _, base, 0 => by simp [namedGraphsAux, listNth]
  | _ :: rest, base, i + 1 => by
      simp only [namedGraphsAux, listNth, Nat.succ_ne_zero, if_false,
                 Nat.add_sub_cancel]
      rw [namedGraphsAux_nth rest (base + 1) i]
      have h : base + 1 + i = base + (i + 1) := by omega
      rw [h]

theorem namedGraphs_nth (ds : Store) (i : Nat) :
    listNth (namedGraphs ds) i
      = (listNth ds.handle.graphs i).map (fun g => (g, i)) := by
  simp [namedGraphs, namedGraphsAux_nth]

/-! ## 5. Bound term-id → raw column token -/

/-- The out-of-range fallback. The `\x00` prefix is what makes it
unreachable as a real column token: a COTTAS cell is an N-Triples term,
and no N-Triples term starts with a NUL. -/
def oorSentinel : String := "\x00cottas_decode_oor"

def idToRawToken (raws : List String) (id : Option TermRef) : Option String :=
  match id with
  | none => none
  | some i =>
      match listNth raws i with
      | some s => some s
      | none => some oorSentinel

theorem idToRawToken_outOfRange (raws : List String) (i : Nat)
    (h : raws.length ≤ i) : idToRawToken raws (some i) = some oorSentinel := by
  simp [idToRawToken, listNth_eq_getElem?, List.getElem?_eq_none h]

/-- `none` accepts any cell; `some s` requires equality. -/
def cellMatch (expected : Option String) (actual : String) : Bool :=
  match expected with
  | none => true
  | some s => s == actual

def graphCellMatch (expected : Option String) (actual : String) : Bool :=
  cellMatch expected actual

theorem cellMatch_none (a : String) : cellMatch none a = true := rfl

theorem cellMatch_some (s a : String) : cellMatch (some s) a = true ↔ s = a := by
  simp [cellMatch]

/-! ## 6. Query-time graph scope

Port of `cottas_ondisk_graph_scope`. There is deliberately no
"unrestricted" constructor: every on-disk backend value is one scope or
the other, never "match anything". That absence is the fix for
<https://github.com/danbri/factoidal/issues/267>. -/

inductive GraphScope where
  | defaultOnly
  | namedGraph (i : Iri)
deriving DecidableEq, Repr

/-! ## 7. The dictionary boundary, as a parameter

The eight `assume val`s of the F\* source, gathered into one record. -/

structure TokenTables where
  idToSubjToken : String → Nat → Option String
  idToPredToken : String → Nat → Option String
  idToObjToken : String → Nat → Option String
  idToGraphToken : String → Nat → Option String
  lookupSubjId : String → String → Option Nat
  lookupPredId : String → String → Option Nat
  lookupObjId : String → String → Option Nat
  lookupGraphId : String → String → Option Nat

/-- The instance a fully-populated handle already determines: read the
four raw-token lists forwards, and the four raw-keyed reverse maps
backwards. This is the definition the F\* soundness comment names. -/
def tablesOfHandle (h : Handle) : TokenTables where
  idToSubjToken := fun _ i => listNth h.subjectsRaw i
  idToPredToken := fun _ i => listNth h.predicatesRaw i
  idToObjToken := fun _ i => listNth h.objectsRaw i
  idToGraphToken := fun _ i => listNth h.graphsRaw i
  lookupSubjId := fun _ t => revmapLookup h.subjRawRevmap t
  lookupPredId := fun _ t => revmapLookup h.predRawRevmap t
  lookupObjId := fun _ t => revmapLookup h.objRawRevmap t
  lookupGraphId := fun _ t => revmapLookup h.graphRawRevmap t

/-- **The F\* source's soundness comment, as a proposition.** A table
agrees with a handle when every one of the eight directions answers what
the handle's own lists would answer. -/
def TokenTables.AgreesWith (tt : TokenTables) (h : Handle) : Prop :=
  (∀ i, tt.idToSubjToken h.path i = listNth h.subjectsRaw i) ∧
  (∀ i, tt.idToPredToken h.path i = listNth h.predicatesRaw i) ∧
  (∀ i, tt.idToObjToken h.path i = listNth h.objectsRaw i) ∧
  (∀ i, tt.idToGraphToken h.path i = listNth h.graphsRaw i) ∧
  (∀ t, tt.lookupSubjId h.path t = revmapLookup h.subjRawRevmap t) ∧
  (∀ t, tt.lookupPredId h.path t = revmapLookup h.predRawRevmap t) ∧
  (∀ t, tt.lookupObjId h.path t = revmapLookup h.objRawRevmap t) ∧
  (∀ t, tt.lookupGraphId h.path t = revmapLookup h.graphRawRevmap t)

theorem tablesOfHandle_agrees (h : Handle) : (tablesOfHandle h).AgreesWith h :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## 8. Bounds and rows over the boundary -/

/-- `.default` yields `"DEFAULT"`, so a default-graph query filters OUT
named-graph rows the same way a named bound filters out every other
graph. `.unbound` keeps its "no constraint" contract; no on-disk caller
produces it. -/
def graphBoundToRawToken (tt : TokenTables) (path : String) :
    GraphBound → Option String
  | .unbound => none
  | .default => some "DEFAULT"
  | .named r => tt.idToGraphToken path r

theorem graphCellMatch_default (tt : TokenTables) (path actual : String) :
    graphCellMatch (graphBoundToRawToken tt path .default) actual = true
      ↔ actual = "DEFAULT" := by
  simp only [graphCellMatch, graphBoundToRawToken]
  rw [cellMatch_some]
  exact eq_comm

theorem graphCellMatch_unbound (tt : TokenTables) (path actual : String) :
    graphCellMatch (graphBoundToRawToken tt path .unbound) actual = true := rfl

def idToRawTokenViaGlobal (lookup : String → Nat → Option String)
    (path : String) (id : Option TermRef) : Option String :=
  match id with
  | none => none
  | some i => lookup path i

/-- Build the reference-shaped row for a matched row's four tokens.
A `"DEFAULT"` graph cell becomes `none`, which is what marks the row as
a default-graph row downstream. -/
def buildQpRow (tt : TokenTables) (h : Handle)
    (sTok pTok oTok gTok : String) : QpRow :=
  { s := tt.lookupSubjId h.path sTok
    p := tt.lookupPredId h.path pTok
    o := tt.lookupObjId h.path oTok
    g := if gTok == "DEFAULT" then none
         else tt.lookupGraphId h.path gTok }

theorem buildQpRow_default_graph (tt : TokenTables) (h : Handle)
    (sTok pTok oTok : String) :
    (buildQpRow tt h sTok pTok oTok "DEFAULT").g = none := by
  simp [buildQpRow]

/-- **What the F\* comment asked for.** Under agreement the assumed
tables and the handle's own assoc-lists build the SAME row, so the fast
path is a refinement of the specification rather than a second
specification. -/
theorem buildQpRow_agrees (tt : TokenTables) (h : Handle)
    (hag : tt.AgreesWith h) (sTok pTok oTok gTok : String) :
    buildQpRow tt h sTok pTok oTok gTok
      = buildQpRow (tablesOfHandle h) h sTok pTok oTok gTok := by
  obtain ⟨_, _, _, _, hs, hp, ho, hg⟩ := hag
  simp [buildQpRow, tablesOfHandle, hs, hp, ho, hg]

/-- On an IN-RANGE id the two id→token directions agree. -/
theorem idToRawTokenViaGlobal_agrees (tt : TokenTables) (h : Handle)
    (hag : tt.AgreesWith h) (i : Nat) (hi : i < h.subjectsRaw.length) :
    idToRawTokenViaGlobal tt.idToSubjToken h.path (some i)
      = idToRawToken h.subjectsRaw (some i) := by
  obtain ⟨hs, _⟩ := hag
  have hxe : listNth h.subjectsRaw i = some h.subjectsRaw[i] := by
    rw [listNth_eq_getElem?]; exact List.getElem?_eq_getElem hi
  simp [idToRawTokenViaGlobal, idToRawToken, hs i, hxe]

/-- ⚠️ **And out of range they DIVERGE**, which the F\* source does not
say anywhere. `idToRawToken` returns the sentinel — a token that matches
no row, so the query returns nothing. `idToRawTokenViaGlobal` returns
`none` — which `cellMatch` reads as NO CONSTRAINT, so the query returns
every row on that column.

A caller that reaches for the wrong one on an id the dictionary does not
hold gets the opposite answer, and neither function's own type says so.
The F\* callers all short-circuit an unresolvable bound to an empty
result before this point, so the divergence is not live today; it is one
edit away from being live, which is why it is stated here rather than
left to be rediscovered. -/
theorem idToRawTokenViaGlobal_outOfRange_differs (tt : TokenTables)
    (h : Handle) (hag : tt.AgreesWith h) (i : Nat)
    (hi : h.subjectsRaw.length ≤ i) :
    idToRawTokenViaGlobal tt.idToSubjToken h.path (some i) = none
      ∧ idToRawToken h.subjectsRaw (some i) = some oorSentinel := by
  obtain ⟨hs, _⟩ := hag
  refine ⟨?_, idToRawToken_outOfRange h.subjectsRaw i hi⟩
  simp [idToRawTokenViaGlobal, hs i, listNth_eq_getElem?,
        List.getElem?_eq_none hi]

/-! ## 9. Cell token → typed term

The COTTAS cell grammar is a subset of the N-Triples term grammar, so
these reuse the shipping reader rather than adding a second parser. The
whole cell must be consumed: a COTTAS cell carries the term and nothing
else, no trailing whitespace and no dot. -/

def cottasDecodeOorPredicate : WfIri :=
  ⟨"urn:factoidal:cottas-decode-predicate-unknown-id", by decide⟩

def tokenToSubject (tok : String) : Subject :=
  match readSubject 0 tok.toList with
  | .ok (s, _, []) => s
  | _ => .bnode "cottas_decode_oor"

def tokenToPredicate (tok : String) : WfIri :=
  match readPredicate 0 tok.toList with
  | .ok (p, _, []) => p
  | _ => cottasDecodeOorPredicate

def tokenToObject (tok : String) : Term :=
  match readObject11 0 tok.toList with
  | .ok (o, _, []) => o
  | _ => .bnode "cottas_decode_oor"

/-- Graph cells are IRI-only. The `"DEFAULT"` sentinel is handled by the
caller BEFORE this is reached. -/
def tokenToGraphName (tok : String) : Iri :=
  match readPredicate 0 tok.toList with
  | .ok (g, _, []) => g.val
  | _ => ""

/-- A cell with a trailing byte is a REJECTION, not a truncation. -/
theorem tokenToSubject_partial_falls_back
    (tok : String) (s : Subject) (pos : Nat) (c : Char) (rest : List Char)
    (h : readSubject 0 tok.toList = .ok (s, pos, c :: rest)) :
    tokenToSubject tok = .bnode "cottas_decode_oor" := by
  simp [tokenToSubject, h]

/-! ## 10. Typed bound term → cell token

The forward direction. These serialise the QUERY's own term into the
token a cell would hold, so `cellMatch` can compare strings without ever
resolving a corpus-wide term-id.

⚠️ Carried over from the F\* source, disclosed there and repeated here:
the N-Triples literal escaper handles `\\`, `\"`, `\n`, `\r` and `\t`
but not `\b` (0x08) or `\f` (0x0C), which the COTTAS cell grammar also
allows. A bound literal whose lexical form contains a raw backspace or
form feed serialises to the unescaped byte and so fails to match a row
that legitimately holds it. That is a gap in the serialiser shared by
every one of its callers, not something this module papers over. -/

def boundSubjectToToken (s : Subject) : String :=
  Syntax.Subject.toNTriples s

def boundPredicateToToken (p : WfIri) : String := "<" ++ p.val ++ ">"

def boundObjectToToken (o : Term) : String :=
  match Term.toNTriples .rdf12 o with
  | .ok s => s
  | .error _ => oorSentinel

def boundGraphIriToToken (g : Iri) : String := "<" ++ g ++ ">"

theorem boundPredicateToToken_eq_boundGraph (p : WfIri) :
    boundPredicateToToken p = boundGraphIriToToken p.val := rfl

/-! ## 11. The token-shaped row -/

/-- The four already-decoded raw column tokens, held as-is. Deliberately
a NEW type rather than a change to `QpRow`: that type is shared with the
in-memory path, and this one carries no dictionary reference at all. -/
structure QpRowTok where
  s : String
  p : String
  o : String
  g : String
deriving DecidableEq, Repr, Inhabited

def buildQpRowTok (sTok pTok oTok gTok : String) : QpRowTok :=
  { s := sTok, p := pTok, o := oTok, g := gTok }

/-- Defensive minimum across the four columns of a row group;
well-formed Parquet has them equal. -/
def natMin (a b : Nat) : Nat := if a ≤ b then a else b

theorem natMin_eq_min (a b : Nat) : natMin a b = min a b := by
  simp [natMin, Nat.min_def]

/-! ## Build-time checks -/

private def exA : WfIri := ⟨"http://example.org/a", by decide⟩
private def exB : WfIri := ⟨"http://example.org/b", by decide⟩

/-! Keys keep the term families apart. -/
#guard subjectToRevmapKey (.iri exA) == "I_http://example.org/a"
#guard subjectToRevmapKey (.bnode "b0") == "B_b0"
#guard objectToRevmapKey (.iri exA) == "I_http://example.org/a"
#guard iriToRevmapKey "http://example.org/a" == "I_http://example.org/a"

/-! A plain `xsd:string` literal keys as datatype, empty tag, lexical
form. -/
#guard objectToRevmapKey (.literal (Literal.string "hi"))
        == "L_http://www.w3.org/2001/XMLSchema#string\x1f\x1fhi"

/-! Named graphs come back with position as reference. -/
#guard namedGraphsAux ["g0", "g1", "g2"] 0
        == [("g0", 0), ("g1", 1), ("g2", 2)]
#guard namedGraphsAux ([] : List Iri) 0 == ([] : List (Iri × GraphRef))

/-! Predicate presence reads the reverse map and nothing else. -/
private def hPred : Handle :=
  { path := "/x.cottas",
    predRevmap := [(iriToRevmapKey exA.val, 0)] }
#guard predicatePresent { artifactPath := "/x.cottas", handle := hPred } exA
#guard ! predicatePresent { artifactPath := "/x.cottas", handle := hPred } exB

/-! Out-of-range ids give the sentinel, not `none`. -/
#guard idToRawToken ["<a>", "<b>"] (some 1) == some "<b>"
#guard idToRawToken ["<a>", "<b>"] (some 7) == some oorSentinel
#guard idToRawToken ["<a>"] none == (none : Option String)

/-! A default bound matches the sentinel cell and nothing else. -/
private def ttEmpty : TokenTables :=
  tablesOfHandle { path := "/x.cottas" }
#guard graphCellMatch (graphBoundToRawToken ttEmpty "/x.cottas" .default) "DEFAULT"
#guard ! graphCellMatch (graphBoundToRawToken ttEmpty "/x.cottas" .default) "<http://example.org/g>"
#guard graphCellMatch (graphBoundToRawToken ttEmpty "/x.cottas" .unbound) "<http://example.org/g>"

/-! Cell decode: a whole cell parses, a cell with a trailing byte does
not. -/
#guard tokenToSubject "<http://example.org/a>" == Subject.iri exA
#guard tokenToSubject "<http://example.org/a> " == Subject.bnode "cottas_decode_oor"
#guard tokenToSubject "_:b0" == Subject.bnode "b0"
#guard tokenToPredicate "<http://example.org/a>" == exA
#guard tokenToPredicate "not-a-term" == cottasDecodeOorPredicate
#guard tokenToObject "<http://example.org/a>" == Term.iri exA
#guard tokenToGraphName "<http://example.org/a>" == "http://example.org/a"
#guard tokenToGraphName "DEFAULT" == ""

/-! Bound encode, and the round trip through it. -/
#guard boundSubjectToToken (.iri exA) == "<http://example.org/a>"
#guard boundPredicateToToken exA == "<http://example.org/a>"
#guard boundObjectToToken (.iri exA) == "<http://example.org/a>"
#guard boundGraphIriToToken "http://example.org/a" == "<http://example.org/a>"
#guard tokenToSubject (boundSubjectToToken (.iri exA)) == Subject.iri exA
#guard tokenToSubject (boundSubjectToToken (.bnode "b0")) == Subject.bnode "b0"
#guard tokenToObject (boundObjectToToken (.iri exA)) == Term.iri exA

/-! The row builder, over the handle's own tables. -/
private def hRow : Handle :=
  { path := "/x.cottas",
    subjRawRevmap := [("<http://example.org/a>", 0)],
    predRawRevmap := [("<http://example.org/a>", 0)],
    objRawRevmap := [("<http://example.org/b>", 1)],
    graphRawRevmap := [("<http://example.org/g>", 2)] }

#guard (buildQpRow (tablesOfHandle hRow) hRow
          "<http://example.org/a>" "<http://example.org/a>"
          "<http://example.org/b>" "DEFAULT")
        == { s := some 0, p := some 0, o := some 1, g := none : QpRow }
#guard (buildQpRow (tablesOfHandle hRow) hRow
          "<http://example.org/a>" "<http://example.org/a>"
          "<http://example.org/b>" "<http://example.org/g>")
        == { s := some 0, p := some 0, o := some 1, g := some 2 : QpRow }

/-! An unknown token is `none`, not a sentinel id. -/
#guard (buildQpRow (tablesOfHandle hRow) hRow
          "<http://example.org/zzz>" "<http://example.org/a>"
          "<http://example.org/b>" "DEFAULT").s == (none : Option Nat)

#guard natMin 3 7 == 3
#guard natMin 7 3 == 3

/-! ## Axiom audit -/

#print axioms listNth_eq_getElem?
#print axioms namedGraphsAux_nth
#print axioms tablesOfHandle_agrees
#print axioms buildQpRow_agrees
#print axioms graphCellMatch_default
#print axioms idToRawToken_outOfRange
#print axioms idToRawTokenViaGlobal_outOfRange_differs

end L4Factoidal.Cottas.OnDiskStore
