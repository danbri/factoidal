/-
L4Factoidal.JSONLD.Compact — JSON-LD 1.1 Compaction.

Port of `formal/fstar/JSONLD.Compact.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §6.1 Compaction Algorithm      — `compactElem` / `compactMap` and the
    field and item folds;
  * §6.2 Inverse Context Creation  — `inverseContext`;
  * §6.3 IRI Compaction            — `compactIri`;
  * §6.4 Term Selection            — `selectTerm`;
  * §6.5 Value Compaction          — `compactValue`;
  * the `JsonLdProcessor.compact()` entry point (`compactDocument`):
    expand the input with §5.1 Expansion, process the supplied context
    with §4.1 Context Processing, compact, then re-attach the ORIGINAL
    context value under `@context`.

All map lookups here are on EXPANDED-form JSON (literal `@id` / `@value`
keys — expansion has already resolved aliases), so no alias-aware field
lookup is needed on the input side; aliases matter only for OUTPUT keys,
where `aliasKw` runs the keyword itself through IRI compaction.

## Error model

`Res` (`Except JsonLdError`), where the F* source returns a bare
`option`. The extra information is the manifest's `expectErrorCode`: the
compact manifest's seventeen negative tests name codes such as
`compaction to list of lists` and `IRI confused with prefix`, and this
port produces them, so the probe can check codes as well as failure.
Fuel exhaustion is an honest failure (`contextOverflow`), never a wrong
answer.

## Scoped out

Framing (`@embed`, `@explicit`, `@omitDefault`, `@default`) is a
separate specification with its own suite; `@preserve`, the one framing
keyword that can appear mid-algorithm, is dropped where §6.1 step 12.6
says it may be.

## Termination

The compaction fold recurses over the document tree through a mutual
group. Exactly as the F* source does, every function in that group
carries an explicit fuel `Nat` and decrements it on every call, and the
entry point derives the initial fuel from `Json.size` of the expanded
document. No `partial`, no `sorry`.
-/
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Options and small helpers -/

/-- `arrays` is the API's `compactArrays` option (default true);
`rel` is `compactToRelative` (default true) — whether a `vocab = false`
IRI compaction may relativize against the active context's base IRI. -/
structure CmpOpts where
  arrays : Bool
  rel    : Bool
  deriving Repr

def cmpLookup {α : Type} (xs : List (String × α)) (k : String) : Option α :=
  (xs.find? (fun kv => kv.1 == k)).map Prod.snd

def cmpField (fields : List (String × Json)) (k : String) : Option Json :=
  cmpLookup fields k

def cmpObjField (v : Json) (k : String) : Option Json :=
  match v with
  | .object fields => cmpField fields k
  | _              => none

def cmpIsScalar : Json → Bool
  | .null | .bool _ | .string _ | .number _ => true
  | _ => false

def cmpIsValueObject : Json → Bool
  | .object fields => hasField "@value" fields
  | _              => false

def cmpIsListObject : Json → Bool
  | .object fields => hasField "@list" fields
  | _              => false

/-- A graph object in EXPANDED form: an `@graph` entry plus at most
`@id` / `@index` siblings (JSON-LD 1.1 §"graph object"). Deliberately
stricter than `Expand`'s "has `@graph`" test, which is right for
expansion's uses and wrong for compaction's container dispatch. -/
def cmpOnlyGraphKeys (fields : List (String × Json)) : Bool :=
  fields.all (fun kv => kv.1 == "@graph" || kv.1 == "@id" || kv.1 == "@index")

def cmpIsGraphObject : Json → Bool
  | .object fields => hasField "@graph" fields && cmpOnlyGraphKeys fields
  | _              => false

def cmpIsSimpleGraph (v : Json) : Bool :=
  cmpIsGraphObject v &&
  (match v with
   | .object fields => !hasField "@id" fields
   | _              => false)

/-- ASCII case fold. The spec lowercases language tags and directions,
both of which are ASCII by grammar (BCP 47 / `"ltr"` / `"rtl"`). -/
def cmpLower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- "Shortest term first, ties broken lexicographically least" — the
ordering both Inverse Context Creation (its term-iteration order) and
compact-IRI candidate preference use. -/
def cmpTermLess (a b : String) : Bool :=
  let la := slen a
  let lb := slen b
  if la < lb then true else if la > lb then false else strLt a b

def cmpKeysOnly (fields : List (String × Json)) (allowed : List String) : Bool :=
  fields.all (fun kv => allowed.contains kv.1)

def cmpRemoveKey (xs : List (String × Json)) (k : String) : List (String × Json) :=
  xs.filter (fun kv => kv.1 != k)

def cmpReplaceOrAdd : List (String × Json) → String → Json → List (String × Json)
  | [],              k, v => [(k, v)]
  | (k2, v2) :: rest, k, v =>
    if k2 == k then (k2, v) :: rest else (k2, v2) :: cmpReplaceOrAdd rest k v

/-! ## "Add value to entry" — API §6.1's spec-text helper

Merge one compacted value into an accumulating field list, wrapping into
or appending onto an array as required. `asArrayF` forces array form on
first insertion. -/

def cmpMergeInto (existing v : Json) : Json :=
  match existing with
  | .array xs => .array (xs ++ [v])
  | x         => .array [x, v]

def cmpAddValue : List (String × Json) → String → Json → Bool → List (String × Json)
  | [],              k, v, asArrayF => [(k, if asArrayF then .array [v] else v)]
  | (k2, v2) :: rest, k, v, asArrayF =>
    if k2 == k then (k2, cmpMergeInto v2 v) :: rest
    else (k2, v2) :: cmpAddValue rest k v asArrayF

def cmpAddValues (res : List (String × Json)) (k : String) : List Json → Bool
    → List (String × Json)
  | [],      _        => res
  | v :: vs, asArrayF => cmpAddValues (cmpAddValue res k v asArrayF) k vs asArrayF

/-- An arbitrary compacted value: arrays SPREAD element-wise (matching
the spec's per-element add-value semantics); an empty array claims the
key with `[]` only if the key is not already present. -/
def cmpGenericAdd (res : List (String × Json)) (k : String) (v : Json) (asArrayF : Bool)
    : List (String × Json) :=
  match v with
  | .array [] => match cmpLookup res k with
                 | some _ => res
                 | none   => res ++ [(k, .array [])]
  | .array xs => cmpAddValues res k xs asArrayF
  | x         => cmpAddValue res k x asArrayF

/-! ## `@nest` plumbing (API §6.1 step 12.8.7)

Adds for a nest-carrying term land inside a map stored under the nest
property's own key in the result. -/

def cmpNestedGet (res : List (String × Json)) : Option String → List (String × Json)
  | none    => res
  | some nk => match cmpLookup res nk with
               | some (.object nf) => nf
               | _                 => []

def cmpNestedPut (res : List (String × Json)) : Option String → List (String × Json)
    → List (String × Json)
  | none,    nres => nres
  | some nk, nres => cmpReplaceOrAdd res nk (.object nres)

/-! ## Term-definition views -/

/-- The term's container mapping as a member LIST (e.g.
`["@graph", "@id", "@set"]`). -/
def cmpContainerList (td : TermDef) : List String :=
  let base :=
    match td.container with
    | ContainerKind.none       => []
    | ContainerKind.list       => ["@list"]
    | ContainerKind.index      => ["@index"]
    | ContainerKind.language   => ["@language"]
    | ContainerKind.id         => ["@id"]
    | ContainerKind.type       => ["@type"]
    | ContainerKind.graph      => ["@graph"]
    | ContainerKind.graphId    => ["@graph", "@id"]
    | ContainerKind.graphIndex => ["@graph", "@index"]
  if td.set_ then base ++ ["@set"] else base

/-- The inverse context's container KEY: the members sorted
lexicographically and concatenated, `"@none"` when there are none
(§6.2 step 3.2). -/
def cmpContainerKey (td : TermDef) : String :=
  match sortStrings (cmpContainerList td) with
  | [] => "@none"
  | xs => String.join xs

def cmpApropTd (ac : ActiveContext) : Option String → Option TermDef
  | some p => match findTerm ac.terms p with
              | some td => if td.iri == "@null" then none else some td
              | none    => none
  | none   => none

def cmpContainerOf (ac : ActiveContext) (aprop : Option String) : List String :=
  match cmpApropTd ac aprop with
  | some td => cmpContainerList td
  | none    => []

def cmpHasContainer (ac : ActiveContext) (aprop : Option String) (c : String) : Bool :=
  (cmpContainerOf ac aprop).contains c

/-- `terms` accumulates redefinitions by PREPENDING (`findTerm` takes the
first hit), so shadowed stale entries must be dropped before any
whole-context iteration (inverse creation, compact-IRI candidates). -/
def cmpDedupeTerms : List (String × TermDef) → List String → List (String × TermDef)
  | [],             _    => []
  | (k, td) :: rest, seen =>
    if seen.contains k then cmpDedupeTerms rest seen
    else (k, td) :: cmpDedupeTerms rest (k :: seen)

def cmpInsertTerm (kv : String × TermDef) : List (String × TermDef) → List (String × TermDef)
  | []      => [kv]
  | y :: rest => if cmpTermLess kv.1 y.1 then kv :: y :: rest else y :: cmpInsertTerm kv rest

def cmpSortTerms : List (String × TermDef) → List (String × TermDef)
  | []        => []
  | x :: rest => cmpInsertTerm x (cmpSortTerms rest)

def cmpLiveTerms (ac : ActiveContext) : List (String × TermDef) :=
  cmpDedupeTerms ac.terms []

def cmpOrderedTerms (ac : ActiveContext) : List (String × TermDef) :=
  cmpSortTerms (cmpLiveTerms ac)

/-! ## Inverse Context Creation — API §6.2

Represented as nested association lists: IRI → container key →
{`@language` / `@type` / `@any` submaps} → term. Entries are inserted
first-writer-wins while walking terms in shortest-least order, which
realises the spec's "only add if no entry exists" preference for shorter
terms. -/

inductive InvSlot where
  | lang | type | any
  deriving DecidableEq, Repr

structure InvMaps where
  language : List (String × String)
  type     : List (String × String)
  any      : List (String × String)
  deriving Repr

def invEmptyMaps : InvMaps := { language := [], type := [], any := [] }

abbrev InverseCtx := List (String × List (String × InvMaps))

def invAddIfAbsent (m : List (String × String)) (k v : String) : List (String × String) :=
  match cmpLookup m k with
  | some _ => m
  | none   => m ++ [(k, v)]

def invMapsAdd (maps : InvMaps) (slot : InvSlot) (k term : String) : InvMaps :=
  match slot with
  | .lang => { maps with language := invAddIfAbsent maps.language k term }
  | .type => { maps with type := invAddIfAbsent maps.type k term }
  | .any  => { maps with any := invAddIfAbsent maps.any k term }

def invUpdateCont : List (String × InvMaps) → String → InvSlot → String → String
    → List (String × InvMaps)
  | [],              ckey, slot, k, term => [(ckey, invMapsAdd invEmptyMaps slot k term)]
  | (c, maps) :: rest, ckey, slot, k, term =>
    if c == ckey then (c, invMapsAdd maps slot k term) :: rest
    else (c, maps) :: invUpdateCont rest ckey slot k term

def invUpdate : InverseCtx → String → String → InvSlot → String → String → InverseCtx
  | [],               iri, ckey, slot, k, term => [(iri, invUpdateCont [] ckey slot k term)]
  | (i, conts) :: rest, iri, ckey, slot, k, term =>
    if i == iri then (i, invUpdateCont conts ckey slot k term) :: rest
    else (i, conts) :: invUpdate rest iri ckey slot k term

/-- §6.2 step 3.11's language-and-direction key: both non-null gives
`"l_d"` lowercased; language only gives the lowercased language;
direction only gives `"_d"`; both explicitly null gives `"@null"`. -/
def invLangDirKey : Option String → Option String → String
  | some l, some d => cmpLower (l ++ "_" ++ d)
  | some l, none   => cmpLower l
  | none,   some d => "_" ++ cmpLower d
  | none,   none   => "@null"

/-- The `(slot, key)` insertions one term definition contributes
(§6.2 steps 3.8-3.15). Every term ALSO contributes `(any, "@none")`,
appended by the fold below — equivalent to the spec's seeding of the
`@any` map at container-map creation, since insertion is
first-writer-wins. -/
def invTermInsertions (ac : ActiveContext) (td : TermDef) (defaultLangKey : String)
    : List (InvSlot × String) :=
  if td.reverse then [(.type, "@reverse")]
  else
    match td.typeMapping with
    | some "@none" => [(.lang, "@any"), (.type, "@any")]
    | some t       => [(.type, t)]
    | none =>
      match td.language, td.direction with
      | some lo, some dopt => [(.lang, invLangDirKey lo dopt)]
      | some lo, none =>
        [(.lang, match lo with | some l => cmpLower l | none => "@null")]
      | none, some dopt =>
        [(.lang, match dopt with | some d => "_" ++ cmpLower d | none => "@none")]
      | none, none =>
        match ac.direction with
        | some d =>
          let langDir := cmpLower ((match ac.language with
                                    | some l => l
                                    | none   => "@none") ++ "_" ++ d)
          [(.lang, langDir), (.lang, "@none"), (.type, "@none")]
        | none =>
          [(.lang, defaultLangKey), (.lang, "@none"), (.type, "@none")]

def invApplyInsertions (inv : InverseCtx) (iri ckey name : String)
    : List (InvSlot × String) → InverseCtx
  | []             => inv
  | (slot, k) :: rest =>
    invApplyInsertions (invUpdate inv iri ckey slot k name) iri ckey name rest

def invFoldTerms (inv : InverseCtx) (ac : ActiveContext) (defaultLangKey : String)
    : List (String × TermDef) → InverseCtx
  | []              => inv
  | (name, td) :: rest =>
    if td.iri == "@null" then invFoldTerms inv ac defaultLangKey rest
    else
      let ckey := cmpContainerKey td
      let ins := invTermInsertions ac td defaultLangKey ++ [(InvSlot.any, "@none")]
      invFoldTerms (invApplyInsertions inv td.iri ckey name ins) ac defaultLangKey rest

def inverseContext (ac : ActiveContext) : InverseCtx :=
  let defaultLangKey := match ac.language with | some l => cmpLower l | none => "@none"
  invFoldTerms [] ac defaultLangKey (cmpOrderedTerms ac)

/-! ## Term Selection — API §6.4 -/

def invSlotMap (maps : InvMaps) (tl : String) : List (String × String) :=
  if tl == "@type" then maps.type
  else if tl == "@any" then maps.any
  else maps.language

def cmpSelectPrefs (m : List (String × String)) : List String → Option String
  | []        => none
  | p :: rest => match cmpLookup m p with
                 | some term => some term
                 | none      => cmpSelectPrefs m rest

def selectTerm (conts : List (String × InvMaps)) : List String → String → List String
    → Option String
  | [],       _,  _     => none
  | c :: rest, tl, prefs =>
    match cmpLookup conts c with
    | some maps =>
      match cmpSelectPrefs (invSlotMap maps tl) prefs with
      | some t => some t
      | none   => selectTerm conts rest tl prefs
    | none => selectTerm conts rest tl prefs

/-! ## IRI Compaction step 4's container / type-language preference
assembly (API §6.3 steps 4.3-4.12) -/

/-- One `@list` item's (item language key, item type) for the
common-language/type walk (§6.3 step 4.6.4). `"@none"` means "no
preference signal"; `"@null"` means "an explicit no-language value". -/
def cmpItemLangType (it : Json) : String × String :=
  match it with
  | .object f =>
    if hasField "@value" f then
      match cmpField f "@direction" with
      | some (.string d) =>
        ((match cmpField f "@language" with
          | some (.string l) => cmpLower (l ++ "_" ++ d)
          | _                => "_" ++ cmpLower d), "@none")
      | _ =>
        match cmpField f "@language" with
        | some (.string l) => (cmpLower l, "@none")
        | _ =>
          match cmpField f "@type" with
          | some (.string t) => ("@none", t)
          | _                => ("@null", "@none")
    else ("@none", "@id")
  | _ => ("@none", "@id")

def cmpListCommonWalk : List Json → Option String → Option String → String × String
  | [],       clang, ctype =>
    ((match clang with | some c => c | none => "@none"),
     (match ctype with | some c => c | none => "@none"))
  | it :: rest, clang, ctype =>
    let (il, ity) := cmpItemLangType it
    let isVal := cmpIsValueObject it
    let clang' := match clang with
                  | none   => some il
                  | some c => if c == il then some c else (if isVal then some "@none" else some c)
    let ctype' := match ctype with
                  | none   => some ity
                  | some c => if c == ity then some c else some "@none"
    cmpListCommonWalk rest clang' ctype'

/-- `(containers, type/language slot, type/language value)` for a
property's value shape. `"@null"` in the third slot is the spec's
null-normalised value. -/
def cmpIriSelectors (ac : ActiveContext) (value : Option Json) (rev : Bool)
    : List String × String × String :=
  let hasIndex := match value with
                  | some (.object f) => hasField "@index" f
                  | _                => false
  let isMap := match value with | some (.object _) => true | _ => false
  let idxPre := match value with
                | some (.object f) =>
                  if hasField "@index" f && !cmpIsGraphObject (.object f)
                  then ["@index", "@index@set"] else []
                | _ => []
  let (mid, tl, tlv) :=
    if rev then (["@set"], "@type", "@reverse")
    else
      match value with
      | some (.object f) =>
        if hasField "@list" f then
          let lst := match cmpField f "@list" with | some v => asArray v | none => []
          let contList := if hasField "@index" f then [] else ["@list"]
          match lst with
          | [] => (contList, "@any", "@none")
          | _  =>
            let (cl, ct) := cmpListCommonWalk lst none none
            if ct != "@none" then (contList, "@type", ct) else (contList, "@language", cl)
        else if cmpIsGraphObject (.object f) then
          let gi := hasField "@index" f
          let gid := hasField "@id" f
          ((if gi then ["@graph@index", "@graph@index@set"] else [])
             ++ (if gid then ["@graph@id", "@graph@id@set"] else [])
             ++ ["@graph", "@graph@set", "@set"]
             ++ (if gi then [] else ["@graph@index", "@graph@index@set"])
             ++ (if gid then [] else ["@graph@id", "@graph@id@set"])
             ++ ["@index", "@index@set"],
           "@type", "@id")
        else if hasField "@value" f then
          let noIdx := !hasField "@index" f
          let (langconts, tl0, tlv0) :=
            match cmpField f "@direction" with
            | some (.string d) =>
              if noIdx then
                (["@language", "@language@set"], "@language",
                 (match cmpField f "@language" with
                  | some (.string l) => cmpLower (l ++ "_" ++ d)
                  | _                => "_" ++ cmpLower d))
              else
                match cmpField f "@type" with
                | some (.string t) => (([] : List String), "@type", t)
                | _                => (([] : List String), "@language", "@null")
            | _ =>
              match cmpField f "@language" with
              | some (.string l) =>
                if noIdx then (["@language", "@language@set"], "@language", cmpLower l)
                else
                  match cmpField f "@type" with
                  | some (.string t) => (([] : List String), "@type", t)
                  | _                => (([] : List String), "@language", "@null")
              | _ =>
                match cmpField f "@type" with
                | some (.string t) => (([] : List String), "@type", t)
                | _                => (([] : List String), "@language", "@null")
          (langconts ++ ["@set"], tl0, tlv0)
        else (["@id", "@id@set", "@type", "@set@type", "@set"], "@type", "@id")
      | _ => (["@id", "@id@set", "@type", "@set@type", "@set"], "@type", "@id")
  let tail2 := if !ac.mode10 && (!isMap || !hasIndex) then ["@index", "@index@set"] else []
  let tail3 :=
    if !ac.mode10 &&
       (match value with
        | some (.object [kv]) => kv.1 == "@value"
        | _                   => false)
    then ["@language", "@language@set"] else []
  (idxPre ++ mid ++ ["@none"] ++ tail2 ++ tail3, tl, tlv)

/-- The `_direction` suffix variant of a language-direction preference
(§6.3 step 4.18): `"de_ltr"` also tries `"_ltr"`. -/
def cmpUnderscoreSuffix (s : String) : Option String :=
  match s.toList.findIdx? (· == '_') with
  | some pos => some (String.ofList (s.toList.drop pos))
  | none     => none

/-! ## IRI Compaction — API §6.3

`depth` bounds the single spec-mandated recursive probe (step 4.15: does
the value's `@id` itself compact to a term that round-trips?); that
probe passes `value = none` so it cannot recurse again. Depth 2 at every
external call site, matching the F* source. -/

def cmpStartsWith (s p : String) : Bool := s.startsWith p

/-- §6.3 step 9: the IRI's scheme/prefix part names a prefix-capable term
whose IRI mapping does NOT actually prefix this IRI (fixture e002). -/
def cmpConfusedWithPrefix (ac : ActiveContext) (iri : String) : Bool :=
  match findColon iri with
  | none      => false
  | some cpos =>
    let pfx := substr iri 0 cpos
    match findTerm ac.terms pfx with
    | some td => td.prefix_ && td.iri != "@null" && !cmpStartsWith iri td.iri
    | none    => false

def cmpCurieLoop (ac : ActiveContext) (iri : String) (hasValue : Bool)
    : List (String × TermDef) → Option String → Option String
  | [],              best => best
  | (name, td) :: rest, best =>
    let li := slen iri
    let lt := slen td.iri
    -- `!td.prefix_`: the 1.1 API's prefix flag — a term may only shorten
    -- an IRI as the prefix half of a compact IRI when its definition
    -- grants prefix status. Deliberately NOT relaxed under `mode10`:
    -- compact/#tp001 ("Compact IRI will not use an expanded term
    -- definition in 1.0", processingMode=json-ld-1.0) pins that the 1.1
    -- API keeps this gate even in 1.0 processing mode, while the 1.0-era
    -- compact/#t0038 expects a genuine 1.0 processor's opposite
    -- behaviour. The two cannot both pass from one engine state; #t0038
    -- is a documented local-override (tests/local-overrides/).
    let skip := (findColon name).isSome || td.iri == "@null" || !td.prefix_
                || lt == 0 || li ≤ lt || !cmpStartsWith iri td.iri
    if skip then cmpCurieLoop ac iri hasValue rest best
    else
      let suffix := substr iri lt (li - lt)
      let candidate := name ++ ":" ++ suffix
      let usable := match findTerm ac.terms candidate with
                    | none     => true
                    | some ctd => !hasValue && ctd.iri == iri
      let better := usable && (match best with
                               | none   => true
                               | some b => cmpTermLess candidate b)
      cmpCurieLoop ac iri hasValue rest (if better then some candidate else best)

/-! ### Relative-reference construction (§6.3 step 10, `compactToRelative`)

Shared-segment stripping, `../` for unshared base directories,
query/fragment reattachment, `./` for the degenerate empty result. -/

def cmpSplitSlash (s : String) : List String := s.splitOn "/"

def cmpStripCommon : List String → List String → Nat → List String × List String
  | b :: brest, i :: irest, last =>
    if b == i && (i :: irest).length > last then cmpStripCommon brest irest last
    else (b :: brest, i :: irest)
  | bs, isegs, _ => (bs, isegs)

def cmpRepeatDotDot : Nat → String
  | 0     => ""
  | n + 1 => "../" ++ cmpRepeatDotDot n

def cmpJoinSlash : List String → String
  | []        => ""
  | [x]       => x
  | x :: rest => x ++ "/" ++ cmpJoinSlash rest

/-- Split an IRI into `(root, path, query?, fragment?)` where `root` is
scheme + `":"` (+ `"//"` + authority when present). Local and minimal on
purpose: relativization needs no more than this, and `Syntax.IriResolve`
exports resolution only. A `""` root means "no scheme found" (not
relativizable). -/
def cmpIriSplit (s : String) : String × String × Option String × Option String :=
  let cs := s.toList
  let n := cs.length
  let idxOf (c : Char) : Nat := match cs.findIdx? (· == c) with
                                | some i => i
                                | none   => n
  let h := idxOf '#'
  let q0 := idxOf '?'
  let hasFrag := h < n
  let hasQuery := q0 < h && q0 < n
  let frag := if hasFrag then some (String.ofList (cs.drop (h + 1))) else none
  let query :=
    if hasQuery then
      let qend := if h < n then h else n
      some (String.ofList ((cs.drop (q0 + 1)).take (qend - q0 - 1)))
    else none
  let pe := if hasQuery then q0 else (if h < n then h else n)
  let c := idxOf ':'
  let sl := idxOf '/'
  let rootLen :=
    if c ≥ n || c ≥ pe || sl < c then 0
    else
      let after := c + 1
      if after + 1 < n && cs[after]? == some '/' && cs[after + 1]? == some '/' then
        let a0 := after + 2
        let asl := match (cs.drop a0).findIdx? (· == '/') with
                   | some i => a0 + i
                   | none   => n
        if asl < pe then asl else pe
      else after
  let rootLen := if rootLen > pe then pe else rootLen
  (String.ofList (cs.take rootLen),
   String.ofList ((cs.drop rootLen).take (pe - rootLen)),
   query, frag)

def cmpRelativize (base iri : String) : String :=
  let (broot, bpath, _, _) := cmpIriSplit base
  let (iroot, ipath, iq, ifr) := cmpIriSplit iri
  if broot.isEmpty || broot != iroot then iri
  else
    let bsegs := cmpSplitSlash bpath
    let isegs := cmpSplitSlash ipath
    let last := if iq.isSome || ifr.isSome then 0 else 1
    let (brem, irem) := cmpStripCommon bsegs isegs last
    let ups := if brem.length > 0 then brem.length - 1 else 0
    let rel := cmpRepeatDotDot ups ++ cmpJoinSlash irem
    let rel1 := match iq with | some q => rel ++ "?" ++ q | none => rel
    let rel2 := match ifr with | some fg => rel1 ++ "#" ++ fg | none => rel1
    if rel2.isEmpty then "./"
    -- a relative reference that would LOOK like a keyword gets an
    -- explicit "./" prefix (compact/0111: "@special" -> "./@special")
    else if charAtD rel2 0 == '@' then "./" ++ rel2
    else rel2

/-- §6.3. `.error .iriConfusedWithPrefix` is step 9's failure. -/
def compactIri (ac : ActiveContext) (co : CmpOpts) (iri : String)
    (value : Option Json) (vocab rev : Bool) (depth : Nat) : Res String :=
    let inv := inverseContext ac
    let termSel : Option String :=
      if !vocab then none
      else
        match cmpLookup inv iri with
        | none => none
        | some conts =>
          let (containers, tl0, tlv) := cmpIriSelectors ac value rev
          let tl := if tlv == "@none" && tl0 == "@any" then "@any" else tl0
          -- preferred values (steps 4.13-4.18)
          let idPref : Option (List String) :=
            if tlv == "@id" || tlv == "@reverse" then
              match value with
              | some (.object f) =>
                match cmpField f "@id" with
                | some (.string idv) =>
                  let cand := if h : depth = 0 then none
                              else (compactIri ac co idv none true false (depth - 1)).toOption
                  match cand with
                  | some ct =>
                    match findTerm ac.terms ct with
                    | some ctd =>
                      if ctd.iri == idv then some ["@vocab", "@id", "@none"]
                      else some ["@id", "@vocab", "@none"]
                    | none => some ["@id", "@vocab", "@none"]
                  | none => some ["@id", "@vocab", "@none"]
                | _ => none
              | _ => none
            else none
          let prefsBase :=
            match idPref with
            | some ps => if tlv == "@reverse" then "@reverse" :: ps else ps
            | none    => if tlv == "@reverse" then ["@reverse", tlv, "@none"] else [tlv, "@none"]
          let prefs1 := prefsBase ++ ["@any"]
          let prefs := match cmpUnderscoreSuffix tlv with
                       | some u => prefs1 ++ [u]
                       | none   => prefs1
          selectTerm conts containers tl prefs
    match termSel with
    | some t => .ok t
    | none =>
      -- step 5: vocabulary-mapping suffix
      let sfx : Option String :=
        if vocab then
          match ac.vocab with
          | some vm =>
            let li := slen iri
            let lv := slen vm
            if lv > 0 && li > lv && cmpStartsWith iri vm then
              let suffix := substr iri lv (li - lv)
              match findTerm ac.terms suffix with
              | some _ => none
              | none   => some suffix
            else none
          | none => none
        else none
      match sfx with
      | some s => .ok s
      | none =>
        match cmpCurieLoop ac iri value.isSome (cmpLiveTerms ac) none with
        | some c => .ok c
        | none =>
          if cmpConfusedWithPrefix ac iri then .error .iriConfusedWithPrefix
          else if !vocab && co.rel then
            match ac.base with
            | some b => .ok (cmpRelativize b iri)
            | none   => .ok iri
          else .ok iri
termination_by depth
decreasing_by omega

/-- Keyword aliasing. A keyword contains no colon, so `compactIri`
cannot error on it — this total wrapper keeps call sites clean. -/
def aliasKw (ac : ActiveContext) (co : CmpOpts) (kw : String) : String :=
  match compactIri ac co kw none true false 2 with
  | .ok s    => s
  | .error _ => kw

/-! ## Value Compaction — API §6.5

Returns the collapsed scalar when the active property's mappings license
dropping the value-object wrapper; otherwise the (possibly re-keyed)
map. -/

def compactValue (ac : ActiveContext) (co : CmpOpts) (aprop : Option String)
    (vfields : List (String × Json)) : Res Json :=
  let td := cmpApropTd ac aprop
  let tmap := match td with | some t => t.typeMapping | none => none
  let lang : Option String :=
    match td with
    | some t => (match t.language with | some lo => lo | none => ac.language)
    | none   => ac.language
  let dir : Option String :=
    match td with
    | some t => (match t.direction with | some dd => dd | none => ac.direction)
    | none   => ac.direction
  let hasIndex := hasField "@index" vfields
  let preserveIndex := hasIndex && !cmpHasContainer ac aprop "@index"
  if hasField "@id" vfields && cmpKeysOnly vfields ["@id", "@index"] then
    -- step 6: a subject reference
    match cmpField vfields "@id" with
    | some (.string idv) =>
      if tmap == some "@id" then
        match compactIri ac co idv none false false 2 with
        | .ok s    => .ok (.string s)
        | .error e => .error e
      else if tmap == some "@vocab" then
        match compactIri ac co idv none true false 2 with
        | .ok s    => .ok (.string s)
        | .error e => .error e
      else .ok (.object vfields)
    | _ => .ok (.object vfields)
  else if !hasField "@value" vfields then
    -- a node object that reached here through its `@id` entry but is not
    -- a bare reference: value compaction leaves it alone and §6.1's map
    -- processing takes over
    .ok (.object vfields)
  else
    let vval := match cmpField vfields "@value" with | some v => v | none => .null
    let vtypeS := match cmpField vfields "@type" with | some (.string t) => some t | _ => none
    let vlangS := match cmpField vfields "@language" with | some (.string l) => some l | _ => none
    let vdirS := match cmpField vfields "@direction" with | some (.string d) => some d | _ => none
    let tmapNone := tmap == some "@none"
    let langMatches := match vlangS, lang with
                       | some a, some b => cmpLower a == cmpLower b
                       | none,   none   => true
                       | _, _           => false
    let dirMatches := match vdirS, dir with
                      | some a, some b => cmpLower a == cmpLower b
                      | none,   none   => true
                      | _, _           => false
    let typeCollapse := vtypeS.isSome && tmap.isSome && vtypeS == tmap
    let valueIsString := match vval with | .string _ => true | _ => false
    if !preserveIndex && !tmapNone && typeCollapse then .ok vval
    else if !preserveIndex && !tmapNone && vtypeS.isNone && !valueIsString
            && vlangS.isNone && vdirS.isNone then .ok vval
    else if !preserveIndex && !tmapNone && vtypeS.isNone && langMatches && dirMatches then .ok vval
    else
      -- keep the map, re-keyed through the active context's aliases,
      -- with the datatype IRI compacted (steps 8.1 + 11)
      let idxFields :=
        if preserveIndex then
          match cmpField vfields "@index" with
          | some ix => [(aliasKw ac co "@index", ix)]
          | none    => []
        else []
      let langFields := match vlangS with
                        | some l => [(aliasKw ac co "@language", Json.string l)]
                        | none   => []
      let dirFields := match vdirS with
                       | some d => [(aliasKw ac co "@direction", Json.string d)]
                       | none   => []
      match vtypeS with
      | some t =>
        match compactIri ac co t none true false 2 with
        | .error e => .error e
        | .ok ct =>
          .ok (.object (idxFields ++ [(aliasKw ac co "@type", Json.string ct)]
                                  ++ [(aliasKw ac co "@value", vval)]))
      | none =>
        .ok (.object (idxFields ++ langFields ++ dirFields
                      ++ [(aliasKw ac co "@value", vval)]))

/-- The nest target for a compacted item property. `ok none` = no
nesting; `ok (some nk)` = nest under key `nk`; `error` = the term's
`@nest` member neither is nor expands to the `@nest` keyword. -/
def cmpNestOf (ac : ActiveContext) (iap : String) : Res (Option String) :=
  match findTerm ac.terms iap with
  | some td =>
    match td.nest with
    | none    => .ok none
    | some nt =>
      if nt == "@nest" then .ok (some nt)
      else
        match expandIri ac nt true with
        | some e => if e == "@nest" then .ok (some nt) else .error .invalidNestValue
        | none   => .error .invalidNestValue
  | none => .ok none

/-- Move reverse-capable properties out of a compacted `@reverse` map
into the parent result (§6.1 step 12.3.2). -/
def cmpMoveReverse (ac : ActiveContext) (co : CmpOpts)
    : List (String × Json) → List (String × Json) → List (String × Json)
    → List (String × Json) × List (String × Json)
  | [],            leftover, res => (leftover, res)
  | (p, pv) :: rest, leftover, res =>
    match findTerm ac.terms p with
    | some td =>
      if td.reverse then
        let asArrayF := td.set_ || !co.arrays
        let res1 := match pv with
                    | .array xs => cmpAddValues res p xs asArrayF
                    | x         => cmpAddValue res p x asArrayF
        cmpMoveReverse ac co rest leftover res1
      else cmpMoveReverse ac co rest (leftover ++ [(p, pv)]) res
    | none => cmpMoveReverse ac co rest (leftover ++ [(p, pv)]) res

/-- `@type` output values compact against the TYPE-SCOPED context
snapshot (§6.1 step 12.2 — the pre-pop, pre-property-scoped active
context), preserving input order. -/
def cmpCompactTypes (tsc : ActiveContext) (co : CmpOpts) : List Json → Res (List String)
  | []              => .ok []
  | .string t :: rest =>
    match compactIri tsc co t none true false 2 with
    | .error e => .error e
    | .ok ct   => match cmpCompactTypes tsc co rest with
                  | .ok cs   => .ok (ct :: cs)
                  | .error e => .error e
  | _ :: rest => cmpCompactTypes tsc co rest

/-! ## The Compaction Algorithm — API §6.1 (the mutual group)

Fuel decreases on every mutual call; exhaustion is `contextOverflow`. -/

mutual

/-- §6.1 on an arbitrary element. -/
def compactElem (loader : Loader) (ac : ActiveContext) (aprop : Option String)
    (elem : Json) (co : CmpOpts) (fuel : Nat) : Res Json :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match elem with
    | .null | .bool _ | .string _ | .number _ => .ok elem
    | .array items =>
      match compactItems loader ac aprop items co fuel with
      | .error e => .error e
      | .ok outs =>
        let collapse := co.arrays
                        && (match outs with | [_] => true | _ => false)
                        && aprop != some "@graph" && aprop != some "@set"
                        && (cmpContainerOf ac aprop).isEmpty
        if collapse then
          match outs with
          | [x] => .ok x
          | _   => .ok (.array outs)
        else .ok (.array outs)
    | .object fields => compactMap loader ac aprop fields co fuel
termination_by fuel

def compactItems (loader : Loader) (ac : ActiveContext) (aprop : Option String)
    (items : List Json) (co : CmpOpts) (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | []       => .ok []
    | it :: rest =>
      match compactElem loader ac aprop it co fuel with
      | .error e => .error e
      | .ok c =>
        match compactItems loader ac aprop rest co fuel with
        | .error e => .error e
        | .ok cs   => .ok (c :: cs)
termination_by fuel

/-- §6.1 steps 4-7 on a map element. -/
def compactMap (loader : Loader) (ac0 : ActiveContext) (aprop : Option String)
    (fields : List (String × Json)) (co : CmpOpts) (fuel : Nat) : Res Json :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    -- step 4: snapshot the type-scoped context
    let tsc := ac0
    -- step 5: pop a non-propagated context unless the element is a value
    -- object or a bare node reference
    let isValue := hasField "@value" fields
    let idOnly := match fields with | [kv] => kv.1 == "@id" | _ => false
    let ac1 := if ac0.prev.isEmpty then ac0
               else if isValue || idOnly then ac0 else ac0.pop
    -- step 6: the active property's own scoped context, found in the
    -- PRE-pop context and applied onto the popped one, override protected
    let ac2Res : Res ActiveContext :=
      match cmpApropTd tsc aprop with
      | some td =>
        match td.scopedContext with
        | some (scopedCtx, defUrl) =>
          applyContextWithPropagate loader (ac1.upd (fun c => { c with docUrl := defUrl }))
            scopedCtx true true
        | none => .ok ac1
      | none => .ok ac1
    match ac2Res with
    | .error e => .error e
    | .ok ac2 =>
      -- step 7: value compaction for value objects and node references
      let hasId := hasField "@id" fields
      let tmap2 := match cmpApropTd ac2 aprop with | some t => t.typeMapping | none => none
      if isValue || hasId then
        match compactValue ac2 co aprop fields with
        | .error e => .error e
        | .ok r =>
          if cmpIsScalar r || tmap2 == some "@json" then .ok r
          else compactMapBody loader ac2 tsc aprop fields co fuel
      else compactMapBody loader ac2 tsc aprop fields co fuel
termination_by fuel

/-- §6.1 steps 8-12. -/
def compactMapBody (loader : Loader) (ac2 tsc : ActiveContext) (aprop : Option String)
    (fields : List (String × Json)) (co : CmpOpts) (fuel : Nat) : Res Json :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    -- step 8: a list object under an `@list`-container property compacts
    -- to its bare item array
    if cmpIsListObject (.object fields) && cmpHasContainer ac2 aprop "@list" then
      match cmpField fields "@list" with
      | some lv => compactElem loader ac2 aprop lv co fuel
      | none    => .error .notJsonLd
    else
      let insideRev := aprop == some "@reverse"
      -- step 11: apply the type-scoped contexts named by this node's
      -- compacted `@type` terms (looked up in `tsc`, folded onto `ac2`,
      -- sorted, propagate false)
      let rawTypes := match cmpField fields "@type" with | some v => asArray v | none => []
      match cmpCompactTypes tsc co rawTypes with
      | .error e => .error e
      | .ok ctypeNames =>
        match applyTypeScoped loader tsc ac2 (sortStrings ctypeNames) false with
        | .error e => .error e
        | .ok (ac3a, anyNonProp) =>
          let ac3 := if anyNonProp then ac3a.setPrev ac2 else ac3a
          match compactFields loader ac3 tsc aprop insideRev fields [] co fuel with
          | .error e => .error e
          | .ok res  => .ok (.object res)
termination_by fuel

/-- §6.1 step 12: fold this node's members into the result. -/
def compactFields (loader : Loader) (ac tsc : ActiveContext) (aprop : Option String)
    (insideRev : Bool) (pending res : List (String × Json)) (co : CmpOpts) (fuel : Nat)
    : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match pending with
    | []            => .ok res
    | (k, v) :: rest =>
      if k == "@id" then
        match v with
        | .string s =>
          match compactIri ac co s none false false 2 with
          | .error e => .error e
          | .ok cs =>
            compactFields loader ac tsc aprop insideRev rest
              (res ++ [(aliasKw ac co "@id", Json.string cs)]) co fuel
        | _ =>
          compactFields loader ac tsc aprop insideRev rest
            (res ++ [(aliasKw ac co "@id", v)]) co fuel
      else if k == "@type" then
        match cmpCompactTypes tsc co (asArray v) with
        | .error e => .error e
        | .ok cts =>
          let alias := aliasKw ac co "@type"
          let asSet := !ac.mode10 && (match findTerm ac.terms alias with
                                      | some td => td.set_
                                      | none    => false)
          let cv := match cts with
                    | [single] => if co.arrays && !asSet then Json.string single
                                  else Json.array [Json.string single]
                    | xs       => Json.array (xs.map Json.string)
          compactFields loader ac tsc aprop insideRev rest (res ++ [(alias, cv)]) co fuel
      else if k == "@reverse" then
        match compactElem loader ac (some "@reverse") v co fuel with
        | .error e => .error e
        | .ok cv =>
          match cv with
          | .object rf =>
            let (leftover, res1) := cmpMoveReverse ac co rf [] res
            let res2 := match leftover with
                        | [] => res1
                        | _  => res1 ++ [(aliasKw ac co "@reverse", Json.object leftover)]
            compactFields loader ac tsc aprop insideRev rest res2 co fuel
          | _ =>
            compactFields loader ac tsc aprop insideRev rest
              (res ++ [(aliasKw ac co "@reverse", cv)]) co fuel
      else if k == "@index" && cmpHasContainer ac aprop "@index" then
        -- step 12.5: the `@index` is re-expressed as the parent's map key
        compactFields loader ac tsc aprop insideRev rest res co fuel
      else if k == "@index" || k == "@value" || k == "@language" || k == "@direction" then
        compactFields loader ac tsc aprop insideRev rest
          (res ++ [(aliasKw ac co k, v)]) co fuel
      else if k == "@preserve" then
        -- framing-only keyword; never present in expanded (non-framed) input
        compactFields loader ac tsc aprop insideRev rest res co fuel
      else
        match v with
        | .array [] =>
          -- step 12.7: preserve an empty property value as an empty array
          match compactIri ac co k (some (.array [])) true insideRev 2 with
          | .error e => .error e
          | .ok iap =>
            match cmpNestOf ac iap with
            | .error e => .error e
            | .ok nest =>
              let nres := cmpNestedGet res nest
              let nres1 := match cmpLookup nres iap with
                           | some _ => nres
                           | none   => nres ++ [(iap, Json.array [])]
              compactFields loader ac tsc aprop insideRev rest
                (cmpNestedPut res nest nres1) co fuel
        | _ =>
          match compactPropItems loader ac k (asArray v) insideRev res co fuel with
          | .error e  => .error e
          | .ok res1  => compactFields loader ac tsc aprop insideRev rest res1 co fuel
termination_by fuel

def compactPropItems (loader : Loader) (ac : ActiveContext) (k : String)
    (items : List Json) (insideRev : Bool) (res : List (String × Json))
    (co : CmpOpts) (fuel : Nat) : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | []         => .ok res
    | it :: rest =>
      match compactOneItem loader ac k it insideRev res co fuel with
      | .error e => .error e
      | .ok res1 => compactPropItems loader ac k rest insideRev res1 co fuel
termination_by fuel

/-- §6.1 step 12.8 for one item of one property. -/
def compactOneItem (loader : Loader) (ac : ActiveContext) (k : String) (item : Json)
    (insideRev : Bool) (res : List (String × Json)) (co : CmpOpts) (fuel : Nat)
    : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match compactIri ac co k (some item) true insideRev 2 with
    | .error e => .error e
    | .ok iap =>
      match cmpNestOf ac iap with
      | .error e => .error e
      | .ok nest =>
        let tdIap := findTerm ac.terms iap
        let container := match tdIap with
                         | some td => if td.iri == "@null" then [] else cmpContainerList td
                         | none    => []
        let isList := cmpIsListObject item
        let isGraph := cmpIsGraphObject item
        let inner := if isList then (match cmpObjField item "@list" with
                                     | some x => x | none => item)
                     else if isGraph then (match cmpObjField item "@graph" with
                                           | some x => x | none => item)
                     else item
        match compactElem loader ac (some iap) inner co fuel with
        | .error e => .error e
        | .ok ci0 =>
          let nres := cmpNestedGet res nest
          if isList then
            let ciArr := match ci0 with | .array _ => ci0 | x => .array [x]
            if !container.contains "@list" then
              let listobj := [(aliasKw ac co "@list", ciArr)]
                             ++ (match cmpObjField item "@index" with
                                 | some ix => [(aliasKw ac co "@index", ix)]
                                 | none    => [])
              cmpItemAdd loader ac k iap container item (.object listobj) nest res nres co fuel
            else
              -- an `@list` container holds AT MOST one list; a second is
              -- the "compaction to list of lists" error (fixture e001)
              match cmpLookup nres iap with
              | some _ => .error .compactionToListOfLists
              | none   => .ok (cmpNestedPut res nest (nres ++ [(iap, ciArr)]))
          else if isGraph then
            compactGraphItem loader ac k iap container item ci0 nest res nres co fuel
          else
            cmpItemAdd loader ac k iap container item ci0 nest res nres co fuel
termination_by fuel

/-- §6.1 step 12.8.9: a graph object under the various `@graph`
containers. -/
def compactGraphItem (_loader : Loader) (ac : ActiveContext) (_k iap : String)
    (container : List String) (item ci0 : Json) (nest : Option String)
    (res nres : List (String × Json)) (co : CmpOpts) (fuel : Nat)
    : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | _ + 1 =>
    let asSet := container.contains "@set"
    let hasGraph := container.contains "@graph"
    if hasGraph && container.contains "@id" then
      let keyRes := match cmpObjField item "@id" with
                    | some (.string gid) => compactIri ac co gid none false false 2
                    | _                  => compactIri ac co "@none" none true false 2
      match keyRes with
      | .error e => .error e
      | .ok keyk =>
        let mapObj := match cmpLookup nres iap with | some (.object mf) => mf | _ => []
        -- the compacted graph content is an array of graph NODES; spread
        -- them into the map entry (t0084: a single node collapses, `@set`
        -- keeps the array)
        let mapObj1 := cmpGenericAdd mapObj keyk ci0 asSet
        .ok (cmpNestedPut res nest (cmpReplaceOrAdd nres iap (.object mapObj1)))
    else if hasGraph && container.contains "@index" && cmpIsSimpleGraph item then
      let keyk := match cmpObjField item "@index" with
                  | some (.string ix) => ix
                  | _                 => aliasKw ac co "@none"
      let mapObj := match cmpLookup nres iap with | some (.object mf) => mf | _ => []
      let mapObj1 := cmpGenericAdd mapObj keyk ci0 asSet
      .ok (cmpNestedPut res nest (cmpReplaceOrAdd nres iap (.object mapObj1)))
    else if hasGraph && cmpIsSimpleGraph item then
      -- multiple nodes of one simple graph re-wrap under `@included`
      let ci1 := match ci0 with
                 | .array xs => if xs.length > 1 then .object [(aliasKw ac co "@included", ci0)]
                                else ci0
                 | _ => ci0
      let asArrayF := !co.arrays || asSet
      .ok (cmpNestedPut res nest (cmpGenericAdd nres iap ci1 asArrayF))
    else
      -- no matching graph container: wrap explicitly as a graph object
      let ci1 := match ci0 with
                 | .array [x] => if co.arrays then x else ci0
                 | _          => ci0
      let idFieldsRes : Res (List (String × Json)) :=
        match cmpObjField item "@id" with
        | some (.string gid) =>
          match compactIri ac co gid none false false 2 with
          | .ok cg   => .ok [(aliasKw ac co "@id", Json.string cg)]
          | .error e => .error e
        | _ => .ok []
      match idFieldsRes with
      | .error e => .error e
      | .ok idFields =>
        let gwrap := [(aliasKw ac co "@graph", ci1)] ++ idFields
                     ++ (match cmpObjField item "@index" with
                         | some ix => [(aliasKw ac co "@index", ix)]
                         | none    => [])
        let asArrayF := !co.arrays || asSet
        .ok (cmpNestedPut res nest (cmpGenericAdd nres iap (.object gwrap) asArrayF))

/-- §6.1 step 12.8.9.6-9: add one compacted item under `iap`, honouring
the `@language` / `@index` / `@id` / `@type` container maps. -/
def cmpItemAdd (loader : Loader) (ac : ActiveContext) (k iap : String)
    (container : List String) (item ci : Json) (nest : Option String)
    (res nres : List (String × Json)) (co : CmpOpts) (fuel : Nat)
    : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    let asSet := container.contains "@set"
    if container.contains "@language" || container.contains "@index"
       || container.contains "@id" || container.contains "@type" then
      let mapObj := match cmpLookup nres iap with | some (.object mf) => mf | _ => []
      -- (map key if determined, adjusted compacted item, needs-@type-recompact)
      let stepRes : Option (Option String × Json × Bool) :=
        if container.contains "@language" then
          let ci' := match item with
                     | .object f =>
                       if hasField "@value" f then
                         (match cmpField f "@value" with | some vv => vv | none => ci)
                       else ci
                     | _ => ci
          some ((match cmpObjField item "@language" with
                 | some (.string l) => some l
                 | _                => none), ci', false)
        else if container.contains "@index" then
          match findTerm ac.terms iap with
          | some td =>
            match td.index with
            | some ik =>
              -- property-valued index: pull the index property's first
              -- value out of the compacted item as the map key. The
              -- container key is tried under the RAW `index` spelling
              -- first (how the property usually appears in the compacted
              -- item — compact/0112, 0114), then under the IRI compaction
              -- of its expansion (the spec's "reinitialize container key
              -- by IRI compacting index key", needed when `index` is
              -- spelled as an absolute IRI — compact/0113).
              match ci with
              | .object cf =>
                let ckOpt : Option String :=
                  match cmpLookup cf ik with
                  | some _ => some ik
                  | none =>
                    match expandIri ac ik true with
                    | some ikiri => (compactIri ac co ikiri none true false 2).toOption
                    | none       => none
                match ckOpt with
                | none    => some (none, ci, false)
                | some ck =>
                  match cmpLookup cf ck with
                  | some kv =>
                    match asArray kv with
                    | .string k0 :: others =>
                      let cf1 := match others with
                                 | []  => cmpRemoveKey cf ck
                                 | [o] => cmpReplaceOrAdd cf ck o
                                 | os  => cmpReplaceOrAdd cf ck (.array os)
                      some (some k0, .object cf1, false)
                    | _ => some (none, ci, false)
                  | none => some (none, ci, false)
              | _ => some (none, ci, false)
            | none =>
              let ci' := match ci with
                         | .object cf => Json.object (cmpRemoveKey cf (aliasKw ac co "@index"))
                         | _          => ci
              some ((match cmpObjField item "@index" with
                     | some (.string ix) => some ix
                     | _                 => none), ci', false)
          | none =>
            let ci' := match ci with
                       | .object cf => Json.object (cmpRemoveKey cf (aliasKw ac co "@index"))
                       | _          => ci
            some ((match cmpObjField item "@index" with
                   | some (.string ix) => some ix
                   | _                 => none), ci', false)
        else if container.contains "@id" then
          let idk := aliasKw ac co "@id"
          match ci with
          | .object cf =>
            some ((match cmpLookup cf idk with
                   | some (.string s) => some s
                   | _                => none), Json.object (cmpRemoveKey cf idk), false)
          | _ => some (none, ci, false)
        else
          -- a `@type` map
          let tk := aliasKw ac co "@type"
          match ci with
          | .object cf =>
            match cmpLookup cf tk with
            | some tv =>
              match asArray tv with
              | .string k0 :: others =>
                let cf1 := match others with
                           | []  => cmpRemoveKey cf tk
                           | [o] => cmpReplaceOrAdd cf tk o
                           | os  => cmpReplaceOrAdd cf tk (.array os)
                some (some k0, .object cf1, true)
              | _ => some (none, Json.object (cmpRemoveKey cf tk), true)
            | none => some (none, ci, true)
          | _ => some (none, ci, false)
      match stepRes with
      | none => .error .notJsonLd
      | some (keyOpt, ci1, typeRecheck) =>
        -- `@type`-map refinement: a bare `{"@id": …}` remnant recompacts
        -- as a node reference, possibly all the way to a plain string
        -- (compact/tm020, s002's `mytype`)
        let ci2Res : Res Json :=
          if typeRecheck then
            match ci1 with
            | .object [kv] =>
              if kv.1 == aliasKw ac co "@id" && (cmpObjField item "@id").isSome then
                match cmpObjField item "@id" with
                | some idv =>
                  match compactElem loader ac (some iap) (.object [("@id", idv)]) co fuel with
                  | .error e => .error e
                  | .ok recCi =>
                    match recCi with
                    | .object [kv2] =>
                      if kv2.1 == aliasKw ac co "@id" then .ok kv2.2 else .ok recCi
                    | _ => .ok recCi
                | none => .ok ci1
              else .ok ci1
            | _ => .ok ci1
          else .ok ci1
        match ci2Res with
        | .error e => .error e
        | .ok ci2 =>
          let keyk := match keyOpt with | some s => s | none => aliasKw ac co "@none"
          let mapObj1 := cmpAddValue mapObj keyk ci2 asSet
          .ok (cmpNestedPut res nest (cmpReplaceOrAdd nres iap (.object mapObj1)))
    else
      let asArrayF := !co.arrays || asSet || container.contains "@list"
                      || (match ci with | .array [] => true | _ => false)
                      || k == "@list" || k == "@graph"
      .ok (cmpNestedPut res nest (cmpGenericAdd nres iap ci asArrayF))
termination_by fuel

end

/-! ## `JsonLdProcessor.compact()`

Expand, process the supplied context, compact, re-attach the original
context. -/

/-- Is the supplied context value "empty" for the purposes of the final
`@context` re-attachment? -/
def cmpCtxIsEmpty : Json → Bool
  | .null      => true
  | .object [] => true
  | .array []  => true
  | _          => false

/-- Compact a JSON-LD document against a context document.

  * `input`         — the JSON-LD document text (expanded by §5.1 first,
    so un-expanded input is fine);
  * `ctxDoc`        — the compaction context DOCUMENT text; its top-level
    `@context` member (or, failing that, the whole document value) is
    both processed and re-attached verbatim to the output;
  * `base`          — the input document's base IRI (the manifest's
    `option.base`, or `baseIri ++ input`); seeds expansion AND the active
    context's base for relative-IRI compaction;
  * `ctxUrl`        — the context document's own URL (remote references
    inside it resolve against this, not against `base`);
  * `compactArrays` / `compactToRelative` — the API options;
  * `processingMode` — `"json-ld-1.0"` selects 1.0 mode, anything else
    1.1 (the same convention `expandDocument` uses). -/
def compactDocument (loader : Loader) (input ctxDoc : String) (base ctxUrl : Option String)
    (compactArrays compactToRelative : Bool) (processingMode : Option String) : Res Json :=
  match expandDocument loader input base none processingMode with
  | .error e => .error e
  | .ok expanded =>
    match parseJson ctxDoc with
    | .error _ => .error .invalidLocalContext
    | .ok ctxRoot =>
      let ctxVal := match ctxRoot with
                    | .object cf => (match cmpField cf "@context" with
                                     | some c => c | none => ctxRoot)
                    | _ => ctxRoot
      let mode10 := processingMode == some "json-ld-1.0"
      let acSeed : ActiveContext :=
        { cur := { emptyContextCore with
                   base := base, mode10 := mode10,
                   docUrl := (match ctxUrl with | some u => some u | none => base),
                   originalBase := base },
          prev := [] }
      match contextProcess loader acSeed ctxVal false contextFuel remoteContextFuel [] with
      | .error e => .error e
      | .ok ac =>
        let co : CmpOpts := { arrays := compactArrays, rel := compactToRelative }
        let fuel := 16 * Json.size expanded + 128
        match compactElem loader ac none expanded co fuel with
        | .error e => .error e
        | .ok compacted0 =>
          let compacted1 :=
            if compactArrays then
              match compacted0 with
              | .array []  => Json.object []
              | .array [x] => x
              | other      => other
            else compacted0
          let wrapped := match compacted1 with
                         | .array _   => Json.object [(aliasKw ac co "@graph", compacted1)]
                         | .object fs => Json.object fs
                         | other      => other
          if cmpCtxIsEmpty ctxVal then .ok wrapped
          else
            match wrapped with
            | .object fs => .ok (.object (("@context", ctxVal) :: fs))
            | other      => .ok other

end L4Factoidal.JSONLD
