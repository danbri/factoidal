/-
L4Factoidal.JSONLD.ApiTests — build-time guards and theorems for the
JSON-LD 1.1 API algorithms beyond expansion: Compaction (§6), Flattening
(§7), Serialize RDF as JSON-LD (§8.5-8.7), and HTML script extraction.

`#guard` expressions evaluate during elaboration, so a wrong answer here
is a BUILD ERROR. Concrete-input facts live as `#guard`s rather than as
`decide`/`rfl` proofs — pitfall #10 in
`skills/factoidal-lean-basics/SKILL.md`: kernel evaluation of a concrete
algorithm run costs gigabytes of RAM and fills the disk with swap.
Theorems here are the ALGEBRAIC ones, stated over symbolic inputs, which
the kernel checks cheaply.

The conformance measurement is `lake exe l4jsonld-api` against the W3C
json-ld-api manifests; these guards are a fast tripwire, not the score.
-/
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.Flatten
import L4Factoidal.JSONLD.Html

namespace L4Factoidal.JSONLD.ApiTests

open L4Factoidal.JSON
open L4Factoidal.JSONLD

/-! ## Theorems

Three small statements, each about a step the manifests cannot isolate.
Nothing more is claimed: these are NOT a proof that the algorithms are
correct — the conformance evidence is the manifest score. -/

/-- Term Selection never prefers a LONGER term. The spec's ordering
(§6.2 step 3, §6.3 step 4.16) is "shortest term first, ties broken
lexicographically least"; `cmpTermLess` is the whole of that ordering,
and this is its length half. The sabotage test for this module inverts
the length comparison and watches named compact fixtures fail. -/
theorem cmpTermLess_length_le (a b : String) (h : cmpTermLess a b = true) :
    slen a ≤ slen b := by
  unfold cmpTermLess at h
  by_cases hlt : slen a < slen b
  · omega
  · by_cases hgt : slen a > slen b
    · simp [hlt, hgt] at h
    · omega

/-- Compaction of an EMPTY expanded document is the empty array, for
every active context and every option setting. This is the algebraic
half of "compaction of the expanded empty document is `{}`": the entry
point `compactDocument` then rewrites `.array []` to `.object []` under
`compactArrays` (see `compactDocument`'s `compacted1`, and the
whole-pipeline guard below). -/
theorem compactElem_empty_array (loader : Loader) (ac : ActiveContext)
    (co : CmpOpts) (fuel : Nat) :
    compactElem loader ac none (.array []) co (fuel + 2) = .ok (.array []) := by
  unfold compactElem
  simp [compactItems]

/-- Node Map Generation leaves the state and the `@list` accumulator
untouched on an empty element array (§7.1 step 1 over no items). This is
the step that makes flattening of an empty document yield no nodes; the
whole-pipeline fact is the guard `flattenExpanded (.array []) = .ok []`
below. -/
theorem nmg_empty_array (st : NmState) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (acc : Option (List Json)) (fuel : Nat) :
    nmg st (.array []) agraph asubj aprop acc (fuel + 2) = .ok (st, acc) := by
  unfold nmg
  simp [nmgItems]

/-! ## Guards — Compaction (API §6) -/

/-- A term definition with no `@container`, `@type` or language mapping:
the base case the container-key guards below vary. -/
def plainTerm : TermDef :=
  { iri := "http://example/p", typeMapping := none, container := ContainerKind.none,
    reverse := false, language := none, direction := none, index := none,
    scopedContext := none, protected_ := false, prefix_ := false, set_ := false,
    nest := none }

-- §6.2 step 3.2: the container key is the members sorted and
-- concatenated, `"@none"` when there are none.
#guard cmpContainerKey plainTerm == "@none"
#guard cmpContainerKey { plainTerm with container := ContainerKind.graphId } == "@graph@id"
#guard cmpContainerKey { plainTerm with container := ContainerKind.index, set_ := true }
         == "@index@set"

-- §6.2 step 3 / §6.3 step 4.16: shortest term first, ties broken
-- lexicographically least.
#guard cmpTermLess "ab" "abc" == true
#guard cmpTermLess "abc" "ab" == false
#guard cmpTermLess "abc" "abd" == true
#guard cmpTermLess "abd" "abc" == false

-- §6.3 step 10: relativization against the active context's base.
#guard cmpRelativize "http://example/base/doc" "http://example/base/other" == "other"
#guard cmpRelativize "http://example/base/doc" "http://example/other/x" == "../other/x"
#guard cmpRelativize "http://example/base/doc" "http://example/base/doc" == "doc"
#guard cmpRelativize "http://example/base/doc" "http://other/x" == "http://other/x"
-- The degenerate empty relative reference becomes "./".
#guard cmpRelativize "http://example/base/" "http://example/base/" == "./"
-- A relative reference that would LOOK like a keyword keeps an explicit
-- "./" prefix (compact/0111).
#guard cmpRelativize "http://example/base/doc" "http://example/base/@special"
         == "./@special"

-- The whole `JsonLdProcessor.compact()` pipeline on the empty document
-- with an empty context: `{}` — the API's `compactArrays` rewrite of an
-- empty result array.
#guard compactDocument (fun _ => none) "[]" "{}" (some "http://example/") none
         true true none == .ok (.object [])

/-! ## Guards — Flattening (API §7) -/

#guard flattenExpanded (.array []) == .ok []

-- §7.2: the issuer relabels in first-issue order, starting at `_:b0`,
-- and an already-issued label maps to the SAME identifier a second time.
#guard (issueKeyed { graphs := [], idmap := [], ctr := 0 } "_:x").1 == "_:b0"
#guard (let st0 : NmState := { graphs := [], idmap := [], ctr := 0 }
        let (a, st1) := issueKeyed st0 "_:x"
        let (b, _)   := issueKeyed st1 "_:x"
        a == b && a == "_:b0")

-- Flattening is a FIXED POINT on an already-flattened, blank-node-free
-- node array: node map generation re-collects the same single node and
-- emission puts it back in the same order. The blank-node-free
-- restriction is real — flattening RE-ISSUES `_:b0`, `_:b1`, … , so a
-- document already carrying `_:b`-shaped labels is a fixed point while
-- one carrying `_:foo` is not: the second pass renames it.
#guard (let doc : Json := .array [.object
          [("@id", .string "http://example/a"),
           ("http://example/p", .array [.object [("@value", .string "v")]])]]
        match flattenExpanded doc with
        | .ok once => (match flattenExpanded (.array once) with
                       | .ok twice => expandedEqual (.array once) (.array twice)
                       | .error _  => false)
        | .error _ => false)

/-! ## Guards — Serialize RDF as JSON-LD (API §8.5-8.7) -/

#guard FromRdf.fromRdf L4Factoidal.RDF.Dataset.empty FromRdf.defaultOptions
         == some (.array [])

-- §8.6 `useNativeTypes`, including the `xsd:boolean` lexical space
-- {true, false, 1, 0} and the infinite-double rejection (fixture 0027).
#guard FromRdf.nativeValue "1" FromRdf.sXsdBoolean
         == FromRdf.Ov.val (.object [("@value", .bool true)])
#guard FromRdf.nativeValue "True" FromRdf.sXsdBoolean
         == FromRdf.Ov.val (.object [("@value", .string "True"),
                                     ("@type", .string FromRdf.sXsdBoolean)])
#guard FromRdf.nativeValue "-7" FromRdf.sXsdInteger
         == FromRdf.Ov.val (.object [("@value", .number "-7")])
#guard FromRdf.isFiniteDouble "1.1E-1" == true
#guard FromRdf.isFiniteDouble "0.1e999999999999999" == false

-- §8.5 `rdfDirection = "i18n-datatype"`: the datatype fragment splits on
-- its LAST `_`, so a hyphenated language subtag stays intact (di05, di06).
#guard FromRdf.i18nValueObject "x" (FromRdf.i18nPrefix ++ "en-us_rtl")
         == FromRdf.Ov.val (.object [("@value", .string "x"),
                                     ("@language", .string "en-us"),
                                     ("@direction", .string "rtl")])
#guard FromRdf.i18nValueObject "x" (FromRdf.i18nPrefix ++ "_rtl")
         == FromRdf.Ov.val (.object [("@value", .string "x"),
                                     ("@direction", .string "rtl")])

/-! ## Guards — HTML script extraction -/

def htmlDoc : String :=
  "<html><head><base href=\"http://base.example/d/\"></head><body>" ++
  "<script type=\"application/ld+json\" id=\"first\">{\"a\":1}</script>" ++
  "<script type=\"text/javascript\">ignored()</script>" ++
  "<script type=\"application/ld+json\" id=\"second\">[{\"b\":2}]</script>" ++
  "</body></html>"

#guard Html.extractHtmlBase htmlDoc == some "http://base.example/d/"
#guard Html.extractJsonLdFromHtml htmlDoc none false == some "{\"a\":1}"
#guard Html.extractJsonLdFromHtml htmlDoc (some "second") false == some "[{\"b\":2}]"
#guard Html.extractJsonLdFromHtml htmlDoc (some "missing") false == none
-- `extractAllScripts` SPLICES a member that is itself an array.
#guard Html.extractJsonLdFromHtml htmlDoc none true == some "[{\"a\":1},{\"b\":2}]"
-- No `ld+json` script at all: an error without `extractAllScripts`, the
-- empty document with it.
#guard Html.extractJsonLdFromHtml "<html></html>" none false == none
#guard Html.extractJsonLdFromHtml "<html></html>" none true == some "[]"
-- A script whose content is not JSON is `invalid script element`
-- (fixtures e014-e017), distinct from `loading document failed`.
#guard Html.loadHtmlJsonLd
         "<script type=\"application/ld+json\">{oops}</script>" none false
         == .error .invalidScriptElement
#guard Html.loadHtmlJsonLd "<html></html>" none false == .ok none
#guard Html.splitFragment "html/e003-in.html#second"
         == ("html/e003-in.html", some "second")

/-! ## Axiom audit

Every theorem above must rest on Lean's standard foundations only —
`propext`, `Classical.choice`, `Quot.sound` — and on nothing else. -/

#print axioms cmpTermLess_length_le
#print axioms compactElem_empty_array
#print axioms nmg_empty_array

end L4Factoidal.JSONLD.ApiTests
