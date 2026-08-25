/-
L4Factoidal.Testing.Enumerate — grammar-driven test generation.

## Prior art

W3C, 1998: <https://www.w3.org/RDF/Test/Janne/>. Janne Saarela wrote
the RDF 1.0 M&S grammar as Prolog clauses (`rdf.pl`), let Prolog
backtrack through every derivation, and got 534 RDF documents plus one
deliberately broken file. `runtests.pl` ran SiRPAC over all of them.

Three things limited it, and all three are properties of the setup
rather than of the idea:

1. **The grammar was a second artefact.** `rdf.pl` transcribes the
   productions by hand; SiRPAC implements them separately. A
   production mistyped in `rdf.pl` generates wrong documents, and one
   omitted generates none — with nothing to detect either.
2. **The oracle was "did it crash".** `runtests.pl` runs the parser
   and greps the output for `null` and `Error`, then checks the file
   is non-empty. It separates a crash from a non-crash. It cannot
   separate right triples from wrong triples.
3. **Termination was managed by editing the grammar.** `rdf.pl` pins
   `bagIdAttr` to the constant `bagID1` and comments out the
   `parseResource` productions, both marked HACK, because unrestricted
   enumeration does not terminate.

## What is different here

1. The grammar is not a second artefact. `L4Factoidal.XML.Document`'s
   `Node` carries the XML production number on every constructor
   (`[14] CharData`, `[39] element`, …), and it is the type the parser
   produces and the serialiser consumes. Enumerating it enumerates the
   grammar the implementation actually uses.
2. The oracle is a property, not a smoke test. `roundTrips` below
   checks `parseXML ∘ serialize = id` on the document, which
   distinguishes wrong output from right output.
3. Termination is a parameter. `nodes` is structurally recursive on a
   `Nat` depth, so every call is total and the bound is an argument
   rather than a source edit.

## What is the same

Generate from the grammar rather than from imagination; ship the
generator alongside the corpus; and include deliberately invalid
inputs, not only valid ones.
-/
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Theorems

namespace L4Factoidal.Testing

open L4Factoidal.XML

/-! ## Leaf alphabets

Small on purpose. The generator's job is to cover the SHAPE of the
grammar; the character-level cases are covered by the W3C XML
conformance suite, which this does not replace. Each alphabet holds
one ordinary value and one value that has bitten a parser here. -/

def tagNames : List String := ["a", "ns:b"]
def attrNames : List String := ["x", "xml:lang"]
def attrValues : List String := ["1", "a b"]
def textBodies : List String := ["t", "a &amp; b"]
def piTargets : List String := ["p"]

def attrsUpTo : Nat → List (List Attribute)
  | 0     => [[]]
  | n + 1 =>
      let smaller := attrsUpTo n
      smaller ++ (attrNames.flatMap (fun nm =>
        attrValues.flatMap (fun v =>
          smaller.map (fun rest => { name := nm, value := v } :: rest))))

/-! ## The enumeration, and why exhaustive is the wrong target

The first version of this enumerated every `Node` up to a depth. The
count is doubly exponential and it does not finish: with 6 leaves, 2
tag names, 5 attribute lists and a sibling bound of 2, depth 1 gives
496 nodes, depth 2 gives 2,470,586, and depth 3 — which `documents 2`
needs — is past 10¹³.

That is the same wall `rdf.pl` hit in 1998. Its two HACK comments —
`bagIdAttr` pinned to the constant `bagID1`, the `parseResource`
productions commented out — are what a person does when exhaustive
enumeration will not terminate. They were the fix, not sloppiness.

So exhaustive enumeration is not the target. **Production coverage**
is: every constructor of the grammar appears, and every pair of
constructors appears in a parent-child relationship. A corpus of a
few hundred documents does that; ten trillion adds nothing a parser
distinguishes.

`cap` is the budget. `interleave` is what keeps the budget from
spending itself on one production: the lists are round-robined
before the cap applies, so cutting at `cap` still takes from every
constructor. -/

/-! Round-robin, so a later `take` draws from every source list. -/
partial def interleave : List (List α) → List α
  | [] => []
  | ls =>
      let heads := ls.filterMap List.head?
      let tails := (ls.filterMap List.tail?).filter (fun l => !l.isEmpty)
      heads ++ interleave tails

def leaves : List (List Node) :=
  [ textBodies.map Node.text,
    textBodies.map Node.cdata,
    [Node.comment "c"],
    piTargets.map (fun t => Node.pi t "d") ]

mutual

/-- At most `cap` nodes of nesting depth at most `d`. -/
partial def nodes (cap : Nat) : Nat → List Node
  | 0     => (interleave leaves).take cap
  | d + 1 =>
      let deeper := tagNames.map (fun tag =>
        (attrsUpTo 1).flatMap (fun attrs =>
          (childLists cap d 2).map (fun kids => Node.element tag attrs kids)))
      (interleave (leaves ++ deeper)).take cap

/-- At most `cap` child lists of length at most `w`. -/
partial def childLists (cap : Nat) (d : Nat) : Nat → List (List Node)
  | 0     => [[]]
  | w + 1 =>
      let ns := nodes cap d
      (childLists cap d w ++ ns.flatMap (fun n =>
        (childLists cap d w).map (fun rest => n :: rest))).take cap

end

/-- At most `cap` documents whose root element nests at most `d`
    deep. Only `element` roots: `[1] document` requires exactly one
    element. -/
def documents (cap : Nat) (d : Nat) : List Document :=
  ((nodes cap (d + 1)).filterMap (fun n =>
    match n with
    | .element _ _ _ => some ({ decl := none, doctype := none,
                                prolog := [], root := n, epilog := [] } : Document)
    | _              => none)).take cap

/-! ## The parser's image is smaller than the type

`documents` above generates values of `Node`, and `Node` can
represent trees the parser never builds. Two adjacent `text` children
are one: XML §2.4 has no way to write a boundary between two runs of
character data, so `<a>tt</a>` parses to a single `text "tt"`. The
same holds for a `text` beside a `cdata`, since §2.7 says a CDATA
section's content is character data.

MEASURED, 2026-08-23. Every round-trip failure the generator found is
this and nothing else:

| Corpus | Documents | Round-trip failures | Failures with adjacent character data |
| --- | --- | --- | --- |
| cap 60, depth 0 | 54 | 4 | 4 |
| cap 200, depth 2 | 194 | 16 | 16 |
| cap 400, depth 3 | 394 | 32 | 32 |

Excluding them leaves 38, 146 and 298 documents with zero failures.

So `parseXML ∘ serialize = id` is a property of the parser's IMAGE,
not of `Node`. `noAdjacentCharData` is that image's defining
condition, stated here because nothing in the tree stated it before —
and a hand-written test would not have found it, because nobody
writes a tree with two adjacent text nodes on purpose. -/

def isCharData : Node → Bool
  | .text _  => true
  | .cdata _ => true
  | _        => false

/-- No element has two adjacent character-data children, at any
    depth. True of every tree `parseXML` produces. -/
partial def noAdjacentCharData : Node → Bool
  | .element _ _ kids =>
      !((kids.zip (kids.drop 1)).any (fun (a, b) => isCharData a && isCharData b))
      && kids.all noAdjacentCharData
  | _ => true

/-- The generated documents the parser could have produced. -/
def canonicalDocuments (cap : Nat) (d : Nat) : List Document :=
  (documents cap d).filter (fun doc => noAdjacentCharData doc.root)

/-- The generated documents it could NOT. Kept rather than discarded:
    they are the inputs that show what the serialiser does with a
    tree outside the parser's image. -/
def nonCanonicalDocuments (cap : Nat) (d : Nat) : List Document :=
  (documents cap d).filter (fun doc => !(noAdjacentCharData doc.root))

/-! ## The oracle

`XML.roundTrips` already states the property: serialise the document,
parse the result, require the parsed document to equal the one we
started from. The generator supplies inputs to it. Without a property
of this kind the setup is the 1998 one — it separates a crash from a
non-crash and nothing else. -/

/-- Canonical documents that fail `XML.roundTrips`. Expected empty. -/
def roundTripFailures (cap : Nat) (d : Nat) : List Document :=
  (canonicalDocuments cap d).filter (fun doc => !(XML.roundTrips doc))

/-- `(canonical, round-tripping, failing)`. -/
def census (cap : Nat) (d : Nat) : Nat × Nat × Nat :=
  let docs := canonicalDocuments cap d
  let bad := (roundTripFailures cap d).length
  (docs.length, docs.length - bad, bad)

/-! ## Build-time checks

Small caps so the build stays fast. The larger corpora are run from
a driver, not from the build. -/

#guard (census 40 0).2.2 == 0
#guard (census 60 1).2.2 == 0
#guard (census 40 0).1 > 20

/-! The invariant holds of what the parser produces. -/

#guard (match parseXML "<a>t<b/>u</a>" with
        | .ok d => noAdjacentCharData d.root
        | .error _ => false)

/-! And the trees it excludes are exactly the ones that do not round
    trip. Two adjacent text children serialise to one run of
    character data and parse back as one node. -/

#guard !(noAdjacentCharData (.element "a" [] [.text "t", .text "t"]))
#guard !(XML.roundTrips { decl := none, doctype := none, prolog := [],
                          root := .element "a" [] [.text "t", .text "t"],
                          epilog := [] })
#guard XML.roundTrips { decl := none, doctype := none, prolog := [],
                        root := .element "a" [] [.text "tt"], epilog := [] }

end L4Factoidal.Testing
