/-
L4Factoidal.JSONLD.Frame — the JSON-LD 1.1 Framing algorithm.

Port of `formal/fstar/JSONLD.Frame.fst` (335 lines).

Spec: <https://www.w3.org/TR/json-ld11-framing/>.

Framing shapes a JSON-LD document into a tree a caller describes with a
FRAME document: which node types appear at the top level, which
properties are embedded inline and which are left as references.

The pipeline: expand the input, flatten it to a node map, match nodes
against the frame, embed the matched references recursively, wrap the
result in `@graph`, compact it against the frame's context.

## What this covers, and what it does not

Covered: `@type` matching (present, wildcard, IRI-set intersection);
`@id` matching (present, wildcard, id-set membership); property matching
(must be present, must be ABSENT via `[]`, wildcard via `{}`); embedding
of node references with a visited set to break cycles, which
approximates the default `@embed: @once`; and `@explicit`, whose default
`false` outputs every property the matched NODE carries while `true`
restricts output to the properties the frame names.

Not covered, and the F\* source says the same: `@default`,
`@omitDefault`, `@requireAll` OR-matching, the other `@embed` modes,
`@reverse`, `@included`, named graphs, value-object-level matching
inside a property frame, and blank-node `@id` pruning on output.

## Recursion over an untrusted graph

The node graph may be cyclic, so the walk is fuel-bounded AND carries a
visited set. The F\* source needs a lexicographic measure over three
mutually recursive functions; here the three are one `frameNode` with
two local helpers over the same fuel, and the fuel decrements at the one
edge that can revisit a node.

## The frame is expanded under a different grammar

`expandDocument` gained a `frameExpansion` flag for this module.
Only the FRAME is expanded with it set — never the input being framed.
Without it the frame's `@explicit` and its `@id` patterns are dropped as
keyword lookalikes before the algorithm ever sees them.
-/
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Flatten

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Small helpers over `Json` -/

/-- A JSON-LD keyword key starts with a commercial at. -/
def isKeyword (k : String) : Bool := k.startsWith "@"

def objFields : Json → List (String × Json)
  | .object fs => fs
  | _ => []

def objGet (v : Json) (k : String) : Option Json :=
  (objFields v).find? (fun kv => kv.1 == k) |>.map Prod.snd

def objHas (v : Json) (k : String) : Bool := (objGet v k).isSome

/-- The string payloads a value carries, flattening one level of array.
Used for `@type` and `@id`, which are arrays of IRIs in expanded form. -/
def jstrings : Json → List String
  | .string s => [s]
  | .array items => items.flatMap jstrings
  | _ => []

def nodeTypes (node : Json) : List String :=
  match objGet node "@type" with
  | some tv => jstrings tv
  | none => []

def nodeId (node : Json) : Option String :=
  match objGet node "@id" with
  | some (.string s) => some s
  | _ => none

/-- The empty object: the framing wildcard, "match if present". -/
def isWildcard : Json → Bool
  | .object [] => true
  | _ => false

/-- The empty array: the framing marker for "match if ABSENT". -/
def isEmptyArray : Json → Bool
  | .array [] => true
  | _ => false

/-- The values a node holds for a property. Expanded form is an array;
a bare value is accepted leniently. -/
def propValues (node : Json) (k : String) : List Json :=
  match objGet node k with
  | some (.array xs) => xs
  | some other => [other]
  | none => []

/-- If a value is a bare node reference `{"@id": X}`, its X. -/
def refId : Json → Option String
  | .object fs => (match (fs.find? (fun kv => kv.1 == "@id")).map Prod.snd with
                   | some (.string x) => some x
                   | _ => none)
  | _ => none

/-- The sub-frame governing a framed property's values. In expanded form
the frame's property value is an array; the first object in it is the
frame, and an empty frame matches everything. -/
def propSubframe : Json → Json
  | .array (.object o :: _) => .object o
  | .object o => .object o
  | _ => .object []

/-- The spec default is `@explicit: false`, which OUTPUTS every property
the matched node carries. Only `true` restricts output to the properties
the frame names. The directive survives frame-mode expansion as a raw
member, so it is read straight off the frame object. -/
def frameExplicit (frame : Json) : Bool :=
  match objGet frame "@explicit" with
  | some (.bool b) => b
  | _ => false

/-! ## Matching -/

/-- Does one frame constraint hold for a node? -/
def matchOne (k : String) (fv : Json) (node : Json) : Bool :=
  if k == "@type" then
    let ft := jstrings fv
    let nt := nodeTypes node
    -- present or wildcard: the node must declare SOME type. Otherwise
    -- the node's types must intersect the frame's.
    if ft.isEmpty || isWildcard fv then !nt.isEmpty
    else nt.any (fun t => ft.contains t)
  else if k == "@id" then
    let fid := jstrings fv
    if isWildcard fv || fid.isEmpty then true
    else match nodeId node with
         | some nid => fid.contains nid
         | none => false
  else if isKeyword k then
    -- any other keyword imposes no constraint here
    true
  else if isEmptyArray fv then !objHas node k        -- `[]`: must be absent
  else objHas node k                                 -- present, or `{}` wildcard

def nodeMatches (frame node : Json) : Bool :=
  (objFields frame).all (fun kv => matchOne kv.1 kv.2 node)

/-! ## Framing and embedding

Fuel bounds the depth; `visited` breaks a cycle by leaving the reference
in place rather than embedding it again. -/

def frameNode (map : List (String × Json)) (frame node : Json)
    (visited : List String) : Nat → Json
  | 0 => node
  | fuel + 1 =>
      -- Frame each value of one property. A reference into the map that
      -- is not on the visited path is embedded; everything else is
      -- copied as it stands.
      let frameValues (subframe : Json) (vals : List Json) : List Json :=
        vals.map (fun v =>
          match refId v with
          | some x =>
              match (map.find? (fun kv => kv.1 == x)).map Prod.snd with
              | some target =>
                  if visited.contains x then v          -- cycle: keep the reference
                  else frameNode map subframe target (x :: visited) fuel
              | none => v                                -- not in the map: keep it
          | none => v)
      -- Walk the NODE's own members. `@id` and `@type` are copied
      -- above, and every other keyword is skipped. Each non-keyword
      -- property is shaped by the frame's sub-frame when the frame
      -- declares one; when the frame is silent, `@explicit: true` drops
      -- the property and the default passes it through under a
      -- match-all frame.
      let propEntries : List (String × Json) :=
        (objFields node).filterMap (fun kv =>
          if isKeyword kv.1 then none
          else match objGet frame kv.1 with
               | some fv =>
                   some (kv.1, .array (frameValues (propSubframe fv) (propValues node kv.1)))
               | none =>
                   if frameExplicit frame then none
                   else some (kv.1,
                     .array (frameValues (.object []) (propValues node kv.1))))
      let idEntry := match objGet node "@id" with | some v => [("@id", v)] | none => []
      let typeEntry := match objGet node "@type" with | some v => [("@type", v)] | none => []
      .object (idEntry ++ typeEntry ++ propEntries)

/-! ## Top level -/

/-- The node map, id to node, in the order the flattened list gives. -/
def buildNodeMap (nodes : List Json) : List (String × Json) :=
  nodes.filterMap (fun n => (nodeId n).map (fun id => (id, n)))

/-- The frame object out of an expanded frame. Anything that is not an
object or an array of one is the empty frame, which matches all. -/
def firstFrame : Json → Json
  | .array (.object o :: _) => .object o
  | .object o => .object o
  | _ => .object []

/-- Frame every matching node, in document order. -/
def topFrame (map : List (String × Json)) (frame : Json) (nodes : List Json)
    (fuel : Nat) : List Json :=
  nodes.filterMap (fun n =>
    if nodeMatches frame n then
      let seed := match nodeId n with | some id => [id] | none => []
      some (frameNode map frame n seed fuel)
    else none)

/-! ## The entry point -/

/-- Put the `@graph` wrapper back after compaction.

The framing API's `omitGraph` option decides whether the result keeps a
top-level `@graph`. It defaults to FALSE under `json-ld-1.0` processing
and TRUE under 1.1, which is why the suite's expected outputs are split
between the two shapes rather than settling on one.

When it is false the wrapper is required, and compaction has usually
just removed it: `{"@graph": [node]}` with `compactArrays` set collapses
the single-element array and drops the key, leaving the bare node. This
puts it back.

`treeCount` decides the empty case, which the shape alone cannot: a
frame that matched NOTHING must produce `"@graph": []`, not a `@graph`
holding one empty object. -/
def restoreGraphWrapper (compacted : Json) (treeCount : Nat) : Json :=
  match compacted with
  | .object fs =>
      if fs.any (fun kv => kv.1 == "@graph") then compacted
      else
        let ctx := fs.filter (fun kv => kv.1 == "@context")
        let rest := fs.filter (fun kv => kv.1 != "@context")
        let graph : List Json := if treeCount == 0 || rest.isEmpty then [] else [.object rest]
        .object (ctx ++ [("@graph", .array graph)])
  | .array items => .object [("@graph", .array items)]
  | other => other

/-- Frame `input` according to `frame`.

`base` seeds expansion and relative-IRI compaction; `processingMode`
selects 1.0 when it is `"json-ld-1.0"`. `omitGraph` overrides the
default for the top-level `@graph` wrapper, which is FALSE under 1.0
processing and TRUE under 1.1.

The INPUT is expanded ordinarily and only the FRAME is expanded under
the framing grammar — that asymmetry is the algorithm's, not an
oversight. -/
def frameDocument (loader : Loader) (input frame : String) (base : Option String)
    (processingMode : Option String) (omitGraph : Option Bool := none) : Res Json :=
  let dropWrapper := omitGraph.getD (processingMode != some "json-ld-1.0")
  match expandDocument loader input base none processingMode false with
  | .error e => .error e
  | .ok expanded =>
    match flattenExpanded expanded with
    | .error e => .error e
    | .ok nodes =>
      let map := buildNodeMap nodes
      match expandDocument loader frame base none processingMode true with
      | .error e => .error e
      | .ok frameExp =>
        let fr := firstFrame frameExp
        -- The flattened node order is already deterministic, so it is
        -- consumed as it comes.
        let fuel := 16 * Json.size expanded + 128
        let trees := topFrame map fr nodes fuel
        let framed : Json := .object [("@graph", .array trees)]
        match compactDocument loader (jcsDocument framed) frame base none true true
                processingMode with
        | .error e => .error e
        | .ok compacted =>
          .ok (if dropWrapper then compacted
               else restoreGraphWrapper compacted trees.length)

/-! ## Build-time checks -/

section Checks

private def framedOf (input frame : String) : Option String :=
  (frameDocument Loader.none input frame none none).toOption.map jcsDocument

/-- How many times `pat` occurs in `s`. The framed output is compared by
what it CONTAINS rather than by its exact text, because the compaction
step's key order is not what these checks are about. -/
private def countOf (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- Does the framed output contain each of `want` and none of `avoid`? -/
private def framedHas (input frame : String) (want avoid : List String) : Bool :=
  match framedOf input frame with
  | none => false
  | some s => want.all (fun w => countOf s w > 0) && avoid.all (fun a => countOf s a == 0)

/-! ### `@type` matching selects the top-level nodes

Two nodes, one of each type. A frame naming one type returns one node. -/

private def twoTypes : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@graph\":[
     {\"@id\":\"http://e.org/a\",\"@type\":\"Person\",\"name\":\"Alice\"},
     {\"@id\":\"http://e.org/b\",\"@type\":\"Place\",\"name\":\"Bath\"}]}"

private def personFrame : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Person\"}"

private def placeFrame : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Place\"}"

#guard (framedOf twoTypes personFrame).isSome
#guard framedHas twoTypes personFrame ["Alice"] ["Bath"]
#guard framedHas twoTypes placeFrame ["Bath"] ["Alice"]

/-! ### A frame that matches NOTHING returns an empty graph, rather than
failing or returning everything -/

private def absentFrame : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Nothing\"}"

#guard framedHas twoTypes absentFrame [] ["Alice", "Bath"]

/-! ### A referenced node is EMBEDDED, not left as a bare reference -/

private def linked : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@graph\":[
     {\"@id\":\"http://e.org/a\",\"@type\":\"Person\",\"knows\":{\"@id\":\"http://e.org/b\"}},
     {\"@id\":\"http://e.org/b\",\"@type\":\"Person\",\"name\":\"Bob\"}]}"

#guard framedHas linked personFrame ["Bob"] []

/-! ### A CYCLE terminates, and keeps the second reference as a
reference rather than embedding forever -/

private def cyclic : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@graph\":[
     {\"@id\":\"http://e.org/a\",\"@type\":\"Person\",\"knows\":{\"@id\":\"http://e.org/b\"}},
     {\"@id\":\"http://e.org/b\",\"@type\":\"Person\",\"knows\":{\"@id\":\"http://e.org/a\"}}]}"

#guard (framedOf cyclic personFrame).isSome

/-! ### `@explicit` changes what is output

The default outputs every property the node carries. With
`@explicit: true` a property the frame does not name is dropped. This is
the pair that shows the directive survived frame-mode expansion: without
that, both frames would behave identically. -/

private def explicitFrame : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Person\",\"@explicit\":true}"

private def personWithTwo : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},
    \"@id\":\"http://e.org/a\",\"@type\":\"Person\",
    \"name\":\"Alice\",\"nick\":\"Al\"}"

#guard framedHas personWithTwo personFrame ["Alice", "\"Al\""] []
#guard framedHas personWithTwo explicitFrame [] ["Alice", "\"Al\""]

/-! ### A property constraint: `{}` requires the property, `[]` forbids
it -/

private def twoPeople : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@graph\":[
     {\"@id\":\"http://e.org/a\",\"@type\":\"Person\",\"nick\":\"Al\"},
     {\"@id\":\"http://e.org/b\",\"@type\":\"Person\",\"name\":\"Bob\"}]}"

private def wantsNick : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Person\",\"nick\":{}}"

private def refusesNick : String :=
  "{\"@context\":{\"@vocab\":\"http://e.org/\"},\"@type\":\"Person\",\"nick\":[]}"

#guard framedHas twoPeople wantsNick ["\"Al\""] ["Bob"]
#guard framedHas twoPeople refusesNick ["Bob"] ["\"Al\""]

/-! ### The matching predicates on their own

Checked directly, because the pipeline checks above cannot distinguish
"matched nothing" from "framed wrongly". -/

private def nodeA : Json :=
  .object [("@id", .string "http://e.org/a"), ("@type", .array [.string "http://e.org/Person"]),
           ("http://e.org/name", .array [.object [("@value", .string "Alice")]])]

#guard nodeMatches (.object []) nodeA
#guard nodeMatches (.object [("@type", .array [.string "http://e.org/Person"])]) nodeA
#guard !nodeMatches (.object [("@type", .array [.string "http://e.org/Place"])]) nodeA
#guard nodeMatches (.object [("@type", .object [])]) nodeA          -- wildcard: has a type
#guard nodeMatches (.object [("@id", .array [.string "http://e.org/a"])]) nodeA
#guard !nodeMatches (.object [("@id", .array [.string "http://e.org/z"])]) nodeA
#guard nodeMatches (.object [("http://e.org/name", .object [])]) nodeA
#guard !nodeMatches (.object [("http://e.org/name", .array [])]) nodeA
#guard nodeMatches (.object [("http://e.org/nick", .array [])]) nodeA
#guard !nodeMatches (.object [("http://e.org/nick", .object [])]) nodeA

/-! ### The `@graph` wrapper follows `omitGraph`, not the shape

Under `json-ld-1.0` processing the wrapper is required and compaction
has usually just removed it; under 1.1 it is omitted. The same input and
frame therefore produce two different top-level shapes, which is the
suite's own split and not a defect. -/

private def framedWith (input frame : String) (pm : Option String) : Option String :=
  (frameDocument Loader.none input frame none pm).toOption.map jcsDocument

#guard match framedWith personWithTwo personFrame (some "json-ld-1.0") with
       | some s => countOf s "\"@graph\"" > 0
       | none => false
#guard match framedWith personWithTwo personFrame (some "json-ld-1.1") with
       | some s => countOf s "\"@graph\"" == 0
       | none => false

/-! A frame that matches nothing keeps an EMPTY `@graph` under 1.0,
rather than a `@graph` holding one empty object. -/

#guard match framedWith twoTypes absentFrame (some "json-ld-1.0") with
       | some s => countOf s "\"@graph\":[]" > 0
       | none => false

/-! ### `frameNode` at zero fuel returns the node untouched rather than
diverging -/

#guard frameNode [] (.object []) nodeA [] 0 == nodeA

end Checks

end L4Factoidal.JSONLD
