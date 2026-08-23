/-
L4Factoidal.XPath.Data — the XPath 1.0 DATA MODEL over the project's
own XML tree, and the thirteen axes stated over it.

Spec: XPath 1.0 §5 (Data Model) and §2.2 (Axes).

## Why a new module beside `XPath/Mini.lean`

`Mini.lean` addresses nodes by a `/tag[i]/tag[j]` PATH STRING built
from ELEMENTS only. That is the right model for Schematron, whose
findings name a node to a human and whose `@context` selects elements.
It cannot carry XSLT: a stylesheet's `text()`, `comment()`,
`processing-instruction()` and `node()` tests address nodes that path
has no name for, and `xsl:copy-of` must reproduce a subtree verbatim
including its attributes. Extending `Mini` would have changed the
node identity Schematron already depends on, so this is a second
model, and `Mini.lean` is left exactly as it is.

## Identity is an ADDRESS, never a value

An item is located by its path of CHILD INDICES from the document
node. Two sibling `<row/>` elements are structurally equal and must
still be two nodes: `position()`, `preceding-sibling::` and the
`generate-id()`-shaped questions are all answered by identity, not by
comparison. This is the same defect the `Mini` port paid for once
(`preceding-sibling-reverse-axis` counted zero for both rows), written
down here so the second model does not repeat it.

## Document order is the address, lexicographically

Namespace nodes and attribute nodes belong to their element and come
BEFORE its children (§5.1). Their address therefore ends in a
NEGATIVE marker, so ordinary lexicographic comparison of the address
puts them where the specification does, and no separate ordering rule
is needed.
-/
import L4Factoidal.XML.Document

/-!
The namespace is `L4Factoidal.XPath.Full`, beside `XPath.Mini`'s
`L4Factoidal.XPath`: the two models both need a type called `Step`
and a function called `eval`, and they are different types and
different functions. Sharing one namespace made the library root
fail to import — which is the good outcome, because the alternative
is two `Step`s that silently shadow each other.
-/
namespace L4Factoidal.XPath.Full

open L4Factoidal.XML
open L4Factoidal.XPath

/-! ## Items -/

/-- What an item IS. `root` is the document node — the parent of the
    document element, which `/` selects and which is NOT the root
    element. -/
inductive Kind where
  | root | element | text | comment | pi | attribute | namespace
deriving Repr, DecidableEq, Inhabited

/-- The address of an item.

    `path` walks the tree by child index from the document node.
    `slot` is `none` for a tree node, `some (false, i)` for the
    element's `i`-th namespace node and `some (true, i)` for its
    `i`-th attribute. -/
structure Loc where
  path : List Nat
  slot : Option (Bool × Nat) := none
deriving Repr, DecidableEq, Inhabited

/-- The address as a list of integers, in DOCUMENT ORDER under plain
    lexicographic comparison. A namespace node gets `-3`, an
    attribute `-2`; every child index is `≥ 0`, so both sort before
    the element's children and namespaces before attributes. -/
def Loc.key (l : Loc) : List Int :=
  (l.path.map (fun n : Nat => (Int.ofNat n))) ++
    (match l.slot with
     | none            => []
     | some (false, i) => [-3, (i : Int)]
     | some (true, i)  => [-2, (i : Int)])

/-- Lexicographic comparison of two address keys. A PREFIX is earlier:
    an element precedes its own descendants, which is what document
    order says. -/
def keyCmp : List Int → List Int → Ordering
  | [],      []      => .eq
  | [],      _ :: _  => .lt
  | _ :: _,  []      => .gt
  | a :: as, b :: bs => if a < b then .lt else if a > b then .gt else keyCmp as bs

/-- A located item. The node (or attribute, or namespace binding) is
    carried alongside its address so that every accessor is a
    projection rather than a re-walk. -/
inductive Item where
  /-- The document node, holding its child list. -/
  | doc  (kids : List Node)
  /-- An element, text, comment or PI node at `loc`. -/
  | tree (loc : Loc) (n : Node)
  /-- An attribute of the element at `loc.path`. -/
  | attr (loc : Loc) (a : Attribute)
  /-- A namespace node: the prefix (empty for the default namespace)
      bound to a URI, on the element at `loc.path`. -/
  | ns   (loc : Loc) (prefix' : String) (uri : String)
deriving Repr, DecidableEq, Inhabited

def Item.loc : Item → Loc
  | .doc _        => { path := [] }
  | .tree l _     => l
  | .attr l _     => l
  | .ns   l _ _   => l

def Item.kind : Item → Kind
  | .doc _              => .root
  | .tree _ (.element ..) => .element
  | .tree _ (.text _)   => .text
  | .tree _ (.cdata _)  => .text
  | .tree _ (.comment _) => .comment
  | .tree _ (.pi ..)    => .pi
  | .attr ..            => .attribute
  | .ns   ..            => .namespace

/-- The item's QName, as written. Empty for every kind that has none
    — §5 gives text, comment and root nodes no expanded name. -/
def Item.qname : Item → String
  | .tree _ (.element t _ _) => t
  | .tree _ (.pi t _)        => t
  | .attr _ a                => a.name
  | .ns   _ p _              => p
  | _                        => ""

/-! ## Names -/

def localOf (q : String) : String :=
  match q.toList.findIdx? (· == ':') with
  | some i => String.ofList (q.toList.drop (i + 1))
  | none   => q

def prefixOf (q : String) : String :=
  match q.toList.findIdx? (· == ':') with
  | some i => String.ofList (q.toList.take i)
  | none   => ""

/-! ## String-value (§5) -/

/-- The string-value of a tree node: for an element or the root, the
    concatenation of all DESCENDANT text; for the others, their own
    character data.

    A comment inside an element contributes NOTHING, and neither does
    a processing instruction — a rule that is invisible until a
    document has one, at which point emitting it corrupts every
    `value-of` above it. -/
partial def nodeText : Node → String
  | .text s     => s
  | .cdata s    => s
  | .comment _  => ""
  | .pi _ _     => ""
  | .element _ _ cs => String.join (cs.map nodeText)

def Item.stringValue : Item → String
  | .doc kids   => String.join (kids.map nodeText)
  | .tree _ n   => match n with
      | .comment b => b
      | .pi _ d    => d
      | other      => nodeText other
  | .attr _ a   => a.value
  | .ns   _ _ u => u

/-! ## Navigation -/

/-- The children of a tree node, as nodes. Attributes are NOT
    children (§5.3): they are reached by the attribute axis only. -/
def kidsOf : Node → List Node
  | .element _ _ cs => cs
  | _               => []

def attrsOfNode : Node → List Attribute
  | .element _ a _ => a
  | _              => []

/-- Follow a child-index path from the document's child list. -/
def nodeAt (kids : List Node) : List Nat → Option Node
  | []      => none
  | i :: rest =>
      match kids[i]? with
      | none   => none
      | some n => rest.foldl (fun acc j => acc.bind (fun m => (kidsOf m)[j]?)) (some n)

/-- The document node's child list, recovered from any item. Every
    evaluation carries it, so it is threaded rather than stored. -/
abbrev Doc := List Node

/-- The item at an address, or `none` when the address does not name
    one. -/
def itemAt (d : Doc) (l : Loc) : Option Item :=
  match l.slot with
  | none =>
      if l.path.isEmpty then some (.doc d)
      else (nodeAt d l.path).map (fun n => .tree l n)
  | some (true, i) =>
      (nodeAt d l.path).bind (fun n => ((attrsOfNode n)[i]?).map (fun a => .attr l a))
  | some (false, _) => none    -- namespace nodes are built, not addressed

/-- The children of an item, in document order. Only the root and
    elements have any. -/
def childrenOf : Item → List Item
  | .doc kids => (kids.zipIdx).map (fun (n, i) => .tree { path := [i] } n)
  | .tree l n => ((kidsOf n).zipIdx).map (fun (c, i) =>
      .tree { path := l.path ++ [i] } c)
  | _ => []

/-- The parent of an item. An attribute's and a namespace node's
    parent is its element even though neither is its child (§5.3) —
    the asymmetry that makes `../@x` work but `@x/..`'s inverse not a
    child step. -/
def parentOf (d : Doc) (it : Item) : Option Item :=
  match it with
  | .doc _ => none
  | .attr l _ | .ns l _ _ => itemAt d { path := l.path }
  | .tree l _ =>
      match l.path with
      | []  => none
      | [_] => some (.doc d)
      | p   => itemAt d { path := p.dropLast }

/-- Every descendant of an item, in document order. -/
partial def descendantsOf (it : Item) : List Item :=
  (childrenOf it).flatMap (fun c => c :: descendantsOf c)

/-- The attribute nodes of an element, in the order the start tag
    wrote them. Namespace DECLARATIONS are excluded: `xmlns` and
    `xmlns:p` are namespace nodes, not attributes (§5.3), and
    returning them from `@*` is a defect that shows up as extra
    attributes copied onto every result element. -/
def isNsDecl (a : Attribute) : Bool :=
  a.name == "xmlns" || a.name.startsWith "xmlns:"

def attributesOf (it : Item) : List Item :=
  match it with
  | .tree l n =>
      ((attrsOfNode n).zipIdx).filterMap (fun (a, i) =>
        if isNsDecl a then none
        else some (.attr { path := l.path, slot := some (true, i) } a))
  | _ => []

/-- The namespace nodes IN SCOPE on an element: every declaration on
    it or on an ancestor, nearer declarations winning, plus the
    implicit `xml` binding §5.4 requires on every element. A prefix
    undeclared by `xmlns:p=""` contributes no node. -/
def namespacesOf (d : Doc) (it : Item) : List Item :=
  match it with
  | .tree l (.element _ _ _) =>
      let chain : List (List Nat) :=
        (List.range (l.path.length + 1)).map (fun k => l.path.take k)
      let decls : List (String × String) :=
        chain.flatMap (fun p =>
          match nodeAt d p with
          | some n => (attrsOfNode n).filterMap (fun a =>
              if a.name == "xmlns" then some ("", a.value)
              else if a.name.startsWith "xmlns:" then
                some (String.ofList (a.name.toList.drop 6), a.value)
              else none)
          | none => [])
      -- Nearer declarations are LATER in `chain`, so folding forward
      -- with replacement makes the nearest win.
      let merged := decls.foldl (fun acc (p, u) =>
        (acc.filter (fun (q, _) => q != p)) ++ [(p, u)])
        [("xml", "http://www.w3.org/XML/1998/namespace")]
      ((merged.filter (fun (_, u) => u != "")).zipIdx).map (fun ((p, u), i) =>
        .ns { path := l.path, slot := some (false, i) } p u)
  | _ => []

/-! ## The thirteen axes -/

/-- Sort items into document order and drop duplicates. Every axis
    result and every union is a NODE-SET, and a node-set is a set in
    document order — a list that keeps a node twice makes `count()`
    lie. -/
def normalize (xs : List Item) : List Item :=
  let sorted := xs.toArray.qsort (fun a b => keyCmp a.loc.key b.loc.key == .lt) |>.toList
  sorted.foldl (fun acc x =>
    match acc.reverse.head? with
    | some y => if y.loc == x.loc then acc else acc ++ [x]
    | none   => [x]) []

/-- The ancestors of an item, nearest first (reverse document order,
    which is the axis's own order). -/
partial def ancestorsOf (d : Doc) (it : Item) : List Item :=
  match parentOf d it with
  | some p => p :: ancestorsOf d p
  | none   => []

/-- Every item of the document, in document order: the root, then
    each node with its namespace and attribute nodes. -/
def allItems (d : Doc) : List Item :=
  let root : Item := .doc d
  root :: (descendantsOf root).flatMap (fun n =>
    namespacesOf d n ++ attributesOf n ++ [n])

/-- The following axis: everything after the item in document order
    that is not one of its descendants, attributes or namespace
    nodes. -/
def followingOf (d : Doc) (it : Item) : List Item :=
  let k := it.loc.key
  ((allItems d).filter (fun x =>
    keyCmp x.loc.key k == .gt && x.kind != .attribute && x.kind != .namespace)).filter
    (fun x => !((descendantsOf it).any (fun y => y.loc == x.loc)))

/-- The preceding axis: everything before the item in document order
    that is not one of its ancestors. -/
def precedingOf (d : Doc) (it : Item) : List Item :=
  let k := it.loc.key
  let anc := (ancestorsOf d it).map (fun a => a.loc)
  ((allItems d).filter (fun x =>
    keyCmp x.loc.key k == .lt && x.kind != .attribute && x.kind != .namespace)).filter
    (fun x => !(anc.contains x.loc))

def siblingsOf (d : Doc) (it : Item) : List Item :=
  match parentOf d it with
  | some p => childrenOf p
  | none   => []

def precedingSiblingsOf (d : Doc) (it : Item) : List Item :=
  ((siblingsOf d it).filter (fun x => keyCmp x.loc.key it.loc.key == .lt)).reverse

def followingSiblingsOf (d : Doc) (it : Item) : List Item :=
  (siblingsOf d it).filter (fun x => keyCmp x.loc.key it.loc.key == .gt)

end L4Factoidal.XPath.Full
