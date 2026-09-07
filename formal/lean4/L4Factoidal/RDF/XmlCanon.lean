/-
L4Factoidal.RDF.XmlCanon — rdf:XMLLiteral value equality.

Port of the exclusive-canonical-XML comparison machinery from
`formal/fstar/RDF.Term.fsti` (the `xmlc_*` family), extended with the
NAMESPACE AXIS that the F* version never had. RDF 1.1 §5.1 defines the
value space of `rdf:XMLLiteral` via **Exclusive XML Canonicalization
1.0** (W3C Rec. 18 July 2002), so two XMLLiterals denote the same value
iff their exclusive canonical forms are equal. Comparing raw lexical
forms is unsound for functional-property counting (the
WebOnt-miscellaneous-202 false clash).

What this canonicaliser normalises:
  * ATTRIBUTE ORDER — each start tag's attributes are sorted by name;
  * SELF-CLOSING START TAGS — `<br/>` expands to `<br></br>` (same
    infoset);
  * the NAMESPACE AXIS — exc-c14n §3.2: an element renders a namespace
    declaration for a prefix only when that prefix is **visibly
    utilized** by the element (it is the prefix of the element's own
    QName, or of one of its attributes' QNames) AND the declaration is
    not already in force from an OUTPUT ancestor with the same value.
    Every other in-scope declaration is dropped, and an inherited
    declaration is re-rendered on the first descendant that uses it.

Text content (including whitespace), end tags, comments (`<!`) and
processing instructions (`<?`) are copied verbatim.

The namespace axis is what reconciles the two W3C `rdf-xml` fixture
families that state the SAME value in different lexical forms:
`xml-canon/test00{1,2}` write every ambient declaration onto the
content's outermost element (`<br xmlns:rdf="…" xmlns:eg="…"/>`, where
neither prefix is used), while
`rdfms-xml-literal-namespaces/test00{1,2}` write only the visibly-used
ones and push an inherited default namespace down to the descendant
that uses it. Both canonicalise to the same string here; before the
namespace axis existed, no single serialiser could satisfy both.
Those fixtures' own headers say the treatment of namespaces that are
not visibly used is implementation dependent — exc-c14n is the rule
that makes the choice unobservable.

The F* code walks `list FStar.Char.char` with explicit fuel; the port
keeps the same shape on `List Char` — fuel-bounded recursion becomes
structural recursion on a `Nat` fuel argument, and the F*
`decreases cs` walks become structural recursion Lean checks itself.
-/
namespace L4Factoidal.RDF.XmlCanon

def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Lexicographic comparison of two char lists by codepoint. -/
def charsLt : List Char → List Char → Bool
  | [],      []      => false
  | [],      _ :: _  => true
  | _ :: _,  []      => false
  | x :: xs, y :: ys =>
      if x.toNat < y.toNat then true
      else if x.toNat > y.toNat then false
      else charsLt xs ys

/-- Read a tag/attribute name: up to whitespace, `/`, `=`, or end.
Returns (name, remainder-at-delimiter). -/
def takeName : List Char → List Char → List Char × List Char
  | [],        acc => (acc.reverse, [])
  | c :: rest, acc =>
      if isWs c || c = '/' || c = '=' then (acc.reverse, c :: rest)
      else takeName rest (c :: acc)

/-- Drop leading whitespace. -/
def dropWs : List Char → List Char
  | c :: rest => if isWs c then dropWs rest else c :: rest
  | []        => []

/-- Position just past the `=` between an attribute name and value. -/
def dropToValue (cs : List Char) : List Char :=
  match dropWs cs with
  | c :: rest => if c = '=' then dropWs rest else c :: rest
  | []        => []

/-- Read chars up to (and consuming) the closing quote `q`. -/
def takeUntil (q : Char) : List Char → List Char → List Char × List Char
  | [],        acc => (acc.reverse, [])
  | c :: rest, acc =>
      if c = q then (acc.reverse, rest) else takeUntil q rest (c :: acc)

/-- Read one quoted attribute value; returns (value, remainder). -/
def takeQuoted : List Char → List Char × List Char
  | c :: rest =>
      if c = '"' || c = '\'' then takeUntil c rest [] else ([], c :: rest)
  | [] => ([], [])

/-- Parse a start tag's attributes into (name, value) pairs, reporting
whether the tag self-closes (`/>`). Fuel-bounded, as in the source. -/
def parseAttrs : Nat → List Char → List (List Char × List Char) →
    List (List Char × List Char) × Bool
  | 0,     _,         acc => (acc.reverse, false)
  | _ + 1, [],        acc => (acc.reverse, false)
  | fuel + 1, c :: rest, acc =>
      if isWs c then parseAttrs fuel rest acc
      else if c = '/' then (acc.reverse, true)
      else
        let (nm, r1) := takeName (c :: rest) []
        let r2 := dropToValue r1
        let (v, r3) := takeQuoted r2
        parseAttrs fuel r3 ((nm, v) :: acc)

/-- Insertion sort of attribute pairs by name. -/
def insertAttr (p : List Char × List Char) :
    List (List Char × List Char) → List (List Char × List Char)
  | []        => [p]
  | q :: rest =>
      if charsLt p.1 q.1 then p :: q :: rest
      else q :: insertAttr p rest

def sortAttrs : List (List Char × List Char) → List (List Char × List Char)
  | []        => []
  | x :: rest => insertAttr x (sortAttrs rest)

/-- Render sorted attributes as ` name="value"` fragments. -/
def renderAttrs : List (List Char × List Char) → List Char
  | []               => []
  | (nm, v) :: rest  =>
      ' ' :: (nm ++ '=' :: '"' :: v ++ '"' :: renderAttrs rest)

/-! ## The namespace axis (exc-c14n §3.2)

`Bindings` is an association list from namespace prefix to namespace
URI, both as `List Char`; the empty prefix `[]` is the DEFAULT
namespace, and the empty URI means "not bound". New entries are
PREPENDED, so `lookupB` (first match wins) reports the innermost
binding. Two of them travel down the walk together: `scope` is what
the INPUT declares at this point, `rendered` is what the OUTPUT has
already declared on this element's output ancestors. -/

abbrev Bindings := List (List Char × List Char)

/-- The reserved names Namespaces in XML §3 binds without declaring. -/
def xmlnsName : List Char := ['x', 'm', 'l', 'n', 's']

/-- The `xml` prefix is bound to its namespace without a declaration,
so exc-c14n never renders one for it. -/
def xmlPrefix : List Char := ['x', 'm', 'l']

/-- Split a `[7] QName` at its FIRST colon. -/
def splitColonAux : List Char → List Char → Option (List Char × List Char)
  | [],        _   => none
  | c :: rest, acc => if c = ':' then some (acc.reverse, rest)
                      else splitColonAux rest (c :: acc)

def splitColon (nm : List Char) : Option (List Char × List Char) :=
  splitColonAux nm []

/-- A name's namespace prefix; `[]` for an unprefixed name (which takes
the default namespace when it is an element name). -/
def qnamePrefix (nm : List Char) : List Char :=
  match splitColon nm with
  | some (p, _) => p
  | none        => []

/-- `(prefix, uri)` when this attribute is a namespace declaration —
`xmlns="…"` binds the empty prefix, `xmlns:p="…"` binds `p`. -/
def asNsDecl (a : List Char × List Char) : Option (List Char × List Char) :=
  if a.1 == xmlnsName then some ([], a.2)
  else
    match splitColon a.1 with
    | some (p, l) => if p == xmlnsName then some (l, a.2) else none
    | none        => none

/-- First-match lookup: the innermost binding for a prefix. -/
def lookupB (k : List Char) : Bindings → Option (List Char)
  | []             => none
  | (a, b) :: rest => if a == k then some b else lookupB k rest

/-- Append a prefix to a first-seen-order list, without duplicates. -/
def addPrefix (ps : List (List Char)) (p : List Char) : List (List Char) :=
  if ps.contains p then ps else ps ++ [p]

/-- exc-c14n §3.2 "visibly utilizes": the prefix of the element's own
QName, plus the prefix of each of its attributes' QNames. An UNPREFIXED
attribute is in no namespace (Namespaces in XML §6.2), so it does not
utilize the default; an unprefixed ELEMENT name does, which is why the
element's own prefix (`[]` when unprefixed) always counts. Namespace
declarations themselves are not attributes for this purpose and are
excluded by the caller. -/
def visiblePrefixes (nm : List Char) (others : Bindings) : List (List Char) :=
  others.foldl
    (fun acc a =>
      match splitColon a.1 with
      | some (p, _) => addPrefix acc p
      | none        => acc)
    [qnamePrefix nm]

/-- exc-c14n §3.2: render a declaration for a visibly-utilized prefix
only when no output ancestor already declared that prefix with the same
URI. A prefix bound to nothing needs no declaration unless an output
ancestor bound it, in which case the empty value undeclares it (this is
the `xmlns=""` case for the default namespace). -/
def emitDecls (scope rendered : Bindings) : List (List Char) → Bindings
  | []       => []
  | p :: rest =>
    let tail := emitDecls scope rendered rest
    if p == xmlPrefix then tail
    else
      let v := (lookupB p scope).getD []
      match lookupB p rendered with
      | some r => if r == v then tail else (p, v) :: tail
      | none   => if v.isEmpty then tail else (p, v) :: tail

/-- The attribute name a rendered declaration is written under. -/
def declAttrName (p : List Char) : List Char :=
  if p.isEmpty then xmlnsName else xmlnsName ++ ':' :: p

/-- Canonicalise one START tag body (the chars strictly between `<` and
`>`) against the scope it inherits and what its output ancestors have
already declared. Returns the canonical start tag WITH its angle
brackets, whether the tag self-closed, and the two binding lists its
children inherit. -/
def canonStartTag (scope rendered : Bindings) (body : List Char) :
    List Char × Bool × Bindings × Bindings :=
  let (nm, r1) := takeName body []
  let (attrs, selfClose) := parseAttrs (r1.length + 1) r1 []
  let decls := attrs.filterMap asNsDecl
  let others := attrs.filter (fun a => (asNsDecl a).isNone)
  let scope' := decls ++ scope
  let emitted := emitDecls scope' rendered (visiblePrefixes nm others)
  let rendered' := emitted ++ rendered
  let declAttrs := emitted.map (fun b => (declAttrName b.1, b.2))
  let openTag := '<' :: nm ++ renderAttrs (sortAttrs (declAttrs ++ others)) ++ ['>']
  (openTag, selfClose, scope', rendered')

/-- Canonicalise one tag body, ignoring the namespace axis. Kept as the
shape the F* `xmlc_canon_tag` has; `walk` uses `canonStartTag`. -/
def canonTag (body : List Char) : List Char :=
  match body with
  | []       => ['<', '>']
  | '/' :: _ => '<' :: body ++ ['>']
  | '!' :: _ => '<' :: body ++ ['>']
  | '?' :: _ => '<' :: body ++ ['>']
  | _        =>
      let (openTag, selfClose, _, _) := canonStartTag [] [] body
      let (nm, _) := takeName body []
      if selfClose then openTag ++ '<' :: '/' :: nm ++ ['>']
      else openTag

/-- Scan up to (and consuming) the closing `>`; returns
(body-without-brackets, remainder-after-`>`). -/
def splitTag : List Char → List Char → List Char × List Char
  | [],        acc => (acc.reverse, [])
  | c :: rest, acc =>
      if c = '>' then (acc.reverse, rest) else splitTag rest (c :: acc)

/-- Walk the char stream: text verbatim; `<` begins a tag that is
canonicalised. `stack` holds one `(scope, rendered)` frame per OPEN
element, innermost first; a start tag pushes, an end tag pops.
Fuel-bounded. -/
def walk : Nat → List Char → List (Bindings × Bindings) → List Char
  | 0,        _,         _     => []
  | _ + 1,    [],        _     => []
  | fuel + 1, c :: rest, stack =>
      if c = '<' then
        let (body, remainder) := splitTag rest []
        match body with
        | []       => '<' :: '>' :: walk fuel remainder stack
        | '/' :: _ => ('<' :: body ++ ['>']) ++ walk fuel remainder stack.tail
        | '!' :: _ => ('<' :: body ++ ['>']) ++ walk fuel remainder stack
        | '?' :: _ => ('<' :: body ++ ['>']) ++ walk fuel remainder stack
        | _        =>
            let frame := stack.head?.getD ([], [])
            let (openTag, selfClose, scope', rendered') :=
              canonStartTag frame.1 frame.2 body
            let (nm, _) := takeName body []
            if selfClose then
              openTag ++ ('<' :: '/' :: nm ++ ['>']) ++ walk fuel remainder stack
            else
              openTag ++ walk fuel remainder ((scope', rendered') :: stack)
      else c :: walk fuel rest stack

def canonicalize (s : String) : List Char :=
  let cs := s.toList
  walk (cs.length + 1) cs []

/-- XMLLiteral value equality: canonical char streams match.
Reflexive by construction (`f x = f x`). -/
def xmlCanonEq (s1 s2 : String) : Bool :=
  canonicalize s1 == canonicalize s2

@[simp] theorem xmlCanonEq_refl (s : String) : xmlCanonEq s s = true := by
  simp [xmlCanonEq]

end L4Factoidal.RDF.XmlCanon
