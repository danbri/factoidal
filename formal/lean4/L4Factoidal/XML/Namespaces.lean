/-
L4Factoidal.XML.Namespaces — "Namespaces in XML" well-formedness.

Port of `formal/fstar/XML.Namespaces.fst` (F*) to Lean 4. Section
numbers cite **Namespaces in XML 1.0 (Third Edition)**, W3C
Recommendation 8 December 2009, https://www.w3.org/TR/xml-names/ ;
the 1.1 differences cite https://www.w3.org/TR/xml-names11/ .

This is a SEPARATE layer over `L4Factoidal.XML.Parser`'s plain XML 1.0
parse tree, deliberately not baked into `parseXML`. Plain XML 1.0
legally allows `:` anywhere in a `[5] Name` outside a namespace-aware
reading — the W3C `xmltest/` collection exercises that on purpose,
predating Namespaces in XML — so folding the namespace rules into the
parser would change what plain XML the parser accepts. Keeping them
apart is what lets the same parser score both the plain-XML and the
`eduni/namespaces/*` collections of the conformance suite.

## What this module decides

Walking the tree from the root, with the in-scope bindings threaded
down:

  * **§3 QName syntax.** Every element and attribute name must be a
    `[7] QName`: at most one colon, and that colon neither first nor
    last.
  * **§3 declarations.** `xmlns` declares the default namespace;
    `xmlns:prefix` declares a prefix. A declaration is in scope for the
    element that carries it, INCLUDING that element's own name and its
    other attributes.
  * **§4 default namespace.** It applies to unprefixed ELEMENT names
    only.
  * **§6.2 unprefixed attributes.** An unprefixed attribute name is
    never in the default namespace; its expanded name has no namespace.
  * **§3 reserved prefixes and namespace names.** `xml` is bound to
    `http://www.w3.org/XML/1998/namespace` and may be bound to nothing
    else; no other prefix may be bound to that name. `xmlns` is never a
    bindable prefix, and `http://www.w3.org/2000/xmlns/` binds to no
    prefix at all — not even as a default namespace.
  * **Undeclaring.** The default namespace may always be undeclared
    with `xmlns=""`. A PREFIXED binding may be undeclared with
    `xmlns:p=""` only in Namespaces 1.1; in 1.0 that is an error. This
    is the one place the document's declared XML version matters.
  * **§6.3 attribute uniqueness after expansion.** Two attributes whose
    QNames differ can still collide once their prefixes resolve to the
    same namespace name, so uniqueness is checked on the EXPANDED
    names, not on the QNames.
  * **Undeclared prefix.** Every prefix actually used on an element or
    attribute name must resolve.

## Scope

`isNamespaceWellFormed` reports a Bool, exactly as the F* does — it is
the namespace-suite scoring signal, not a diagnostic engine. It says
nothing about plain XML 1.0 well-formedness, which is `parseXML`'s job
and must be established first.
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XML

/-! ## Reserved namespace names — §3 -/

/-- The namespace name bound, permanently and exclusively, to the
prefix `xml`. -/
def xmlNsUri : String := "http://www.w3.org/XML/1998/namespace"

/-- The namespace name of the `xmlns` attributes themselves. It may be
bound to no prefix, and may not be a default namespace. -/
def xmlnsNsUri : String := "http://www.w3.org/2000/xmlns/"

/-! ## `[7] QName` -/

/-- The positions of every `:` in a character list, in order.
Port of F* `find_colon_positions` (structurally recursive on the list,
where the F* walks byte offsets under a fuel bound). -/
def findColons : List Char → Nat → List Nat
  | [], _ => []
  | c :: rest, i =>
    if c == ':' then i :: findColons rest (i + 1) else findColons rest (i + 1)

/-- Split a raw `[5] Name` against
`[7] QName ::= PrefixedName | UnprefixedName`.

A Name is a QName iff it carries at most one colon and that colon is
neither the first nor the last character (either would leave an empty
`[8] Prefix` or an empty `[10] LocalPart`). Any other colon pattern is
`malformed` — a violation of the NAMESPACE layer only, never of XML 1.0
itself. Port of F* `split_qname`. -/
def splitQName (str : String) : QNameSplit :=
  let cs := str.toList
  match findColons cs 0 with
  | [] => .simple str
  | [i] =>
    if i == 0 || i + 1 ≥ cs.length then .malformed
    else .prefixed (String.ofList (cs.take i)) (String.ofList (cs.drop (i + 1)))
  | _ => .malformed

/-! ## Namespace scope

A binding list. `(prefix, some uri)` is a binding; `(prefix, none)`
records an EXPLICIT undeclaration (`xmlns:p=""`), so a lookup that hits
it reports "unbound" rather than falling through to an outer scope's
stale binding for the same prefix — which is what makes "illegal use of
a prefix that has been unbound", on the SAME element as the undeclaring
attribute, reject correctly. New declarations are PREPENDED, so the
innermost declaration for a prefix always shadows the outer ones. -/

/-- The in-scope namespace bindings. Port of F* `ns_scope`. -/
abbrev NsScope := List (String × Option String)

/-- The scope every document starts in: `xml` is bound without being
declared (§3). The default namespace starts absent. Port of F*
`initial_scope`. -/
def initialScope : NsScope := [("xml", some xmlNsUri)]

/-- Resolve a prefix against the in-scope bindings; `""` is the key of
the default namespace. Port of F* `lookup_prefix`. -/
def lookupPrefix (scope : NsScope) (prefix_ : String) : Option String :=
  match scope.find? (fun b => b.1 == prefix_) with
  | some (_, u) => u
  | none => none

/-- Apply one element's own `xmlns` / `xmlns:*` declarations to the
scope it inherits.

`version` is the document's declared XML version (`"1.0"` when absent).
It decides one thing only: Namespaces in XML 1.0 forbids undeclaring a
PREFIXED binding with an empty value, while 1.1 permits it. The default
namespace may be undeclared in both.

Returns `none` when a declaration on this element is itself illegal —
a reserved-prefix or reserved-namespace-name violation, or an
out-of-version undeclaration. Port of F* `apply_declarations`. -/
def applyDeclarations (version : String) (scope : NsScope) :
    List Attribute → Option NsScope
  | [] => some scope
  | a :: rest =>
    match splitQName a.name with
    | .simple "xmlns" =>
      -- Default-namespace declaration. The reserved-namespace-name
      -- rules apply as they do to prefixed declarations; unlike a
      -- prefixed binding, the default may always be undeclared with "".
      let v := a.value
      if v == xmlNsUri || v == xmlnsNsUri then none
      else
        let entry := if v == "" then ("", none) else ("", some v)
        (applyDeclarations version scope rest).map (entry :: ·)
    | .prefixed "xmlns" localPart =>
      let v := a.value
      if localPart == "xmlns" then none              -- never a bindable prefix
      else if localPart == "xml" && v != xmlNsUri then none  -- `xml` is fixed to its one name
      else if localPart != "xml" && v == xmlNsUri then none  -- that name is reserved to `xml`
      else if v == xmlnsNsUri then none              -- binds to no prefix
      else if v == "" && version != "1.1" then none  -- 1.0: prefixed undeclaring is illegal
      else
        let entry := if v == "" then (localPart, none) else (localPart, some v)
        (applyDeclarations version scope rest).map (entry :: ·)
    | _ => applyDeclarations version scope rest

/-- Every attribute name on this element must be a `[7] QName`.
Port of F* `all_attr_names_wellformed`. -/
def allAttrNamesWellFormed (attrs : List Attribute) : Bool :=
  attrs.all (fun a => splitQName a.name != .malformed)

/-- An element's own name resolves: an unprefixed name always does (it
takes the default namespace, or none), a prefixed one only if its
prefix is bound. Port of F* `tag_prefix_bound`. -/
def tagPrefixBound (scope : NsScope) : QNameSplit → Bool
  | .simple _ => true
  | .prefixed pfx _ => (lookupPrefix scope pfx).isSome
  | .malformed => false

/-- Every attribute prefix resolves. The `xmlns` / `xmlns:*`
declarations are themselves exempt — they are the declarations, not
names to be resolved against them. Port of F*
`attrs_prefixes_bound`. -/
def attrsPrefixesBound (scope : NsScope) (attrs : List Attribute) : Bool :=
  attrs.all (fun a =>
    match splitQName a.name with
    | .simple "xmlns" => true
    | .prefixed "xmlns" _ => true
    | .simple _ => true
    | .prefixed pfx _ => (lookupPrefix scope pfx).isSome
    | .malformed => false)

/-- The expanded name an attribute compares under, or `none` when it is
a namespace declaration (which is excluded from the comparison).

Unprefixed attributes are never in the default namespace (§6.2), so
their key is `(none, name)`. Port of F* `expand_attr_key`. -/
def expandAttrKey (scope : NsScope) (a : Attribute) : Option ExpandedName :=
  match splitQName a.name with
  | .simple "xmlns" => none
  | .prefixed "xmlns" _ => none
  | .simple name => some { namespace_ := none, localPart := name }
  | .prefixed pfx localPart =>
      some { namespace_ := lookupPrefix scope pfx, localPart := localPart }
  | .malformed => none

/-- §6.3: no two attributes of one element may have the same expanded
name. Two attributes whose QNames differ still collide when their
prefixes are bound to the same namespace name. Port of F*
`attrs_unique_expanded` (via `expand_attr_keys` / `keys_unique`). -/
def attrsUniqueExpanded (scope : NsScope) (attrs : List Attribute) : Bool :=
  let keys := attrs.filterMap (expandAttrKey scope)
  keys.length == keys.eraseDups.length

mutual

/-- Check one node and, for an element, everything under it. A
declaration on an element is in scope for that element's own name and
its other attributes, so the scope is extended BEFORE any of the three
checks that consult it. Non-element nodes carry no names and always
pass. Port of F* `check_element`. -/
def checkElement (version : String) (scope : NsScope) : Node → Bool
  | .element tag attrs children =>
    let tagSplit := splitQName tag
    if tagSplit == .malformed then false
    else if !allAttrNamesWellFormed attrs then false
    else
      match applyDeclarations version scope attrs with
      | none => false
      | some newScope =>
        tagPrefixBound newScope tagSplit &&
        attrsPrefixesBound newScope attrs &&
        attrsUniqueExpanded newScope attrs &&
        checkChildren version newScope children
  | _ => true

/-- `checkElement` over a child list. Port of F* `check_children`. -/
def checkChildren (version : String) (scope : NsScope) : List Node → Bool
  | [] => true
  | n :: rest => checkElement version scope n && checkChildren version scope rest

end

/-- True iff every element and attribute name, every `xmlns` / `xmlns:*`
declaration, and the §6.3 expanded-name uniqueness constraint in the
tree rooted at `root` satisfy "Namespaces in XML" well-formedness.

`version` is the document's declared XML version string (`"1.0"` when
absent), which affects only whether an empty-valued PREFIXED
declaration is a legal undeclaration (1.1) or a violation (1.0).
Port of F* `is_namespace_wellformed`. -/
def isNamespaceWellFormed (version : String) (root : Node) : Bool :=
  checkElement version initialScope root

/-- The namespace check applied to a parsed `Document`, reading the
declared version out of its `[23] XMLDecl` and defaulting to `"1.0"`
when there is none — the `version` argument the F* entry point requires
the caller to supply. -/
def Document.namespaceWellFormed (d : Document) : Bool :=
  isNamespaceWellFormed ((d.decl.map (·.version)).getD "1.0") d.root

/-- Parse `input` and then decide namespace well-formedness on top of
plain XML 1.0 well-formedness. `false` when the document is not
well-formed XML at all — namespace well-formedness is a constraint over
a parse tree, so there is nothing to check without one. -/
def isNamespaceWellFormedDoc (input : String) : Bool :=
  match parseXML input with
  | .error _ => false
  | .ok d => d.namespaceWellFormed

/-! ## Resolving a name against a scope

The checks above are the F* module's own content. These two are the
natural readout of the same scope walk: what expanded name a QName
actually denotes. -/

/-- The expanded name of an ELEMENT tag under `scope`: an unprefixed
tag takes the default namespace (§4, unlike an attribute), a prefixed
one takes its prefix's binding. `none` when the name is not a QName or
its prefix is unbound. -/
def resolveElementName (scope : NsScope) (tag : String) : Option ExpandedName :=
  match splitQName tag with
  | .simple name => some { namespace_ := lookupPrefix scope "", localPart := name }
  | .prefixed pfx localPart =>
    match lookupPrefix scope pfx with
    | none => none
    | some uri => some { namespace_ := some uri, localPart := localPart }
  | .malformed => none

/-- The expanded name of an ATTRIBUTE under `scope`. Unprefixed
attribute names are never in the default namespace (§6.2). -/
def resolveAttributeName (scope : NsScope) (name : String) : Option ExpandedName :=
  match splitQName name with
  | .simple n => some { namespace_ := none, localPart := n }
  | .prefixed pfx localPart =>
    match lookupPrefix scope pfx with
    | none => none
    | some uri => some { namespace_ := some uri, localPart := localPart }
  | .malformed => none

end L4Factoidal.XML
