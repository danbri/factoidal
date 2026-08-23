/-
L4Factoidal.GRDDL.Discovery — GRDDL transformation discovery and the
GRDDL result of a document.

Spec: GRDDL, W3C Recommendation 11 September 2007
(https://www.w3.org/TR/grddl/). Port of
`formal/fstar/GRDDL.Discovery.fst`.

GRDDL says: given a document, find the transformations it associates
with itself, run each, and MERGE the results (§7). The four ways a
document names a transformation, and where each is implemented:

  * §2 the `grddl:transformation` attribute on the ROOT element — a
    whitespace-separated list of IRI references (`transformationAttr`);
  * §4 an XHTML `head/@profile` naming the GRDDL profile, which GATES
    `link`/`a` elements whose `@rel` token list includes
    `transformation` (`profileLinks`);
  * §5 a CUSTOM `head/@profile` document, whose own
    `rel="profileTransformation"` links apply to every document
    referencing it (`profileDocTransformations`);
  * §3 the root element's NAMESPACE document, whose
    `grddl:namespaceTransformation` elements apply to every document
    in that namespace (`namespaceDocTransformations`).

The first two read the document itself. The second two need a SECOND
resource, and fetching it is the caller's business — those functions
take an already-parsed tree. Nothing in this module does I/O.

A source that is ITSELF RDF/XML is its own GRDDL result (§2, the
"faithful rendition" case), so `grddlResult` unions the RDF/XML
reading of the source with every transform's output.

## One level, not a fixpoint

A fetched namespace or profile document that itself declares further
namespace or profile documents is NOT recursed into. The corpus's
`loop`, `loopx` and `ns-ns-*` cases exercise exactly that, and they
stay named residue rather than an approximation — an approximation
would answer them confidently and wrongly.
-/
import L4Factoidal.XSLT.Transform
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.GRDDL

open L4Factoidal.XML
open L4Factoidal.RDF
open L4Factoidal.XSLT

/-! ## Vocabulary -/

/-- The GRDDL namespace: the attribute namespace of
    `grddl:transformation`. -/
def grddlNS : String := "http://www.w3.org/2003/g/data-view#"

/-- The GRDDL profile URI. Note the deliberate absence of a trailing
    `#`: §4 uses the bare form. -/
def grddlProfile : String := "http://www.w3.org/2003/g/data-view"

def rdfNS : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

def testVocabNS : String :=
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#"
def networkedTestIri : String := testVocabNS ++ "NetworkedTest"

/-! ## Whitespace token lists -/

private def isWsC (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def splitWs (s : String) : List String :=
  (s.toList.foldr (fun c acc =>
      if isWsC c then [] :: acc
      else match acc with
           | w :: r => (c :: w) :: r
           | []     => [[c]]) [[]]).filterMap (fun w =>
    if w.isEmpty then none else some (String.ofList w))

/-! ## Names -/

/-- The local part of a QName. XHTML test documents bind the XHTML
    namespace as the DEFAULT namespace, so `head`, `link` and `a`
    arrive unprefixed; stripping any prefix keeps the walk working
    either way. -/
def localOf (name : String) : String :=
  match name.toList.findIdx? (· == ':') with
  | some i => String.ofList (name.toList.drop (i + 1))
  | none   => name

def prefixOf (name : String) : String :=
  match name.toList.findIdx? (· == ':') with
  | some i => String.ofList (name.toList.take i)
  | none   => ""

def attrsOf : Node → List Attribute
  | .element _ a _ => a
  | _              => []

def kidsOf : Node → List Node
  | .element _ _ ks => ks
  | _               => []

def tagOf : Node → String
  | .element t _ _ => t
  | _              => ""

def attrVal (n : Node) (name : String) : Option String :=
  ((attrsOf n).find? (fun a => a.name == name)).map (·.value)

/-- Prefix → namespace URI, from an element's own `xmlns:*`
    attributes. -/
def nsMapOf (attrs : List Attribute) : List (String × String) :=
  attrs.filterMap (fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:" then
      some (String.ofList (a.name.toList.drop 6), a.value)
    else none)

/-! ## §2 — the `grddl:transformation` attribute -/

/-- The root element's `grddl:transformation` attribute value, under
    ANY prefix bound to the data-view namespace. Matching the literal
    prefix `grddl` would miss every document that binds it to
    something else, which the corpus does. -/
def transformationAttrValue (root : Node) : Option String :=
  let attrs := attrsOf root
  let nsm := nsMapOf attrs
  (attrs.find? (fun a =>
    localOf a.name == "transformation" &&
    ((nsm.find? (fun (p, _) => p == prefixOf a.name)).map (·.2)) == some grddlNS)).map
    (·.value)

/-- §2: the unresolved IRI references that attribute carries. -/
def transformationAttr (root : Node) : List String :=
  match transformationAttrValue root with
  | some v => splitWs v
  | none   => []

/-! ## §4 — the XHTML profile gate and `rel="transformation"` links -/

partial def headElement : Node → Option Node
  | n@(.element t _ ks) => if localOf t == "head" then some n else ks.findSome? headElement
  | _ => none

/-- §4: does the document's `head` declare the GRDDL profile? That is
    the gate; without it a `rel="transformation"` link means nothing. -/
def headHasGrddlProfile (root : Node) : Bool :=
  match headElement root with
  | some h => match attrVal h "profile" with
      | some v => (splitWs v).contains grddlProfile
      | none   => false
  | none   => false

def relHasToken (n : Node) (token : String) : Bool :=
  let t := localOf (tagOf n)
  (t == "link" || t == "a") &&
  (match attrVal n "rel" with
   | some v => (splitWs v).contains token
   | none   => false)

partial def collectLinks (token : String) : Node → List String
  | n@(.element _ _ ks) =>
      (if relHasToken n token then (attrVal n "href").toList else []) ++
      ks.flatMap (collectLinks token)
  | _ => []

/-- §4: the `@href` of every `rel="transformation"` link ANYWHERE in
    the document — head or body, which the `InBody` cases require —
    but only when the head declares the GRDDL profile. -/
def profileLinks (root : Node) : List String :=
  if headHasGrddlProfile root then collectLinks "transformation" root else []

/-! ## Bases -/

/-- An XHTML `<base href="...">` in the head sets the document base. -/
def htmlBaseHref (root : Node) : Option String :=
  match headElement root with
  | some h => ((kidsOf h).find? (fun k => localOf (tagOf k) == "base")).bind
                (fun b => attrVal b "href")
  | none   => none

/-- The document base: an XHTML `<base href>` first, then a root
    `xml:base`, then the document's own IRI. -/
def docBase (fallback : String) (root : Node) : String :=
  match htmlBaseHref root with
  | some b => L4Factoidal.Syntax.resolveIri fallback b
  | none   => match attrVal root "xml:base" with
      | some b => L4Factoidal.Syntax.resolveIri fallback b
      | none   => fallback

def resolveAll (base : String) (refs : List String) : List String :=
  refs.map (L4Factoidal.Syntax.resolveIri base)

/-- §2 + §4: everything the document says about itself, resolved. -/
def sameDocumentTransformations (fallback : String) (root : Node) : List String :=
  resolveAll (docBase fallback root) (transformationAttr root ++ profileLinks root)

/-! ## §5 — profile documents -/

/-- The profile URIs the agent must DEREFERENCE: the head's `@profile`
    tokens minus the fixed GRDDL profile constant, which only gates
    same-document links and is never itself a document to fetch. -/
def customProfileUris (fallback : String) (root : Node) : List String :=
  match headElement root with
  | some h => match attrVal h "profile" with
      | some v => resolveAll (docBase fallback root)
          ((splitWs v).filter (· != grddlProfile))
      | none   => []
  | none   => []

/-- §5: the transformations a fetched profile document associates with
    documents that reference it — the `@href` of every
    `rel="profileTransformation"` link — resolved against the profile
    document's own base. The profile document must itself carry the
    GRDDL profile in its head, which is the §5 gate. -/
def profileDocTransformations (profileIri : String) (profileDoc : Node)
    : List String :=
  if headHasGrddlProfile profileDoc then
    resolveAll (docBase profileIri profileDoc)
      (collectLinks "profileTransformation" profileDoc)
  else []

/-! ## §3 — namespace documents -/

/-- The root element's namespace URI: the namespace document the agent
    dereferences. An unprefixed root name takes the default `xmlns`; a
    prefixed one takes its prefix's binding. -/
def rootNamespaceUri (root : Node) : Option String :=
  let nsm := nsMapOf (attrsOf root)
  (nsm.find? (fun (p, _) => p == prefixOf (tagOf root))).map (·.2)

/-- A `grddl:namespaceTransformation` element carries the transform
    IRI in its `rdf:resource` attribute. Matched by LOCAL NAME, and
    gated on the presence of an `rdf:resource`, so a stray element of
    that name without one contributes nothing. -/
partial def collectNsTransforms : Node → List String
  | n@(.element t _ ks) =>
      (if localOf t == "namespaceTransformation" then
         (attrVal n "rdf:resource").toList else []) ++
      ks.flatMap collectNsTransforms
  | _ => []

/-- §3: the transformations a fetched namespace document declares,
    resolved against that document's own base. -/
def namespaceDocTransformations (nsIri : String) (nsDoc : Node) : List String :=
  resolveAll (docBase nsIri nsDoc) (collectNsTransforms nsDoc)

/-! ## The result -/

/-- Is the root element `rdf:RDF`? -/
def isRdfXmlRoot (root : Node) : Bool :=
  let nsm := nsMapOf (attrsOf root)
  localOf (tagOf root) == "RDF" &&
  ((nsm.find? (fun (p, _) => p == prefixOf (tagOf root))).map (·.2)) == some rdfNS

/-- The result of applying ONE transformation: run the stylesheet, then
    read its output as RDF/XML against the document base.

    An `Except` with a REASON, not an `Option`. A transform that
    produced nothing usable is not the same as a transform that
    produced an empty graph, and treating them alike would score a
    broken stylesheet as a document with no triples; a refusal that
    names nothing is one the reader cannot act on. -/
def applyTransformation (base : String) (stylesheet : Document) (source : Document)
    (imports : List (String × Node) := []) : Except String Graph :=
  match transform stylesheet source [] imports with
  | .refused why => .error ("the transform was declined: " ++ why)
  | .produced t =>
      match L4Factoidal.Syntax.RdfXml.parseRdfXml t (some base) with
      | .ok g    => .ok g
      | .error e => .error ("the transform output is not RDF/XML: " ++ e.msg)

/-- The full GRDDL result: the RDF/XML-base contribution unioned with
    every transform's output (§7, "merge those GRDDL results").
    An error when any transformation failed to produce a graph,
    carrying that transformation's reason. -/
def grddlResult (fallbackBase : String) (source : Document) (sourceText : String)
    (stylesheets : List (Document × List (String × Node))) : Except String Graph :=
  -- The transform's output describes the SOURCE, and a relative
  -- reference in it — `rdf:about=""` above all — resolves against the
  -- source's EFFECTIVE base, which a root `xml:base` or an XHTML
  -- `<base href>` may move. Using the fetch IRI instead named the
  -- wrong subject while producing exactly the right number of
  -- triples: `xmlbase1` and five others differed in one IRI and
  -- nothing else.
  let base := docBase fallbackBase source.root
  let ownTriples : Graph :=
    if isRdfXmlRoot source.root then
      match L4Factoidal.Syntax.RdfXml.parseRdfXml sourceText (some base) with
      | .ok g    => g
      | .error _ => []
    else []
  stylesheets.foldlM (fun acc (s, imps) =>
    (applyTransformation base s source imps).map (fun g => acc ++ g)) ownTriples

end L4Factoidal.GRDDL
