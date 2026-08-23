/-
L4Factoidal.XSLT.Transform — an XSLT 1.0 transform: read a stylesheet
into instructions, instantiate them against a source tree, and
serialise the result tree.

Spec: XSL Transformations (XSLT) Version 1.0, W3C Recommendation
16 November 1999. Section numbers below cite it.

`Templates.lean` already held §5.5 conflict resolution — WHICH
template fires. This module is everything else: the pattern-matching
that feeds it, instantiation of the instruction set, attribute value
templates, variables and parameters, sorting, and output
serialisation.

## An instruction this engine does not have is a REFUSAL

`instantiate` returns `Option (List RNode)`, and every element in the
XSLT namespace that is not in `Instr` becomes `none`. That propagates
to the runner as UNDECIDED, never as a produced document. The failure
this avoids is the one that has cost this project the most across six
suites: output of the right SHAPE with content missing, which reads as
a near-miss rather than as a gap.

## Attributes are produced, then absorbed

`xsl:attribute` is an instruction, so it produces a result node like
any other — but an attribute is not a child. `RNode.attr` is that
produced attribute, and the enclosing element constructor ABSORBS
every one that appears at the head of its content. §7.1.3 makes it an
error for an attribute to be produced after a child; this engine
absorbs such an attribute anyway rather than dropping it silently,
because dropping it would remove information the stylesheet asked
for.
-/
import L4Factoidal.XPath.Eval
import L4Factoidal.XSLT.Templates
import L4Factoidal.XML.Parser

namespace L4Factoidal.XSLT

open L4Factoidal.XML
open L4Factoidal.XPath
open L4Factoidal.XPath.Full

/-- The XSLT namespace URI. An element is an instruction because of
    THIS URI, never because its tag happens to start with `xsl:` —
    a stylesheet may bind the prefix to anything. -/
def xsltNS : String := "http://www.w3.org/1999/XSL/Transform"

/-! ## The result tree -/

inductive RNode where
  | elem (tag : String) (attrs : List Attribute) (kids : List RNode)
  | text (s : String)
  | comment (s : String)
  | pi (target : String) (data : String)
  /-- An attribute produced by `xsl:attribute`, awaiting absorption
      by the element that encloses it. -/
  | attr (name : String) (value : String)
deriving Repr, Inhabited

/-- Split a produced content list into the attributes to absorb and
    the children to keep. A LATER attribute of the same name
    overrides an earlier one (§7.1.3). -/
partial def splitContent (rs : List RNode) : List Attribute × List RNode :=
  rs.foldl (fun (as, ks) r =>
    match r with
    | .attr n v => ((as.filter (fun a => a.name != n)) ++ [{ name := n, value := v }], ks)
    -- An EMPTY text node is not a node. Keeping one made an element
    -- with no content serialise as `<td></td>` instead of `<td/>`
    -- (position-8101) — the same infoset, a different document under
    -- the canonical comparison the suite makes.
    | .text ""  => (as, ks)
    | other     => (as, ks ++ [other])) ([], [])

/-! ## Sort keys -/

structure SortSpec where
  select    : String := "."
  dataType  : String := "text"
  order     : String := "ascending"
  /-- `lang` and `case-order` select a LANGUAGE collation instead of
      codepoint order. XSLT 1.0 leaves the collation
      implementation-defined; what is implemented here is the one the
      corpus asks for and no more — see `collateLe`. -/
  lang      : String := ""
  caseOrder : String := ""
deriving Repr, Inhabited

/-! ## Instructions -/

mutual

inductive Instr where
  /-- A literal result element: its tag, its attribute value
      templates, the namespace declarations to copy to the result,
      and its content. -/
  | lre       (tag : String) (avts : List (String × String))
              (nsdecls : List (String × String)) (body : List Instr)
  | textN     (s : String)
  | valueOf   (select : String)
  | applyT    (select : Option String) (mode : String) (sorts : List SortSpec)
              (withParams : List (String × Binding))
  | callT     (name : String) (withParams : List (String × Binding))
  | forEach   (select : String) (sorts : List SortSpec) (body : List Instr)
  | ifI       (test : String) (body : List Instr)
  | choose    (whens : List (String × List Instr)) (otherwise : List Instr)
  | elemI     (name : String) (nsAvt : Option String) (body : List Instr)
  | attrI     (name : String) (nsAvt : Option String) (body : List Instr)
  | commentI  (body : List Instr)
  | piI       (name : String) (body : List Instr)
  | copyI     (body : List Instr)
  | copyOf    (select : String) (dropNs : Bool)
  | varI      (name : String) (bind : Binding) (rest : List Instr)
  /-- An element in the XSLT namespace this engine does not
      implement. Instantiating it REFUSES the transform. -/
  | unknown   (tag : String)
deriving Repr, Inhabited

/-- What a variable, parameter or `xsl:with-param` binds to: either a
    select expression, or a body whose result is a fragment. -/
inductive Binding where
  | sel  (expr : String)
  | body (is : List Instr)
deriving Repr, Inhabited

end

structure Tmpl where
  pat      : String := ""
  name     : String := ""
  mode     : String := ""
  priority : Option Int := none
  order    : Nat := 0
  params   : List (String × Binding) := []
  body     : List Instr := []
  nsctx    : List (String × String) := []
deriving Repr, Inhabited

structure Stylesheet where
  templates : List Tmpl := []
  /-- Top-level `xsl:variable` and `xsl:param`, in declaration order. -/
  globals   : List (String × Binding × List (String × String)) := []
  /-- `xsl:strip-space` name tests. -/
  stripSpace : List String := []
  preserveSpace : List String := []
  outputMethod : String := "xml"
  indent : Bool := false
  omitDecl : Bool := false
deriving Repr, Inhabited
/-! ## Reading a stylesheet -/

private def trimS (s : String) : String :=
  String.ofList (((s.toList.dropWhile isXmlSpace).reverse.dropWhile isXmlSpace).reverse)

private def isAllWs (s : String) : Bool := s.toList.all isXmlSpace

/-- The namespace bindings an element ADDS. -/
def nsDeclsOn (n : Node) : List (String × String) :=
  (attrsOfNode n).filterMap (fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:" then some (String.ofList (a.name.toList.drop 6), a.value)
    else none)

/-- Extend a namespace context with an element's own declarations.

    A REDECLARED prefix keeps its original position and only changes
    its URI. Removing and re-appending it instead moved it to the end
    of the list, and since that list is the order the result element's
    declarations are written in, a stylesheet that redeclares a prefix
    to the same URI produced the right declarations in the wrong order
    (copy-3102). -/
def extendNs (ctx : List (String × String)) (n : Node) : List (String × String) :=
  (nsDeclsOn n).foldl (fun acc (p, u) =>
    if acc.any (fun (q, _) => q == p)
    then acc.map (fun (q, v) => if q == p then (q, u) else (q, v))
    else acc ++ [(p, u)]) ctx

def uriOfPrefix (ctx : List (String × String)) (p : String) : String :=
  ((ctx.find? (fun (q, _) => q == p)).map (·.2)).getD ""

/-- Is this element an XSLT instruction, and if so which one? Decided
    by the NAMESPACE the tag's prefix resolves to. -/
def xslLocal (ctx : List (String × String)) (tag : String) : Option String :=
  if uriOfPrefix ctx (prefixOf tag) == xsltNS then some (localOf tag) else none

def attrOf (n : Node) (nm : String) : Option String :=
  ((attrsOfNode n).find? (fun a => a.name == nm)).map (·.value)

private def elemsOf (n : Node) : List Node :=
  (kidsOf n).filter (fun c => match c with | .element .. => true | _ => false)

/-- `xsl:sort` children of an instruction. -/
def sortsOf (ctx : List (String × String)) (n : Node) : List SortSpec :=
  (elemsOf n).filterMap (fun c =>
    match c with
    | .element t _ _ =>
        if xslLocal (extendNs ctx c) t == some "sort" then
          some { select := (attrOf c "select").getD "."
                 dataType := (attrOf c "data-type").getD "text"
                 order := (attrOf c "order").getD "ascending"
                 lang := (attrOf c "lang").getD ""
                 caseOrder := (attrOf c "case-order").getD "" }
        else none
    | _ => none)

/-- `xsl:with-param` children, as bindings. -/
partial def paramsOf (ctx : List (String × String)) (n : Node)
    (wanted : String) (read : List (String × String) → List Node → List Instr)
    : List (String × Binding) :=
  (elemsOf n).filterMap (fun c =>
    match c with
    | .element t _ kids =>
        let c2 := extendNs ctx c
        if xslLocal c2 t == some wanted then
          match attrOf c "name" with
          | none    => none
          | some nm => some (nm, match attrOf c "select" with
              | some e => Binding.sel e
              | none   => Binding.body (read c2 kids))
        else none
    | _ => none)

/-- Prepare an element's stylesheet content: drop comments and
    processing instructions, then MERGE the adjacent character data
    they were separating.

    The order matters. §3.4 strips a whitespace-only text node, and a
    comment sitting between two runs of character data splits what is
    one text node in the prepared stylesheet into two — the first of
    which is often whitespace-only. Stripping before merging deleted
    indentation the transform is supposed to emit, in a way that only
    shows up in documents that carry a comment inside a literal
    result element (axes-090, id-016). -/
def styleKids (kids : List Node) : List Node :=
  (kids.filter (fun k =>
    match k with | .comment _ => false | .pi _ _ => false | _ => true)).foldl
    (fun acc k =>
      let t? := match k with
        | .text s  => some s
        | .cdata s => some s
        | _        => none
      match t?, acc.reverse.head? with
      | some s, some (.text p) => acc.dropLast ++ [.text (p ++ s)]
      | some s, _              => acc ++ [.text s]
      | none,   _              => acc ++ [k]) []

mutual

/-- Read a stylesheet element's content into instructions. -/
partial def readBody (ctx : List (String × String)) (excl : List String)
    (kids : List Node) : List Instr :=
  readSeq ctx excl (styleKids kids)

partial def readSeq (ctx : List (String × String)) (excl : List String)
    (kids : List Node) : List Instr :=
  -- `xsl:variable` and `xsl:param` SCOPE over their following
  -- siblings, so a variable is read as a node whose `rest` is
  -- everything after it. Reading them as a flat list makes every
  -- variable global to the template, which is wrong the moment two
  -- branches bind the same name.
  match kids with
  | [] => []
  | k :: rest =>
      match k with
      | .element t _ ks =>
          let c2 := extendNs ctx k
          match xslLocal c2 t with
          | some "variable" | some "param" =>
              let nm := (attrOf k "name").getD ""
              let b := match attrOf k "select" with
                | some e => Binding.sel e
                | none   => Binding.body (readBody c2 excl ks)
              [.varI nm b (readSeq ctx excl rest)]
          | _ => readOne ctx excl k ++ readSeq ctx excl rest
      | .text s =>
          -- §3.4: a whitespace-only text node in the stylesheet is
          -- stripped. Keeping it puts stray indentation into every
          -- result document.
          (if isAllWs s then [] else [Instr.textN s]) ++ readSeq ctx excl rest
      | .cdata s   => Instr.textN s :: readSeq ctx excl rest
      | .comment _ => readSeq ctx excl rest
      | .pi _ _    => readSeq ctx excl rest

partial def readOne (ctx : List (String × String)) (excl : List String)
    (n : Node) : List Instr :=
  match n with
  | .element t attrs kids =>
      let c2 := extendNs ctx n
      match xslLocal c2 t with
      | none =>
          -- A literal result element. Its `xsl:*` attributes are
          -- stylesheet directives, not result attributes.
          let avts := attrs.filterMap (fun a =>
            if isNsDecl a then none
            else if uriOfPrefix c2 (prefixOf a.name) == xsltNS then none
            else some (a.name, a.value))
          -- §7.1.1: an `xsl:exclude-result-prefixes` on THIS element
          -- adds to the exclusions for it and everything inside it.
          -- `#default` names the default namespace.
          let more := (attrs.filterMap (fun a =>
            if uriOfPrefix c2 (prefixOf a.name) == xsltNS &&
               (localOf a.name == "exclude-result-prefixes" ||
                localOf a.name == "extension-element-prefixes")
            then some a.value else none)).flatMap splitWs
          let excl2 := excl ++ more.map (fun p => if p == "#default" then "" else p)
          -- A default-namespace UNDECLARATION (`xmlns=""`) is kept:
          -- dropping it let the element inherit the enclosing default
          -- namespace, which is a DIFFERENT element name (namespace-4501).
          let decls := c2.filter (fun (p, u) =>
            u != xsltNS && p != "xml" && !(excl2.contains p))
          [.lre t avts decls (readBody c2 excl2 kids)]
      | some "text" =>
          [.textN (String.join ((kidsOf n).map (fun c =>
            match c with | .text s => s | .cdata s => s | _ => "")))]
      | some "value-of"  => [.valueOf ((attrOf n "select").getD ".")]
      | some "copy-of"   =>
          -- `copy-namespaces="no"` is an XSLT 2.0 attribute. It is
          -- implemented rather than refused because the F* engine
          -- this module ports implements it, and because IGNORING it
          -- is the one option that is certainly wrong: the namespaces
          -- would be copied where the test asks for them to be
          -- dropped, and a document of the right shape would come out
          -- carrying declarations nobody asked for (copy-0601).
          [.copyOf ((attrOf n "select").getD ".")
                   ((attrOf n "copy-namespaces").getD "yes" == "no")]
      | some "apply-templates" =>
          [.applyT (attrOf n "select") ((attrOf n "mode").getD "")
                   (sortsOf c2 n) (paramsOf c2 n "with-param" (fun c ks => readBody c excl ks))]
      | some "call-template" =>
          [.callT ((attrOf n "name").getD "") (paramsOf c2 n "with-param" (fun c ks => readBody c excl ks))]
      | some "for-each" =>
          [.forEach ((attrOf n "select").getD ".") (sortsOf c2 n)
                    (readBody c2 excl (kids.filter (fun c =>
                      match c with
                      | .element t2 _ _ => xslLocal (extendNs c2 c) t2 != some "sort"
                      | _               => true)))]
      | some "if"     => [.ifI ((attrOf n "test").getD "true()") (readBody c2 excl kids)]
      | some "choose" =>
          let ws := (elemsOf n).filterMap (fun c =>
            match c with
            | .element t2 _ ks2 =>
                let c3 := extendNs c2 c
                if xslLocal c3 t2 == some "when" then
                  some (((attrOf c "test").getD "true()"), readBody c3 excl ks2)
                else none
            | _ => none)
          let ot := (elemsOf n).findSome? (fun c =>
            match c with
            | .element t2 _ ks2 =>
                let c3 := extendNs c2 c
                if xslLocal c3 t2 == some "otherwise" then some (readBody c3 excl ks2) else none
            | _ => none)
          [.choose ws (ot.getD [])]
      | some "element" =>
          [.elemI ((attrOf n "name").getD "") (attrOf n "namespace") (readBody c2 excl kids)]
      | some "attribute" =>
          [.attrI ((attrOf n "name").getD "") (attrOf n "namespace") (readBody c2 excl kids)]
      | some "comment"  => [.commentI (readBody c2 excl kids)]
      | some "processing-instruction" =>
          [.piI ((attrOf n "name").getD "") (readBody c2 excl kids)]
      | some "copy"     => [.copyI (readBody c2 excl kids)]
      | some "sort"     => []            -- consumed by the parent
      | some "fallback" => []            -- §15: only used when the parent is absent
      | some other      => [.unknown other]
  | .text s   => if isAllWs s then [] else [.textN s]
  | .cdata s  => [.textN s]
  | _         => []

end

/-- Split a pattern on its TOP-LEVEL `|` only. A `|` inside a
    predicate or a string literal is a union operator belonging to
    that subexpression: splitting `*[self::a|self::b]` on it yields
    two fragments, neither of which parses, and the template then
    matches nothing while the stylesheet looks fine (sort-012). -/
def splitAlternatives (pat : String) : List String :=
  let rec go (depth : Nat) (quote : Option Char) (cur : List Char) (acc : List String)
      : List Char → List String
    | [] => acc ++ [String.ofList cur.reverse]
    | c :: r =>
        match quote with
        | some q => go depth (if c == q then none else quote) (c :: cur) acc r
        | none =>
            if c == '\'' || c == '"' then go depth (some c) (c :: cur) acc r
            else if c == '[' || c == '(' then go (depth + 1) none (c :: cur) acc r
            else if c == ']' || c == ')' then go (depth - 1) none (c :: cur) acc r
            else if c == '|' && depth == 0 then
              go 0 none [] (acc ++ [String.ofList cur.reverse]) r
            else go depth none (c :: cur) acc r
  go 0 none [] [] pat.toList

/-- Read the whole stylesheet element. A template whose `match`
    carries `|` alternatives becomes ONE `Tmpl` PER ALTERNATIVE:
    §5.5 says a multi-alternative pattern is equivalent to several
    template rules, and its priority is the alternative's own. Taking
    the maximum over alternatives instead lets a specific alternative
    raise the priority of a general one. -/
def readStylesheet (root : Node) : Stylesheet :=
  let ctx0 := extendNs [("xml", "http://www.w3.org/XML/1998/namespace")] root
  let excl0 := ((attrsOfNode root).filterMap (fun a =>
    if a.name == "exclude-result-prefixes" || a.name == "extension-element-prefixes"
    then some a.value else none)).flatMap splitWs
      |>.map (fun p => if p == "#default" then "" else p)
  let tops := elemsOf root
  let out := (tops.zipIdx).foldl (fun (st : Stylesheet) (c, i) =>
    match c with
    | .element t _ kids =>
        let c2 := extendNs ctx0 c
        match xslLocal c2 t with
        | some "template" =>
            let params := (elemsOf c).filterMap (fun p =>
              match p with
              | .element pt _ pk =>
                  let c3 := extendNs c2 p
                  if xslLocal c3 pt == some "param" then
                    some (((attrOf p "name").getD ""),
                          match attrOf p "select" with
                          | some e => Binding.sel e
                          | none   => Binding.body (readBody c3 excl0 pk))
                  else none
              | _ => none)
            let bodyKids := kids.filter (fun k =>
              match k with
              | .element kt _ _ => xslLocal (extendNs c2 k) kt != some "param"
              | _               => true)
            let base : Tmpl :=
              { name := (attrOf c "name").getD ""
                mode := (attrOf c "mode").getD ""
                priority := (attrOf c "priority").bind (fun p =>
                  -- Priorities are x10-scaled integers, matching
                  -- `Templates.lean`, so that `0.5` and `-0.25`
                  -- compare exactly.
                  match (Num.ofString (trimS p)) with
                  | .finite m s => some (if s == 0 then m * 10
                                         else if s == 1 then m
                                         else m / (Num.pow10 (s - 1)))
                  | _ => none)
                order := i
                params := params
                body := readBody c2 excl0 bodyKids
                nsctx := c2 }
            let pat := (attrOf c "match").getD ""
            if pat == "" then { st with templates := st.templates ++ [base] }
            else
              { st with templates := st.templates ++
                  ((splitAlternatives pat).map (fun alt => { base with pat := trimS alt })) }
        | some "variable" | some "param" =>
            { st with globals := st.globals ++
                [(((attrOf c "name").getD ""),
                  (match attrOf c "select" with
                   | some e => Binding.sel e
                   | none   => Binding.body (readBody c2 excl0 kids)), c2)] }
        | some "output" =>
            { st with outputMethod := (attrOf c "method").getD st.outputMethod
                      indent := (attrOf c "indent").getD "no" == "yes"
                      omitDecl := (attrOf c "omit-xml-declaration").getD "no" == "yes" }
        | some "strip-space" =>
            { st with stripSpace := st.stripSpace ++ splitWs ((attrOf c "elements").getD "") }
        | some "preserve-space" =>
            { st with preserveSpace := st.preserveSpace ++ splitWs ((attrOf c "elements").getD "") }
        | _ => st
    | _ => st) {}
  out

/-! ## Attribute value templates (§7.6.2) -/

/-- Split an AVT into literal and expression pieces. `{{` and `}}`
    are the escapes for a literal brace. `none` when a `{` is never
    closed — an unbalanced AVT is not a literal string. -/
partial def splitAvt (cs : List Char) : Option (List (Bool × String)) :=
  match cs with
  | [] => some []
  | '{' :: '{' :: r => (splitAvt r).map (fun t => (false, "{") :: t)
  | '}' :: '}' :: r => (splitAvt r).map (fun t => (false, "}") :: t)
  | '{' :: r =>
      let e := r.takeWhile (· != '}')
      let after := r.dropWhile (· != '}')
      match after with
      | _ :: r2 => (splitAvt r2).map (fun t => (true, String.ofList e) :: t)
      | []      => none
  | ch :: r => (splitAvt r).map (fun t => (false, String.ofList [ch]) :: t)

/-! ## Patterns (§5.2)

A node matches a pattern when it is a member of the node-set the
pattern selects from SOME node of the document. The equivalent
formulation the specification gives — and the one used here — is to
evaluate `/descendant-or-self::node()/PATTERN` from the root and test
membership. It is exact for the pattern grammar, including
predicates: `chapter[1]` selects, for every node, the first `chapter`
CHILD of it, so the union is precisely the set of first-chapter
children, which is what the pattern means. -/

/-- Turn a pattern alternative into the expression whose value is the
    set of nodes it matches. -/
def patternExpr (alt : String) : Option Expr := do
  let e ← parseExpr (trimS alt)
  match e with
  | .path true  st steps => some (.path true st steps)
  | .path false none steps =>
      some (.path true none (Step.mk .descendantOrSelf .nodeT [] :: steps))
  | .path false st steps => some (.path false st steps)
  | other => some other

/-- The set of node ADDRESSES a pattern alternative matches, computed
    once per document. -/
def patternLocs (d : Doc) (nsctx : List (String × String)) (alt : String)
    : Option (List Loc) := do
  let e ← patternExpr alt
  let v ← evalExpr { doc := d, item := .doc d, nsctx := nsctx } e
  match v with
  | .nodes ns => some (ns.map (·.loc))
  | _         => none

/-! ## Serialising the result tree -/

def escText (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;"
    else if c == '>' then "&gt;" else String.ofList [c]))

def escAttr (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;"
    else if c == '"' then "&quot;" else if c == '\n' then "&#10;"
    else if c == '\t' then "&#9;" else if c == '\r' then "&#13;"
    else String.ofList [c]))

/-- Serialise, carrying the namespace bindings already in force on the
    enclosing result element so that a declaration is written only
    where it CHANGES. Re-declaring an inherited binding on every
    element produces a document that is equivalent as an infoset but
    unequal as canonical XML, which is what `assert-xml` compares. -/
partial def serializeNode (inScope : List (String × String)) : RNode → String
  | .text s     => escText s
  | .comment s  => "<!--" ++ s ++ "-->"
  | .pi t d     => "<?" ++ t ++ (if d == "" then "" else " " ++ d) ++ "?>"
  | .attr _ _   => ""                    -- absorbed; never serialised alone
  | .elem tag attrs kids =>
      let decls := attrs.filterMap (fun a =>
        if a.name == "xmlns" then some ("", a.value)
        else if a.name.startsWith "xmlns:" then
          some (String.ofList (a.name.toList.drop 6), a.value)
        else none)
      -- Namespace declarations are written in DECLARATION order.
      -- Sorting them by prefix was tried, because `assert-xml` is
      -- described as a canonical-XML comparison and C14N sorts them:
      -- it fixed copy-3102 and broke conflict-resolution-1301 and
      -- copy-3701, whose expected files keep declaration order with
      -- the default namespace NOT first. The suite's expected files
      -- are not consistent about this, so the rule that matches the
      -- most of them is the one the stylesheet itself states.
      let newDecls := decls.filter (fun (p, u) =>
        ((inScope.find? (fun (q, _) => q == p)).map (·.2)).getD "" != u)
      let plain := attrs.filter (fun a => !isNsDecl a)
      let scope2 := decls.foldl (fun acc (p, u) =>
        (acc.filter (fun (q, _) => q != p)) ++ [(p, u)]) inScope
      let attrText := String.join (
        (newDecls.map (fun (p, u) =>
          " " ++ (if p == "" then "xmlns" else "xmlns:" ++ p) ++ "=\"" ++ escAttr u ++ "\""))
        ++ (plain.map (fun a => " " ++ a.name ++ "=\"" ++ escAttr a.value ++ "\"")))
      if kids.isEmpty then "<" ++ tag ++ attrText ++ "/>"
      else "<" ++ tag ++ attrText ++ ">"
           ++ String.join (kids.map (serializeNode scope2))
           ++ "</" ++ tag ++ ">"

def serialize (rs : List RNode) : String :=
  String.join (rs.map (serializeNode []))

/-! ## Copying a source node into the result -/

partial def copyNode : Node → RNode
  | .text s     => .text s
  | .cdata s    => .text s
  | .comment s  => .comment s
  | .pi t d     => .pi t d
  | .element t a ks => .elem t a (ks.map copyNode)

/-- Drop every namespace declaration from a result subtree, for
    `xsl:copy-of copy-namespaces="no"`. -/
partial def stripNsDecls : RNode → RNode
  | .elem t a ks => .elem t (a.filter (fun x => !isNsDecl x)) (ks.map stripNsDecls)
  | other        => other

/-- Copy a source item, with its subtree. Namespace declarations IN
    SCOPE on a copied element are attached to the copy: a subtree
    lifted out of its document loses the declarations its ancestors
    carried, and the copy would then be in no namespace, or in the
    wrong one. -/
def copyItem (d : Doc) (it : Item) : List RNode :=
  match it with
  | .attr _ a  => [.attr a.name a.value]
  | .ns _ _ _  => []
  | .doc kids  => kids.map copyNode
  | .tree _ n  =>
      match n with
      | .element t a ks =>
          let inherited := (namespacesOf d it).filterMap (fun x =>
            match x with
            | .ns _ p u =>
                if p == "xml" then none
                else
                  let nm := if p == "" then "xmlns" else "xmlns:" ++ p
                  if a.any (fun b => b.name == nm) then none
                  else some ({ name := nm, value := u } : Attribute)
            | _ => none)
          [.elem t (inherited ++ a) (ks.map copyNode)]
      | other => [copyNode other]

/-! ## The runtime -/

structure Rt where
  st      : Stylesheet
  doc     : Doc
  /-- The addresses each template's pattern matches, computed once per
      document. `none` marks a pattern this engine could not read;
      such a template never fires and the runner is told. -/
  locs    : List (Option (List Loc))
  globals : List (String × Value) := []
  self?   : Option Doc := none
  /-- What `document(uri)` may return. Supplied by the caller — see
      `XPath.Ctx.docs`. -/
  docs    : List (String × Doc) := []
deriving Inhabited

def tmplOf (i : Nat) (t : Tmpl) : Template :=
  { matchPattern := t.pat, name := t.name, mode := t.mode,
    priority := t.priority, importPrec := 0, docOrder := i }

/-- §5.5 selection: among the templates whose pattern matches this
    node in this mode, the one `Templates.better` prefers. -/
def selectTemplate (rt : Rt) (mode : String) (it : Item) : Option Tmpl :=
  let cands := (rt.st.templates.zipIdx).filter (fun (t, i) =>
    t.mode == mode && t.pat != "" &&
    (match rt.locs[i]? with
     | some (some ls) => ls.contains it.loc
     | _              => false))
  (cands.foldl (fun acc (t, i) =>
    match acc with
    | none          => some (t, i)
    | some (b, j)   => if better (tmplOf i t) (tmplOf j b) then some (t, i) else acc)
    none).map (·.1)

/-- A stable insertion sort. Stability is not a detail: XSLT §10 says
    two nodes with equal sort keys keep their original relative order,
    and the corpus checks it directly. -/
def insertBy (le : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys =>
      -- `x` came BEFORE every element of the sorted tail, so it must
      -- pass `y` only when `y` is STRICTLY smaller. Skipping whenever
      -- `y ≤ x` puts `x` after its equals and loses stability, which
      -- §10 requires and which the corpus checks directly: sort-001
      -- sorts `Hello` and `617-939-5938`, both NaN, and asks for them
      -- in document order in BOTH the ascending and the descending
      -- pass.
      if le y x && !(le x y) then y :: insertBy le x ys else x :: y :: ys

def sortStable (le : α → α → Bool) : List α → List α
  | []      => []
  | x :: xs => insertBy le x (sortStable le xs)

/-- The LANGUAGE collation, in the one shape the corpus exercises: a
    case-insensitive primary comparison, with `case-order` breaking a
    tie at the first position whose case differs.

    This is not a Unicode Collation Algorithm and does not claim to
    be. It is what `lang="en-US" case-order="lower-first"` means for
    ASCII words, which is the whole of what sort-043 asks: `prefix`
    before `preFIX`, and `Namespaces` between `must` and `prefix`
    rather than before every lowercase word. Codepoint order — what
    this engine uses when neither attribute is present — puts every
    capitalised word first, which is a correctly ordered list under
    the wrong ordering. A stylesheet asking for a collation this
    module does not have still gets THIS one, so the residue is a
    known narrowness, recorded here. -/
def collateLe (caseOrder : String) (a b : String) : Bool :=
  let la := a.toLower
  let lb := b.toLower
  if la != lb then la ≤ lb
  else
    let rec go : List Char → List Char → Bool
      | [], _ => true
      | _, [] => false
      | x :: xs, y :: ys =>
          if x == y then go xs ys
          else if x.isUpper && y.isLower then caseOrder == "upper-first"
          else if x.isLower && y.isUpper then caseOrder != "upper-first"
          else x ≤ y
    go a.toList b.toList

/-- Compare one sort key. `text` compares by codepoint unless a
    collation is asked for; `number` compares numerically with NaN
    FIRST in ascending order, which is what the specification's
    "implementation-defined" leeway is resolved to here and what the
    corpus's expected files show. -/
def keyLe (sp : SortSpec) (a b : String) : Bool :=
  if sp.dataType == "number" then
    let m := Num.ofString a
    let n := Num.ofString b
    match Num.cmp m n with
    | some .lt | some .eq => true
    | some .gt            => false
    | none                => m == Num.nan      -- NaN sorts first
  else if sp.lang != "" || sp.caseOrder != "" then collateLe sp.caseOrder a b
  else a ≤ b

def keyEq (sp : SortSpec) (a b : String) : Bool :=
  if sp.dataType == "number" then Num.eq (Num.ofString a) (Num.ofString b) else a == b

def keysLe (specs : List SortSpec) (a b : List String) : Bool :=
  let rec go : List SortSpec → List String → List String → Bool
    | [], _, _ => true
    | s :: ss, x :: xs, y :: ys =>
        if keyEq s x y then go ss xs ys
        else if s.order == "descending" then keyLe s y x
        else keyLe s x y
    | _, _, _ => true
  go specs a b

/-- Turn a produced result node back into a source-shaped node, for a
    result-tree fragment. An attribute has no place in a fragment's
    node list and is dropped — the one case where dropping is right,
    because §11.1 gives a fragment a ROOT node whose children are
    nodes, and an attribute is not one. -/
partial def rnodeToNode : RNode → Option Node
  | .text s    => some (.text s)
  | .comment s => some (.comment s)
  | .pi t d    => some (.pi t d)
  | .attr _ _  => none
  | .elem t a ks => some (.element t a (ks.filterMap rnodeToNode))

/-! ## Instantiation (§7) -/

def findNamedTmpl (rt : Rt) (nm : String) : Option Tmpl :=
  rt.st.templates.find? (fun t => t.name == nm)

mutual

/-- Instantiate a template body. `fuel` bounds template APPLICATION,
    not the body: a stylesheet whose templates apply to each other in
    a cycle would otherwise not terminate, and `none` is the honest
    answer for it. -/
partial def inst (rt : Rt) (fuel : Nat) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat)
    : List Instr → Option (List RNode)
  | [] => some []
  | i :: rest => do
      let a ← instOne rt fuel vars nsctx it pos size i
      match i with
      -- A variable's scope is its FOLLOWING SIBLINGS, which
      -- `readBody` has already nested inside the instruction, so
      -- nothing follows it at this level.
      | .varI .. => some a
      | _ => do
          let b ← inst rt fuel vars nsctx it pos size rest
          some (a ++ b)

partial def instOne (rt : Rt) (fuel : Nat) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat)
    : Instr → Option (List RNode)
  | .textN s => some [.text s]
  | .unknown _ => none
  | .varI nm b rest => do
      let v ← evalBinding rt fuel vars nsctx it pos size b
      inst rt fuel ((vars.filter (fun (k, _) => k != nm)) ++ [(nm, v)])
           nsctx it pos size rest
  | .valueOf sel => do
      let v ← evalIn rt vars nsctx it pos size sel
      some [.text v.toStr]
  | .copyOf sel dropNs => do
      let v ← evalIn rt vars nsctx it pos size sel
      let out ← match v with
        | .nodes ns => some ((normalize ns).flatMap (copyItem rt.doc))
        | .frag ns  => some (ns.map copyNode)
        | other     => some [RNode.text other.toStr]
      some (if dropNs then out.map stripNsDecls else out)
  | .ifI test body => do
      let v ← evalIn rt vars nsctx it pos size test
      if v.toBool then inst rt fuel vars nsctx it pos size body else some []
  | .choose whens otherwise => do
      let rec pick : List (String × List Instr) → Option (List RNode)
        | [] => inst rt fuel vars nsctx it pos size otherwise
        | (t, b) :: r => do
            let v ← evalIn rt vars nsctx it pos size t
            if v.toBool then inst rt fuel vars nsctx it pos size b else pick r
      pick whens
  | .lre tag avts decls body => do
      let attrs ← avts.foldlM (fun acc (n, v) => do
        let s ← expandAvt rt vars nsctx it pos size v
        some (acc ++ [({ name := n, value := s } : Attribute)])) []
      let kids ← inst rt fuel vars nsctx it pos size body
      let (extra, ks) := splitContent kids
      let nsAttrs := decls.map (fun (p, u) =>
        ({ name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u } : Attribute))
      some [.elem tag (nsAttrs ++ attrs ++ extra) ks]
  | .elemI nameAvt nsAvt body => do
      let nm ← expandAvt rt vars nsctx it pos size nameAvt
      let uri ← match nsAvt with
        | none   => some none
        | some a => (expandAvt rt vars nsctx it pos size a).map some
      let kids ← inst rt fuel vars nsctx it pos size body
      let (extra, ks) := splitContent kids
      -- A `namespace` attribute declares the name's prefix; without
      -- one the prefix is resolved in the STYLESHEET's context, so
      -- the declaration must travel with the element.
      -- §7.1.2: with no `namespace` attribute the name is expanded in
      -- the STYLESHEET's namespace context, and an unprefixed name
      -- then lands in the default namespace — which may be NONE.
      -- Emitting no declaration in that case let the element inherit
      -- the enclosing result element's default namespace, so
      -- `<xsl:element name="hello1"/>` inside a namespaced parent came
      -- out with the parent's namespace on it (namespace-4501).
      let decl : List Attribute := match uri with
        | some u =>
            [{ name := if prefixOf nm == "" then "xmlns" else "xmlns:" ++ prefixOf nm,
               value := u }]
        | none =>
            let p := prefixOf nm
            if p == "" then
              [{ name := "xmlns", value := uriOfPrefix nsctx "" }]
            else match nsctx.find? (fun (q, _) => q == p) with
              | some (_, u) => [{ name := "xmlns:" ++ p, value := u }]
              | none        => []
      some [.elem nm (decl ++ extra) ks]
  | .attrI nameAvt _ body => do
      let nm ← expandAvt rt vars nsctx it pos size nameAvt
      let kids ← inst rt fuel vars nsctx it pos size body
      some [.attr nm (String.join (kids.map rnodeText))]
  | .commentI body => do
      let kids ← inst rt fuel vars nsctx it pos size body
      some [.comment (String.join (kids.map rnodeText))]
  | .piI nameAvt body => do
      let nm ← expandAvt rt vars nsctx it pos size nameAvt
      let kids ← inst rt fuel vars nsctx it pos size body
      some [.pi nm (String.join (kids.map rnodeText))]
  | .copyI body =>
      match it with
      | .attr _ a => some [.attr a.name a.value]
      | .ns _ _ _ => some []
      | .doc _    => inst rt fuel vars nsctx it pos size body
      | .tree _ n =>
          match n with
          | .element t _ _ => do
              let kids ← inst rt fuel vars nsctx it pos size body
              let (extra, ks) := splitContent kids
              let inherited := (namespacesOf rt.doc it).filterMap (fun x =>
                match x with
                | .ns _ p u =>
                    if p == "xml" then none
                    else some ({ name := if p == "" then "xmlns" else "xmlns:" ++ p,
                                 value := u } : Attribute)
                | _ => none)
              some [.elem t (inherited ++ extra) ks]
          | other => some [copyNode other]
  | .forEach sel sorts body => do
      let v ← evalIn rt vars nsctx it pos size sel
      match v with
      | .nodes ns => do
          let ordered ← applySorts rt vars nsctx it pos size (normalize ns) sorts
          let n := ordered.length
          (ordered.zipIdx).foldlM (fun acc (x, k) => do
            let r ← inst rt fuel vars nsctx x (k + 1) n body
            some (acc ++ r)) []
      | _ => none
  | .callT nm ps =>
      if fuel == 0 then none
      else match findNamedTmpl rt nm with
        | none   => none
        | some t => do
            let bound ← bindParams rt fuel vars nsctx it pos size t.params ps
            inst rt (fuel - 1) bound t.nsctx it pos size t.body
  | .applyT sel mode sorts ps =>
      if fuel == 0 then none
      else do
        let targets ←
          match sel with
          | none   => some (childrenOf it)
          | some e => do
              let v ← evalIn rt vars nsctx it pos size e
              match v with
              | .nodes ns => some (normalize ns)
              | _         => none
        let ordered ← applySorts rt vars nsctx it pos size targets sorts
        let n := ordered.length
        (ordered.zipIdx).foldlM (fun acc (x, k) => do
          let r ← applyTo rt (fuel - 1) vars nsctx mode ps x (k + 1) n
          some (acc ++ r)) []

/-- Apply templates to ONE node, falling back to the §5.8 built-in
    rules. The built-ins are what make a stylesheet with a single
    `match="/"` template still reach the text of the document. -/
partial def applyTo (rt : Rt) (fuel : Nat) (vars : List (String × Value))
    (nsctx : List (String × String)) (mode : String)
    (ps : List (String × Binding)) (it : Item) (pos size : Nat)
    : Option (List RNode) :=
  match selectTemplate rt mode it with
  | some t => do
      let bound ← bindParams rt fuel vars nsctx it pos size t.params ps
      inst rt fuel bound t.nsctx it pos size t.body
  | none =>
      match it.kind with
      | .root | .element =>
          if fuel == 0 then none
          else
            let kids := childrenOf it
            let n := kids.length
            (kids.zipIdx).foldlM (fun acc (x, k) => do
              let r ← applyTo rt (fuel - 1) vars nsctx mode [] x (k + 1) n
              some (acc ++ r)) []
      | .text | .attribute => some [.text it.stringValue]
      | _                  => some []

/-- Bind a template's parameters: each declared parameter takes the
    matching `xsl:with-param` when there is one, and its own default
    otherwise. A `with-param` with no matching declaration is
    IGNORED, per §11.6. -/
partial def bindParams (rt : Rt) (fuel : Nat) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat)
    (decls : List (String × Binding)) (given : List (String × Binding))
    : Option (List (String × Value)) := do
  let supplied ← given.foldlM (fun acc (n, b) => do
    let v ← evalBinding rt fuel vars nsctx it pos size b
    some (acc ++ [(n, v)])) []
  decls.foldlM (fun acc (n, b) => do
    let v ← match supplied.find? (fun (k, _) => k == n) with
      | some (_, v) => some v
      | none        => evalBinding rt fuel acc nsctx it pos size b
    some ((acc.filter (fun (k, _) => k != n)) ++ [(n, v)])) rt.globals

partial def evalBinding (rt : Rt) (fuel : Nat) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat)
    : Binding → Option Value
  | .sel e   => evalIn rt vars nsctx it pos size e
  | .body is => do
      let rs ← inst rt fuel vars nsctx it pos size is
      some (.frag (rs.filterMap rnodeToNode))

/-- Evaluate an XPath expression in the current context. -/
partial def evalIn (rt : Rt) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat) (e : String)
    : Option Value :=
  evalText { doc := rt.doc, item := it, pos := pos, size := size,
             vars := rt.globals ++ vars, nsctx := nsctx, self? := rt.self?,
             docs := rt.docs } e

/-- Expand an attribute value template. -/
partial def expandAvt (rt : Rt) (vars : List (String × Value))
    (nsctx : List (String × String)) (it : Item) (pos size : Nat) (s : String)
    : Option String := do
  let parts ← splitAvt s.toList
  let strs ← parts.foldlM (fun acc (isExpr, txt) => do
    if isExpr then
      let v ← evalIn rt vars nsctx it pos size txt
      some (acc ++ [v.toStr])
    else some (acc ++ [txt])) []
  some (String.join strs)

/-- Order a node list by `xsl:sort` keys.

    `data-type` and `order` are ATTRIBUTE VALUE TEMPLATES (§10), so
    they are expanded against the context node before they can be
    read. Taking them literally made `data-type="{$typer}"` neither
    `number` nor `text`, which silently fell back to a text sort — a
    correctly ordered list under the wrong ordering (sort-041/042/
    043). The AVT is expanded against the node the enclosing
    instruction is processing, not against a node of the list being
    sorted, which is why the context is a separate parameter here. -/
partial def applySorts (rt : Rt) (vars : List (String × Value))
    (nsctx : List (String × String)) (cit : Item) (cpos csize : Nat)
    (ns : List Item) (specs0 : List SortSpec)
    : Option (List Item) :=
  if specs0.isEmpty then some ns
  else do
    let specs ← specs0.foldlM (fun acc (sp : SortSpec) => do
      let dt ← expandAvt rt vars nsctx cit cpos csize sp.dataType
      let od ← expandAvt rt vars nsctx cit cpos csize sp.order
      let lg ← expandAvt rt vars nsctx cit cpos csize sp.lang
      let co ← expandAvt rt vars nsctx cit cpos csize sp.caseOrder
      some (acc ++ [{ sp with dataType := dt, order := od, lang := lg, caseOrder := co }])) []
    let n := ns.length
    let keyed ← (ns.zipIdx).foldlM (fun acc (x, k) => do
      let ks ← specs.foldlM (fun a s => do
        let v ← evalIn rt vars nsctx x (k + 1) n s.select
        some (a ++ [v.toStr])) []
      some (acc ++ [(x, ks)])) []
    some ((sortStable (fun a b => keysLe specs a.2 b.2) keyed).map (·.1))

/-- The text a produced node contributes to a string-valued
    instruction. -/
partial def rnodeText : RNode → String
  | .text s      => s
  | .comment _   => ""
  | .pi _ _      => ""
  | .attr _ _    => ""
  | .elem _ _ ks => String.join (ks.map rnodeText)

end

/-! ## Whitespace stripping (§3.4) -/

/-- Does a `strip-space` / `preserve-space` name test cover this
    element? Only `*` and a QName appear in the corpus; a
    `prefix:*` test is compared on the prefix. -/
def nameTestCovers (test : String) (tag : String) : Bool :=
  test == "*" || test == tag ||
  (test.endsWith ":*" && prefixOf tag == String.ofList (test.toList.take (test.toList.length - 2)))

partial def stripWsIn (st : Stylesheet) (n : Node) : Node :=
  match n with
  | .element t a ks =>
      let strip := st.stripSpace.any (fun x => nameTestCovers x t) &&
                   !(st.preserveSpace.any (fun x => nameTestCovers x t))
      .element t a ((ks.filter (fun k =>
        match k with
        | .text s => !(strip && isAllWs s)
        | _       => true)).map (stripWsIn st))
  | other => other

/-! ## Reporting what the engine could not read -/

mutual

partial def unknownIn : List Instr → List String
  | []      => []
  | i :: r  => unknownOne i ++ unknownIn r

partial def unknownOne : Instr → List String
  | .unknown t      => ["xsl:" ++ t]
  | .lre _ _ _ b    => unknownIn b
  | .forEach _ _ b  => unknownIn b
  | .ifI _ b        => unknownIn b
  | .choose ws o    => ws.flatMap (fun (_, b) => unknownIn b) ++ unknownIn o
  | .elemI _ _ b | .attrI _ _ b | .commentI b | .piI _ b | .copyI b => unknownIn b
  | .varI _ b r     => bindUnknown b ++ unknownIn r
  | .applyT _ _ _ ps | .callT _ ps => ps.flatMap (fun (_, b) => bindUnknown b)
  | _ => []

partial def bindUnknown : Binding → List String
  | .sel _   => []
  | .body is => unknownIn is

end

/-! ## The transform -/

/-- The outcome of a transform. `refused` is NOT a failure to
    transform correctly — it is this engine declining to guess, and
    the runner scores it in its own bucket. -/
inductive Outcome where
  | produced (text : String)
  | refused  (reason : String)
deriving Repr, Inhabited

def isStylesheetRoot (root : Node) : Bool :=
  let ctx := extendNs [] root
  match root with
  | .element t _ _ =>
      (xslLocal ctx t == some "stylesheet") || (xslLocal ctx t == some "transform")
  | _ => false

/-- Run a stylesheet against a source document. `docs` is what
    `document(uri)` may return, keyed by the URI as the stylesheet
    writes it. -/
def transform (style : Document) (src : Document)
    (docs : List (String × Doc) := []) : Outcome :=
  if !isStylesheetRoot style.root then
    .refused "the stylesheet root is not xsl:stylesheet or xsl:transform"
  else
    let st := readStylesheet style.root
    let missing := (st.templates.flatMap (fun t => unknownIn t.body)).eraseDups
    if !missing.isEmpty then
      .refused ("unimplemented XSLT element(s): " ++ String.intercalate ", " missing)
    else
      let d : Doc := src.prolog ++ (stripWsIn st src.root :: src.epilog)
      let styleDoc : Doc := style.prolog ++ (style.root :: style.epilog)
      -- A NAME-ONLY template (`xsl:template name="x"` with no
      -- `match`) has no pattern to compute. Running the empty string
      -- through the pattern parser made it unreadable, and the whole
      -- stylesheet was then refused for a template that matches
      -- nothing by design (sort-012).
      let locs := st.templates.map (fun t =>
        if t.pat == "" then some [] else patternLocs d t.nsctx t.pat)
      let unread := ((st.templates.zipIdx).filterMap (fun (t, i) =>
        match locs[i]? with
        | some none => some t.pat
        | _         => none)).eraseDups
      if !unread.isEmpty then
        .refused ("unreadable match pattern(s): " ++ String.intercalate ", " unread)
      else
        let rt0 : Rt := { st := st, doc := d, locs := locs, self? := some styleDoc,
                          docs := docs }
        -- Top-level variables are evaluated against the DOCUMENT
        -- node, in declaration order, each seeing the ones before it.
        match st.globals.foldlM (fun (acc : List (String × Value)) (nm, b, ns) =>
                (evalBinding { rt0 with globals := acc } 64 [] ns (.doc d) 1 1 b).map
                  (fun v => acc ++ [(nm, v)])) [] with
        | none    => .refused "a top-level xsl:variable or xsl:param did not evaluate"
        | some gs =>
            let rt := { rt0 with globals := gs }
            match applyTo rt 4096 [] [] "" [] (.doc d) 1 1 with
            | none    => .refused "an expression or instruction did not evaluate"
            | some rs => .produced (serialize rs)

end L4Factoidal.XSLT
