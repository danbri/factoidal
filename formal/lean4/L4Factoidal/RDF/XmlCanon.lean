/-
L4Factoidal.RDF.XmlCanon — rdf:XMLLiteral value equality.

Port of the exclusive-canonical-XML comparison machinery from
`formal/fstar/RDF.Term.fsti` (the `xmlc_*` family). RDF 1.1 §5.1
defines the value space of `rdf:XMLLiteral` via exclusive canonical
XML: two XMLLiterals denote the same value iff their canonical forms
are equal. Comparing raw lexical forms is unsound for
functional-property counting (the WebOnt-miscellaneous-202 false
clash); the one c14n-insignificant difference the upstream RDF/XML
parser leaves behind is ATTRIBUTE ORDER, so this canonicaliser sorts
each start tag's attributes and is otherwise verbatim:
  * text content (including whitespace) preserved exactly;
  * end tags, comments (`<!`), processing instructions (`<?`) verbatim;
  * self-closing start tags expand to open+close (same infoset).
Only genuinely-insignificant aspects are normalised, so two DISTINCT
XMLLiterals never canonicalise equal, and equal-value variants do.

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

/-- Canonicalise one tag body (chars strictly between `<` and `>`),
returning the canonical tag WITH its angle brackets. -/
def canonTag (body : List Char) : List Char :=
  match body with
  | []       => ['<', '>']
  | '/' :: _ => '<' :: body ++ ['>']
  | '!' :: _ => '<' :: body ++ ['>']
  | '?' :: _ => '<' :: body ++ ['>']
  | _        =>
      let (nm, r1) := takeName body []
      let (attrs, selfClose) := parseAttrs (r1.length + 1) r1 []
      let openTag := '<' :: nm ++ renderAttrs (sortAttrs attrs) ++ ['>']
      if selfClose then openTag ++ '<' :: '/' :: nm ++ ['>']
      else openTag

/-- Scan up to (and consuming) the closing `>`; returns
(body-without-brackets, remainder-after-`>`). -/
def splitTag : List Char → List Char → List Char × List Char
  | [],        acc => (acc.reverse, [])
  | c :: rest, acc =>
      if c = '>' then (acc.reverse, rest) else splitTag rest (c :: acc)

/-- Walk the char stream: text verbatim; `<` begins a tag that is
canonicalised. Fuel-bounded. -/
def walk : Nat → List Char → List Char
  | 0,     _  => []
  | _ + 1, [] => []
  | fuel + 1, c :: rest =>
      if c = '<' then
        let (body, remainder) := splitTag rest []
        canonTag body ++ walk fuel remainder
      else c :: walk fuel rest

def canonicalize (s : String) : List Char :=
  let cs := s.toList
  walk (cs.length + 1) cs

/-- XMLLiteral value equality: canonical char streams match.
Reflexive by construction (`f x = f x`). -/
def xmlCanonEq (s1 s2 : String) : Bool :=
  canonicalize s1 == canonicalize s2

@[simp] theorem xmlCanonEq_refl (s : String) : xmlCanonEq s s = true := by
  simp [xmlCanonEq]

end L4Factoidal.RDF.XmlCanon
