/-
L4Factoidal.XSLT.Templates — template patterns, default priorities and
conflict resolution, ported from `formal/fstar/XSLT.Transform.fst`.

Spec: XSLT 1.0 §5.5 (conflict resolution for template rules) and
§2.6.2 (import precedence).

SCOPE: this is the SEMANTIC HEART of template selection, not the whole
transform. The F* module is 4,183 lines covering instantiation,
attribute sets, number formatting, output serialisation and keys.
What is here is the part that decides WHICH template fires — which is
where XSLT implementations disagree with each other and with the spec.

Priorities are scaled by TEN and kept as integers. XSLT's defaults are
0, -0.25, -0.5 and 0.5; scaling makes every comparison exact and
removes float ordering from the one place where a tie decides which
template runs.
-/

namespace L4Factoidal.XSLT

/-- A template rule. `matchPattern` is empty for a name-only
    (`call-template`) template. Priority is x10-scaled; `none` means
    "use the default for the pattern". -/
structure Template where
  matchPattern : String := ""
  name         : String := ""
  mode         : String := ""
  priority     : Option Int := none
  importPrec   : Int := 0
  /-- Position in the stylesheet, for the last-wins tiebreak. -/
  docOrder     : Nat := 0
deriving Repr, DecidableEq, Inhabited

private def trim (s : String) : String :=
  String.ofList (((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse)

private def splitOn (c : Char) (s : String) : List String :=
  let rec go (cur : List Char) (acc : List String) : List Char → List String
    | []     => acc ++ [String.ofList cur.reverse]
    | x :: r => if x == c then go [] (acc ++ [String.ofList cur.reverse]) r
                else go (x :: cur) acc r
  go [] [] s.toList

private def contains (c : Char) (s : String) : Bool := s.toList.contains c

private def localPart (s : String) : String :=
  match (s.toList.findIdx? (· == ':')) with
  | some i => String.ofList (s.toList.drop (i + 1))
  | none   => s

private def prefixPart (s : String) : String :=
  match (s.toList.findIdx? (· == ':')) with
  | some i => String.ofList (s.toList.take i)
  | none   => ""

/-- §5.5 default priority of ONE pattern alternative, x10-scaled.

    The four levels, and why each is where it is:
    * `-5` (-0.5): a bare node test like `*`, `text()`, `node()` — the
      least specific thing a pattern can say.
    * `-2` (-0.25): a namespace wildcard `pfx:*` — more specific than
      a bare test, less than a name.
    * `0`: a QName test — the ordinary case.
    * `5` (0.5): anything with a `/` or a predicate `[...]` — the most
      specific.

    Note the ORDER of the checks: the `/`-or-`[` test comes BEFORE the
    wildcard test, so `foo/*` scores 5 rather than -5. Reversing them
    makes compound patterns lose to bare ones. -/
def altPriority (alt : String) : Int :=
  let a := trim alt
  if ["*", "@*", "node()", "text()", "comment()",
      "processing-instruction()", "attribute::*"].contains a then -5
  else if contains '/' a || contains '[' a then 5
  else
    let core := if a.startsWith "@" then String.ofList (a.toList.drop 1) else a
    if localPart core == "*" && prefixPart core != "" then -2
    else 0

/-- A pattern may list alternatives with `|`; the template's default
    priority is the HIGHEST among them. -/
def defaultPriority (pattern : String) : Int :=
  (splitOn '|' pattern).foldl (fun cur a => max cur (altPriority a)) (-100)

def templatePriority (t : Template) : Int :=
  match t.priority with
  | some p => p
  | none   => defaultPriority t.matchPattern

/-- §5.5 + §2.6.2 conflict resolution, in the SPEC'S ORDER:

    1. IMPORT PRECEDENCE first — a higher-precedence template wins
       outright, whatever its priority.
    2. Then PRIORITY.
    3. Then document order, LAST declared wins (the spec permits
       recovering this way, and it is what implementations do).

    Checking priority before precedence is the classic bug: an
    imported template with a very specific pattern would beat an
    importing stylesheet's override, which defeats the entire point
    of `xsl:import`. -/
def better (a b : Template) : Bool :=
  if a.importPrec != b.importPrec then a.importPrec > b.importPrec
  else
    let pa := templatePriority a
    let pb := templatePriority b
    if pa != pb then pa > pb else a.docOrder ≥ b.docOrder

/-- Pick the winning template among those that match, in the given
    mode. `patMatches` supplies pattern matching (`matches` is a Lean
    keyword) — a parameter, so this
    module is testable without an XPath engine. -/
def pickTemplate (templates : List Template) (mode : String)
    (patMatches : String → Bool) : Option Template :=
  let candidates := templates.filter (fun t =>
    t.mode == mode && t.matchPattern != "" && patMatches t.matchPattern)
  candidates.foldl (fun acc t =>
    match acc with
    | none   => some t
    | some b => if better t b then some t else acc) none

/-- Look up a named template for `xsl:call-template`. Names are
    resolved by IMPORT PRECEDENCE, not by document order. -/
def findNamed (templates : List Template) (name : String) : Option Template :=
  (templates.filter (fun t => t.name == name)).foldl (fun acc t =>
    match acc with
    | none   => some t
    | some b => if t.importPrec > b.importPrec then some t else acc) none

/-! ## Pattern steps -/

inductive Connector where
  | child | descendant
deriving Repr, DecidableEq, Inhabited

/-- Split a location pattern into steps.

    `//x` is a RELATIVE descendant pattern, `/x` is ROOT-ANCHORED.
    The two differ only in a leading slash and mean quite different
    things, which is why the parse returns the anchoring flag rather
    than folding it into the steps. -/
def parseSteps (pattern : String) : Bool × List (Connector × String) :=
  let normStep (s : String) : String :=
    let s := trim s
    if s.startsWith "child::" then String.ofList (s.toList.drop 7) else s
  let rec build (toks : List String) (pending : Connector)
      : List (Connector × String) :=
    match toks with
    | []      => []
    | t :: rest =>
        if trim t == "" then build rest .descendant
        else (pending, normStep t) :: build rest .child
  match splitOn '/' pattern with
  | first :: t2 :: rest =>
      if trim first == "" then
        if trim t2 == "" then (false, build rest .descendant)     -- "//x"
        else (true, build (t2 :: rest) .child)                    -- "/x"
      else (false, build (first :: t2 :: rest) .child)
  | toks => (false, build toks .child)

end L4Factoidal.XSLT
