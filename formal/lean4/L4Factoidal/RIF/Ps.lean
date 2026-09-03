/-
L4Factoidal.RIF.Ps — the RIF Core PRESENTATION SYNTAX parser.

Spec: RIF Core §3 (EBNF of the presentation syntax) plus the shared
`Const` production of RIF-BLD §3.

## The grammar accepted, stated in full

    Document ::= 'Document' '(' Base? Prefix* Import* Group? ')'
    Base     ::= 'Base' '(' IRI ')'
    Prefix   ::= 'Prefix' '(' NCName IRI ')'
    Import   ::= 'Import' '(' IRI IRI? ')'
    Group    ::= 'Group' '(' (Rule | Group)* ')'
    Rule     ::= 'Forall' Var+ '(' Clause ')' | Clause
    Clause   ::= Atomic (':-' Formula)?
    Formula  ::= 'And' '(' Formula* ')' | 'Or' '(' Formula* ')'
               | 'Exists' Var+ '(' Formula ')'
               | 'External' '(' Atom ')' | Atomic
    Atomic   ::= Term ( '[' (Term '->' Term)* ']'
                      | '##' Term | '#' Term | '=' Term
                      | '(' Term* ')' )?
    Term     ::= Var | Const | 'List' '(' Term* ')'
               | 'External' '(' Const '(' Term* ')' ')'
               | Const '(' Term* ')'
    Const    ::= '"' chars '"' '^^' Const | '"' chars '"'
               | NCName ':' localpart | '<' IRI '>' | NUMBER | '_' NCName

Anything outside it FAILS TO PARSE, with the position. A parser that
guessed would turn a syntax test into a semantics test.

## Why the tokens carry no positions

The `NegativeSyntaxTest` cases ask only whether a document parses, so
a position is a diagnostic and never a verdict. The error carries one
anyway, because a runner that cannot say WHERE a document stopped
being RIF is a runner nobody can debug.
-/
import L4Factoidal.RIF.Syntax

namespace L4Factoidal.RIF

/-! ## Tokens -/

inductive Tok where
  | name  (s : String)          -- an NCName, a keyword, or a prefixed name
  | iri   (s : String)          -- `<…>`
  | str   (s : String)          -- `"…"`, before any `^^`
  /-- `"text"@lang` — a PLAIN LITERAL. RIF writes its lexical form as
      `text@lang` in the `rdf:PlainLiteral` space, and the corpus
      compares the two spellings against each other
      (`Builtins_PlainLiteral`), so they must not be conflated. -/
  | plain (s : String)
  | num   (s : String)
  | var   (s : String)          -- `?x`
  | lparen | rparen | lbrack | rbrack
  | arrow | implies | hash | hashhash | eq | caretcaret | comma
deriving Repr, DecidableEq, Inhabited

structure PErr where
  msg : String
  pos : Nat
deriving Repr

private def isNameStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == ':'

/-- A name, stopping BEFORE a `-` that begins `->`. `-` is a name
    character and so is every letter, so `ex:a->1` scanned as the name
    `ex:a-` and then met a `>` it had no token for. A frame written
    without spaces is ordinary RIF (`Frame_slots_are_independent`
    writes `ex:o[ex:a->1]`), so this is the scan, not a special
    case. -/
private def takeNameChars : List Char → List Char
  | c :: '>' :: r => if c == '-' then [] else if isNameChar c then c :: takeNameChars ('>' :: r) else []
  | c :: r        => if isNameChar c then c :: takeNameChars r else []
  | []            => []

/-- Skip whitespace and `(* … *)`-free comments. RIF-PS has no comment
    production in the corpus, so only whitespace is skipped; anything
    else is a token. -/
private def skipWs (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)

/-- Tokenise. `fuel` is the input length, so the bound is exact. -/
def tokenize (input : String) : Except PErr (List Tok) :=
  let all := input.toList
  let total := all.length
  let rec go (acc : List Tok) : Nat → List Char → Except PErr (List Tok)
    | 0,        _  => .error { msg := "input too long", pos := 0 }
    | fuel + 1, cs =>
      let cs := skipWs cs
      let pos := total - cs.length
      match cs with
      | [] => .ok acc.reverse
      -- `(* … *)` is an ANNOTATION (RIF-BLD `IRIMETA`), not a
      -- comment, and it carries no truth: `Non-Annotation_Entailment`
      -- is the case that says a conclusion may not be derived from
      -- one. Skipping it is therefore right, and treating `(` as an
      -- open paren here made every annotated document unparsable.
      | '(' :: '*' :: r =>
          let rec skipAnn : Nat → List Char → List Char
            | 0,     cs => cs
            | f + 1, cs => match cs with
              | [] => []
              | '*' :: ')' :: t => t
              | _ :: t => skipAnn f t
          go acc fuel (skipAnn (r.length + 1) r)
      | '(' :: r => go (.lparen :: acc) fuel r
      | ')' :: r => go (.rparen :: acc) fuel r
      | '[' :: r => go (.lbrack :: acc) fuel r
      | ']' :: r => go (.rbrack :: acc) fuel r
      | ',' :: r => go (.comma :: acc) fuel r
      | ':' :: '-' :: r => go (.implies :: acc) fuel r
      | '-' :: '>' :: r => go (.arrow :: acc) fuel r
      | '#' :: '#' :: r => go (.hashhash :: acc) fuel r
      | '#' :: r => go (.hash :: acc) fuel r
      | '=' :: r => go (.eq :: acc) fuel r
      | '^' :: '^' :: r => go (.caretcaret :: acc) fuel r
      | '?' :: r =>
          let n := takeNameChars r
          if n.isEmpty then .error { msg := "expected a variable name after '?'", pos := pos }
          else go (.var (String.ofList n) :: acc) fuel (r.drop n.length)
      | '<' :: r =>
          let body := r.takeWhile (· != '>')
          (match r.dropWhile (· != '>') with
           | '>' :: r2 => go (.iri (String.ofList body) :: acc) fuel r2
           | _ => .error { msg := "unterminated IRI", pos := pos })
      | '"' :: r =>
          let body := r.takeWhile (· != '"')
          (match r.dropWhile (· != '"') with
           | '"' :: '@' :: r2 =>
               let lang := r2.takeWhile (fun c => c.isAlphanum || c == '-')
               go (.plain (String.ofList body ++ "@" ++ String.ofList lang) :: acc) fuel
                 (r2.dropWhile (fun c => c.isAlphanum || c == '-'))
           | '"' :: r2 => go (.str (String.ofList body) :: acc) fuel r2
           | _ => .error { msg := "unterminated string literal", pos := pos })
      | c :: _ =>
          if c.isDigit || ((c == '-' || c == '+') &&
                           ((cs.drop 1).head?.map Char.isDigit).getD false) then
            let n := (cs.take 1) ++ (cs.drop 1).takeWhile (fun d => d.isDigit || d == '.')
            go (.num (String.ofList n) :: acc) fuel (cs.drop n.length)
          else if isNameStart c then
            let n := takeNameChars cs
            go (.name (String.ofList n) :: acc) fuel (cs.drop n.length)
          else .error { msg := s!"unexpected character '{c}'", pos := pos }
  go [] (total + 1) all

/-! ## The parser

A `List Tok` in, an AST out. Errors carry the number of tokens LEFT,
which is a position a reader can act on; the tokens carry no source
offsets, and the `NegativeSyntaxTest` cases ask only whether a
document parses, so a position is a diagnostic and never a verdict.
-/

abbrev PRes (α : Type) := Except PErr (α × List Tok)

private def fail (ts : List Tok) (m : String) : PErr := { msg := m, pos := ts.length }

/-- The context a Const needs: the prefixes and base in force. -/
structure Ctx where
  base     : Option String := none
  prefixes : List (String × String) := []
deriving Inhabited

/-- The prefixes RIF-DTB and the corpus use without declaring them.
    A conclusion file is a BARE FORMULA with no prologue at all, and
    `_p(<http://example.org/#a>)` and `"a"^^rif:local` both appear in
    one; a reader that demanded a declaration would call 41 of the
    corpus's 80 documents unparsable. A DECLARED prefix wins over
    these. -/
def wellKnownPrefixes : List (String × String) :=
  [ ("rif",  "http://www.w3.org/2007/rif#")
  , ("xs",   xsdNs)
  , ("rdf",  rdfNs)
  , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
  , ("owl",  "http://www.w3.org/2002/07/owl#")
  , ("func", "http://www.w3.org/2007/rif-builtin-function#")
  , ("pred", "http://www.w3.org/2007/rif-builtin-predicate#")
  , ("dc",   "http://purl.org/dc/terms/") ]

def expandPrefixed (c : Ctx) (n : String) : Option String :=
  match n.splitOn ":" with
  | [p, local'] =>
      ((c.prefixes ++ wellKnownPrefixes).find? (fun (k, _) => k == p)).map
        (fun (_, u) => u ++ local')
  | _           => none

/-- A NUMBER's datatype: RIF-DTB gives an integer lexical form
    `xs:integer` and one with a point `xs:decimal`. -/
def numDatatype (n : String) : String :=
  if n.toList.contains '.' then xsdNs ++ "decimal" else xsdNs ++ "integer"

/-- `Const` — the one production every term position starts from. -/
def parseConst (c : Ctx) : List Tok → PRes (String × String)
  | .iri s :: r =>
      let abs := match c.base with
        | some b => if s.toList.contains ':' then s else b ++ s
        | none   => s
      .ok ((abs, iriSpace), r)
  | .num n :: r => .ok ((n, numDatatype n), r)
  | .str s :: .caretcaret :: r =>
      (match r with
       | .iri d :: r2  => .ok ((s, d), r2)
       | .name d :: r2 =>
           (match expandPrefixed c d with
            | some u => .ok ((s, u), r2)
            | none   => .error (fail r s!"unknown prefix in datatype '{d}'"))
       | _ => .error (fail r "expected a datatype after '^^'"))
  | .str s :: r => .ok ((s, xsdNs ++ "string"), r)
  | .plain s :: r => .ok ((s, rdfNs ++ "PlainLiteral"), r)
  | .name n :: r =>
      if n.startsWith "_" then .ok ((String.ofList (n.toList.drop 1), localSpace), r)
      else (match expandPrefixed c n with
            | some u => .ok ((u, iriSpace), r)
            | none   => .error (fail (Tok.name n :: r) s!"unknown prefix or bare name '{n}'"))
  | ts => .error (fail ts "expected a constant")

/-! ### Fuel

The recursive-descent functions below consume a token list and return
the REMAINDER. Lean cannot see that the remainder is shorter, because
the shortening happens inside `parseConst` and inside the recursive
functions themselves. Each one therefore takes a fuel bound, exactly as
`parseDocument.prologue` already does in this module.

The bound is not a limit on the input. Every step of a group either
consumes a token or hands control to the one function of the group that
consumes a token before it recurses, so a group descends at most three
levels per token. `parseFuel ts = 3 * ts.length + 3` is above that for
every token list, and running out is reported as a parse error rather
than a wrong parse. -/

def parseFuel (ts : List Tok) : Nat := 3 * ts.length + 3

mutual

/-- `Term`, with a fuel bound. -/
def parseTermF (c : Ctx) : Nat → List Tok → PRes Tm
  | 0, ts => .error (fail ts "term nesting is too deep")
  | _ + 1, .var v :: r => .ok (.var v, r)
  | f + 1, .name "List" :: .lparen :: r =>
      (match parseTermsGoF c f [] r with
       | .error e => .error e
       | .ok (xs, r2) => .ok (.list xs, r2))
  | f + 1, .name "External" :: .lparen :: r =>
      (match parseConst c r with
       | .error e => .error e
       | .ok ((fn, _), r2) =>
         (match r2 with
          | .lparen :: r3 =>
              (match parseTermsGoF c f [] r3 with
               | .error e => .error e
               | .ok (args, r4) =>
                 (match r4 with
                  | .rparen :: r5 => .ok (.external fn args, r5)
                  | _ => .error (fail r4 "expected ')' closing External(")))
          | _ => .error (fail r2 "expected '(' after the function of an External term")))
  | f + 1, ts =>
      (match parseConst c ts with
       | .error e => .error e
       | .ok ((lex, sp), r) =>
         (match r with
          | .lparen :: r2 =>
              (match parseTermsGoF c f [] r2 with
               | .error e => .error e
               | .ok (args, r3) => .ok (.fapp lex sp args, r3))
          | _ => .ok (.const lex sp, r)))

/-- The comma-separated argument list up to `)`, with a fuel bound. -/
def parseTermsGoF (c : Ctx) : Nat → List Tm → List Tok → PRes (List Tm)
  | 0, _, ts => .error (fail ts "argument list is too long")
  | _ + 1, acc, .rparen :: r => .ok (acc, r)
  | f + 1, acc, .comma :: r  => parseTermsGoF c f acc r
  | _ + 1, _, [] => .error (fail [] "expected ')' closing an argument list")
  | f + 1, acc, ts =>
      (match parseTermF c f ts with
       | .error e => .error e
       | .ok (t, r) => parseTermsGoF c f (acc ++ [t]) r)

end

/-- `Term`. -/
def parseTerm (c : Ctx) (ts : List Tok) : PRes Tm := parseTermF c (parseFuel ts) ts

/-- The argument list up to `)`. -/
def parseTermsUntilRParen (c : Ctx) (ts : List Tok) : PRes (List Tm) :=
  parseTermsGoF c (parseFuel ts) [] ts

/-- The `->` slot pairs of a frame, up to `]`, with a fuel bound. Each
    slot consumes a predicate term, an arrow and a value term, so one
    unit of fuel per token is above the bound. -/
def parseSlotsF (c : Ctx) (o : Tm) : Nat → List Atom → List Tok → PRes (List Atom)
  | 0, _, ts => .error (fail ts "frame has too many slots")
  | _ + 1, acc, .rbrack :: r => .ok (acc, r)
  | _ + 1, _, [] => .error (fail [] "expected ']' closing a frame")
  | f + 1, acc, ts =>
      match parseTerm c ts with
      | .error e => .error e
      | .ok (p, r) =>
        match r with
        | .arrow :: r2 =>
            (match parseTerm c r2 with
             | .error e => .error e
             | .ok (v, r3) => parseSlotsF c o f (acc ++ [.frame o p v]) r3)
        | _ => .error (fail r "expected '->' in a frame slot")

/-- The `->` slot pairs of a frame, up to `]`. -/
def parseSlots (c : Ctx) (o : Tm) (acc : List Atom) (ts : List Tok) : PRes (List Atom) :=
  parseSlotsF c o (parseFuel ts) acc ts

/-- `Atomic` — everything that can stand where a formula does. -/
def parseAtomic (c : Ctx) (ts : List Tok) : PRes (List Atom) :=
  match ts with
  | .name "External" :: .lparen :: r =>
      (match parseConst c r with
       | .error e => .error e
       | .ok ((fn, _), r2) =>
         (match r2 with
          | .lparen :: r3 =>
              (match parseTermsUntilRParen c r3 with
               | .error e => .error e
               | .ok (args, r4) =>
                 (match r4 with
                  | .rparen :: .eq :: r5 =>
                      -- `External( func:… ( … ) ) = term` is an
                      -- EQUALITY whose left side is a function call,
                      -- not a predicate. The corpus states most of
                      -- its function tests that way, and returning
                      -- the External alone left the `=` and the right
                      -- side unread.
                      (match parseTerm c r5 with
                       | .error e => .error e
                       | .ok (rhs, r6) => .ok ([Atom.equal (.external fn args) rhs], r6))
                  | .rparen :: r5 => .ok ([Atom.externalPred fn args], r5)
                  | _ => .error (fail r4 "expected ')' closing External(")))
          | _ => .error (fail r2 "expected '(' after the predicate of an External atom")))
  | _ =>
    match parseTerm c ts with
    | .error e => .error e
    | .ok (t, r) =>
      match r, t with
      | .lbrack :: r2, _ => parseSlots c t [] r2
      | .hashhash :: r2, _ =>
          (match parseTerm c r2 with
           | .error e => .error e
           | .ok (d, r3) => .ok ([.sub t d], r3))
      | .hash :: r2, _ =>
          (match parseTerm c r2 with
           | .error e => .error e
           | .ok (d, r3) => .ok ([.member t d], r3))
      | .eq :: r2, _ =>
          (match parseTerm c r2 with
           | .error e => .error e
           | .ok (d, r3) => .ok ([.equal t d], r3))
      -- A positional atom is a function application in atom position.
      | _, .fapp fn sp args => .ok ([.pos fn sp args], r)
      | _, _ => .error (fail r "a term is not a formula ([2] ATOMIC)")

mutual

/-- `FORMULA`, with a fuel bound. -/
def parseFormulaF (c : Ctx) : Nat → List Tok → PRes Formula
  | 0, ts => .error (fail ts "formula nesting is too deep")
  | fuel + 1, ts =>
  match ts with
  | .name "And" :: .lparen :: r =>
      (match parseFormulasGoF c fuel [] r with
       | .error e => .error e
       | .ok (fs, r2) => .ok (.and fs, r2))
  | .name "Or" :: .lparen :: r =>
      (match parseFormulasGoF c fuel [] r with
       | .error e => .error e
       | .ok (fs, r2) => .ok (.or fs, r2))
  | .name "Exists" :: r =>
      let vars := (r.takeWhile (fun t => match t with | .var _ => true | _ => false)).filterMap
        (fun t => match t with | .var v => some v | _ => none)
      let r2 := r.drop vars.length
      (match r2 with
       | .lparen :: r3 =>
           (match parseFormulaF c fuel r3 with
            | .error e => .error e
            | .ok (f, r4) =>
              (match r4 with
               | .rparen :: r5 => .ok (.exists vars f, r5)
               | _ => .error (fail r4 "expected ')' closing Exists(")))
       | _ => .error (fail r2 "expected '(' after the variables of Exists"))
  | _ =>
      (match parseAtomic c ts with
       | .error e => .error e
       | .ok ([a], r) => .ok (.atom a, r)
       | .ok (as', r) => .ok (.and (as'.map Formula.atom), r))

/-- The arguments of `And(…)` / `Or(…)`, with a fuel bound. -/
def parseFormulasGoF (c : Ctx) : Nat → List Formula → List Tok → PRes (List Formula)
  | 0, _, ts => .error (fail ts "connective has too many arguments")
  | _ + 1, acc, .rparen :: r => .ok (acc, r)
  | _ + 1, _, [] => .error (fail [] "expected ')' closing a connective")
  | fuel + 1, acc, ts =>
      (match parseFormulaF c fuel ts with
       | .error e => .error e
       | .ok (f, r) => parseFormulasGoF c fuel (acc ++ [f]) r)

end

/-- `FORMULA`. -/
def parseFormula (c : Ctx) (ts : List Tok) : PRes Formula :=
  parseFormulaF c (parseFuel ts) ts

/-- `Clause` — one or more head atoms (a frame with several slots is
    several atoms) and an optional body. -/
def parseClause (c : Ctx) (vars : List String) (ts : List Tok) : PRes (List Rule) :=
  match parseAtomic c ts with
  | .error e => .error e
  | .ok (heads, r) =>
    match r with
    | .implies :: r2 =>
        (match parseFormula c r2 with
         | .error e => .error e
         | .ok (b, r3) => .ok (heads.map (fun h => { vars := vars, head := h, body := some b }), r3))
    | _ => .ok (heads.map (fun h => ({ vars := vars, head := h } : Rule)), r)

/-- The items of a `Group(…)`, with a fuel bound. -/
def parseGroupItemsF (c : Ctx) : Nat → List Rule → List Tok → PRes (List Rule)
  | 0, _, ts => .error (fail ts "Group has too many items")
  | _ + 1, acc, .rparen :: r => .ok (acc, r)
  | _ + 1, _, [] => .error (fail [] "expected ')' closing Group(")
  | fuel + 1, acc, .name "Group" :: .lparen :: r =>
      (match parseGroupItemsF c fuel [] r with
       | .error e => .error e
       | .ok (rs, r2) => parseGroupItemsF c fuel (acc ++ rs) r2)
  | fuel + 1, acc, .name "Forall" :: r =>
      let vars := (r.takeWhile (fun t => match t with | .var _ => true | _ => false)).filterMap
        (fun t => match t with | .var v => some v | _ => none)
      let r2 := r.drop vars.length
      (match r2 with
       | .lparen :: r3 =>
           (match parseClause c vars r3 with
            | .error e => .error e
            | .ok (rs, r4) =>
              (match r4 with
               | .rparen :: r5 => parseGroupItemsF c fuel (acc ++ rs) r5
               | _ => .error (fail r4 "expected ')' closing Forall(")))
       | _ => .error (fail r2 "expected '(' after the variables of Forall"))
  | fuel + 1, acc, ts =>
      (match parseClause c [] ts with
       | .error e => .error e
       | .ok (rs, r) => parseGroupItemsF c fuel (acc ++ rs) r)

/-- The items of a `Group(…)`. -/
def parseGroupItems (c : Ctx) (acc : List Rule) (ts : List Tok) : PRes (List Rule) :=
  parseGroupItemsF c (parseFuel ts) acc ts

/-- The whole document. -/
def parseDocument (input : String) : Except PErr Document := do
  let toks ← tokenize input
  match toks with
  | .name "Document" :: .lparen :: rest0 =>
      let rec prologue (c : Ctx) (imports : List (String × Option String))
          (fuel : Nat) (ts : List Tok)
          : Except PErr (Ctx × List (String × Option String) × List Tok) :=
        match fuel, ts with
        | 0, _ => .error (fail ts "prologue too long")
        | f + 1, .name "Base" :: .lparen :: .iri b :: .rparen :: r =>
            prologue { c with base := some b } imports f r
        | f + 1, .name "Prefix" :: .lparen :: .name p :: .iri u :: .rparen :: r =>
            prologue { c with prefixes := c.prefixes ++ [(p, u)] } imports f r
        | f + 1, .name "Import" :: .lparen :: .iri u :: .rparen :: r =>
            prologue c (imports ++ [(u, none)]) f r
        | f + 1, .name "Import" :: .lparen :: .iri u :: .iri p :: .rparen :: r =>
            prologue c (imports ++ [(u, some p)]) f r
        | _, r => .ok (c, imports, r)
      match prologue {} [] (toks.length + 1) rest0 with
      | .error e => .error e
      | .ok (c, imports, r) =>
        match r with
        | .name "Group" :: .lparen :: r2 =>
            (match parseGroupItems c [] r2 with
             | .error e => .error e
             | .ok (rules, r3) =>
               (match r3 with
                | [.rparen] | [] =>
                    .ok { base := c.base, prefixes := c.prefixes,
                          imports := imports, rules := rules }
                | _ => .error (fail r3 "unexpected tokens after Group(…)")))
        | [.rparen] | [] =>
            .ok { base := c.base, prefixes := c.prefixes, imports := imports }
        | _ => .error (fail r "expected Group( or ')' in a Document")
  | ts => .error (fail ts "a RIF document must begin with Document(")

/-- A CONCLUSION file: a bare formula, read in the PREMISE document's
    prefix context. The corpus writes conclusions with no prologue —
    `ex:myOnto[ex:hasTitle -> "Example ontology"]` — and `ex:` is
    declared in the premise beside it. -/
def parseFormulaText (c : Ctx) (input : String) : Except PErr Formula := do
  let toks ← tokenize input
  match parseFormula c toks with
  | .error e => .error e
  | .ok (f, rest) =>
      if rest.isEmpty then .ok f
      else .error (fail rest "unexpected tokens after a formula")

/-- The prefix context a parsed document carries. -/
def Document.ctx (d : Document) : Ctx := { base := d.base, prefixes := d.prefixes }

end L4Factoidal.RIF
