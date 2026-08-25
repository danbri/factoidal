/-
L4Factoidal.CL.Clif — a CLIF reader and serialiser.

CLIF (Common Logic Interchange Format) per ISO/IEC 24707 Annex A,
restricted to the single-sentence fragment of `CL.Syntax`, plus IKL's
`(that <sentence>)` term (IKL guide, "IKL Overview",
https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html).

Pipeline: character list → tokens (`lex`) → S-expressions
(`parseSExpr`) → abstract syntax (`readSentence` / `readTerm`), each
stage total, `Except ParseError` with a message and 0-based codepoint
offset following `L4Factoidal.Syntax.Lexing`'s convention. Recursion
that is not structural on a direct suffix carries explicit fuel — the
style chosen for mechanical F* transcription (tracking:
https://github.com/danbri/factoidal/issues/580).

## What IS covered

* Lexing: parentheses; bare names (maximal runs of name characters);
  enclosed names `"..."` with `\"` and `\\` escapes; quoted strings
  `'...'` with `\'` and `\\` escapes (ISO/IEC 24707 A.2.2 lexical
  syntax); sequence markers `...name` (three dots then name
  characters, A.2.2); whitespace (space, tab, CR, LF).
* Reading: the `CL.Syntax` sentence forms — predication, equations,
  `and`/`or`/`not`/`if`/`iff`, `forall`/`exists` with plain,
  sequence-marker, and restricted `(name term)` bindings — and IKL
  `(that S)` terms, including the assertion form `((that S))` which
  reads as predication of the `that`-term on the empty sequence.
* Serialisation back to CLIF text, one space between items, names
  re-enclosed exactly when their spelling requires it; round-trip
  `#guard`s at the end of this file (more in `CL.Examples`).

## What is NOT covered (named per issue 580)

* `/* ... */` lexical comments, and the `cl:comment` phrase form —
  the reader rejects `cl:` phrase keywords with an explicit error.
* `cl:text` / `cl:module` / `cl:imports` phrase structure.
* IKL numeric quantifiers: `(exists 3 (...))` fails because a
  boundlist must be parenthesised; the error message says so.
* Unicode escapes inside strings, and any name-character set beyond
  "printable, not a delimiter" — ISO/IEC 24707 A.2.2's exact
  character classes are wider (they admit arbitrary Unicode); this
  reader accepts any non-delimiter character in a bare name, which is
  a SUPERSET of the standard's bare-name spellings on the ASCII
  range it is used with here.
-/

import L4Factoidal.Syntax.Lexing
import L4Factoidal.CL.Syntax

namespace L4Factoidal.CL

open L4Factoidal.Syntax (ParseError)

/-! ## Tokens -/

/-- A CLIF token, each carrying the 0-based codepoint offset of its
first character. `name` is a bare name, `enclosed` a `"..."` enclosed
name (already unescaped), `str` a `'...'` quoted string (already
unescaped), `seqmark` a sequence marker WITHOUT its leading `...`. -/
inductive Tok where
  | lparen (pos : Nat)
  | rparen (pos : Nat)
  | name (s : String) (pos : Nat)
  | enclosed (s : String) (pos : Nat)
  | str (s : String) (pos : Nat)
  | seqmark (s : String) (pos : Nat)
  deriving Repr, DecidableEq

/-- The offset a token starts at. -/
def Tok.pos : Tok → Nat
  | .lparen p | .rparen p | .name _ p | .enclosed _ p
  | .str _ p | .seqmark _ p => p

/-! ## Lexer -/

/-- CLIF whitespace: space, tab, CR, LF (ISO/IEC 24707 A.2.2 `white`). -/
def isClifWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- A character that may appear in a bare name: anything that is not
whitespace and not one of the five delimiters `( ) ' " \`. See the
module header: on the ASCII range this is a superset of
ISO/IEC 24707 A.2.2's name character classes. -/
def isNameChar (c : Char) : Bool :=
  !(isClifWs c) && c ≠ '(' && c ≠ ')' && c ≠ '\'' && c ≠ '"' && c ≠ '\\'

/-- Read a `'...'`-or-`"..."` body up to the unescaped closing `quote`,
unescaping `\<quote>` and `\\` (ISO/IEC 24707 A.2.2: quoted strings
and enclosed names each admit exactly the backslash escapes of their
own quote and of backslash). Structural on the character list: every
branch recurses on a strict suffix. Returns (content, offset after the
closing quote, rest). -/
def readQuotedBody (quote : Char) (pos : Nat) :
    List Char → List Char → Except ParseError (String × Nat × List Char)
  | _, [] => .error ⟨s!"unterminated {quote}-quoted text", pos⟩
  | acc, '\\' :: c :: rest =>
      if c = quote || c = '\\' then
        readQuotedBody quote (pos + 2) (c :: acc) rest
      else
        .error ⟨s!"invalid escape '\\{c}' in {quote}-quoted text", pos⟩
  | _, '\\' :: [] => .error ⟨"dangling backslash in quoted text", pos⟩
  | acc, c :: rest =>
      if c = quote then .ok (String.ofList acc.reverse, pos + 1, rest)
      else readQuotedBody quote (pos + 1) (c :: acc) rest

/-- Read a maximal run of name characters. Structural on the list. -/
def readNameRun (pos : Nat) :
    List Char → List Char → (String × Nat × List Char)
  | acc, [] => (String.ofList acc.reverse, pos, [])
  | acc, c :: rest =>
      if isNameChar c then readNameRun (pos + 1) (c :: acc) rest
      else (String.ofList acc.reverse, pos, c :: rest)

/-- Turn a bare-name run into its token: a run starting with `...` is
a sequence marker (ISO/IEC 24707 A.2.2 `seqmark`), anything else a
name. -/
def nameRunToken (s : String) (pos : Nat) : Tok :=
  if s.startsWith "..." then .seqmark (String.ofList (s.toList.drop 3)) pos
  else .name s pos

/-- Tokenise a CLIF document. `fuel` bounds the number of tokens; every
recursive call consumes at least one character, so
`fuel := cs.length + 1` never runs out before the input does (same
argument as `Syntax.NTriples.parseLinesAcc`). -/
def lexAcc : Nat → Nat → List Char → List Tok → Except ParseError (List Tok)
  | 0, pos, _, _ =>
      .error ⟨"internal error: lexer fuel exhausted (should be unreachable)", pos⟩
  | _, _, [], acc => .ok acc.reverse
  | fuel' + 1, pos, c :: rest, acc =>
      if isClifWs c then lexAcc fuel' (pos + 1) rest acc
      else if c = '(' then lexAcc fuel' (pos + 1) rest (.lparen pos :: acc)
      else if c = ')' then lexAcc fuel' (pos + 1) rest (.rparen pos :: acc)
      else if c = '\'' then
        match readQuotedBody '\'' (pos + 1) [] rest with
        | .error e => .error e
        | .ok (s, pos', rest') => lexAcc fuel' pos' rest' (.str s pos :: acc)
      else if c = '"' then
        match readQuotedBody '"' (pos + 1) [] rest with
        | .error e => .error e
        | .ok (s, pos', rest') => lexAcc fuel' pos' rest' (.enclosed s pos :: acc)
      else if c = '\\' then
        .error ⟨"'\\' cannot start a token", pos⟩
      else
        match readNameRun (pos + 1) [c] rest with
        | (s, pos', rest') => lexAcc fuel' pos' rest' (nameRunToken s pos :: acc)

/-- Tokenise a whole string. -/
def lex (input : String) : Except ParseError (List Tok) :=
  let cs := input.toList
  lexAcc (cs.length + 1) 0 cs []

/-! ## S-expressions -/

/-- An atomic S-expression: the four non-parenthesis token kinds. -/
inductive SAtom where
  | name (s : String)
  | enclosed (s : String)
  | str (s : String)
  | seqmark (s : String)
  deriving Repr, DecidableEq

/-- An S-expression with the source offset of its first token. -/
inductive SExpr where
  | atom (a : SAtom) (pos : Nat)
  | list (es : List SExpr) (pos : Nat)
  deriving Repr

/-- The offset an S-expression starts at. -/
def SExpr.pos : SExpr → Nat
  | .atom _ p => p
  | .list _ p => p

mutual

/-- Parse one S-expression from a token stream. `fuel` decreases on
every call across the mutual pair; each `parseSExpr` call consumes at
least one token and each `parseSExprList` step consumes at least one
token per two fuel units, so `2 * toks.length + 2` suffices at the
top level. -/
def parseSExpr : Nat → List Tok → Except ParseError (SExpr × List Tok)
  | 0, ts =>
      .error ⟨"internal error: S-expression fuel exhausted (should be unreachable)",
              (ts.head?.map Tok.pos).getD 0⟩
  | _ + 1, [] => .error ⟨"unexpected end of input", 0⟩
  | fuel' + 1, t :: rest =>
      match t with
      | .lparen p => parseSExprList fuel' p [] rest
      | .rparen p => .error ⟨"unexpected ')'", p⟩
      | .name s p => .ok (.atom (.name s) p, rest)
      | .enclosed s p => .ok (.atom (.enclosed s) p, rest)
      | .str s p => .ok (.atom (.str s) p, rest)
      | .seqmark s p => .ok (.atom (.seqmark s) p, rest)

/-- Parse list elements up to the closing `)`. `openPos` is the offset
of the opening `(`, for the unclosed-parenthesis error. -/
def parseSExprList : Nat → Nat → List SExpr → List Tok →
    Except ParseError (SExpr × List Tok)
  | 0, openPos, _, _ =>
      .error ⟨"internal error: S-expression fuel exhausted (should be unreachable)", openPos⟩
  | _ + 1, openPos, _, [] => .error ⟨"unclosed '('", openPos⟩
  | _ + 1, openPos, acc, .rparen _ :: rest => .ok (.list acc.reverse openPos, rest)
  | fuel' + 1, openPos, acc, ts =>
      match parseSExpr fuel' ts with
      | .error e => .error e
      | .ok (e, rest) => parseSExprList fuel' openPos (e :: acc) rest

end

/-! ## Reading S-expressions into the abstract syntax

Dispatch on the head of each list: a reserved bare name selects the
sentence form (ISO/IEC 24707 A.2.2.2); any other head is a
predication. `fuel` decreases on every call across the group; the
recursion depth is bounded by the S-expression's node count, which the
token count bounds, so the entry points pass `2 * toks.length + 2`. -/

mutual

/-- Read a sentence (CLIF `sentence`, ISO/IEC 24707 A.2.2.2). -/
def readSentence : Nat → SExpr → Except ParseError Sentence
  | 0, e => .error ⟨"internal error: reader fuel exhausted (should be unreachable)", e.pos⟩
  | _ + 1, .atom _ pos =>
      .error ⟨"a CLIF sentence must be parenthesised", pos⟩
  | _ + 1, .list [] pos => .error ⟨"empty sentence '()'", pos⟩
  | fuel' + 1, .list (head :: args) pos =>
      match head with
      | .atom (.name "and") _ =>
          match readSentences fuel' args with
          | .error e => .error e
          | .ok ss => .ok (.conj ss)
      | .atom (.name "or") _ =>
          match readSentences fuel' args with
          | .error e => .error e
          | .ok ss => .ok (.disj ss)
      | .atom (.name "not") _ =>
          match args with
          | [s] =>
              (match readSentence fuel' s with
               | .error e => .error e
               | .ok s' => .ok (.neg s'))
          | _ => .error ⟨"'not' takes exactly one sentence", pos⟩
      | .atom (.name "if") _ =>
          match args with
          | [a, b] =>
              (match readSentence fuel' a with
               | .error e => .error e
               | .ok a' =>
                   match readSentence fuel' b with
                   | .error e => .error e
                   | .ok b' => .ok (.impl a' b'))
          | _ => .error ⟨"'if' takes exactly two sentences", pos⟩
      | .atom (.name "iff") _ =>
          match args with
          | [a, b] =>
              (match readSentence fuel' a with
               | .error e => .error e
               | .ok a' =>
                   match readSentence fuel' b with
                   | .error e => .error e
                   | .ok b' => .ok (.iff a' b'))
          | _ => .error ⟨"'iff' takes exactly two sentences", pos⟩
      | .atom (.name "=") _ =>
          match args with
          | [a, b] =>
              (match readTerm fuel' a with
               | .error e => .error e
               | .ok a' =>
                   match readTerm fuel' b with
                   | .error e => .error e
                   | .ok b' => .ok (.eq a' b'))
          | _ => .error ⟨"'=' takes exactly two terms", pos⟩
      | .atom (.name "forall") _ =>
          match readQuantBody fuel' pos args with
          | .error e => .error e
          | .ok (bs, body) => .ok (.all bs body)
      | .atom (.name "exists") _ =>
          match readQuantBody fuel' pos args with
          | .error e => .error e
          | .ok (bs, body) => .ok (.ex bs body)
      | .atom (.name "that") _ =>
          .error ⟨"'(that S)' is a term; to assert the proposition write '((that S))'", pos⟩
      | .atom (.name n) p =>
          if n = "cl:text" || n = "cl:module" || n = "cl:imports" || n = "cl:comment" then
            .error ⟨s!"'{n}' phrases are not covered by this reader (issue 580)", p⟩
          else
            -- Predication with a bare-name predicate term.
            (match readSeqItems fuel' args with
             | .error e => .error e
             | .ok items => .ok (.atom (.name n) items))
      | _ =>
          -- Predication with a general operator term, e.g. ((that S)).
          match readTerm fuel' head with
          | .error e => .error e
          | .ok p =>
              match readSeqItems fuel' args with
              | .error e => .error e
              | .ok items => .ok (.atom p items)

/-- Read the `boundlist sentence` tail of a quantified sentence
(CLIF `quantsent`, ISO/IEC 24707 A.2.2.2.5). -/
def readQuantBody : Nat → Nat → List SExpr →
    Except ParseError (List Binding × Sentence)
  | 0, pos, _ =>
      .error ⟨"internal error: reader fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, args =>
      match args with
      | [.list bs _, body] =>
          (match readBindings fuel' bs with
           | .error e => .error e
           | .ok bs' =>
               match readSentence fuel' body with
               | .error e => .error e
               | .ok body' => .ok (bs', body'))
      | [.atom _ p, _] =>
          .error ⟨"a quantifier's boundlist must be parenthesised (IKL numeric quantifiers are not covered — issue 580)", p⟩
      | _ => .error ⟨"a quantified sentence is 'quantifier (boundlist) sentence'", pos⟩

/-- Read a boundlist (plain names, sequence markers, restricted
`(name term)` pairs). -/
def readBindings : Nat → List SExpr → Except ParseError (List Binding)
  | 0, es =>
      .error ⟨"internal error: reader fuel exhausted (should be unreachable)",
              (es.head?.map SExpr.pos).getD 0⟩
  | _ + 1, [] => .ok []
  | fuel' + 1, e :: rest =>
      match e with
      | .atom (.name n) p =>
          if isReservedWord n then
            .error ⟨s!"reserved word '{n}' cannot be bound", p⟩
          else
            (match readBindings fuel' rest with
             | .error e' => .error e'
             | .ok bs => .ok (.plain n :: bs))
      | .atom (.enclosed n) _ =>
          (match readBindings fuel' rest with
           | .error e' => .error e'
           | .ok bs => .ok (.plain n :: bs))
      | .atom (.seqmark m) _ =>
          (match readBindings fuel' rest with
           | .error e' => .error e'
           | .ok bs => .ok (.seqmark m :: bs))
      | .atom (.str _) p =>
          .error ⟨"a quoted string cannot be bound", p⟩
      | .list [nameE, guardE] p =>
          (match nameE with
           | .atom (.name n) _ =>
               if isReservedWord n then
                 .error ⟨s!"reserved word '{n}' cannot be bound", p⟩
               else
                 (match readTerm fuel' guardE with
                  | .error e' => .error e'
                  | .ok g =>
                      match readBindings fuel' rest with
                      | .error e' => .error e'
                      | .ok bs => .ok (.restricted n g :: bs))
           | .atom (.enclosed n) _ =>
               (match readTerm fuel' guardE with
                | .error e' => .error e'
                | .ok g =>
                    match readBindings fuel' rest with
                    | .error e' => .error e'
                    | .ok bs => .ok (.restricted n g :: bs))
           | _ => .error ⟨"a restricted binding is '(name term)'", p⟩)
      | .list _ p => .error ⟨"a restricted binding is '(name term)'", p⟩

/-- Read each element of a sentence list. -/
def readSentences : Nat → List SExpr → Except ParseError (List Sentence)
  | 0, es =>
      .error ⟨"internal error: reader fuel exhausted (should be unreachable)",
              (es.head?.map SExpr.pos).getD 0⟩
  | _ + 1, [] => .ok []
  | fuel' + 1, e :: rest =>
      match readSentence fuel' e with
      | .error e' => .error e'
      | .ok s =>
          match readSentences fuel' rest with
          | .error e' => .error e'
          | .ok ss => .ok (s :: ss)

/-- Read a term (CLIF `term`, ISO/IEC 24707 A.2.2.2.1, plus IKL
`(that S)`). -/
def readTerm : Nat → SExpr → Except ParseError Term
  | 0, e => .error ⟨"internal error: reader fuel exhausted (should be unreachable)", e.pos⟩
  | _ + 1, .atom (.name n) pos =>
      if isReservedWord n then
        .error ⟨s!"reserved word '{n}' cannot be used as a name", pos⟩
      else .ok (.name n)
  | _ + 1, .atom (.enclosed n) _ => .ok (.name n)
  | _ + 1, .atom (.str s) _ => .ok (.str s)
  | _ + 1, .atom (.seqmark _) pos =>
      .error ⟨"a sequence marker can appear only inside an argument sequence or boundlist", pos⟩
  | _ + 1, .list [] pos => .error ⟨"empty term '()'", pos⟩
  | fuel' + 1, .list (head :: args) pos =>
      match head with
      | .atom (.name "that") _ =>
          match args with
          | [s] =>
              (match readSentence fuel' s with
               | .error e => .error e
               | .ok s' => .ok (.that s'))
          | _ => .error ⟨"'that' takes exactly one sentence", pos⟩
      | .atom (.name n) p =>
          if isReservedWord n then
            .error ⟨s!"reserved word '{n}' cannot head a functional term", p⟩
          else
            (match readSeqItems fuel' args with
             | .error e => .error e
             | .ok items => .ok (.funapp (.name n) items))
      | _ =>
          match readTerm fuel' head with
          | .error e => .error e
          | .ok op =>
              match readSeqItems fuel' args with
              | .error e => .error e
              | .ok items => .ok (.funapp op items)

/-- Read an argument sequence: terms interleaved with sequence markers
(ISO/IEC 24707 6.1.2). -/
def readSeqItems : Nat → List SExpr → Except ParseError (List SeqItem)
  | 0, es =>
      .error ⟨"internal error: reader fuel exhausted (should be unreachable)",
              (es.head?.map SExpr.pos).getD 0⟩
  | _ + 1, [] => .ok []
  | fuel' + 1, e :: rest =>
      match e with
      | .atom (.seqmark m) _ =>
          (match readSeqItems fuel' rest with
           | .error e' => .error e'
           | .ok items => .ok (.seqmark m :: items))
      | _ =>
          match readTerm fuel' e with
          | .error e' => .error e'
          | .ok t =>
              match readSeqItems fuel' rest with
              | .error e' => .error e'
              | .ok items => .ok (.term t :: items)

end

/-! ## Entry points -/

/-- Parse one CLIF sentence from a string: lex, build the
S-expression, read it, and reject trailing tokens. -/
def parseClifSentence (input : String) : Except ParseError Sentence :=
  match lex input with
  | .error e => .error e
  | .ok toks =>
      match parseSExpr (2 * toks.length + 2) toks with
      | .error e => .error e
      | .ok (e, []) => readSentence (2 * toks.length + 2) e
      | .ok (_, t :: _) => .error ⟨"trailing input after sentence", t.pos⟩

/-- Parse one CLIF term from a string (exposed for tests and for the
F* twin's differential tables). -/
def parseClifTerm (input : String) : Except ParseError Term :=
  match lex input with
  | .error e => .error e
  | .ok toks =>
      match parseSExpr (2 * toks.length + 2) toks with
      | .error e => .error e
      | .ok (e, []) => readTerm (2 * toks.length + 2) e
      | .ok (_, t :: _) => .error ⟨"trailing input after term", t.pos⟩

/-! ## Serialisation

One canonical rendering: a single space between items, `(and ...)`
n-ary forms flattened as written, names re-enclosed exactly when the
bare spelling would not re-lex to the same name. -/

/-- Escape for `"..."` enclosed names: `\` and `"`. -/
def escapeEnclosed (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = '\\' || c = '"' then ['\\', c] else [c])

/-- Escape for `'...'` quoted strings: `\` and `'`. -/
def escapeQuoted (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = '\\' || c = '\'' then ['\\', c] else [c])

/-- Render a name: bare when the spelling re-lexes to the same bare
name token (nonempty, all name characters, not a `...` prefix, not a
reserved word), otherwise `"..."`-enclosed. -/
def renderName (n : String) : String :=
  if n.length > 0 && n.toList.all isNameChar
      && !(n.startsWith "...") && !(isReservedWord n) then n
  else "\"" ++ escapeEnclosed n ++ "\""

mutual

/-- Serialise a term to CLIF text. -/
def Term.toClif : Term → String
  | .name n => renderName n
  | .str s => "'" ++ escapeQuoted s ++ "'"
  | .funapp op args => "(" ++ op.toClif ++ seqItemsToClif args ++ ")"
  | .that s => "(that " ++ s.toClif ++ ")"

/-- Serialise an argument sequence; each item is preceded by one
space, so it appends directly after a head term. -/
def seqItemsToClif : List SeqItem → String
  | [] => ""
  | .term t :: r => " " ++ t.toClif ++ seqItemsToClif r
  | .seqmark m :: r => " ..." ++ m ++ seqItemsToClif r

/-- Serialise a boundlist's entries; space-separated, no leading
space. -/
def bindingsToClif : List Binding → String
  | [] => ""
  | [b] => bindingToClif b
  | b :: r => bindingToClif b ++ " " ++ bindingsToClif r

/-- Serialise one binding. -/
def bindingToClif : Binding → String
  | .plain n => renderName n
  | .seqmark m => "..." ++ m
  | .restricted n g => "(" ++ renderName n ++ " " ++ g.toClif ++ ")"

/-- Serialise the elements of an `and`/`or`; each preceded by one
space. -/
def sentencesToClif : List Sentence → String
  | [] => ""
  | s :: r => " " ++ s.toClif ++ sentencesToClif r

/-- Serialise a sentence to CLIF text. -/
def Sentence.toClif : Sentence → String
  | .atom p args => "(" ++ p.toClif ++ seqItemsToClif args ++ ")"
  | .eq a b => "(= " ++ a.toClif ++ " " ++ b.toClif ++ ")"
  | .conj ss => "(and" ++ sentencesToClif ss ++ ")"
  | .disj ss => "(or" ++ sentencesToClif ss ++ ")"
  | .neg s => "(not " ++ s.toClif ++ ")"
  | .impl a b => "(if " ++ a.toClif ++ " " ++ b.toClif ++ ")"
  | .iff a b => "(iff " ++ a.toClif ++ " " ++ b.toClif ++ ")"
  | .all bs body => "(forall (" ++ bindingsToClif bs ++ ") " ++ body.toClif ++ ")"
  | .ex bs body => "(exists (" ++ bindingsToClif bs ++ ") " ++ body.toClif ++ ")"

end

/-! ## Round-trip checks

`canon` parses and re-serialises; `stable` additionally checks the
canonical text is a fixed point of parse-then-serialise, which is the
round-trip property statable without a decidable equality on the
mutual syntax family. -/

/-- Parse a sentence and serialise it back, or `none` on a parse
error. -/
def canon (input : String) : Option String :=
  match parseClifSentence input with
  | .ok s => some s.toClif
  | .error _ => none

/-- The input parses, and its canonical form re-parses to the same
canonical form. -/
def stable (input : String) : Bool :=
  match canon input with
  | some c => canon c == some c
  | none => false

/-- Whether a string parses as a sentence at all. -/
def parses (input : String) : Bool :=
  match parseClifSentence input with
  | .ok _ => true
  | .error _ => false

/-- `some true` / `some false`: whether the parsed sentence is pure
ISO/IEC 24707 CL (no IKL `that`); `none` on a parse error. -/
def pureOf (input : String) : Option Bool :=
  match parseClifSentence input with
  | .ok s => some s.isPureCL
  | .error _ => none

-- Canonical spelling: whitespace collapses, names stay bare.
#guard canon "( and (P a)  (Q b) )" == some "(and (P a) (Q b))"
-- Fixed-point round trips.
#guard stable "(P a b)"
#guard stable "(= (fatherOf Bill) John)"
#guard stable "(forall (x) (if (Boy x) (Human x)))"
#guard stable "(exists ((x isHuman) ...rest) (P x ...rest))"
#guard stable "((that (isHuman \"Brant Cheikes\")))"
-- Enclosed names and quoted strings survive with their escapes.
#guard canon "(customer x \"Bank Melli Iran\")"
  == some "(customer x \"Bank Melli Iran\")"
-- An unescaped quote ENDS the string: two string tokens result.
#guard canon "(P 'it''s wrong')" == some "(P 'it' 's wrong')"
#guard canon "(P 'it\\'s right')" == some "(P 'it\\'s right')"
-- A reserved word as a bare name is rejected; enclosed it is a name.
#guard parses "(P and)" == false
#guard parses "(P \"and\")" == true
-- Sequence markers only where the grammar admits them.
#guard parses "(P ...xs)" == true
#guard parses "(= ...xs a)" == false
-- Numeric quantifiers are IKL forms this reader does not cover.
#guard parses "(exists 3 ((y aircraft)) (owns x y))" == false
-- (that S) is a term, not a sentence.
#guard parses "(that (P a))" == false
#guard parses "((that (P a)))" == true

end L4Factoidal.CL
