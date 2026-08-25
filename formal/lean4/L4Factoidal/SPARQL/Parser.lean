/-
L4Factoidal.SPARQL.Parser — the SPARQL 1.1 / 1.2 query grammar.

Port of `formal/fstar/SPARQL11.Parser.fst` Parts 4-7 (the parse-result
type, the combinators, the recursive-descent grammar, the top-level
entry points) and Part 8 (the SSE algebra printer). The terminal layer
is `SPARQL/Tokenizer.lean`.

Grammar: "SPARQL 1.1 Query Language" §19.8. Every parsing function
cites the production numbers it covers.

WHAT IS PORTED
  * [4] Prologue — BASE / PREFIX, with RFC 3986 resolution of a
    relative PREFIX namespace and of every relative IRIREF in the
    token stream (`resolveRelativeIriTokens`), plus the SPARQL 1.2
    [4a] VERSION declaration.
  * [7] SelectClause / [8] SubSelect — DISTINCT, REDUCED, `*`,
    `(expr AS ?v)`.
  * [10] ConstructQuery, both forms (incl. the `CONSTRUCT WHERE`
    short form and its basic-graph-pattern restriction).
  * [11] DescribeQuery, [12] AskQuery.
  * [13]-[16] DatasetClause — FROM / FROM NAMED.
  * [17]-[19] WhereClause / SolutionModifier / GroupClause,
    [21] HavingClause, [23] OrderClause, [25]-[27] LIMIT / OFFSET
    (either order, per [25] LimitOffsetClauses).
  * [28] ValuesClause and [61]-[65] InlineData — both the
    `VALUES ?x { … }` and `VALUES (?x ?y) { ( … ) }` forms, UNDEF,
    the trailing VALUES after the WHERE clause.
  * [53]-[57] GroupGraphPattern / GraphPatternNotTriples — OPTIONAL,
    MINUS, LATERAL, UNION, GRAPH, SERVICE (IRI and variable
    endpoints, SILENT), BIND, VALUES, sub-SELECT, nested groups.
  * [68] Constraint / [58] Filter.
  * [75]-[87] TriplesBlock, PropertyListPathNotEmpty, ObjectList,
    Verb, collections `( … )`, blank-node property lists `[ … ]`,
    `a`, and the numeric / string / boolean literal sugar.
  * [88]-[101] Path — the full §18.4 syntax: `|`, `/`, `^`, `*`,
    `+`, `?`, `!`, negated property sets, parenthesised paths.
  * [110]-[138] Expression — the §18.2.2.1 precedence ladder
    (`||` < `&&` < relational/IN/NOT IN < `+ -` < `* /` < unary),
    every §17 builtin the `Expr` AST carries, aggregates with
    DISTINCT and GROUP_CONCAT's SEPARATOR, EXISTS / NOT EXISTS,
    IN / NOT IN, function calls on unknown IRIs.
  * The SSE printer (`Query.toSse`), port of `sse_ggp` and siblings.

WELL-FORMEDNESS REJECTIONS — every check the F* performs, with the F*
function or inline test each mirrors:

  | message | F* site |
  |---|---|
  | `duplicate variable in SELECT` | `parse_select_items`, via `select_items_has_var` |
  | `SELECT * not allowed with GROUP BY` | `parse_select_body` |
  | `SELECT projects ungrouped variable` | `parse_select_body`, via `expr_has_ungrouped_var` (both the explicit-GROUP BY and the implicit-grouping arms) |
  | `SELECT expression aliases variable already in scope` | `parse_select_body`, via `ggp_has_var` |
  | `LATERAL: right-hand side reassigns a variable already bound by the left-hand pattern` | `parse_ggp_body`, via `lateral_assignable_vars` + `ggp_has_var` |
  | `BIND variable already in scope` | `parse_ggp_body`, via `ggp_has_var` |
  | `nested aggregate in aggregate argument` | `parse_aggregate`, via `expr_has_aggregate` |
  | `nested aggregate in GROUP_CONCAT argument` | `parse_group_concat` |
  | `duplicate variable in VALUES clause` | `parse_values_clause`, via `var_list_has_dup` |
  | `VALUES row has wrong number of terms` | `parse_values_clause` |
  | `blank node label reused across nested group scope` | `parse_ggp_body`, via `ggp_labeled_bnodes` + `local_string_overlaps` |
  | `blank node label reused across graph-pattern scope` | `validate_bnode_scope_top` / `validate_bnode_scope_pattern` |
  | `CONSTRUCT WHERE short form only allows basic graph patterns` | `parse_construct_body`, via `is_basic_pattern` |
  | `DESCRIBE expects at least one IRI/var or '*'` | `parse_describe_body` |
  | `invalid PREFIX name (must be prefix: with no local part)` | `parse_prologue` |
  | `unexpected tokens after query` | `parse_sparql_with_base`, via `tokens_only_eof` |
  | `VERSION requires a plain string literal, …` | the tokenizer (`scan_pname_or_keyword`) |
  | `invalid string escape (surrogate or malformed)` | the tokenizer, surfaced by `first_invalid_token_msg` |

  Message TEXT is the F*'s verbatim — the repo's tests grep for some
  of it (notably "reassigns a variable already bound by the left-hand
  pattern"). `ParseError.pos` adds the character offset of the
  offending token, which the F* does not carry.

TERMINATION. The whole grammar is ONE mutual block recursive on a
`fuel : Nat`, structurally, exactly as the F* is (`decreases fuel`),
with the F*'s own top-level seed of 10000. No `partial`, no
well-founded recursion, no `termination_by`.

EXISTS. `Expr.existsPat` / `Expr.notExistsPat` carry the operand AS
PARSED, a `QueryPattern` (the F* `E_Exists : group_graph_pattern ->
expr`; `Expr` and `QueryPattern` are one mutual inductive in
`Expr.lean` — design record in `SPARQL/Exists.lean`). So `Query.toSse`
prints inside an EXISTS with full fidelity, byte-identical to the F*
`sse_ggp`. One F* check is placed differently: `validate_bnode_scope_expr`
walks into `E_Exists` after parsing; this port runs the same check on
the EXISTS operand AT CONSTRUCTION TIME, in the parser's EXISTS arm.
That is equivalent, not weaker: the F* function returns `(ok, [])` for
an EXISTS, so an EXISTS operand's blank-node labels never escape to the
enclosing scope — only its own internal validity matters.

NOT PORTED (each with its reason)
  * SPARQL 1.1 Update ([29]-[52]). The tokenizer emits the update
    keywords, but `parse_single_update_op` and friends are a separate
    rung; `parseSparql` is a QUERY parser, as its name says.
  * The jena-text `text:query` object grammar
    (`parse_fulltext_query_object`). A vendor extension outside
    §19.8, whose encoding lives in `SPARQL.FullText.fst` — no Lean
    counterpart exists to encode into.

PORTED IN A LATER WAVE (issue #556): SPARQL 1.2 bare reified triples
`<< s p o (~ reifier)? >>` in subject and object position, and the
`~` / `{| predicateObjectList |}` annotation sequence after a
simple-predicate object (`parse_reified_triple_pattern` /
`parse_reifier_id` / `parse_annotations` → `pReifiedTriplePattern` /
`pReifierId` / `pAnnotations`). Triple-term patterns `<<( s p o )>>`
and the `TRIPLE`/`SUBJECT`/`PREDICATE`/`OBJECT`/`isTRIPLE` builtins
were already ported. All of it is v12-only: the tokenizer emits the
`<<` / `>>` / `~` / `{|` / `|}` tokens only under the v12 flag.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Tokenizer
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## The parse-result type and combinators — F* Part 5 -/

/-- A token stream: the F* `token_stream`, with positions. -/
abbrev TStream := List PosToken

/-! The F* `parse_result a` is `Except ParseError (a × TStream)`: a
value plus the unconsumed stream, or a message. `Except` gives the
`do`-notation the F* writes out by hand as nested `match parse_bind`
chains. The type is written out at every signature rather than hidden
behind an abbreviation, because Lean's `do` elaborator would otherwise
read the abbreviation itself as the monad. -/

/-- The parser's context: the prologue's prefix map and BASE, and the
version mode. Port of the F* `prefix_map` argument plus the `sparql12`
flag. -/
structure PState where
  prefixes : List (String × String) := []
  base     : Option String := none
  v12      : Bool := false

/-- `parse_peek`: the current token, `eof` past the end. -/
def peekTok : TStream → Token
  | []      => .eof
  | pt :: _ => pt.tok

/-- The character offset of the current token, for error reporting. -/
def peekPos : TStream → Nat
  | []      => 0
  | pt :: _ => pt.pos

/-- `parse_advance`. -/
def advTok : TStream → TStream
  | []       => []
  | _ :: rest => rest

/-- Fail at the current position. -/
def pErr (msg : String) (ts : TStream) : Except ParseError α :=
  .error ⟨msg, peekPos ts⟩

/-- `parse_expect`: consume exactly this token. -/
def expectTok (t : Token) (ts : TStream) : Except ParseError (Unit × TStream) :=
  if peekTok ts == t then .ok ((), advTok ts)
  else pErr s!"expected {repr t}" ts

/-! ## Vocabulary and term construction — F* Part 6 helpers -/

/-- `make_iri`: §19.8 [139] IRIREF content is well-formed when it is
non-empty and carries a scheme separator (`RDF.isIri`). -/
def mkIri? (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

/-- `make_plain_literal`: a bare `"…"` is `xsd:string`. -/
def mkPlainLit (lex : String) : WfLiteral := Literal.string lex

/-- `make_typed_literal`: `"…"^^<dt>`. `rdf:langString` and
`rdf:dirLangString` are REJECTED as explicit datatypes (a
language-tagged literal must come from a LANGTAG), which is why this
returns an `Option` where `Expr.mkTypedLiteral` silently falls back. -/
def mkTypedLit? (lex : String) (dt : String) : Option WfLiteral :=
  match mkIri? dt with
  | none    => none
  | some d  =>
    if h : (d != rdfLangString) && (d != rdfDirLangString) then
      some ⟨{ lexicalForm := lex, datatype := d, langTag := none, direction := none },
             by simpa [literalWf] using h⟩
    else none

/-- `make_lang_literal`. -/
def mkLangLit (lex tag : String) : WfLiteral := Literal.langString lex tag

/-- `make_dir_lang_literal` — RDF 1.2 Concepts §3.3. -/
def mkDirLangLit (lex tag : String) (d : TextDirection) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := rdfDirLangString,
     langTag := some tag, direction := some d }, rfl⟩

/-- `rdf_type_iri_str` — [82] VerbSimple's `a`. -/
def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
/-- `rdf_nil_iri_str` — the empty collection [102] Collection. -/
def rdfNilIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩
/-- `rdf_first_iri_str`. -/
def rdfFirstIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
/-- `rdf_rest_iri_str`. -/
def rdfRestIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
/-- `rdf_reifies_iri_str` — SPARQL 1.2 reification (issue #556). -/
def rdfReifiesIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩
/-- `fn_langmatches_iri_str` — LANGMATCHES is modelled as a call. -/
def fnLangMatchesIri : WfIri :=
  ⟨"http://www.w3.org/2005/xpath-functions#langMatches", rfl⟩
/-- `fn_rand_iri_str` — RAND has no `Expr` constructor. -/
def fnRandIri : WfIri := ⟨"http://www.w3.org/2005/xpath-functions#rand", rfl⟩
/-- `fn_uuid_iri_str`. -/
def fnUuidIri : WfIri := ⟨"http://www.w3.org/2005/xpath-functions#uuid", rfl⟩
/-- `fn_struuid_iri_str`. -/
def fnStrUuidIri : WfIri := ⟨"http://www.w3.org/2005/xpath-functions#struuid", rfl⟩
/-- `fn_bnode_iri_str`. -/
def fnBnodeIri : WfIri := ⟨"http://www.w3.org/2005/xpath-functions#bnode", rfl⟩

/-- The three XSD datatypes the numeric and boolean literal sugar
uses ([146]-[148], [134] BooleanLiteral). -/
def xsdInteger : String := "http://www.w3.org/2001/XMLSchema#integer"
/-- xsd:decimal. -/
def xsdDecimal : String := "http://www.w3.org/2001/XMLSchema#decimal"
/-- xsd:double. -/
def xsdDouble  : String := "http://www.w3.org/2001/XMLSchema#double"
/-- xsd:boolean. -/
def xsdBoolean : String := "http://www.w3.org/2001/XMLSchema#boolean"

/-! ## Prefixed names — [140] PNAME_LN / [141] PNAME_NS -/

/-- `split_pname`: split at the FIRST colon. -/
def splitPname (pn : String) : String × String :=
  let cs := pn.toList
  let rec go : List Char → List Char → List Char × List Char
    | [],        acc => (acc.reverse, [])
    | c :: rest, acc => if c == ':' then (acc.reverse, rest) else go rest (c :: acc)
  let (a, b) := go cs []
  (String.ofList a, String.ofList b)

/-- `lookup_prefix`. -/
def lookupPrefix (p : String) : List (String × String) → Option String
  | []            => none
  | (k, v) :: rest => if k == p then some v else lookupPrefix p rest

/-- `resolve_pname`: namespace ++ local. Note the F* does NOT undo the
[173] PN_LOCAL_ESC backslashes here — the lexeme is concatenated
verbatim — and the port keeps that, because changing it would change
which W3C fixtures resolve to which IRI. -/
def resolvePname (st : PState) (pn : String) : Option String :=
  let (pfx, loc) := splitPname pn
  match lookupPrefix pfx st.prefixes with
  | some ns => some (ns ++ loc)
  | none    => none

/-- Resolve a prefixed name all the way to a `WfIri`. -/
def resolvePnameIri (st : PState) (pn : String) : Option WfIri :=
  match resolvePname st pn with
  | none   => none
  | some s => mkIri? s

/-! ## Integers — [146] INTEGER as a value -/

/-- `chars_to_int`. -/
def charsToInt : List Char → Int → Int
  | [],        acc => acc
  | c :: rest, acc => charsToInt rest (acc * 10 + (Int.ofNat c.toNat - 0x30))

/-- `parse_int_str`: an optionally signed digit run, or `none`. -/
def parseIntStr (s : String) : Option Int :=
  match s.toList with
  | []        => none
  | c :: rest =>
    if c == '-' then
      if rest.length > 0 && rest.all isDigitC then some (0 - charsToInt rest 0) else none
    else if c == '+' then
      if rest.length > 0 && rest.all isDigitC then some (charsToInt rest 0) else none
    else if (c :: rest).all isDigitC then some (charsToInt (c :: rest) 0)
    else none

/-! ## Pattern assembly — the F* `ggp_*` helpers -/

/-- `ggp_join`: `empty` is the unit. -/
def ggpJoin (a b : QueryPattern) : QueryPattern :=
  match a with
  | .empty => b
  | _      => match b with
              | .empty => a
              | _      => .join a b

/-- `ggp_add_triple`: extend the accumulator's BGP in place when it is
one, so a triples block stays a single §18.3 BGP. -/
def ggpAddTriple (acc : QueryPattern) (tp : TriplePattern) : QueryPattern :=
  match acc with
  | .bgp ts => .bgp (ts ++ [tp])
  | .empty  => .bgp [tp]
  | _       => .join acc (.bgp [tp])

/-- `ggp_add_pp`. -/
def ggpAddPp (acc : QueryPattern) (s : PatternSubject) (pp : PropertyPath)
    (o : PatternTerm) : QueryPattern :=
  ggpJoin acc (.propertyPath s pp o)

/-- `fresh_bnode_id`: the label is derived from the REMAINING token
count, so it is stable and collision-free within one parse. The `_:`
is part of the label, exactly as in the F*; `isLabeledBnodeId` below
uses that to tell a generated label from a user-written one. -/
def freshBnodeId (ts : TStream) : String := "_:bnode_" ++ toString ts.length

/-- `is_labeled_bnode_id`: true for a label the QUERY wrote, false for
one this parser generated for `[]` or a collection. -/
def isLabeledBnodeId (b : String) : Bool := !("_:bnode_".isPrefixOf b)

/-- `pattern_term_to_subject`: a literal cannot be a subject. -/
def patternTermToSubject : PatternTerm → Option PatternSubject
  | .var v            => some (.var v)
  | .iri i            => some (.iri i)
  | .bnode b          => some (.bnode b)
  | .literal _        => none
  | .tripleTerm s p o => some (.tripleTerm s p o)

/-- `pattern_subject_to_term`: every subject form is also a term. -/
def patternSubjectToTerm : PatternSubject → PatternTerm
  | .var v            => .var v
  | .iri i            => .iri i
  | .bnode b          => .bnode b
  | .tripleTerm s p o => .tripleTerm s p o

/-- `select_item_var`. -/
def selectItemVar : SelectItem → VarName
  | .var v    => v
  | .expr _ v => v

/-- `select_items_has_var`. -/
def selectItemsHasVar (v : VarName) (items : List SelectItem) : Bool :=
  items.any (fun i => selectItemVar i == v)

/-- `var_list_has_dup` — rejects `VALUES (?a ?a) { … }`. -/
def varListHasDup : List VarName → Bool
  | []       => false
  | x :: rest => rest.any (fun y => x == y) || varListHasDup rest

/-! ## String-set helpers — the F* `string_*` family -/

/-- `string_mem`. -/
def strMem (x : String) (xs : List String) : Bool := xs.any (fun y => y == x)

/-- `string_add_unique`. -/
def strAddUnique (x : String) (xs : List String) : List String :=
  if strMem x xs then xs else x :: xs

/-- `string_union`. -/
def strUnion : List String → List String → List String
  | [],        ys => ys
  | x :: rest, ys => strUnion rest (strAddUnique x ys)

/-- `string_overlaps`. -/
def strOverlaps : List String → List String → Bool
  | [],        _  => false
  | x :: rest, ys => strMem x ys || strOverlaps rest ys

/-- `bnodes_in_pattern_subject` — generated labels are excluded. -/
def bnodesInSubject : PatternSubject → List String
  | .bnode b => if isLabeledBnodeId b then [b] else []
  | _        => []

/-- `bnodes_in_pattern_term`. -/
def bnodesInTerm : PatternTerm → List String
  | .bnode b => if isLabeledBnodeId b then [b] else []
  | _        => []

/-- `bnodes_in_triple_pattern`. -/
def bnodesInTriple (tp : TriplePattern) : List String :=
  strUnion (bnodesInSubject tp.s) (strUnion (bnodesInTerm tp.p) (bnodesInTerm tp.o))

/-- `bnodes_in_bgp`. -/
def bnodesInBgp : Bgp → List String
  | []        => []
  | tp :: rest => strUnion (bnodesInTriple tp) (bnodesInBgp rest)

/-! ## Aggregate detection — `expr_has_aggregate` (F* line 1586)

Does NOT descend into EXISTS / NOT EXISTS: a sub-pattern is a separate
grouping scope, so an aggregate inside one is not "nested" in the
§18.5.1 sense. That is exactly why the port needs no `GraphPattern`
walker here. -/

mutual

/-- `expr_has_aggregate`. -/
def exprHasAggregateFull : Expr → Bool
  | .aggregate _ _ _   => true
  | .var _ | .iri _ | .lit _ | .boolLit _ | .numericLit _
  | .decimalLit _ | .doubleLit _ | .bound _ | .now
  | .existsPat _ | .notExistsPat _ => false
  | .arith _ a b | .compare _ a b | .and a b | .or a b
  | .strDt a b | .strLang a b
  | .strStarts a b | .strEnds a b | .contains a b
  | .strBefore a b | .strAfter a b | .sameTerm a b =>
      exprHasAggregateFull a || exprHasAggregateFull b
  | .unaryMinus a | .unaryPlus a | .not a
  | .isIri a | .isBlank a | .isLiteral a | .isNumeric a
  | .str a | .lang a | .datatype a | .iriFn a
  | .hasLang a | .hasLangDir a | .langDir a
  | .strLen a | .uCase a | .lCase a | .encodeForUri a
  | .abs a | .round a | .ceil a | .floor a
  | .md5 a | .sha1 a | .sha256 a | .sha384 a | .sha512 a
  | .year a | .month a | .day a | .hours a | .minutes a | .seconds a
  | .timezone a | .tz a
  | .ttSubject a | .ttPredicate a | .ttObject a | .isTriple a =>
      exprHasAggregateFull a
  | .strLangDir a b c | .cond a b c | .tripleTerm a b c =>
      exprHasAggregateFull a || exprHasAggregateFull b || exprHasAggregateFull c
  | .coalesce es | .concat es | .functionCall _ es => exprsHaveAggregate es
  | .inList a es | .notInList a es => exprHasAggregateFull a || exprsHaveAggregate es
  | .substr a b o => exprHasAggregateFull a || exprHasAggregateFull b || exprOptHasAggregate o
  | .replace a b c o =>
      exprHasAggregateFull a || exprHasAggregateFull b || exprHasAggregateFull c || exprOptHasAggregate o
  | .regex a b o => exprHasAggregateFull a || exprHasAggregateFull b || exprOptHasAggregate o

/-- `expr_list_has_aggregate`. -/
def exprsHaveAggregate : List Expr → Bool
  | []        => false
  | e :: rest => exprHasAggregateFull e || exprsHaveAggregate rest

/-- `expr_opt_has_aggregate`. -/
def exprOptHasAggregate : Option Expr → Bool
  | none   => false
  | some e => exprHasAggregate e

end

/-- `expr_has_ungrouped_var` (`SPARQL11.Algebra.fst` line 5579): does
this projection expression mention a variable the GROUP BY did not
group on? Aggregates are always fine. The F* arm list stops at the
constructors below — anything else answers `false`, which this port
keeps verbatim rather than widening. -/
def exprHasUngroupedVar (isGrp : VarName → Bool) : Expr → Bool
  | .var v             => !isGrp v
  | .aggregate _ _ _   => false
  | .arith _ a b | .compare _ a b | .and a b | .or a b
  | .strDt a b | .strLang a b =>
      exprHasUngroupedVar isGrp a || exprHasUngroupedVar isGrp b
  | .not a | .unaryMinus a | .unaryPlus a
  | .str a | .lang a | .datatype a | .iriFn a
  | .hasLang a | .hasLangDir a | .langDir a
  | .isIri a | .isBlank a | .isLiteral a | .isNumeric a =>
      exprHasUngroupedVar isGrp a
  | .cond a b c | .strLangDir a b c =>
      exprHasUngroupedVar isGrp a || exprHasUngroupedVar isGrp b ||
      exprHasUngroupedVar isGrp c
  | _ => false

/-! ## Variables and blank nodes in a pattern

`ggpHasVar` (`SPARQL11.Algebra.fst` line 7387), `lateralAssignableVars`
(line 3113) and `ggpLabeledBnodes` (`SPARQL11.Parser.fst` line 1466)
walk `QueryPattern`, which is mutual with `Query`. -/

/-- Does a triple pattern mention `v`? (`bgp_has_var`.) -/
def tpHasVar (v : VarName) (tp : TriplePattern) : Bool :=
  (match tp.s with | .var x => x == v | _ => false) ||
  ptHasVar v tp.p || ptHasVar v tp.o
where
  ptHasVar (v : VarName) : PatternTerm → Bool
    | .var x            => x == v
    | .tripleTerm a b c => ptHasVar v a || ptHasVar v b || ptHasVar v c
    | _                 => false

mutual

/-- `ggp_has_var`: is `v` in scope anywhere in this pattern? -/
def ggpHasVar (v : VarName) : QueryPattern → Bool
  | .bgp b            => b.any (fun tp => tpHasVar v tp)
  | .join a b | .union a b | .minus a b | .lateral a b =>
      ggpHasVar v a || ggpHasVar v b
  | .leftJoin a b _   => ggpHasVar v a || ggpHasVar v b
  | .filter _ p       => ggpHasVar v p
  | .graph _ p        => ggpHasVar v p
  | .bind _ bv p      => bv == v || ggpHasVar v p
  | .values vars _    => vars.any (fun vn => vn == v)
  | .service _ _ p    => ggpHasVar v p
  | .serviceVar sv _ p => sv == v || ggpHasVar v p
  | .subSelect q      => queryHasVar v q
  | .propertyPath s _ o =>
      (match s with | .var sv => sv == v | _ => false) ||
      (match o with | .var ov => ov == v | _ => false)
  | .empty            => false

/-- A sub-SELECT exposes exactly its projected variables; `SELECT *`
cannot be checked statically and answers `false`, as in the F*. -/
def queryHasVar (v : VarName) : Query → Bool
  | .mk form _ _ _ _ _ _ _ =>
    match form with
    | .select (.vars items) => items.any (fun i => selectItemVar i == v)
    | _                     => false

end

/-- `lateral_assignable_vars` is ALREADY in `SPARQL/Query.lean`
(line 787) with the same arms as the F*, so the parser reuses it
rather than shadowing it. -/
def lateralAssignable : QueryPattern → List VarName := lateralAssignableVars

mutual

/-- `ggp_labeled_bnodes`: the USER-written blank-node labels a pattern
mentions. Reusing one across two group scopes is rejected. -/
def ggpLabeledBnodes : QueryPattern → List String
  | .bgp b            => bnodesInBgp b
  | .propertyPath s _ o => strUnion (bnodesInSubject s) (bnodesInTerm o)
  | .join a b | .union a b | .minus a b | .lateral a b =>
      strUnion (ggpLabeledBnodes a) (ggpLabeledBnodes b)
  | .leftJoin a b _   => strUnion (ggpLabeledBnodes a) (ggpLabeledBnodes b)
  | .filter _ p       => ggpLabeledBnodes p
  | .graph _ p        => ggpLabeledBnodes p
  | .bind _ _ p       => ggpLabeledBnodes p
  | .service _ _ p    => ggpLabeledBnodes p
  | .serviceVar _ _ p => ggpLabeledBnodes p
  | .subSelect q      => ggpLabeledBnodesQ q
  | .values _ _ | .empty => []

/-- The sub-SELECT case. -/
def ggpLabeledBnodesQ : Query → List String
  | .mk _ _ pat _ _ _ _ _ => ggpLabeledBnodes pat

end

/-! ## Blank-node scope validation — `validate_bnode_scope_pattern`
(F* line 4350)

SPARQL 1.1 §19.6: a blank-node label may not be reused in two
graph-pattern scopes that could name different nodes. A Join of two
BGP-preserving sides may share labels (they are one BGP after
lowering); a Union, Minus, LeftJoin or Lateral may not. -/

mutual

/-- `preserves_bgp_scope`. -/
def preservesBgpScope : QueryPattern → Bool
  | .bgp _ | .propertyPath _ _ _ | .values _ _ | .empty => true
  | .filter _ p => preservesBgpScope p
  | .bind _ _ p => preservesBgpScope p
  | .join a b   => preservesBgpScope a && preservesBgpScope b
  | _           => false

/-- `validate_bnode_scope_pattern`: `(ok, labels visible outward)`. -/
def validateBnodeScope : QueryPattern → Bool × List String
  | .bgp b              => (true, bnodesInBgp b)
  | .propertyPath s _ o => (true, strUnion (bnodesInSubject s) (bnodesInTerm o))
  | .filter _ p         => let (ok, bs) := validateBnodeScope p; (ok, bs)
  | .bind _ _ p         => let (ok, bs) := validateBnodeScope p; (ok, bs)
  | .values _ _         => (true, [])
  | .empty              => (true, [])
  | .join a b =>
      let (ok1, b1) := validateBnodeScope a
      let (ok2, b2) := validateBnodeScope b
      let allow := preservesBgpScope a && preservesBgpScope b
      (ok1 && ok2 && (allow || !strOverlaps b1 b2), strUnion b1 b2)
  | .union a b | .minus a b | .lateral a b =>
      let (ok1, b1) := validateBnodeScope a
      let (ok2, b2) := validateBnodeScope b
      (ok1 && ok2 && !strOverlaps b1 b2, strUnion b1 b2)
  | .leftJoin a b _ =>
      let (ok1, b1) := validateBnodeScope a
      let (ok2, b2) := validateBnodeScope b
      (ok1 && ok2 && !strOverlaps b1 b2, strUnion b1 b2)
  | .graph _ p | .service _ _ p | .serviceVar _ _ p => validateBnodeScope p
  | .subSelect q => validateBnodeScopeQ q

/-- `validate_bnode_scope_query`. -/
def validateBnodeScopeQ : Query → Bool × List String
  | .mk _ _ pat _ _ _ _ _ => validateBnodeScope pat

end

/-- `validate_bnode_scope_top`. -/
def validateBnodeScopeTop (q : Query) : Bool := (validateBnodeScopeQ q).1

/-! ## CONSTRUCT template helpers -/

/-- `is_basic_pattern`: the `CONSTRUCT WHERE` short form ([10.1]) only
accepts BGPs, paths, joins of those, and the empty pattern. -/
def isBasicPattern : QueryPattern → Bool
  | .bgp _ | .empty | .propertyPath _ _ _ => true
  | .join a b => isBasicPattern a && isBasicPattern b
  | _         => false

/-- `collect_template_triples`: a CONSTRUCT template ([73]
ConstructTemplate) may hold only triple patterns, so paths and
non-BGP constructs contribute nothing. -/
def collectTemplateTriples : QueryPattern → List TriplePattern
  | .bgp b    => b
  | .empty    => []
  | .join a b => collectTemplateTriples a ++ collectTemplateTriples b
  | _         => []

/-! ## Relative-IRI resolution over the token stream

`resolve_relative_iri_token` (F* line 1128). The prologue's BASE is
applied to EVERY `iri` token of the rest of the query in one pass,
which is why the grammar functions below never see a relative
reference. RFC 3986 resolution itself is `Syntax.resolveIri`. -/

/-- Resolve one token's IRIREF against the base, if it needs it. -/
def resolveIriToken (base : Option String) (pt : PosToken) : PosToken :=
  match pt.tok with
  | .iri s =>
    if isIri s then pt
    else match base with
         | none   => pt
         | some b => { pt with tok := .iri (resolveIri b s) }
  | _ => pt

/-- `resolve_relative_iri_tokens`. -/
def resolveIriTokens (base : Option String) (ts : TStream) : TStream :=
  ts.map (resolveIriToken base)

/-- `first_invalid_token_msg`: surface a lexer-detected error before
the grammar runs. -/
def firstInvalidToken : TStream → Option ParseError
  | []       => none
  | pt :: rest =>
    match pt.tok with
    | .invalid m => some ⟨m, pt.pos⟩
    | _          => firstInvalidToken rest

/-- `tokens_only_eof`: nothing but padding left. -/
def tokensOnlyEof : TStream → Bool
  | []       => true
  | pt :: rest => (pt.tok == Token.eof) && tokensOnlyEof rest

/-! ## The token sets the grammar branches on

Named so the branch conditions below read like the F*'s
multi-constructor `match` arms. -/

/-- The tokens that can START a triples block — the F* `parse_ggp_body`
and `parse_triples_block` term arms. -/
def startsTriples : Token → Bool
  | .var _ | .iri _ | .pname _ | .bnode _ | .lbracket
  | .lparen | .a | .integer _ | .decimal _ | .double _
  | .str _ | .trueKw | .falseKw | .ttOpen | .ttBareOpen => true
  | _ => false

/-- The builtin-call tokens a FILTER may take without parentheses
([68] Constraint = BrackettedExpression | BuiltInCall | FunctionCall). -/
def startsBuiltinCall : Token → Bool
  | .exists | .notKw | .strKw | .langKw | .langMatches | .datatype
  | .bound | .sameTerm | .isIri | .isBlank | .isLiteral | .isNumeric
  | .regexKw | .ifKw
  | .iriKw | .uriKw | .bnodeKw | .rand
  | .absKw | .ceil | .floor | .roundKw
  | .concat | .strLen | .uCase | .lCase
  | .encodeForUri | .contains | .strStarts | .strEnds
  | .strBefore | .strAfter | .replaceKw | .substr
  | .strDt | .strLang
  | .coalesce | .now | .uuid | .strUuid
  | .year | .month | .day | .hours | .minutes | .seconds
  | .timezone | .tz
  | .md5 | .sha1 | .sha256 | .sha384 | .sha512 => true
  | _ => false

/-- The tokens `parse_group_by_list` accepts as the start of a
[19] GroupCondition. -/
def startsGroupCondition : Token → Bool
  | .var _ | .lparen | .strKw | .langKw | .langMatches | .datatype
  | .bound | .ifKw | .iriKw | .uriKw | .concat | .strLen
  | .uCase | .lCase | .encodeForUri | .contains | .strStarts
  | .strEnds | .strBefore | .strAfter | .replaceKw | .regexKw | .substr
  | .absKw | .ceil | .floor | .roundKw | .isIri | .isBlank
  | .isLiteral | .isNumeric | .sameTerm | .coalesce | .iri _ | .pname _ => true
  | _ => false

/-- The tokens `parse_order_by_list` accepts as the start of a
[24] OrderCondition. -/
def startsOrderCondition : Token → Bool
  | .asc | .desc | .var _ | .lparen | .iri _ | .pname _
  | .strKw | .langKw | .langMatches | .datatype | .bound
  | .ifKw | .iriKw | .uriKw | .concat | .isIri | .isBlank
  | .isLiteral | .isNumeric | .sameTerm | .coalesce => true
  | _ => false

/-- The tokens `parse_having_list` accepts as a bare [22]
HavingCondition. -/
def startsHavingCondition : Token → Bool
  | .strKw | .langKw | .langMatches | .datatype | .bound
  | .ifKw | .iriKw | .uriKw | .concat | .isIri | .isBlank
  | .isLiteral | .isNumeric | .sameTerm | .coalesce
  | .exists | .notKw | .regexKw => true
  | _ => false

/-- The tokens that TERMINATE a predicate-object list after a `;`
(the F*'s `parse_pred_obj_list` lookahead set). -/
def endsPredObjList : Token → Bool
  | .dot | .rbrace | .optional | .minusKw | .filterKw
  | .bind | .graph | .service | .values | .union
  | .lateral | .lbrace | .rbracket | .eof => true
  | _ => false

/-- SPARQL 1.2 `VarOrReifierId ::= Var | iri | BlankNode`, after a `~`
the caller consumed; any other token means no explicit id was given,
which mints a fresh blank node without consuming anything — rewritten
to a non-distinguished variable downstream, same as an anonymous `[]`
(`parse_reifier_id`). -/
def pReifierId (st : PState) (ts : TStream) : Except ParseError (PatternSubject × TStream) :=
  match peekTok ts with
  | .var v => .ok (.var v, advTok ts)
  | .iri i =>
    (match mkIri? i with
     | some wi => .ok (.iri wi, advTok ts)
     | none    => pErr "invalid reifier IRI" ts)
  | .pname pn =>
    (match resolvePnameIri st pn with
     | some wi => .ok (.iri wi, advTok ts)
     | none    => pErr "unresolved prefix" ts)
  | .bnode b => .ok (.bnode b, advTok ts)
  | _ => .ok (.bnode (freshBnodeId ts), ts)

/-! ## The grammar — one mutual block, structural on `fuel`

Every function takes `fuel` FIRST and every recursive call passes the
post-destructuring `f`, so the block is structurally recursive with no
`termination_by` — the same discipline `JSON/Parser.lean` uses, and the
Lean counterpart of the F*'s `decreases fuel`. -/

mutual

/-- [110] Expression ::= ConditionalOrExpression. -/
def pExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => pOrExpr f st ts

/-- [111] ConditionalOrExpression ::= ConditionalAndExpression
( '||' ConditionalAndExpression )*. -/
def pOrExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e, ts1) ← pAndExpr f st ts
    pOrRest f st e ts1

/-- The left-associative `||` tail. -/
def pOrRest (fuel : Nat) (st : PState) (e : Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => .ok (e, ts)
  | f + 1 =>
    match peekTok ts with
    | .or => do
      let (e2, ts1) ← pAndExpr f st (advTok ts)
      pOrRest f st (.or e e2) ts1
    | _ => .ok (e, ts)

/-- [112] ConditionalAndExpression ::= ValueLogical ( '&&' ValueLogical )*. -/
def pAndExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e, ts1) ← pRelExpr f st ts
    pAndRest f st e ts1

/-- The left-associative `&&` tail. -/
def pAndRest (fuel : Nat) (st : PState) (e : Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => .ok (e, ts)
  | f + 1 =>
    match peekTok ts with
    | .and => do
      let (e2, ts1) ← pRelExpr f st (advTok ts)
      pAndRest f st (.and e e2) ts1
    | _ => .ok (e, ts)

/-- [114] RelationalExpression — NON-associative: at most one
comparison, or an `IN` / `NOT IN` list. -/
def pRelExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e1, ts1) ← pAddExpr f st ts
    match peekTok ts1 with
    | .eq => pRelRhs f st (fun r => .compare .eq e1 r) ts1
    | .ne => pRelRhs f st (fun r => .compare .ne e1 r) ts1
    | .lt => pRelRhs f st (fun r => .compare .lt e1 r) ts1
    | .gt => pRelRhs f st (fun r => .compare .gt e1 r) ts1
    | .le => pRelRhs f st (fun r => .compare .le e1 r) ts1
    | .ge => pRelRhs f st (fun r => .compare .ge e1 r) ts1
    | .inKw => pInList f st e1 false (advTok ts1)
    | .notKw =>
      let ts2 := advTok ts1
      match peekTok ts2 with
      | .inKw => pInList f st e1 true (advTok ts2)
      | _     => .ok (e1, ts1)
    | _ => .ok (e1, ts1)

/-- The right operand of a comparison. -/
def pRelRhs (fuel : Nat) (st : PState) (k : Expr → Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e2, ts1) ← pAddExpr f st (advTok ts)
    .ok (k e2, ts1)

/-- `IN ( … )` / `NOT IN ( … )` — [114]'s ExpressionList arms. -/
def pInList (fuel : Nat) (st : PState) (e : Expr) (negated : Bool) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (es, ts2) ← pExprList f st ts1
    let (_, ts3)  ← expectTok .rparen ts2
    .ok (if negated then .notInList e es else .inList e es, ts3)

/-- [72] ExpressionList ::= NIL | '(' Expression ( ',' Expression )* ')'
— the inner comma-separated part; the parens are the caller's. -/
def pExprList (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (List Expr × TStream) :=
  match fuel with
  | 0     => .ok ([], ts)
  | f + 1 =>
    match peekTok ts with
    | .rparen => .ok ([], ts)
    | _ => do
      let (e, ts1) ← pExpr f st ts
      pExprListRest f st [e] ts1

/-- The `, Expression` tail of an expression list. -/
def pExprListRest (fuel : Nat) (st : PState) (acc : List Expr) (ts : TStream) :
    Except ParseError (List Expr × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .comma => do
      let (e, ts1) ← pExpr f st (advTok ts)
      pExprListRest f st (e :: acc) ts1
    | _ => .ok (acc.reverse, ts)

/-- [116] AdditiveExpression ::= MultiplicativeExpression
( '+' M | '-' M )*. -/
def pAddExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e, ts1) ← pMulExpr f st ts
    pAddRest f st e ts1

/-- The left-associative `+` / `-` tail. -/
def pAddRest (fuel : Nat) (st : PState) (e : Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => .ok (e, ts)
  | f + 1 =>
    match peekTok ts with
    | .plus => do
      let (e2, ts1) ← pMulExpr f st (advTok ts)
      pAddRest f st (.arith .add e e2) ts1
    | .minusOp => do
      let (e2, ts1) ← pMulExpr f st (advTok ts)
      pAddRest f st (.arith .sub e e2) ts1
    | _ => .ok (e, ts)

/-- [117] MultiplicativeExpression ::= UnaryExpression
( '*' U | '/' U )*. -/
def pMulExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (e, ts1) ← pUnaryExpr f st ts
    pMulRest f st e ts1

/-- The left-associative `*` / `/` tail. -/
def pMulRest (fuel : Nat) (st : PState) (e : Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => .ok (e, ts)
  | f + 1 =>
    match peekTok ts with
    | .star => do
      let (e2, ts1) ← pUnaryExpr f st (advTok ts)
      pMulRest f st (.arith .mul e e2) ts1
    | .slash => do
      let (e2, ts1) ← pUnaryExpr f st (advTok ts)
      pMulRest f st (.arith .div e e2) ts1
    | _ => .ok (e, ts)

/-- [118] UnaryExpression ::= '!' U | '+' U | '-' U | PrimaryExpression.
The operand is a UnaryExpression, not a Primary, so unary operators
stack (`!!?v`) — the F* notes no 1.1 negative-syntax test forbids it. -/
def pUnaryExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .bang => do
      let (e, ts1) ← pUnaryExpr f st (advTok ts)
      .ok (.not e, ts1)
    | .plus => do
      let (e, ts1) ← pUnaryExpr f st (advTok ts)
      .ok (.unaryPlus e, ts1)
    | .minusOp => do
      let (e, ts1) ← pUnaryExpr f st (advTok ts)
      .ok (.unaryMinus e, ts1)
    | _ => pPrimaryExpr f st ts

/-- [119] PrimaryExpression ::= BrackettedExpression | BuiltInCall |
iriOrFunction | RDFLiteral | NumericLiteral | BooleanLiteral | Var.
Also, in 1.2 mode, the triple-term forms. -/
def pPrimaryExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v     => .ok (.var v, advTok ts)
    | .trueKw    => .ok (.boolLit true, advTok ts)
    | .falseKw   => .ok (.boolLit false, advTok ts)
    | .integer n =>
      match parseIntStr n with
      | some i => .ok (.numericLit i, advTok ts)
      | none   => .ok (.decimalLit n, advTok ts)
    | .decimal d => .ok (.decimalLit d, advTok ts)
    | .double d  => .ok (.doubleLit d, advTok ts)
    | .str s     => pRdfLiteralExpr f st s (advTok ts)
    | .iri i =>
      match mkIri? i with
      | none    => pErr s!"invalid IRI: {i}" ts
      | some wi =>
        let ts1 := advTok ts
        match peekTok ts1 with
        | .lparen => pFuncCall f st wi (advTok ts1)
        | _       => .ok (.iri wi, ts1)
    | .pname pn  => pPnameExpr f st pn (advTok ts)
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      match expectTok .rparen ts1 with
      | .error _      => pErr "expected ')'" ts1
      | .ok (_, ts2)  => .ok (e, ts2)
    -- SPARQL 1.2 triple-term expressions
    | .ttOpen      => pTtExpr f st (advTok ts)
    | .tripleKw    => pB3 f st (fun a b c => .tripleTerm a b c) (advTok ts)
    | .subjectKw   => pB1 f st .ttSubject (advTok ts)
    | .predicateKw => pB1 f st .ttPredicate (advTok ts)
    | .objectKw    => pB1 f st .ttObject (advTok ts)
    | .isTripleKw  => pB1 f st .isTriple (advTok ts)
    -- §17 one-argument builtins
    | .strKw        => pB1 f st .str (advTok ts)
    | .langKw       => pB1 f st .lang (advTok ts)
    | .datatype     => pB1 f st .datatype (advTok ts)
    | .hasLangKw    => pB1 f st .hasLang (advTok ts)
    | .hasLangDirKw => pB1 f st .hasLangDir (advTok ts)
    | .langDirKw    => pB1 f st .langDir (advTok ts)
    | .iriKw        => pB1 f st .iriFn (advTok ts)
    | .uriKw        => pB1 f st .iriFn (advTok ts)
    | .absKw        => pB1 f st .abs (advTok ts)
    | .ceil         => pB1 f st .ceil (advTok ts)
    | .floor        => pB1 f st .floor (advTok ts)
    | .roundKw      => pB1 f st .round (advTok ts)
    | .strLen       => pB1 f st .strLen (advTok ts)
    | .uCase        => pB1 f st .uCase (advTok ts)
    | .lCase        => pB1 f st .lCase (advTok ts)
    | .encodeForUri => pB1 f st .encodeForUri (advTok ts)
    | .isIri        => pB1 f st .isIri (advTok ts)
    | .isBlank      => pB1 f st .isBlank (advTok ts)
    | .isLiteral    => pB1 f st .isLiteral (advTok ts)
    | .isNumeric    => pB1 f st .isNumeric (advTok ts)
    | .md5          => pB1 f st .md5 (advTok ts)
    | .sha1         => pB1 f st .sha1 (advTok ts)
    | .sha256       => pB1 f st .sha256 (advTok ts)
    | .sha384       => pB1 f st .sha384 (advTok ts)
    | .sha512       => pB1 f st .sha512 (advTok ts)
    | .year         => pB1 f st .year (advTok ts)
    | .month        => pB1 f st .month (advTok ts)
    | .day          => pB1 f st .day (advTok ts)
    | .hours        => pB1 f st .hours (advTok ts)
    | .minutes      => pB1 f st .minutes (advTok ts)
    | .seconds      => pB1 f st .seconds (advTok ts)
    | .timezone     => pB1 f st .timezone (advTok ts)
    | .tz           => pB1 f st .tz (advTok ts)
    -- §17 two-argument builtins
    | .langMatches => do
      -- §17.4.2.5: no `Expr` constructor; modelled as an XPath call,
      -- which is what `Expr.evalIn` dispatches `langMatches` on.
      let (_, ts1)  ← expectTok .lparen (advTok ts)
      let (e1, ts2) ← pExpr f st ts1
      let (_, ts3)  ← expectTok .comma ts2
      let (e2, ts4) ← pExpr f st ts3
      let (_, ts5)  ← expectTok .rparen ts4
      .ok (.functionCall fnLangMatchesIri [e1, e2], ts5)
    | .sameTerm  => pB2 f st .sameTerm (advTok ts)
    | .strStarts => pB2 f st .strStarts (advTok ts)
    | .strEnds   => pB2 f st .strEnds (advTok ts)
    | .contains  => pB2 f st .contains (advTok ts)
    | .strBefore => pB2 f st .strBefore (advTok ts)
    | .strAfter  => pB2 f st .strAfter (advTok ts)
    | .strDt     => pB2 f st .strDt (advTok ts)
    | .strLang   => pB2 f st .strLang (advTok ts)
    | .strLangDirKw => pB3 f st .strLangDir (advTok ts)
    -- §17 special forms
    | .bound    => pBound f st (advTok ts)
    | .ifKw     => pIfExpr f st (advTok ts)
    | .coalesce => pArgListCall f st .coalesce (advTok ts)
    | .concat   => pArgListCall f st .concat (advTok ts)
    | .now =>
      -- NOW's parentheses are optional in the F*, which accepts a bare
      -- `NOW` as well as `NOW()`.
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .lparen =>
         (match expectTok .rparen (advTok ts1) with
          | .error _     => pErr "expected ')' after NOW(" ts1
          | .ok (_, ts2) => .ok (.now, ts2))
       | _ => .ok (.now, ts1))
    | .rand     => pNullaryCall f st fnRandIri "RAND" (advTok ts)
    | .uuid     => pNullaryCall f st fnUuidIri "UUID" (advTok ts)
    | .strUuid  => pNullaryCall f st fnStrUuidIri "STRUUID" (advTok ts)
    | .bnodeKw => do
      -- §17.4.2.2 BNODE() or BNODE(expr).
      let (_, ts1) ← expectTok .lparen (advTok ts)
      match peekTok ts1 with
      | .rparen => .ok (.functionCall fnBnodeIri [], advTok ts1)
      | _ => do
        let (arg, ts2) ← pExpr f st ts1
        match expectTok .rparen ts2 with
        | .error _     => pErr "expected ')' after BNODE(expr" ts2
        | .ok (_, ts3) => .ok (.functionCall fnBnodeIri [arg], ts3)
    | .regexKw   => pRegex f st (advTok ts)
    | .replaceKw => pReplace f st (advTok ts)
    | .substr    => pSubstr f st (advTok ts)
    -- §18.5.1 aggregates
    | .count       => pAggregate f st .count (advTok ts)
    | .sum         => pAggregate f st .sum (advTok ts)
    | .minKw       => pAggregate f st .min (advTok ts)
    | .maxKw       => pAggregate f st .max (advTok ts)
    | .avg         => pAggregate f st .avg (advTok ts)
    | .sample      => pAggregate f st .sample (advTok ts)
    | .groupConcat => pGroupConcat f st (advTok ts)
    -- §8.1.1 EXISTS / NOT EXISTS
    | .exists => do
      let (g, ts1) ← pGroupGraphPattern f st (advTok ts)
      mkExists f st false g ts1
    | .notKw =>
      let ts1 := advTok ts
      match peekTok ts1 with
      | .exists => do
        let (g, ts2) ← pGroupGraphPattern f st (advTok ts1)
        mkExists f st true g ts2
      -- `NOT IN` is handled one level up, at [114]; return a
      -- placeholder without consuming, exactly as the F* does.
      | .inKw => .ok (.boolLit true, ts)
      | _     => pErr "expected EXISTS or IN after NOT" ts1
    | _ => pErr "unexpected token in expression" ts

/-- Build an `Expr.existsPat` / `Expr.notExistsPat` over the operand
AS PARSED (the F* `E_Exists : group_graph_pattern -> expr`). The
blank-node scope check that the F* `validate_bnode_scope_expr` runs
later happens HERE, on the operand — see the module header on why that
is equivalent. -/
def mkExists (fuel : Nat) (_st : PState) (negated : Bool) (g : QueryPattern)
    (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    if !(validateBnodeScope g).1 then
      pErr "blank node label reused across graph-pattern scope" ts
    else
      .ok (if negated then .notExistsPat g else .existsPat g, ts)

/-- [121] BuiltInCall's `BOUND '(' Var ')'` arm. -/
def pBound (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    match peekTok ts1 with
    | .var v => do
      let (_, ts2) ← expectTok .rparen (advTok ts1)
      .ok (.bound v, ts2)
    | _ => pErr "BOUND expects a variable" ts1

/-- `IF '(' Expression ',' Expression ',' Expression ')'` — §17.4.1.4. -/
def pIfExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    let (_, ts5)  ← expectTok .comma ts4
    let (e3, ts6) ← pExpr f st ts5
    let (_, ts7)  ← expectTok .rparen ts6
    .ok (.cond e1 e2 e3, ts7)

/-- COALESCE / CONCAT — a builtin over an ExpressionList. -/
def pArgListCall (fuel : Nat) (st : PState) (k : List Expr → Expr) (ts : TStream) :
    Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (es, ts2) ← pExprList f st ts1
    let (_, ts3)  ← expectTok .rparen ts2
    .ok (k es, ts3)

/-- RAND / UUID / STRUUID: zero-argument calls with no `Expr`
constructor, modelled as XPath function calls (§17.4.1.5, §17.4.2.12). -/
def pNullaryCall (fuel : Nat) (_st : PState) (i : WfIri) (name : String)
    (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    match expectTok .rparen ts1 with
    | .error _     => pErr s!"expected ')' after {name}(" ts1
    | .ok (_, ts2) => .ok (.functionCall i [], ts2)

/-- `REGEX '(' Expression ',' Expression ( ',' Expression )? ')'`. -/
def pRegex (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    match peekTok ts4 with
    | .comma => do
      let (e3, ts5) ← pExpr f st (advTok ts4)
      let (_, ts6)  ← expectTok .rparen ts5
      .ok (.regex e1 e2 (some e3), ts6)
    | _ => do
      let (_, ts5) ← expectTok .rparen ts4
      .ok (.regex e1 e2 none, ts5)

/-- `REPLACE '(' E ',' E ',' E ( ',' E )? ')'`. -/
def pReplace (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    let (_, ts5)  ← expectTok .comma ts4
    let (e3, ts6) ← pExpr f st ts5
    match peekTok ts6 with
    | .comma => do
      let (e4, ts7) ← pExpr f st (advTok ts6)
      let (_, ts8)  ← expectTok .rparen ts7
      .ok (.replace e1 e2 e3 (some e4), ts8)
    | _ => do
      let (_, ts7) ← expectTok .rparen ts6
      .ok (.replace e1 e2 e3 none, ts7)

/-- `SUBSTR '(' E ',' E ( ',' E )? ')'` — §17.4.3.3. -/
def pSubstr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    match peekTok ts4 with
    | .comma => do
      let (e3, ts5) ← pExpr f st (advTok ts4)
      let (_, ts6)  ← expectTok .rparen ts5
      .ok (.substr e1 e2 (some e3), ts6)
    | _ => do
      let (_, ts5) ← expectTok .rparen ts4
      .ok (.substr e1 e2 none, ts5)

/-- [127] Aggregate — COUNT / SUM / MIN / MAX / AVG / SAMPLE, with the
`COUNT(*)` and `COUNT(DISTINCT *)` special case. §18.5.1 forbids an
aggregate inside an aggregate's argument. The star is encoded as
`Expr.boolLit true`, which is what `Query.evalAggregate` matches on. -/
def pAggregate (fuel : Nat) (st : PState) (fn : AggregateFn) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    let (dist, ts2) := match peekTok ts1 with
                       | .distinct => (true, advTok ts1)
                       | _         => (false, ts1)
    match peekTok ts2 with
    | .star => do
      let (_, ts3) ← expectTok .rparen (advTok ts2)
      .ok (.aggregate fn dist (.boolLit true), ts3)
    | _ => do
      let (e, ts3) ← pExpr f st ts2
      let (_, ts4) ← expectTok .rparen ts3
      if exprHasAggregateFull e then pErr "nested aggregate in aggregate argument" ts3
      else .ok (.aggregate fn dist e, ts4)

/-- [127] GROUP_CONCAT with its optional `; SEPARATOR = "…"`. -/
def pGroupConcat (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    let (dist, ts2) := match peekTok ts1 with
                       | .distinct => (true, advTok ts1)
                       | _         => (false, ts1)
    let (e, ts3) ← pExpr f st ts2
    let (sep, ts4) :=
      match peekTok ts3 with
      | .semi =>
        let ts3a := advTok ts3
        (match peekTok ts3a with
         | .separator =>
           let ts3b := advTok ts3a
           (match expectTok .eq ts3b with
            | .ok (_, ts3c) =>
              (match peekTok ts3c with
               | .str s => (some s, advTok ts3c)
               | _      => (none, ts3))
            | .error _ => (none, ts3))
         | _ => (none, ts3))
      | _ => (none, ts3)
    let (_, ts5) ← expectTok .rparen ts4
    if exprHasAggregateFull e then pErr "nested aggregate in GROUP_CONCAT argument" ts3
    else .ok (.aggregate (.groupConcat sep) dist e, ts5)

/-- A one-argument builtin: `'(' Expression ')'`. -/
def pB1 (fuel : Nat) (st : PState) (k : Expr → Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    let (e, ts2) ← pExpr f st ts1
    let (_, ts3) ← expectTok .rparen ts2
    .ok (k e, ts3)

/-- A two-argument builtin. -/
def pB2 (fuel : Nat) (st : PState) (k : Expr → Expr → Expr) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    let (_, ts5)  ← expectTok .rparen ts4
    .ok (k e1 e2, ts5)

/-- A three-argument builtin — SPARQL 1.2 `TRIPLE(s,p,o)` and
`STRLANGDIR(lex,tag,dir)`. -/
def pB3 (fuel : Nat) (st : PState) (k : Expr → Expr → Expr → Expr) (ts : TStream) :
    Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1)  ← expectTok .lparen ts
    let (e1, ts2) ← pExpr f st ts1
    let (_, ts3)  ← expectTok .comma ts2
    let (e2, ts4) ← pExpr f st ts3
    let (_, ts5)  ← expectTok .comma ts4
    let (e3, ts6) ← pExpr f st ts5
    let (_, ts7)  ← expectTok .rparen ts6
    .ok (k e1 e2 e3, ts7)

/-- SPARQL 1.2: one component of a triple-term EXPRESSION `<<( s p o )>>`.
Space-separated, and the predicate may be `a`. -/
def pTtExprComponent (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .a => .ok (.iri rdfTypeIri, advTok ts)
    | _  => pPrimaryExpr f st ts

/-- SPARQL 1.2: the SUBJECT of a triple-term expression is restricted
to VarOrIri — a literal there is a syntax error. -/
def pTtExprSubject (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .var v => .ok (.var v, advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePname st pn with
       | none   => pErr "unresolved prefix" ts
       | some s => match mkIri? s with
                   | some wi => .ok (.iri wi, advTok ts)
                   | none    => pErr "invalid IRI" ts)
    | _ => pErr "triple-term subject must be a variable or IRI" ts

/-- SPARQL 1.2 `<<( s p o )>>` as an expression; the opener is consumed. -/
def pTtExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (es, ts1) ← pTtExprSubject f st ts
    let (ep, ts2) ← pTtExprComponent f st ts1
    let (eo, ts3) ← pTtExprComponent f st ts2
    match expectTok .ttClose ts3 with
    | .error _     => pErr "expected ')>>' to close triple term" ts3
    | .ok (_, ts4) => .ok (.tripleTerm es ep eo, ts4)

/-- [128] iriOrFunction's ArgList arm — an unknown IRI applied to
arguments becomes `Expr.functionCall` (§17.6 extension function). -/
def pFuncCall (fuel : Nat) (st : PState) (i : WfIri) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (args, ts1) ← pExprList f st ts
    let (_, ts2)    ← expectTok .rparen ts1
    .ok (.functionCall i args, ts2)

/-- A prefixed name in expression position: an IRI, or a function call
when a `(` follows. -/
def pPnameExpr (fuel : Nat) (st : PState) (pn : String) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match resolvePname st pn with
    | none => pErr s!"unresolved prefix: {pn}" ts
    | some s =>
      match mkIri? s with
      | none    => pErr s!"resolved IRI invalid: {s}" ts
      | some wi =>
        match peekTok ts with
        | .lparen => pFuncCall f st wi (advTok ts)
        | _       => .ok (.iri wi, ts)

/-- [129] RDFLiteral in expression position: the STRING is consumed;
an optional `^^<dt>` or LANGTAG follows. -/
def pRdfLiteralExpr (fuel : Nat) (st : PState) (s : String) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .hathat =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .iri dt =>
         (match mkTypedLit? s dt with
          | some l => .ok (.lit l, advTok ts1)
          | none   => pErr "invalid typed literal" ts1)
       | .pname pn =>
         (match resolvePname st pn with
          | none    => pErr s!"unresolved datatype prefix: {pn}" ts1
          | some dt => match mkTypedLit? s dt with
                       | some l => .ok (.lit l, advTok ts1)
                       | none   => pErr "invalid typed literal" ts1)
       | _ => pErr "expected IRI after ^^" ts1)
    | .langtag lang    => .ok (.lit (mkLangLit s lang), advTok ts)
    | .langdir lang d  => .ok (.lit (mkDirLangLit s lang d), advTok ts)
    | _                => .ok (.lit (mkPlainLit s), ts)

-- ### Group graph patterns — [53]-[57]

/-- [53] GroupGraphPattern ::= '{' ( SubSelect | GroupGraphPatternSub ) '}'. -/
def pGroupGraphPattern (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1) ← expectTok .lbrace ts
    match peekTok ts1 with
    | .select => do
      -- [8] SubSelect. The outer prologue already rewrote relative
      -- IRIs in the token stream, so no base is threaded in.
      let (q, ts2) ← pSelectQuery f st none ts1
      let (_, ts3) ← expectTok .rbrace ts2
      .ok (.subSelect q, ts3)
    | .rbrace => .ok (.empty, advTok ts1)
    | _ => do
      let (g, ts2) ← pGgpBody f st .empty [] false ts1
      let (_, ts3) ← expectTok .rbrace ts2
      .ok (g, ts3)

/-- [54] GroupGraphPatternSub: triples blocks interleaved with
[56] GraphPatternNotTriples elements. FILTERs are COLLECTED and
wrapped around the whole group at the end, per §18.2.4 — a filter
scopes over its entire group, not over what precedes it.

`crossScope` tracks whether a nested group has already been seen, so a
following triples block's blank-node labels are checked against the
accumulated ones (§19.6). -/
def pGgpBody (fuel : Nat) (st : PState) (acc : QueryPattern)
    (filters : List Expr) (crossScope : Bool) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (filters.foldl (fun g e => .filter e g) acc, ts)
  | f + 1 =>
    let tok := peekTok ts
    if startsTriples tok then do
      let (tri, ts1) ← pTriplesBlock f st .empty ts
      if crossScope && strOverlaps (ggpLabeledBnodes acc) (ggpLabeledBnodes tri) then
        pErr "blank node label reused across nested group scope" ts
      else pGgpBody f st (ggpJoin acc tri) filters false ts1
    else
      match tok with
      | .optional => do
        let (g, ts1) ← pGroupGraphPattern f st (advTok ts)
        let acc' : QueryPattern := .leftJoin acc g (.boolLit true)
        let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
        pGgpBody f st acc' filters true ts2
      | .minusKw => do
        let (g, ts1) ← pGroupGraphPattern f st (advTok ts)
        let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
        pGgpBody f st (.minus acc g) filters true ts2
      | .lateral => do
        -- Jena's LATERAL well-formedness rule: the right-hand side may
        -- not reassign a variable the left-hand pattern already binds.
        let (g, ts1) ← pGroupGraphPattern f st (advTok ts)
        if (lateralAssignableVars g).any (fun v => ggpHasVar v acc) then
          pErr "LATERAL: right-hand side reassigns a variable already bound by the left-hand pattern" ts
        else
          let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
          pGgpBody f st (.lateral acc g) filters true ts2
      | .graph => do
        let (gn, ts1) ← pGraphName f st (advTok ts)
        let (g, ts2)  ← pGroupGraphPattern f st ts1
        let acc' : QueryPattern :=
          match acc with
          | .empty => .graph gn g
          | _      => .join acc (.graph gn g)
        let ts3 := if peekTok ts2 == Token.dot then advTok ts2 else ts2
        pGgpBody f st acc' filters true ts3
      | .service => do
        let ts1 := advTok ts
        let (silent, ts2) := match peekTok ts1 with
                             | .silent => (true, advTok ts1)
                             | _       => (false, ts1)
        match peekTok ts2 with
        | .var v => do
          let (g, ts3) ← pGroupGraphPattern f st (advTok ts2)
          let acc' : QueryPattern :=
            match acc with
            | .empty => .serviceVar v silent g
            | _      => .join acc (.serviceVar v silent g)
          let ts4 := if peekTok ts3 == Token.dot then advTok ts3 else ts3
          pGgpBody f st acc' filters true ts4
        | _ => do
          let (si, ts3) ← pServiceIri f st ts2
          let (g, ts4)  ← pGroupGraphPattern f st ts3
          let acc' : QueryPattern :=
            match acc with
            | .empty => .service si silent g
            | _      => .join acc (.service si silent g)
          let ts5 := if peekTok ts4 == Token.dot then advTok ts4 else ts4
          pGgpBody f st acc' filters true ts5
      | .filterKw => do
        let (e, ts1) ← pFilterExpr f st (advTok ts)
        let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
        pGgpBody f st acc (e :: filters) crossScope ts2
      | .bind => do
        let (_, ts1) ← expectTok .lparen (advTok ts)
        let (e, ts2) ← pExpr f st ts1
        let (_, ts3) ← expectTok .asKw ts2
        match peekTok ts3 with
        | .var v =>
          if ggpHasVar v acc then pErr "BIND variable already in scope" ts3
          else do
            let (_, ts4) ← expectTok .rparen (advTok ts3)
            let ts5 := if peekTok ts4 == Token.dot then advTok ts4 else ts4
            pGgpBody f st (.bind e v acc) filters crossScope ts5
        | _ => pErr "expected variable after AS" ts3
      | .values => do
        let (g, ts1) ← pValuesClause f st (advTok ts)
        let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
        pGgpBody f st (ggpJoin acc g) filters crossScope ts2
      | .lbrace => do
        -- A nested group, possibly a UNION chain.
        let (g, ts1) ← pGroupOrUnion f st ts
        if strOverlaps (ggpLabeledBnodes acc) (ggpLabeledBnodes g) then
          pErr "blank node label reused across nested group scope" ts
        else
          let acc' : QueryPattern := match acc with | .empty => g | _ => .join acc g
          let ts2 := if peekTok ts1 == Token.dot then advTok ts1 else ts1
          pGgpBody f st acc' filters true ts2
      | _ => .ok (filters.foldl (fun g e => .filter e g) acc, ts)

/-- [67] GroupOrUnionGraphPattern ::= GroupGraphPattern
( 'UNION' GroupGraphPattern )* — right-associated, as in the F*. -/
def pGroupOrUnion (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (g1, ts1) ← pGroupGraphPattern f st ts
    match peekTok ts1 with
    | .union => do
      let (g2, ts2) ← pGroupOrUnion f st (advTok ts1)
      .ok (.union g1 g2, ts2)
    | _ => .ok (g1, ts1)

/-- [68] Constraint ::= BrackettedExpression | BuiltInCall |
FunctionCall — the FILTER argument, with or without parentheses. -/
def pFilterExpr (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Expr × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      let (_, ts2) ← expectTok .rparen ts1
      .ok (e, ts2)
    | t =>
      if startsBuiltinCall t then pPrimaryExpr f st ts
      else pErr "expected '(' or built-in call after FILTER" ts

/-- [58] GraphGraphPattern's VarOrIri. -/
def pGraphName (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PatternTerm × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .var v => .ok (.var v, advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | _ => pErr "expected IRI or variable for GRAPH" ts

/-- The SERVICE endpoint IRI (Federated Query §2); the variable form
is handled in `pGgpBody` and never reaches here. -/
def pServiceIri (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (WfIri × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .var _ => pErr "internal: variable SERVICE endpoint reached parse_service_iri" ts
    | _      => pErr "expected IRI for SERVICE" ts

-- ### VALUES — [28] ValuesClause, [61]-[65] InlineData

/-- [65] DataBlockValue ::= iri | RDFLiteral | NumericLiteral |
BooleanLiteral | 'UNDEF' (plus, in 1.2, TripleTermData). -/
def pDataValue (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Option Term × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .undef => .ok (none, advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (some (.iri wi), advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (some (.iri wi), advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .str s => do
      let ts1 := advTok ts
      match peekTok ts1 with
      | .hathat =>
        let ts2 := advTok ts1
        (match peekTok ts2 with
         | .iri dt =>
           (match mkTypedLit? s dt with
            | some l => .ok (some (.literal l), advTok ts2)
            | none   => pErr "invalid typed literal" ts2)
         | .pname pn =>
           (match resolvePname st pn with
            | none    => pErr "unresolved prefix" ts2
            | some dt => match mkTypedLit? s dt with
                         | some l => .ok (some (.literal l), advTok ts2)
                         | none   => pErr "invalid typed literal" ts2)
         | _ => pErr "expected IRI after ^^" ts2)
      | .langtag lang   => .ok (some (.literal (mkLangLit s lang)), advTok ts1)
      | .langdir lang d => .ok (some (.literal (mkDirLangLit s lang d)), advTok ts1)
      | _               => .ok (some (.literal (mkPlainLit s)), ts1)
    | .integer n =>
      (match mkTypedLit? n xsdInteger with
       | some l => .ok (some (.literal l), advTok ts)
       | none   => pErr "invalid integer" ts)
    | .decimal d =>
      (match mkTypedLit? d xsdDecimal with
       | some l => .ok (some (.literal l), advTok ts)
       | none   => pErr "invalid decimal" ts)
    | .double d =>
      (match mkTypedLit? d xsdDouble with
       | some l => .ok (some (.literal l), advTok ts)
       | none   => pErr "invalid double" ts)
    | .trueKw =>
      (match mkTypedLit? "true" xsdBoolean with
       | some l => .ok (some (.literal l), advTok ts)
       | none   => pErr "invalid boolean" ts)
    | .falseKw =>
      (match mkTypedLit? "false" xsdBoolean with
       | some l => .ok (some (.literal l), advTok ts)
       | none   => pErr "invalid boolean" ts)
    | .ttOpen => do
      let (tt, ts1) ← pTtDataTriple f st (advTok ts)
      .ok (some tt, ts1)
    | _ => pErr "expected data value or UNDEF" ts

/-- SPARQL 1.2 TripleTermData: `<<( s p o )>>` as a GROUND data value.
The subject is restricted to an IRI, the predicate to an IRI or `a`,
and the object may nest another triple term. -/
def pTtDataTriple (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Term × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (s, ts1) ← pTtDataSubject f st ts
    let (p, ts2) ← pTtDataPredicate f st ts1
    let (o, ts3) ← pTtDataComponent f st ts2
    match expectTok .ttClose ts3 with
    | .error _     => pErr "expected ')>>' to close triple term" ts3
    | .ok (_, ts4) => .ok (.tripleTerm s p o, ts4)

/-- The IRI-only subject slot of a TripleTermData. -/
def pTtDataSubject (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Subject × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | _ => pErr "triple-term data subject must be an IRI" ts

/-- The predicate slot of a TripleTermData. -/
def pTtDataPredicate (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (WfIri × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .a => .ok (rdfTypeIri, advTok ts)
    | _  => pErr "triple-term data predicate must be an IRI" ts

/-- The object slot of a TripleTermData — any ground term. -/
def pTtDataComponent (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Term × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .bnode b => .ok (.bnode b, advTok ts)
    | .a       => .ok (.iri rdfTypeIri, advTok ts)
    | .str s => do
      let (pt, ts1) ← pRdfLiteralPt f st s (advTok ts)
      match pt with
      | .literal l => .ok (.literal l, ts1)
      | _          => pErr "expected literal" ts1
    | .integer n =>
      (match mkTypedLit? n xsdInteger with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid integer" ts)
    | .decimal d =>
      (match mkTypedLit? d xsdDecimal with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid decimal" ts)
    | .double d =>
      (match mkTypedLit? d xsdDouble with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid double" ts)
    | .trueKw =>
      (match mkTypedLit? "true" xsdBoolean with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid boolean" ts)
    | .falseKw =>
      (match mkTypedLit? "false" xsdBoolean with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid boolean" ts)
    | .ttOpen => pTtDataTriple f st (advTok ts)
    | _ => pErr "expected ground term inside triple-term data value" ts

/-- [64] DataBlockValue row: `( v1 v2 … )`. -/
def pValuesRowItems (fuel : Nat) (st : PState) (acc : List (Option Term))
    (ts : TStream) : Except ParseError (List (Option Term) × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .rparen => .ok (acc.reverse, advTok ts)
    | _ => do
      let (v, ts1) ← pDataValue f st ts
      pValuesRowItems f st (v :: acc) ts1

/-- One parenthesised row. -/
def pValuesRow (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (List (Option Term) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (_, ts1) ← expectTok .lparen ts
    pValuesRowItems f st [] ts1

/-- The row list of the multi-variable VALUES form. -/
def pValuesRows (fuel : Nat) (st : PState) (acc : List (List (Option Term)))
    (ts : TStream) : Except ParseError (List (List (Option Term)) × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .lparen => do
      let (row, ts1) ← pValuesRow f st ts
      pValuesRows f st (row :: acc) ts1
    | _ => .ok (acc.reverse, ts)

/-- The `( ?x ?y )` variable list. -/
def pValuesVars (fuel : Nat) (acc : List VarName) (ts : TStream) : Except ParseError (List VarName × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .var v => pValuesVars f (v :: acc) (advTok ts)
    | _      => .ok (acc.reverse, ts)

/-- The single-variable form's brace-delimited value list. -/
def pSingleVarValues (fuel : Nat) (st : PState) (acc : List (Option Term))
    (ts : TStream) : Except ParseError (List (Option Term) × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .rbrace => .ok (acc.reverse, ts)
    | _ => do
      let (v, ts1) ← pDataValue f st ts
      pSingleVarValues f st (v :: acc) ts1

/-- [61] InlineData — both forms. Rejects a repeated variable and a
row whose arity does not match the variable list. -/
def pValuesClause (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v => do
      let (_, ts1)    ← expectTok .lbrace (advTok ts)
      let (vals, ts2) ← pSingleVarValues f st [] ts1
      let (_, ts3)    ← expectTok .rbrace ts2
      .ok (.values [v] (vals.map (fun x => [x])), ts3)
    | .lparen => do
      let (vars, ts1) ← pValuesVars f [] (advTok ts)
      let (_, ts2)    ← expectTok .rparen ts1
      let (_, ts3)    ← expectTok .lbrace ts2
      let (rows, ts4) ← pValuesRows f st [] ts3
      let (_, ts5)    ← expectTok .rbrace ts4
      if varListHasDup vars then pErr "duplicate variable in VALUES clause" ts
      else if rows.all (fun r => r.length == vars.length) then .ok (.values vars rows, ts5)
      else pErr "VALUES row has wrong number of terms" ts4
    | _ => pErr "expected variable or '(' after VALUES" ts

-- ### Triples — [75]-[87]

/-- [129] RDFLiteral in TERM position. -/
def pRdfLiteralPt (fuel : Nat) (st : PState) (s : String) (ts : TStream) : Except ParseError (PatternTerm × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .hathat =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .iri dt =>
         (match mkTypedLit? s dt with
          | some l => .ok (.literal l, advTok ts1)
          | none   => pErr "invalid typed literal" ts1)
       | .pname pn =>
         (match resolvePname st pn with
          | none    => pErr "unresolved prefix" ts1
          | some dt => match mkTypedLit? s dt with
                       | some l => .ok (.literal l, advTok ts1)
                       | none   => pErr "invalid typed literal" ts1)
       | _ => pErr "expected IRI after ^^" ts1)
    | .langtag lang   => .ok (.literal (mkLangLit s lang), advTok ts)
    | .langdir lang d => .ok (.literal (mkDirLangLit s lang d), advTok ts)
    | _               => .ok (.literal (mkPlainLit s), ts)

/-- [132] NumericLiteralPositive / [133] NumericLiteralNegative — a
sign glued onto the next numeric token. -/
def pSignedNumericPt (fuel : Nat) (sign : String) (ts : TStream) : Except ParseError (PatternTerm × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .integer n =>
      (match mkTypedLit? (sign ++ n) xsdInteger with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid integer literal" ts)
    | .decimal d =>
      (match mkTypedLit? (sign ++ d) xsdDecimal with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid decimal literal" ts)
    | .double d =>
      (match mkTypedLit? (sign ++ d) xsdDouble with
       | some l => .ok (.literal l, advTok ts)
       | none   => pErr "invalid double literal" ts)
    | _ => pErr "expected signed numeric literal" ts

/-- [80] Object — a term plus any triples its sugar generated
(a blank-node property list, a collection). -/
def pObjectWithExtras (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternTerm × QueryPattern) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v => .ok ((.var v, .empty), advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok ((.iri wi, .empty), advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok ((.iri wi, .empty), advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .bnode b => .ok ((.bnode b, .empty), advTok ts)
    | .str s => do
      let (pt, ts1) ← pRdfLiteralPt f st s (advTok ts)
      .ok ((pt, .empty), ts1)
    | .integer n =>
      (match mkTypedLit? n xsdInteger with
       | some l => .ok ((.literal l, .empty), advTok ts)
       | none   => pErr "invalid integer literal" ts)
    | .decimal d =>
      (match mkTypedLit? d xsdDecimal with
       | some l => .ok ((.literal l, .empty), advTok ts)
       | none   => pErr "invalid decimal literal" ts)
    | .double d =>
      (match mkTypedLit? d xsdDouble with
       | some l => .ok ((.literal l, .empty), advTok ts)
       | none   => pErr "invalid double literal" ts)
    | .trueKw =>
      (match mkTypedLit? "true" xsdBoolean with
       | some l => .ok ((.literal l, .empty), advTok ts)
       | none   => pErr "invalid boolean literal" ts)
    | .falseKw =>
      (match mkTypedLit? "false" xsdBoolean with
       | some l => .ok ((.literal l, .empty), advTok ts)
       | none   => pErr "invalid boolean literal" ts)
    | .plus => do
      let (pt, ts1) ← pSignedNumericPt f "+" (advTok ts)
      .ok ((pt, .empty), ts1)
    | .minusOp => do
      let (pt, ts1) ← pSignedNumericPt f "-" (advTok ts)
      .ok ((pt, .empty), ts1)
    | .a => .ok ((.iri rdfTypeIri, .empty), advTok ts)
    | .lbracket =>
      -- [99] BlankNodePropertyList / [138] ANON.
      let bid := freshBnodeId ts
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .rbracket => .ok ((.bnode bid, .empty), advTok ts1)
       | _ =>
         (do let (extras, ts2) ← pPredObjList f st (.bnode bid) .empty ts1
             match expectTok .rbracket ts2 with
             | .error _     => pErr "expected ']' after blank node property list" ts2
             | .ok (_, ts3) => .ok ((.bnode bid, extras), ts3)))
    | .lparen => pCollection f st (advTok ts)
    | .ttOpen => pTripleTermPattern f st (advTok ts)
    | .ttBareOpen => do
      -- SPARQL 1.2 bare reified triple in object position; also the
      -- route by which one nests inside a triple-term COMPONENT slot,
      -- via pTtPatComponent.
      let (rp, ts1) ← pReifiedTriplePattern f st (advTok ts)
      .ok ((patternSubjectToTerm rp.1, rp.2), ts1)
    | _ => pErr "expected object" ts

/-- SPARQL 1.2: a triple-term PATTERN `<<( s p o )>>`; the opener is
consumed. A collection inside a triple term is a syntax error. -/
def pTripleTermPattern (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternTerm × QueryPattern) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (s, ts1) ← pTtPatComponent f st ts
    let (p, ts2) ← pTtPatPredicate f st ts1
    let (o, ts3) ← pTtPatComponent f st ts2
    match expectTok .ttClose ts3 with
    | .error _     => pErr "expected ')>>' to close triple term" ts3
    | .ok (_, ts4) => .ok ((.tripleTerm s.1 p o.1, ggpJoin s.2 o.2), ts4)

/-- A subject / object component of a triple-term pattern. -/
def pTtPatComponent (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternTerm × QueryPattern) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .lparen => pErr "RDF collection not allowed inside a triple term" ts
    | _       => pObjectWithExtras f st ts

/-- The PREDICATE slot of a triple-term pattern: a variable, IRI or
`a` — never a blank node, literal, or nested triple term. -/
def pTtPatPredicate (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PatternTerm × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .var v => .ok (.var v, advTok ts)
    | .a     => .ok (.iri rdfTypeIri, advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | _ => pErr "triple-term predicate must be a variable or IRI" ts

/-- SPARQL 1.2: a bare reified triple `<< s p o (~ reifier)? >>`; the
opening `<<` is consumed. Subject/object components and the predicate
reuse the SAME restricted parsers as the paren'd triple-term form —
collections are rejected, the predicate is var/IRI/`a` only. A
reified triple denotes its REIFIER (the `~`-named var/IRI/blank node,
else a fresh blank node), which takes the triple's place in the
enclosing position; it does NOT itself assert `s p o` (RDF 1.2
reification is deliberately not assertion). It emits ONE extra triple
pattern `reifier rdf:reifies <<( s p o )>>`
(`parse_reified_triple_pattern`). -/
def pReifiedTriplePattern (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternSubject × QueryPattern) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (s, ts1) ← pTtPatComponent f st ts
    let (p, ts2) ← pTtPatPredicate f st ts1
    let (o, ts3) ← pTtPatComponent f st ts2
    let exSo := ggpJoin s.2 o.2
    let tt : PatternTerm := .tripleTerm s.1 p o.1
    match peekTok ts3 with
    | .tilde => do
      let (reif, ts5) ← pReifierId st (advTok ts3)
      match expectTok .ttBareClose ts5 with
      | .error _     => pErr "expected '>>' to close reified triple" ts5
      | .ok (_, ts6) =>
        let reifiesTp : TriplePattern := { s := reif, p := .iri rdfReifiesIri, o := tt }
        .ok ((reif, ggpJoin exSo (.bgp [reifiesTp])), ts6)
    | _ =>
      match expectTok .ttBareClose ts3 with
      | .error _     => pErr "expected '>>' to close reified triple" ts3
      | .ok (_, ts4) =>
        let reif : PatternSubject := .bnode (freshBnodeId ts3)
        let reifiesTp : TriplePattern := { s := reif, p := .iri rdfReifiesIri, o := tt }
        .ok ((reif, ggpJoin exSo (.bgp [reifiesTp])), ts4)

/-- SPARQL 1.2: the annotation sequence after a simple-predicate
object: `( ('~' VarOrReifierId?) | ('{|' PredicateObjectList '|}') )*`,
reifying the triple {baseS, baseP, baseO} (already added to the
caller's BGP). A `~` mints/records a reifier, emits its `rdf:reifies`
triple immediately, and becomes the PENDING reifier for an immediately
following `{| … |}` block; a block with no pending reifier mints its
own fresh blank node. Reachable only from `pObjectListSimple`, never
`pObjectListPath` — the restriction the negative suite's
annotated-*-path fixtures check (`parse_annotations`). -/
def pAnnotations (fuel : Nat) (st : PState) (baseS : PatternSubject)
    (baseP baseO : PatternTerm) (pending : Option PatternSubject) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (.empty, ts)
  | f + 1 =>
    let tt : PatternTerm := .tripleTerm (patternSubjectToTerm baseS) baseP baseO
    match peekTok ts with
    | .tilde => do
      let (rsubj, ts2) ← pReifierId st (advTok ts)
      let reifiesTp : TriplePattern := { s := rsubj, p := .iri rdfReifiesIri, o := tt }
      let (rest, ts3) ← pAnnotations f st baseS baseP baseO (some rsubj) ts2
      .ok (ggpJoin (.bgp [reifiesTp]) rest, ts3)
    | .annotOpen => do
      let ts1 := advTok ts
      let (rsubj, pre) :=
        match pending with
        | some r => (r, QueryPattern.empty)
        | none   =>
          let r : PatternSubject := .bnode (freshBnodeId ts)
          (r, QueryPattern.bgp [{ s := r, p := .iri rdfReifiesIri, o := tt }])
      let (blk, ts2) ← pPredObjList f st rsubj .empty ts1
      match expectTok .annotClose ts2 with
      | .error _     => pErr "expected '|}' to close annotation block" ts2
      | .ok (_, ts3) => do
        let (rest, ts4) ← pAnnotations f st baseS baseP baseO none ts3
        .ok (ggpJoin (ggpJoin pre blk) rest, ts4)
    | _ => .ok (.empty, ts)

/-- [102] Collection ::= '(' GraphNode+ ')' — desugared into an
`rdf:first` / `rdf:rest` chain, `rdf:nil` when empty. -/
def pCollection (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternTerm × QueryPattern) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .rparen => .ok ((.iri rdfNilIri, .empty), advTok ts)
    | _ => do
      let (item, ts1) ← pObjectWithExtras f st ts
      let bid  := freshBnodeId ts
      let bsub : PatternSubject := .bnode bid
      let (rest, ts2) ← pCollection f st ts1
      let firstT : TriplePattern := { s := bsub, p := .iri rdfFirstIri, o := item.1 }
      let restT  : TriplePattern := { s := bsub, p := .iri rdfRestIri,  o := rest.1 }
      let triples : QueryPattern := .bgp [firstT, restT]
      .ok ((.bnode bid, ggpJoin (ggpJoin triples item.2) rest.2), ts2)

/-- [78] Verb / [88] Path in predicate position. A path that turned out
to be a single IRI is reported as a plain term, so a simple triple
stays a BGP entry rather than becoming a `propertyPath` node. -/
def pVerb (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternTerm ⊕ PropertyPath) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v => .ok (.inl (.var v), advTok ts)
    | _ => do
      let (pp, ts1) ← pPathAlternative f st ts
      match pp with
      | .iri i => .ok (.inl (.iri i), ts1)
      | _      => .ok (.inr pp, ts1)

/-- [89] PathAlternative ::= PathSequence ( '|' PathSequence )*. -/
def pPathAlternative (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (p1, ts1) ← pPathSequence f st ts
    pPathAltRest f st p1 ts1

/-- The left-associative `|` tail. -/
def pPathAltRest (fuel : Nat) (st : PState) (acc : PropertyPath) (ts : TStream) :
    Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    match peekTok ts with
    | .pipe => do
      let (p2, ts1) ← pPathSequence f st (advTok ts)
      pPathAltRest f st (.alternative acc p2) ts1
    | _ => .ok (acc, ts)

/-- [90] PathSequence ::= PathEltOrInverse ( '/' PathEltOrInverse )*. -/
def pPathSequence (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (p1, ts1) ← pPathEltOrInverse f st ts
    pPathSeqRest f st p1 ts1

/-- The left-associative `/` tail. -/
def pPathSeqRest (fuel : Nat) (st : PState) (acc : PropertyPath) (ts : TStream) :
    Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    match peekTok ts with
    | .slash => do
      let (p2, ts1) ← pPathEltOrInverse f st (advTok ts)
      pPathSeqRest f st (.sequence acc p2) ts1
    | _ => .ok (acc, ts)

/-- [92] PathEltOrInverse ::= PathElt | '^' PathElt. -/
def pPathEltOrInverse (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .caret => do
      let (p, ts1) ← pPathElt f st (advTok ts)
      .ok (.inverse p, ts1)
    | _ => pPathElt f st ts

/-- [91] PathElt ::= PathPrimary PathMod?  with
[93] PathMod ::= '?' | '*' | '+'. -/
def pPathElt (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (p, ts1) ← pPathPrimary f st ts
    match peekTok ts1 with
    | .star  => .ok (.zeroOrMore p, advTok ts1)
    | .plus  => .ok (.oneOrMore p, advTok ts1)
    | .qmark => .ok (.zeroOrOne p, advTok ts1)
    | _      => .ok (p, ts1)

/-- [94] PathPrimary ::= iri | 'a' | '!' PathNegatedPropertySet
| '(' Path ')'. -/
def pPathPrimary (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .a    => .ok (.iri rdfTypeIri, advTok ts)
    | .bang => pPathNegated f st (advTok ts)
    | .lparen => do
      let (p, ts1) ← pPathAlternative f st (advTok ts)
      match expectTok .rparen ts1 with
      | .error _     => pErr "expected ')' after path" ts1
      | .ok (_, ts2) => .ok (p, ts2)
    | _ => pErr "expected path primary" ts

/-- [95] PathNegatedPropertySet ::= PathOneInPropertySet
| '(' ( PathOneInPropertySet ( '|' PathOneInPropertySet )* )? ')'. -/
def pPathNegated (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .lparen => do
      let (ps, ts1) ← pPathOneInSetList f st (advTok ts)
      match expectTok .rparen ts1 with
      | .error _     => pErr "expected ')' in negated path set" ts1
      | .ok (_, ts2) => .ok (.negatedSet ps, ts2)
    | _ => do
      let (p, ts1) ← pPathOneInSet f st ts
      .ok (.negatedSet [p], ts1)

/-- [96] PathOneInPropertySet ::= iri | 'a' | '^' ( iri | 'a' ). -/
def pPathOneInSet (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PropertyPath × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | _ + 1 =>
    match peekTok ts with
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (.iri wi, advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .a => .ok (.iri rdfTypeIri, advTok ts)
    | .caret =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .iri i =>
         (match mkIri? i with
          | some wi => .ok (.inverse (.iri wi), advTok ts1)
          | none    => pErr "invalid IRI" ts1)
       | .pname pn =>
         (match resolvePnameIri st pn with
          | some wi => .ok (.inverse (.iri wi), advTok ts1)
          | none    => pErr "unresolved prefix" ts1)
       | .a => .ok (.inverse (.iri rdfTypeIri), advTok ts1)
       | _  => pErr "expected IRI or 'a' after ^ in negated set" ts1)
    | _ => pErr "expected path element in negated set" ts

/-- The `|`-separated members of a negated property set. -/
def pPathOneInSetList (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (List PropertyPath × TStream) :=
  match fuel with
  | 0     => .ok ([], ts)
  | f + 1 => do
    let (p, ts1) ← pPathOneInSet f st ts
    match peekTok ts1 with
    | .pipe => do
      let (ps, ts2) ← pPathOneInSetList f st (advTok ts1)
      .ok (p :: ps, ts2)
    | _ => .ok ([p], ts1)

/-- [79] ObjectList for a simple (non-path) predicate. -/
def pObjectListSimple (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pred : PatternTerm) (acc : QueryPattern) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 => do
    let (obj, ts1) ← pObjectWithExtras f st ts
    let acc1 := ggpAddTriple acc { s := subj, p := pred, o := obj.1 }
    let acc2 := ggpJoin acc1 obj.2
    -- SPARQL 1.2: this object may be followed by an annotation
    -- sequence (`~ reifier` and/or `{| … |}`) reifying THIS triple.
    -- Only on the simple-verb path, never pObjectListPath.
    let (ann, ts2) ← pAnnotations f st subj pred obj.1 none ts1
    let acc3 := ggpJoin acc2 ann
    match peekTok ts2 with
    | .comma => pObjectListSimple f st subj pred acc3 (advTok ts2)
    | _      => .ok (acc3, ts2)

/-- [86] ObjectListPath for a property-path predicate. -/
def pObjectListPath (fuel : Nat) (st : PState) (subj : PatternSubject)
    (pp : PropertyPath) (acc : QueryPattern) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 => do
    let (obj, ts1) ← pObjectWithExtras f st ts
    let acc1 := ggpAddPp acc subj pp obj.1
    let acc2 := ggpJoin acc1 obj.2
    match peekTok ts1 with
    | .comma => pObjectListPath f st subj pp acc2 (advTok ts1)
    | _      => .ok (acc2, ts1)

/-- [83] PropertyListPathNotEmpty ::= Verb ObjectList
( ';' ( Verb ObjectList )? )*. -/
def pPredObjList (fuel : Nat) (st : PState) (subj : PatternSubject)
    (acc : QueryPattern) (ts : TStream) : Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 => do
    let (verb, ts1) ← pVerb f st ts
    let (acc1, ts2) ←
      match verb with
      | .inl pred => pObjectListSimple f st subj pred acc ts1
      | .inr pp   => pObjectListPath f st subj pp acc ts1
    match peekTok ts2 with
    | .semi =>
      let ts3 := advTok ts2
      if endsPredObjList (peekTok ts3) then .ok (acc1, ts3)
      else pPredObjList f st subj acc1 ts3
    | _ => .ok (acc1, ts2)

/-- [75] TriplesBlock's subject, plus any triples its sugar generated
and a flag saying whether a predicate-object list is OPTIONAL
(`[ … ]` already forms complete triples on its own). -/
def pSubjectWithExtras (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((PatternSubject × QueryPattern × Bool) × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v => .ok ((.var v, .empty, false), advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => .ok ((.iri wi, .empty, false), advTok ts)
       | none    => pErr "invalid IRI" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok ((.iri wi, .empty, false), advTok ts)
       | none    => pErr "unresolved prefix" ts)
    | .bnode b => .ok ((.bnode b, .empty, false), advTok ts)
    | .lbracket =>
      let bid := freshBnodeId ts
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .rbracket => .ok ((.bnode bid, .empty, false), advTok ts1)
       | _ =>
         (do let (extras, ts2) ← pPredObjList f st (.bnode bid) .empty ts1
             match expectTok .rbracket ts2 with
             | .error _     => pErr "expected ']' after blank node property list" ts2
             | .ok (_, ts3) => .ok ((.bnode bid, extras, true), ts3)))
    | .lparen => do
      let (pt, ts1) ← pCollection f st (advTok ts)
      match patternTermToSubject pt.1 with
      | some s => .ok ((s, pt.2, false), ts1)
      | none   => pErr "collection cannot be used as subject" ts
    | .ttOpen => do
      let (pt, ts1) ← pTripleTermPattern f st (advTok ts)
      match patternTermToSubject pt.1 with
      | some s => .ok ((s, pt.2, false), ts1)
      | none   => pErr "invalid triple-term subject" ts
    | .ttBareOpen => do
      -- SPARQL 1.2 bare reified triple in subject position. Like
      -- `[ … ]`, it can stand alone as a complete triples statement
      -- (pattern-08.rq) — the predicate-object list is OPTIONAL.
      let (rp, ts1) ← pReifiedTriplePattern f st (advTok ts)
      .ok ((rp.1, rp.2, true), ts1)
    | _ => pErr "expected subject" ts

/-- [55] TriplesBlock ::= TriplesSameSubjectPath ( '.' TriplesBlock? )?.
A term token immediately after a completed statement, with no `.`, is
the rejection the F* words "expected dot between triples". -/
def pTriplesBlock (fuel : Nat) (st : PState) (acc : QueryPattern) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    match pSubjectWithExtras f st ts with
    | .error e =>
      (match acc with
       | .empty => .error e
       | _      => .ok (acc, ts))
    | .ok ((subj, subjExtras, predObjOptional), ts1) =>
      let acc0 := ggpJoin acc subjExtras
      let r : Except ParseError (QueryPattern × TStream) :=
        match pPredObjList f st subj acc0 ts1 with
        | .ok res  => .ok res
        | .error e => if predObjOptional then .ok (acc0, ts1) else .error e
      match r with
      | .error e => .error e
      | .ok (acc1, ts2) =>
        match peekTok ts2 with
        | .dot =>
          let ts3 := advTok ts2
          if startsTriples (peekTok ts3) then pTriplesBlock f st acc1 ts3
          else .ok (acc1, ts3)
        | t =>
          if startsTriples t then pErr "expected dot between triples" ts2
          else .ok (acc1, ts2)

-- ### Query forms — [1]-[27]

/-- [2] Query ::= Prologue ( SelectQuery | ConstructQuery |
DescribeQuery | AskQuery ) ValuesClause. `initBase` is the BASE in
scope before the prologue (§4.1.1.1: a service MAY use the request
URI); the prologue's own BASE overrides it. -/
def pSelectQuery (fuel : Nat) (st : PState) (initBase : Option String) (ts : TStream) :
    Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (stb, ts1) ← pPrologue f { st with base := initBase } ts
    let ts2 := resolveIriTokens stb.base ts1
    match peekTok ts2 with
    | .select    => pSelectBody f stb ts2
    | .ask       => pAskBody f stb ts2
    | .construct => pConstructBody f stb ts2
    | .describe  => pDescribeBody f stb ts2
    | _ => pErr "expected SELECT, ASK, CONSTRUCT, or DESCRIBE" ts2

/-- [4] Prologue ::= ( BaseDecl | PrefixDecl )*, plus the SPARQL 1.2
[4a] VersionDecl. A relative PREFIX namespace resolves against the
BASE in force at that point. -/
def pPrologue (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (PState × TStream) :=
  match fuel with
  | 0     => .ok (st, ts)
  | f + 1 =>
    match peekTok ts with
    | .prefixKw =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .pname pn =>
         let (pfx, loc) := splitPname pn
         if loc.length > 0 then
           pErr "invalid PREFIX name (must be prefix: with no local part)" ts1
         else
           let ts2 := advTok ts1
           (match peekTok ts2 with
            | .iri iri =>
              let abs := if isIri iri then iri else resolveAgainst? st.base iri
              if isIri abs then
                pPrologue f { st with prefixes := (pfx, abs) :: st.prefixes } (advTok ts2)
              else pErr "invalid prefix IRI" ts2
            | _ => pErr "expected IRI after PREFIX name" ts2)
       | _ => pErr "expected prefix name after PREFIX" ts1)
    | .baseKw =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .iri iri =>
         if isIri iri then pPrologue f { st with base := some iri } (advTok ts1)
         else pErr "invalid BASE IRI" ts1
       | _ => pErr "expected IRI after BASE" ts1)
    | .versionKw =>
      -- SPARQL 1.2: the declared version is accepted and not threaded
      -- further; no fixture exercises version-dependent parsing.
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .str _ => pPrologue f st (advTok ts1)
       | _      => pErr "expected string literal after VERSION" ts1)
    | _ => .ok (st, ts)

/-- [7] SelectClause ::= 'SELECT' ( 'DISTINCT' | 'REDUCED' )?
( ( Var | '(' Expression 'AS' Var ')' )+ | '*' ). -/
def pSelectVars (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (SelectClause × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .star => .ok (.all, advTok ts)
    | _ => do
      let (items, ts1) ← pSelectItems f st [] ts
      if items.length == 0 then pErr "expected select variables" ts
      else .ok (.vars items, ts1)

/-- The projection item list, rejecting a repeated target name. -/
def pSelectItems (fuel : Nat) (st : PState) (acc : List SelectItem) (ts : TStream) :
    Except ParseError (List SelectItem × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .var v =>
      if selectItemsHasVar v acc then pErr "duplicate variable in SELECT" ts
      else pSelectItems f st (.var v :: acc) (advTok ts)
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      let (_, ts2) ← expectTok .asKw ts1
      match peekTok ts2 with
      | .var v =>
        if selectItemsHasVar v acc then pErr "duplicate variable in SELECT" ts2
        else do
          let (_, ts3) ← expectTok .rparen (advTok ts2)
          pSelectItems f st (.expr e v :: acc) ts3
      | _ => pErr "expected variable after AS" ts2
    | _ => .ok (acc.reverse, ts)

/-- [13]-[16] DatasetClause ::= 'FROM' ( DefaultGraphClause |
NamedGraphClause ). -/
def pDatasetClauses (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (List DatasetClause × TStream) :=
  match fuel with
  | 0     => .ok ([], ts)
  | f + 1 =>
    match peekTok ts with
    | .fromKw =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .named =>
         let ts2 := advTok ts1
         (match peekTok ts2 with
          | .iri i =>
            (match mkIri? i with
             | some wi => (do let (rest, ts3) ← pDatasetClauses f st (advTok ts2)
                              .ok (.named wi :: rest, ts3))
             | none    => pErr "invalid IRI after FROM NAMED" ts2)
          | .pname pn =>
            (match resolvePnameIri st pn with
             | some wi => (do let (rest, ts3) ← pDatasetClauses f st (advTok ts2)
                              .ok (.named wi :: rest, ts3))
             | none    => pErr "unresolved prefix in FROM NAMED" ts2)
          | _ => pErr "expected IRI after FROM NAMED" ts2)
       | .iri i =>
         (match mkIri? i with
          | some wi => (do let (rest, ts2) ← pDatasetClauses f st (advTok ts1)
                           .ok (.default wi :: rest, ts2))
          | none    => pErr "invalid IRI after FROM" ts1)
       | .pname pn =>
         (match resolvePnameIri st pn with
          | some wi => (do let (rest, ts2) ← pDatasetClauses f st (advTok ts1)
                           .ok (.default wi :: rest, ts2))
          | none    => pErr "unresolved prefix in FROM" ts1)
       | _ => pErr "expected IRI or NAMED after FROM" ts1)
    | _ => .ok ([], ts)

/-- [20] GroupCondition ::= BuiltInCall | FunctionCall
| '(' Expression ( 'AS' Var )? ')' | Var. -/
def pGroupCondition (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (GroupCondition × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .var v => .ok (.var v, advTok ts)
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      match peekTok ts1 with
      | .asKw =>
        let ts2 := advTok ts1
        (match peekTok ts2 with
         | .var v => (do let (_, ts3) ← expectTok .rparen (advTok ts2)
                         .ok (GroupCondition.expr e (some v), ts3))
         | _ => pErr "expected variable after AS" ts2)
      | .rparen => .ok (GroupCondition.expr e none, advTok ts1)
      | _       => pErr "expected ')' or AS in GROUP BY" ts1
    | _ => do
      let (e, ts1) ← pExpr f st ts
      .ok (GroupCondition.expr e none, ts1)

/-- [19] GroupClause's condition list. -/
def pGroupByList (fuel : Nat) (st : PState) (acc : List GroupCondition) (ts : TStream) :
    Except ParseError (List GroupCondition × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    if startsGroupCondition (peekTok ts) then do
      let (gc, ts1) ← pGroupCondition f st ts
      pGroupByList f st (gc :: acc) ts1
    else .ok (acc.reverse, ts)

/-- [24] OrderCondition ::= ( ( 'ASC' | 'DESC' ) BrackettedExpression )
| ( Constraint | Var ). The F* also accepts `ASC` without parentheses. -/
def pOrderCondition (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (OrderCondition × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .asc | .desc =>
      let desc := peekTok ts == Token.desc
      let mk := fun (e : Expr) => if desc then OrderCondition.desc e else OrderCondition.asc e
      let ts1 := advTok ts
      (match expectTok .lparen ts1 with
       | .error _ => (do let (e, ts2) ← pExpr f st ts1
                         .ok (mk e, ts2))
       | .ok (_, ts2) => (do let (e, ts3) ← pExpr f st ts2
                             let (_, ts4) ← expectTok .rparen ts3
                             .ok (mk e, ts4)))
    | .var v => .ok (.asc (.var v), advTok ts)
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      let (_, ts2) ← expectTok .rparen ts1
      .ok (.asc e, ts2)
    | _ => do
      let (e, ts1) ← pExpr f st ts
      .ok (.asc e, ts1)

/-- [23] OrderClause's condition list. -/
def pOrderByList (fuel : Nat) (st : PState) (acc : List OrderCondition) (ts : TStream) :
    Except ParseError (List OrderCondition × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    if startsOrderCondition (peekTok ts) then do
      let (oc, ts1) ← pOrderCondition f st ts
      pOrderByList f st (oc :: acc) ts1
    else .ok (acc.reverse, ts)

/-- [21] HavingClause ::= 'HAVING' HavingCondition+. -/
def pHavingList (fuel : Nat) (st : PState) (acc : List Expr) (ts : TStream) :
    Except ParseError (List Expr × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .lparen => do
      let (e, ts1) ← pExpr f st (advTok ts)
      let (_, ts2) ← expectTok .rparen ts1
      pHavingList f st (e :: acc) ts2
    | t =>
      if startsHavingCondition t then do
        let (e, ts1) ← pPrimaryExpr f st ts
        pHavingList f st (e :: acc) ts1
      else .ok (acc.reverse, ts)

/-- [18] SolutionModifier ::= GroupClause? HavingClause? OrderClause?
LimitOffsetClauses?. Returns the modifier together with GROUP BY and
HAVING, which live outside `SolutionModifier` in the AST.

Per [25] LimitOffsetClauses either order of LIMIT and OFFSET parses:
try LIMIT, then OFFSET, then LIMIT again if it was not already seen. -/
def pSolutionModifier (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError ((SolutionModifier × Option (List GroupCondition) × List Expr) × TStream) :=
  match fuel with
  | 0     => .ok (({}, none, []), ts)
  | f + 1 =>
    let (gb, tsA) :=
      match peekTok ts with
      | .group =>
        let ts1 := advTok ts
        (match peekTok ts1 with
         | .by => (match pGroupByList f st [] (advTok ts1) with
                   | .ok (conds, ts2) => (some conds, ts2)
                   | .error _         => (none, ts))
         | _ => (none, ts))
      | _ => (none, ts)
    let (hv, tsB) :=
      match peekTok tsA with
      | .having => (match pHavingList f st [] (advTok tsA) with
                    | .ok (conds, ts1) => (conds, ts1)
                    | .error _         => ([], tsA))
      | _ => ([], tsA)
    let (ob, tsC) :=
      match peekTok tsB with
      | .order =>
        let ts1 := advTok tsB
        (match peekTok ts1 with
         | .by => (match pOrderByList f st [] (advTok ts1) with
                   | .ok (conds, ts2) => (some conds, ts2)
                   | .error _         => (none, tsB))
         | _ => (none, tsB))
      | _ => (none, tsB)
    let (limit1, tsD) := takeLimit tsC
    let (offset, tsE) := takeOffset tsD
    let (limit, tsF)  := match limit1 with
                         | some _ => (limit1, tsE)
                         | none   => takeLimit tsE
    .ok (({ orderBy := ob, distinct := false, reduced := false,
            offset := offset, limit := limit }, gb, hv), tsF)
where
  /-- [26] LimitClause. -/
  takeLimit (ts : TStream) : Option Nat × TStream :=
    match peekTok ts with
    | .limit =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .integer n => (match parseIntStr n with
                        | some i => if i ≥ 0 then (some i.toNat, advTok ts1) else (none, ts1)
                        | none   => (none, ts1))
       | _ => (none, ts1))
    | _ => (none, ts)
  /-- [27] OffsetClause. -/
  takeOffset (ts : TStream) : Option Nat × TStream :=
    match peekTok ts with
    | .offset =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .integer n => (match parseIntStr n with
                        | some i => if i ≥ 0 then (some i.toNat, advTok ts1) else (none, ts1)
                        | none   => (none, ts1))
       | _ => (none, ts1))
    | _ => (none, ts)

/-- [7]-[9] SelectQuery. All four SELECT-level well-formedness
rejections live here — see the module header's table. -/
def pSelectBody (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let ts1 := advTok ts                       -- consume SELECT
    let (dist, red, ts2) :=
      match peekTok ts1 with
      | .distinct => (true, false, advTok ts1)
      | .reduced  => (false, true, advTok ts1)
      | _         => (false, false, ts1)
    let (sel, ts3) ← pSelectVars f st ts2
    let (ds, ts4)  ← pDatasetClauses f st ts3
    let ts5 := if peekTok ts4 == Token.whereKw then advTok ts4 else ts4
    let (pattern, ts6) ← pGroupGraphPattern f st ts5
    let (sm, ts7) ← pSolutionModifier f st ts6
    let md := sm.1
    let gb := sm.2.1
    let hv := sm.2.2
    -- §18.2.4.1: SELECT * cannot be combined with GROUP BY.
    if (match sel with | .all => true | _ => false) && gb.isSome then
      pErr "SELECT * not allowed with GROUP BY" ts6
    else
      let ungroupedWithGroupBy : Bool :=
        match gb with
        | none => false
        | some gcs =>
          let isGrouped := fun (v : VarName) =>
            gcs.any (fun gc => match gc with
                               | .var gv        => gv == v
                               | .expr _ (some gv) => gv == v
                               | _              => false)
          match sel with
          | .vars items =>
            !items.all (fun i => match i with
                                 | .var v    => isGrouped v
                                 | .expr e _ => !exprHasUngroupedVar isGrouped e)
          | _ => false
      -- §18.2.4.1: with an aggregate in the projection and no GROUP BY,
      -- every other projected expression must itself be aggregated.
      let ungroupedImplicit : Bool :=
        match gb with
        | some _ => false
        | none =>
          match sel with
          | .vars items =>
            let hasAgg := items.any (fun i => match i with
                                              | .expr (.aggregate _ _ _) _ => true
                                              | _ => false)
            -- The F* writes this as `not (for_all p items)` with
            -- `p (SI_Var _) = false`, so a BARE PROJECTED VARIABLE
            -- alongside an aggregate is itself ungrouped (agg10.rq:
            -- `SELECT ?P (COUNT(?O) AS ?C) WHERE { ?S ?P ?O }`). The
            -- negation has to be pushed through both arms.
            let hasUngrouped :=
              items.any (fun i => match i with
                                  | .var _    => true
                                  | .expr e _ => exprHasUngroupedVar (fun _ => false) e)
            hasAgg && hasUngrouped
          | _ => false
      if ungroupedWithGroupBy || ungroupedImplicit then
        pErr "SELECT projects ungrouped variable" ts6
      else if (match sel with
               | .vars items =>
                 !items.all (fun i => match i with
                                      | .expr _ v => !ggpHasVar v pattern
                                      | _         => true)
               | _ => false) then
        pErr "SELECT expression aliases variable already in scope" ts6
      else do
        -- [28] the trailing VALUES clause, joined onto the WHERE result.
        let (vals, ts8) :=
          match peekTok ts7 with
          | .values => (match pValuesClause f st (advTok ts7) with
                        | .ok (g, t) => (some g, t)
                        | .error _   => (none, ts7))
          | _ => (none, ts7)
        let pat := match vals with
                   | some g => ggpJoin pattern g
                   | none   => pattern
        .ok (Query.mk (.select sel) ds pat gb hv
               { md with distinct := dist, reduced := red } none st.base, ts8)

/-- [12] AskQuery ::= 'ASK' DatasetClause* WhereClause SolutionModifier. -/
def pAskBody (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let ts1 := advTok ts                       -- consume ASK
    let (ds, ts2) ← pDatasetClauses f st ts1
    let ts3 := if peekTok ts2 == Token.whereKw then advTok ts2 else ts2
    let (pattern, ts4) ← pGroupGraphPattern f st ts3
    .ok (Query.mk .ask ds pattern none [] {} none st.base, ts4)

/-- [10] ConstructQuery — the full form and the `CONSTRUCT WHERE`
short form, whose WHERE pattern must be a basic graph pattern. -/
def pConstructBody (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    let ts1 := advTok ts                       -- consume CONSTRUCT
    match peekTok ts1 with
    | .whereKw | .fromKw => do
      let (ds, ts2) ← pDatasetClauses f st ts1
      let ts3 := if peekTok ts2 == Token.whereKw then advTok ts2 else ts2
      let (pattern, ts4) ← pGroupGraphPattern f st ts3
      if !isBasicPattern pattern then
        pErr "CONSTRUCT WHERE short form only allows basic graph patterns" ts3
      else do
        let (r, ts5) ← pSolutionModifier f st ts4
        .ok (Query.mk (.construct (collectTemplateTriples pattern)) ds pattern
               r.2.1 r.2.2 r.1 none st.base, ts5)
    | .lbrace => do
      let (tmpl, ts2)    ← pGroupGraphPattern f st ts1
      let (ds, ts3)      ← pDatasetClauses f st ts2
      let ts4 := if peekTok ts3 == Token.whereKw then advTok ts3 else ts3
      let (pattern, ts5) ← pGroupGraphPattern f st ts4
      let (r, ts6)       ← pSolutionModifier f st ts5
      .ok (Query.mk (.construct (collectTemplateTriples tmpl)) ds pattern
             r.2.1 r.2.2 r.1 none st.base, ts6)
    | _ => pErr "expected WHERE or '{' after CONSTRUCT" ts1

/-- [11] DescribeQuery's `VarOrIri+` list. -/
def pDescribeTargets (fuel : Nat) (st : PState) (acc : List PatternTerm) (ts : TStream) :
    Except ParseError (List PatternTerm × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .var v => pDescribeTargets f st (.var v :: acc) (advTok ts)
    | .iri i =>
      (match mkIri? i with
       | some wi => pDescribeTargets f st (.iri wi :: acc) (advTok ts)
       | none    => pErr "invalid IRI in DESCRIBE list" ts)
    | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => pDescribeTargets f st (.iri wi :: acc) (advTok ts)
       | none    => pErr "unresolved prefix in DESCRIBE list" ts)
    | _ => .ok (acc.reverse, ts)

/-- [11] DescribeQuery ::= 'DESCRIBE' ( VarOrIri+ | '*' )
DatasetClause* WhereClause? SolutionModifier. -/
def pDescribeBody (fuel : Nat) (st : PState) (ts : TStream) : Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 =>
    let ts1 := advTok ts                       -- consume DESCRIBE
    match peekTok ts1 with
    | .star => pDescribeAfterTargets f st [] (advTok ts1)
    | _ => do
      let (targets, ts2) ← pDescribeTargets f st [] ts1
      if targets.length == 0 then pErr "DESCRIBE expects at least one IRI/var or '*'" ts1
      else pDescribeAfterTargets f st targets ts2

/-- The dataset / WHERE / modifier tail of a DESCRIBE. -/
def pDescribeAfterTargets (fuel : Nat) (st : PState) (targets : List PatternTerm)
    (ts : TStream) : Except ParseError (Query × TStream) :=
  match fuel with
  | 0     => pErr "recursion limit" ts
  | f + 1 => do
    let (ds, ts1) ← pDatasetClauses f st ts
    match peekTok ts1 with
    | .whereKw | .lbrace => do
      let ts2 := if peekTok ts1 == Token.whereKw then advTok ts1 else ts1
      let (pattern, ts3) ← pGroupGraphPattern f st ts2
      let (r, ts4)       ← pSolutionModifier f st ts3
      .ok (Query.mk (.describe targets) ds pattern r.2.1 r.2.2 r.1 none st.base, ts4)
    | _ => do
      let (r, ts2) ← pSolutionModifier f st ts1
      .ok (Query.mk (.describe targets) ds .empty r.2.1 r.2.2 r.1 none st.base, ts2)

end

/-! ## Top-level entry points — F* Part 7's `parse_sparql*` -/

/-- The F*'s own top-level fuel seed. -/
def topFuel : Nat := 10000

/-- Parse a SPARQL query. `base` is the BASE IRI in scope before the
prologue (SPARQL 1.1 §4.1.1.1); `version` selects the 1.1 or 1.2
terminal layer. Port of `parse_sparql_with_base` /
`parse_sparql_12_with_base`. -/
def parseSparqlWith (fuel : Nat) (text : String) (base : Option String)
    (version : SparqlVersion) : Except ParseError Query :=
  let toks := tokenizeAt version text
  match firstInvalidToken toks with
  | some e => .error e
  | none =>
    match pSelectQuery fuel { v12 := version.is12 } base toks with
    | .error e => .error e
    | .ok (q, rest) =>
      if !tokensOnlyEof rest then .error ⟨"unexpected tokens after query", peekPos rest⟩
      else if !validateBnodeScopeTop q then
        .error ⟨"blank node label reused across graph-pattern scope", 0⟩
      else .ok q

/-- Parse at the F*'s own fuel seed. The fuel is a PARAMETER of
`parseSparqlWith` rather than a literal inside it so that a proof can
reason about the entry point without a tactic ever weak-head-
normalising `pSelectQuery 10000 …` — doing so unfolds ten thousand
levels of the mutual block and exhausts memory. See
`SPARQL/ParserTheorems.lean`. -/
def parseSparql (text : String) (base : Option String := none)
    (version : SparqlVersion := .v11) : Except ParseError Query :=
  parseSparqlWith topFuel text base version

/-! ## The SSE algebra printer — F* Part 8

Port of `sse_wrap`, `sse_pattern_term`, `sse_pattern_subject`,
`sse_triple`, `sse_bgp`, `sse_comp_op`, `sse_arith_op`, `sse_expr`,
`sse_path`, `sse_ggp`, `sse_vars`, `sse_select_item`, `sse_query`.
Same keywords, same layout, so the output can be diffed against
`factoidal --explain`.

The one divergence is inside EXISTS / NOT EXISTS — see the module
header's AST-gap note. -/

/-- `sse_wrap`. -/
def sseWrap (tag body : String) : String := "(" ++ tag ++ " " ++ body ++ ")"

/-- `sse_pattern_term`. -/
def ssePatternTerm : PatternTerm → String
  | .var v     => "?" ++ v
  | .iri i     => "<" ++ i.val ++ ">"
  | .bnode b   => "_:" ++ b
  | .literal l => "\"" ++ l.val.lexicalForm ++ "\""
  | .tripleTerm s p o =>
      "<<( " ++ ssePatternTerm s ++ " " ++ ssePatternTerm p ++ " " ++
      ssePatternTerm o ++ " )>>"

/-- `sse_pattern_subject`. -/
def ssePatternSubject : PatternSubject → String
  | .var v   => "?" ++ v
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .tripleTerm s p o =>
      "<<( " ++ ssePatternTerm s ++ " " ++ ssePatternTerm p ++ " " ++
      ssePatternTerm o ++ " )>>"

/-- `sse_triple`. -/
def sseTriple (tp : TriplePattern) : String :=
  sseWrap "triple" (ssePatternSubject tp.s ++ " " ++ ssePatternTerm tp.p ++ " " ++
                    ssePatternTerm tp.o)

/-- `sse_bgp`. -/
def sseBgp (b : Bgp) : String :=
  sseWrap "bgp" (String.intercalate "\n    " (b.map sseTriple))

/-- `sse_comp_op`. -/
def sseCompOp : CompOp → String
  | .eq => "=" | .ne => "!=" | .lt => "<"
  | .gt => ">" | .le => "<=" | .ge => ">="

/-- `sse_arith_op`. -/
def sseArithOp : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

/-- `sse_path`. -/
def ssePath : PropertyPath → String
  | .iri i           => "<" ++ i.val ++ ">"
  | .inverse p       => sseWrap "reverse" (ssePath p)
  | .sequence a b    => sseWrap "seq" (ssePath a ++ " " ++ ssePath b)
  | .alternative a b => sseWrap "alt" (ssePath a ++ " " ++ ssePath b)
  | .zeroOrMore p    => sseWrap "path*" (ssePath p)
  | .oneOrMore p     => sseWrap "path+" (ssePath p)
  | .zeroOrOne p     => sseWrap "path?" (ssePath p)
  | .negatedSet ps   => sseWrap "notoneof" (String.intercalate " " (ps.map ssePath))

/-! `sse_expr` and `sse_ggp` are one mutual block: an EXISTS carries a
`QueryPattern`, and a pattern carries expressions. -/
mutual

/-- `sse_expr`. -/
def sseExpr : Expr → String
  | .var v        => "?" ++ v
  | .iri i        => "<" ++ i.val ++ ">"
  | .lit l        => "\"" ++ l.val.lexicalForm ++ "\""
  | .boolLit b    => if b then "true" else "false"
  | .numericLit n => toString n
  | .decimalLit s => s
  | .doubleLit s  => s
  | .arith op a b => sseWrap (sseArithOp op) (sseExpr a ++ " " ++ sseExpr b)
  | .unaryMinus a => sseWrap "-" (sseExpr a)
  | .unaryPlus a  => sseWrap "+" (sseExpr a)
  | .compare op a b => sseWrap (sseCompOp op) (sseExpr a ++ " " ++ sseExpr b)
  | .and a b      => sseWrap "&&" (sseExpr a ++ " " ++ sseExpr b)
  | .or a b       => sseWrap "||" (sseExpr a ++ " " ++ sseExpr b)
  | .not a        => sseWrap "!" (sseExpr a)
  | .isIri a      => sseWrap "isIRI" (sseExpr a)
  | .isBlank a    => sseWrap "isBlank" (sseExpr a)
  | .isLiteral a  => sseWrap "isLiteral" (sseExpr a)
  | .isNumeric a  => sseWrap "isNumeric" (sseExpr a)
  | .str a        => sseWrap "str" (sseExpr a)
  | .lang a       => sseWrap "lang" (sseExpr a)
  | .datatype a   => sseWrap "datatype" (sseExpr a)
  | .iriFn a      => sseWrap "iri" (sseExpr a)
  | .hasLang a    => sseWrap "haslang" (sseExpr a)
  | .hasLangDir a => sseWrap "haslangdir" (sseExpr a)
  | .langDir a    => sseWrap "langdir" (sseExpr a)
  | .bound v      => sseWrap "bound" ("?" ++ v)
  | .cond c t e   => sseWrap "if" (sseExpr c ++ " " ++ sseExpr t ++ " " ++ sseExpr e)
  | .coalesce es  => sseWrap "coalesce" (sseExprList es)
  | .concat es    => sseWrap "concat" (sseExprList es)
  | .inList a es  => sseWrap "in" (sseExpr a ++ " " ++ sseExprList es)
  | .notInList a es => sseWrap "notin" (sseExpr a ++ " " ++ sseExprList es)
  | .strLen a     => sseWrap "strlen" (sseExpr a)
  | .substr a b none      => sseWrap "substr" (sseExpr a ++ " " ++ sseExpr b)
  | .substr a b (some c)  => sseWrap "substr" (sseExpr a ++ " " ++ sseExpr b ++ " " ++ sseExpr c)
  | .uCase a      => sseWrap "ucase" (sseExpr a)
  | .lCase a      => sseWrap "lcase" (sseExpr a)
  | .strStarts a b => sseWrap "strstarts" (sseExpr a ++ " " ++ sseExpr b)
  | .strEnds a b   => sseWrap "strends" (sseExpr a ++ " " ++ sseExpr b)
  | .contains a b  => sseWrap "contains" (sseExpr a ++ " " ++ sseExpr b)
  | .strBefore a b => sseWrap "strbefore" (sseExpr a ++ " " ++ sseExpr b)
  | .strAfter a b  => sseWrap "strafter" (sseExpr a ++ " " ++ sseExpr b)
  | .encodeForUri a => sseWrap "encode_for_uri" (sseExpr a)
  | .replace a b c none     => sseWrap "replace" (sseExpr a ++ " " ++ sseExpr b ++ " " ++ sseExpr c)
  | .replace a b c (some d) => sseWrap "replace" (sseExpr a ++ " " ++ sseExpr b ++ " " ++
                                                  sseExpr c ++ " " ++ sseExpr d)
  | .regex a b none     => sseWrap "regex" (sseExpr a ++ " " ++ sseExpr b)
  | .regex a b (some c) => sseWrap "regex" (sseExpr a ++ " " ++ sseExpr b ++ " " ++ sseExpr c)
  | .abs a        => sseWrap "abs" (sseExpr a)
  | .round a      => sseWrap "round" (sseExpr a)
  | .ceil a       => sseWrap "ceil" (sseExpr a)
  | .floor a      => sseWrap "floor" (sseExpr a)
  | .md5 a        => sseWrap "md5" (sseExpr a)
  | .sha1 a       => sseWrap "sha1" (sseExpr a)
  | .sha256 a     => sseWrap "sha256" (sseExpr a)
  | .sha384 a     => sseWrap "sha384" (sseExpr a)
  | .sha512 a     => sseWrap "sha512" (sseExpr a)
  | .now          => "(now)"
  | .year a       => sseWrap "year" (sseExpr a)
  | .month a      => sseWrap "month" (sseExpr a)
  | .day a        => sseWrap "day" (sseExpr a)
  | .hours a      => sseWrap "hours" (sseExpr a)
  | .minutes a    => sseWrap "minutes" (sseExpr a)
  | .seconds a    => sseWrap "seconds" (sseExpr a)
  | .timezone a   => sseWrap "timezone" (sseExpr a)
  | .tz a         => sseWrap "tz" (sseExpr a)
  | .sameTerm a b => sseWrap "sameTerm" (sseExpr a ++ " " ++ sseExpr b)
  | .strDt a b    => sseWrap "strdt" (sseExpr a ++ " " ++ sseExpr b)
  | .strLang a b  => sseWrap "strlang" (sseExpr a ++ " " ++ sseExpr b)
  | .strLangDir a b c => sseWrap "strlangdir" (sseExpr a ++ " " ++ sseExpr b ++ " " ++ sseExpr c)
  | .existsPat g    => sseWrap "exists" (sseGgp g)
  | .notExistsPat g => sseWrap "notexists" (sseGgp g)
  | .aggregate _ _ a  => sseWrap "agg" (sseExpr a)
  | .functionCall i args => sseWrap ("call " ++ i.val) (sseExprList args)
  | .tripleTerm a b c => sseWrap "tripleterm" (sseExpr a ++ " " ++ sseExpr b ++ " " ++ sseExpr c)
  | .ttSubject a   => sseWrap "subject" (sseExpr a)
  | .ttPredicate a => sseWrap "predicate" (sseExpr a)
  | .ttObject a    => sseWrap "object" (sseExpr a)
  | .isTriple a    => sseWrap "istriple" (sseExpr a)

/-- `sse_expr_list`. -/
def sseExprList : List Expr → String
  | []       => ""
  | [e]      => sseExpr e
  | e :: rest => sseExpr e ++ " " ++ sseExprList rest

/-- `sse_ggp`. -/
def sseGgp : QueryPattern → String
  | .empty          => "(table unit)"
  | .bgp b          => sseBgp b
  | .join a b       => sseWrap "join" (sseGgp a ++ "\n  " ++ sseGgp b)
  | .leftJoin a b c => sseWrap "leftjoin" (sseGgp a ++ "\n  " ++ sseGgp b ++ "\n  " ++ sseExpr c)
  | .filter e g     => sseWrap "filter" (sseExpr e ++ "\n  " ++ sseGgp g)
  | .union a b      => sseWrap "union" (sseGgp a ++ "\n  " ++ sseGgp b)
  | .graph t g      => sseWrap "graph" (ssePatternTerm t ++ "\n  " ++ sseGgp g)
  | .minus a b      => sseWrap "minus" (sseGgp a ++ "\n  " ++ sseGgp b)
  | .lateral a b    => sseWrap "lateral" (sseGgp a ++ "\n  " ++ sseGgp b)
  | .bind e v g     => sseWrap "extend" ("(?" ++ v ++ " " ++ sseExpr e ++ ")\n  " ++ sseGgp g)
  | .values vars _  => sseWrap "table" (String.intercalate " " (vars.map (fun v => "?" ++ v)))
  | .service i silent g =>
      sseWrap "service" ((if silent then "SILENT " else "") ++ "<" ++ i.val ++ ">\n  " ++ sseGgp g)
  | .serviceVar v silent g =>
      sseWrap "service" ((if silent then "SILENT " else "") ++ "?" ++ v ++ "\n  " ++ sseGgp g)
  | .subSelect q    => sseQuery q
  | .propertyPath s pp o =>
      sseWrap "path" (ssePatternSubject s ++ " " ++ ssePath pp ++ " " ++ ssePatternTerm o)

/-- `sse_query`. -/
def sseQuery : Query → String
  | .mk form _ pat _ _ md _ _ =>
    let head :=
      match form with
      | .select .all          => "(project *"
      | .select (.vars items) => "(project (" ++ sseSelectItems items ++ ")"
      | .ask                  => "(ask"
      | .construct _          => "(construct"
      | .describe _           => "(describe"
    let body := sseGgp pat
    let mods :=
      (match md.orderBy with | none => "" | some _ => "\n  (order ...)") ++
      (if md.distinct then "\n  (distinct)" else "") ++
      (match md.limit with | none => "" | some n => "\n  (slice _ " ++ toString n ++ ")")
    head ++ "\n  " ++ body ++ mods ++ ")"

/-- `sse_select_items`. -/
def sseSelectItems : List SelectItem → String
  | []       => ""
  | [i]      => sseSelectItem i
  | i :: rest => sseSelectItem i ++ " " ++ sseSelectItems rest

/-- `sse_select_item`. -/
def sseSelectItem : SelectItem → String
  | .var v    => "?" ++ v
  | .expr e v => sseWrap "as" (sseExpr e ++ " ?" ++ v)

end

/-- The reviewer-facing algebra printout — `sse_query` under the name
the deliverable asks for. -/
def Query.toSse (q : Query) : String := sseQuery q

/-- Parse and print in one step; the error message on a failure. Every
`toSse` snapshot guard in `ParserTests.lean` goes through this. -/
def sseOf (text : String) (base : Option String := none)
    (version : SparqlVersion := .v11) : String :=
  match parseSparql text base version with
  | .ok q    => q.toSse
  | .error e => "ERROR: " ++ e.msg

/-- Did this text parse? -/
def parses (text : String) (version : SparqlVersion := .v11) : Bool :=
  (parseSparql text none version).toOption.isSome

/-- The rejection message, or `""` when the text parsed. -/
def errMsg (text : String) (version : SparqlVersion := .v11) : String :=
  match parseSparql text none version with
  | .ok _    => ""
  | .error e => e.msg

end L4Factoidal.SPARQL
