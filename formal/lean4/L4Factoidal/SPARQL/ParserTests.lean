/-
L4Factoidal.SPARQL.ParserTests — build-time checks for the SPARQL 1.1
query tokenizer, grammar, and SSE printer.

Every `#guard` here is evaluated during `lake build`, so a wrong answer
is a BUILD ERROR, not a silent regression.

WHAT THESE ARE NOT. This file is not a conformance score. The real
corpus measurement is `Harness/SparqlSyntaxProbe.lean` (`lake exe
l4sparql-probe`), which runs the parser over the W3C sparql11 `.rq`
files and reports each count with its denominator. These guards are
the unit layer: one per grammar production family, one per
well-formedness rejection, and twenty `toSse` snapshots.

WHERE THE SNAPSHOTS COME FROM. `Query.toSse` is a line-for-line port
of `SPARQL11.Parser.fst`'s `sse_query` / `sse_ggp` / `sse_expr` /
`sse_path` family, so the expected strings were derived by READING
that F* source, not by running a binary. The committed
`bin/darwin-arm64/factoidal` exposes no SSE flag — its `--explain` is
a different artifact (a COTTAS plan dump, and it refuses to run
without `--data-cottas`), so it could not serve as the oracle. Two
outputs a reader may find surprising, and both are faithful:
  * a generated blank node prints as `_:_:bnode_6`, because the F*
    `fresh_bnode_id` puts `_:` INSIDE the label and `sse_pattern_term`
    prepends `_:` again;
  * `(agg …)` drops the aggregate's name and its DISTINCT flag —
    `sse_expr`'s `E_Aggregate` arm prints only the argument.
-/
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL

/-! ## §19.8 terminals — the tokenizer -/

-- Keywords are matched case-insensitively (§19.8 note).
#guard tokensOf (tokenize "select") == tokensOf (tokenize "SELECT")
#guard tokensOf (tokenize "Select") == tokensOf (tokenize "sELEct")
#guard tokensOf (tokenize "where distinct") == tokensOf (tokenize "WHERE DISTINCT")
#guard tokensOf (tokenize "SELECT") == [Token.select, Token.eof]

-- [139] IRIREF, [140] PNAME_LN, [143] VAR1 / [144] VAR2.
#guard tokensOf (tokenize "<http://a/b>") == [Token.iri "http://a/b", Token.eof]
#guard tokensOf (tokenize "ex:local") == [Token.pname "ex:local", Token.eof]
#guard tokensOf (tokenize "ex:") == [Token.pname "ex:", Token.eof]
#guard tokensOf (tokenize "?x") == [Token.var "x", Token.eof]
#guard tokensOf (tokenize "$x") == [Token.var "x", Token.eof]

-- [142] BLANK_NODE_LABEL, and the trailing-dot trim that pushes the
-- `.` back as a separate token.
#guard tokensOf (tokenize "_:b1") == [Token.bnode "b1", Token.eof]
#guard tokensOf (tokenize ":foo.") == [Token.pname ":foo", Token.dot, Token.eof]

-- [146]-[148] numeric literals: a `.` counts only before a digit, an
-- exponent makes the whole lexeme a DOUBLE.
#guard tokensOf (tokenize "3") == [Token.integer "3", Token.eof]
#guard tokensOf (tokenize "3.5") == [Token.decimal "3.5", Token.eof]
#guard tokensOf (tokenize "1e6") == [Token.double "1e6", Token.eof]
#guard tokensOf (tokenize "1.5E-3") == [Token.double "1.5E-3", Token.eof]
#guard tokensOf (tokenize "3.") == [Token.integer "3", Token.dot, Token.eof]

-- [135] String with its [160] ECHAR escapes, [145] LANGTAG, `^^`.
#guard tokensOf (tokenize "\"hi\"") == [Token.str "hi", Token.eof]
#guard tokensOf (tokenize "'hi'") == [Token.str "hi", Token.eof]
#guard tokensOf (tokenize "\"\"\"a\nb\"\"\"") == [Token.str "a\nb", Token.eof]
#guard tokensOf (tokenize "\"a\\nb\"") == [Token.str "a\nb", Token.eof]
#guard tokensOf (tokenize "\"\\u0041\"") == [Token.str "A", Token.eof]
#guard tokensOf (tokenize "\"x\"@en") == [Token.str "x", Token.langtag "en", Token.eof]
#guard tokensOf (tokenize "^^") == [Token.hathat, Token.eof]

-- The `<` disambiguation: an IRIREF versus the less-than operator.
#guard tokensOf (tokenize "?a < ?b") == [Token.var "a", Token.lt, Token.var "b", Token.eof]
#guard tokensOf (tokenize "?a <= ?b") == [Token.var "a", Token.le, Token.var "b", Token.eof]
#guard tokensOf (tokenize "?a >= ?b") == [Token.var "a", Token.ge, Token.var "b", Token.eof]
#guard tokensOf (tokenize "?a != ?b") == [Token.var "a", Token.ne, Token.var "b", Token.eof]
#guard tokensOf (tokenize "&& ||") == [Token.and, Token.or, Token.eof]

-- [161] COMMENT runs to end of line.
#guard tokensOf (tokenize "# c\nASK") == [Token.ask, Token.eof]
#guard tokensOf (tokenize "ASK # trailing") == [Token.ask, Token.eof]

-- `a` is [82] VerbSimple's own token; keeping it out of verb position
-- is a parser concern, so the tokenizer emits it unconditionally.
#guard tokensOf (tokenize "a") == [Token.a, Token.eof]

-- Positions are character offsets from the start of the document.
#guard (tokenize "  ASK").map PosToken.pos == [2, 5]

-- SPARQL 1.2 mode adds the triple-term and direction terminals; 1.1
-- mode sees none of them.
#guard tokensOf (tokenize12 "<<( ?s ?p ?o )>>") ==
  [Token.ttOpen, Token.var "s", Token.var "p", Token.var "o", Token.ttClose, Token.eof]
#guard tokensOf (tokenize12 "TRIPLE") == [Token.tripleKw, Token.eof]
#guard tokensOf (tokenize "TRIPLE") == [Token.pname "TRIPLE", Token.eof]
#guard tokensOf (tokenize12 "\"x\"@en--ltr") ==
  [Token.str "x", Token.langdir "en" .ltr, Token.eof]
#guard tokensOf (tokenize "\"x\"@en--ltr") ==
  [Token.str "x", Token.langtag "en--ltr", Token.eof]

/-! ## Query forms — [7]-[12] -/

#guard parses "SELECT ?x WHERE { ?x <http://a/p> ?y }"
#guard parses "SELECT * WHERE { ?x <http://a/p> ?y }"
#guard parses "SELECT DISTINCT ?x { ?x <http://a/p> ?y }"
#guard parses "SELECT REDUCED ?x { ?x <http://a/p> ?y }"
#guard parses "SELECT (1 AS ?n) { }"
#guard parses "ASK { ?s ?p ?o }"
#guard parses "ASK WHERE { }"
#guard parses "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }"
#guard parses "CONSTRUCT WHERE { ?s ?p ?o }"
#guard parses "DESCRIBE <http://a/x>"
#guard parses "DESCRIBE ?x WHERE { ?x <http://a/p> ?y }"
#guard parses "DESCRIBE *"

/-! ## [4] Prologue — BASE, PREFIX, and IRI resolution -/

#guard parses "PREFIX ex: <http://e/> SELECT * { ex:a ex:b ex:c }"
#guard parses "BASE <http://x/> SELECT * { <a> <b> <c> }"
-- BASE resolves relative references in the whole rest of the query.
-- (`<../q>` is NOT usable here: the F* lexer's `<` disambiguation
-- admits only a letter, `>`, `_`, `/`, `#` or `?`/`$` after the
-- bracket, so a reference starting with `.` lexes as less-than. The
-- port keeps that, so this guard uses a plain relative segment.)
#guard sseOf "BASE <http://x/d/> SELECT ?s { ?s <p> <q> }" ==
  "(project (?s)\n  (bgp (triple ?s <http://x/d/p> <http://x/d/q>)))"
-- A relative PREFIX namespace resolves against the BASE in force.
#guard sseOf "BASE <http://x/> PREFIX p: <ns#> SELECT ?s { ?s p:a p:b }" ==
  "(project (?s)\n  (bgp (triple ?s <http://x/ns#a> <http://x/ns#b>)))"
-- Without a BASE a relative reference has no scheme, so it is not a
-- well-formed IRI — the `RDF.isIri` rejection, one layer up.
#guard !parses "SELECT * { <a> <b> <c> }"
#guard parses "SELECT * { <a> <b> <c> }" == false

/-! ## [13]-[16] DatasetClause -/

#guard parses "SELECT * FROM <http://a/g> { ?s ?p ?o }"
#guard parses "SELECT * FROM NAMED <http://a/g> { ?s ?p ?o }"
#guard parses "SELECT * FROM <http://a/g> FROM NAMED <http://a/h> { ?s ?p ?o }"
#guard parses "PREFIX e: <http://e/> SELECT * FROM e:g { ?s ?p ?o }"

/-! ## [53]-[57] Group graph patterns -/

#guard parses "SELECT * { }"
#guard parses "SELECT * { ?s ?p ?o OPTIONAL { ?s <http://a/q> ?z } }"
#guard parses "SELECT * { { ?s ?p ?o } UNION { ?a ?b ?c } }"
#guard parses "SELECT * { ?s ?p ?o MINUS { ?s <http://a/q> ?z } }"
#guard parses "SELECT * { ?s ?p ?o LATERAL { ?o <http://a/q> ?z } }"
#guard parses "SELECT * { GRAPH <http://a/g> { ?s ?p ?o } }"
#guard parses "SELECT * { GRAPH ?g { ?s ?p ?o } }"
#guard parses "SELECT * { SERVICE <http://x/s> { ?s ?p ?o } }"
#guard parses "SELECT * { SERVICE SILENT <http://x/s> { ?s ?p ?o } }"
#guard parses "SELECT * { ?s <http://a/e> ?e SERVICE ?e { ?s ?p ?o } }"
#guard parses "SELECT * { BIND(1 AS ?n) }"
#guard parses "SELECT * { FILTER(true) }"
#guard parses "SELECT * { { SELECT ?o { ?a ?b ?o } LIMIT 1 } }"
#guard parses "SELECT * { { ?s ?p ?o } }"

/-! ## [61]-[65] Inline data -/

#guard parses "SELECT * { VALUES ?x { 1 2 3 } }"
#guard parses "SELECT * { VALUES (?x ?y) { (1 2) (3 UNDEF) } }"
#guard parses "SELECT * { VALUES (?x) { } }"
#guard parses "SELECT * { ?s ?p ?o } VALUES ?o { \"a\" }"
#guard parses "PREFIX e: <http://e/> SELECT * { VALUES ?x { e:a \"s\"^^e:t true } }"

/-! ## [75]-[87] Triples, and the term sugar -/

#guard parses "SELECT * { ?s <http://a/p> ?o ; <http://a/q> ?z }"
#guard parses "SELECT * { ?s <http://a/p> ?o , ?z }"
#guard parses "SELECT * { ?s <http://a/p> ?o . }"
#guard parses "SELECT * { ?s a <http://a/C> }"
#guard parses "SELECT * { [] <http://a/p> ?o }"
#guard parses "SELECT * { ?s <http://a/p> [ <http://a/q> \"v\" ] }"
#guard parses "SELECT * { ?s <http://a/p> ( 1 2 3 ) }"
#guard parses "SELECT * { ?s <http://a/p> () }"
#guard parses "SELECT * { ?s <http://a/p> -3 , +2.5 , 1e3 , true , false }"
#guard parses "SELECT * { ?s <http://a/p> \"v\"@en }"
#guard parses "SELECT * { ?s <http://a/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> }"
#guard parses "SELECT * { _:b <http://a/p> ?o }"
-- §19.8 [55]: two statements need a separating `.`.
#guard errMsg "SELECT * { ?s <http://a/p> ?o ?a <http://a/q> ?b }" ==
  "expected dot between triples"
-- A literal cannot be a subject.
#guard !parses "SELECT * { \"s\" <http://a/p> ?o }"

/-! ## [88]-[96] Property paths — the full §18.4 syntax -/

#guard parses "SELECT * { ?s <http://a/p>/<http://a/q> ?o }"
#guard parses "SELECT * { ?s <http://a/p>|<http://a/q> ?o }"
#guard parses "SELECT * { ?s ^<http://a/p> ?o }"
#guard parses "SELECT * { ?s <http://a/p>* ?o }"
#guard parses "SELECT * { ?s <http://a/p>+ ?o }"
#guard parses "SELECT * { ?s <http://a/p>? ?o }"
#guard parses "SELECT * { ?s !<http://a/p> ?o }"
#guard parses "SELECT * { ?s !(<http://a/p>|^<http://a/q>) ?o }"
#guard parses "SELECT * { ?s (<http://a/p>/<http://a/q>)+ ?o }"
#guard parses "SELECT * { ?s a/<http://a/p> ?o }"
-- `/` binds tighter than `|` ([89] vs [90]).
#guard sseOf "SELECT ?s { ?s <http://a/p>/<http://a/q>|<http://a/r> ?o }" ==
  "(project (?s)\n  (path ?s (alt (seq <http://a/p> <http://a/q>) <http://a/r>) ?o))"
-- A path modifier binds tighter than a sequence ([91]).
#guard sseOf "SELECT ?s { ?s <http://a/p>*/<http://a/q> ?o }" ==
  "(project (?s)\n  (path ?s (seq (path* <http://a/p>) <http://a/q>) ?o))"
-- A single-IRI "path" stays a plain triple pattern, not a path node.
#guard sseOf "SELECT ?s { ?s <http://a/p> ?o }" ==
  "(project (?s)\n  (bgp (triple ?s <http://a/p> ?o)))"

/-! ## [110]-[121] Expressions — §18.2.2.1 precedence and §17 builtins -/

-- `||` binds loosest, then `&&`, then the relational operators.
#guard sseOf "ASK { FILTER(?a || ?b && ?c) }" ==
  "(ask\n  (filter (|| ?a (&& ?b ?c))\n  (table unit)))"
-- `+`/`-` bind looser than `*`//`, and both are left-associative.
#guard sseOf "ASK { FILTER(1 + 2 * 3 - 4) }" ==
  "(ask\n  (filter (- (+ 1 (* 2 3)) 4)\n  (table unit)))"
#guard sseOf "ASK { FILTER(1 - 2 - 3) }" ==
  "(ask\n  (filter (- (- 1 2) 3)\n  (table unit)))"
-- Unary operators stack ([118]: the operand is a UnaryExpression).
#guard sseOf "ASK { FILTER(!!?v) }" ==
  "(ask\n  (filter (! (! ?v))\n  (table unit)))"
#guard sseOf "ASK { FILTER(-?v) }" ==
  "(ask\n  (filter (- ?v)\n  (table unit)))"

-- One guard per §17 builtin family the `Expr` AST carries.
#guard parses "ASK { FILTER(STR(?x)) }"
#guard parses "ASK { FILTER(LANG(?x) = \"en\") }"
#guard parses "ASK { FILTER(LANGMATCHES(LANG(?x), \"en\")) }"
#guard parses "ASK { FILTER(DATATYPE(?x) = <http://a/t>) }"
#guard parses "ASK { FILTER(BOUND(?x)) }"
#guard parses "ASK { FILTER(IF(?a, 1, 2) = 1) }"
#guard parses "ASK { FILTER(COALESCE(?a, ?b, 0) = 0) }"
#guard parses "ASK { FILTER(sameTerm(?a, ?b)) }"
#guard parses "ASK { FILTER(isIRI(?a) || isURI(?a)) }"
#guard parses "ASK { FILTER(isBLANK(?a) || isLITERAL(?a) || isNUMERIC(?a)) }"
#guard parses "ASK { FILTER(STRLEN(?a) > 1) }"
#guard parses "ASK { FILTER(SUBSTR(?a, 1) = SUBSTR(?a, 1, 2)) }"
#guard parses "ASK { FILTER(UCASE(?a) = LCASE(?a)) }"
#guard parses "ASK { FILTER(STRSTARTS(?a,\"x\") && STRENDS(?a,\"y\") && CONTAINS(?a,\"z\")) }"
#guard parses "ASK { FILTER(STRBEFORE(?a,\"x\") = STRAFTER(?a,\"y\")) }"
#guard parses "ASK { FILTER(CONCAT(?a, \"b\", ?c) = \"\") }"
#guard parses "ASK { FILTER(ENCODE_FOR_URI(?a) = \"\") }"
#guard parses "ASK { FILTER(REGEX(?a, \"^x\", \"i\")) }"
#guard parses "ASK { FILTER(REPLACE(?a, \"x\", \"y\") = REPLACE(?a,\"x\",\"y\",\"i\")) }"
#guard parses "ASK { FILTER(ABS(?a) + CEIL(?a) + FLOOR(?a) + ROUND(?a) > 0) }"
#guard parses "ASK { FILTER(MD5(?a) = SHA1(?a)) }"
#guard parses "ASK { FILTER(SHA256(?a) = SHA384(?a) || SHA512(?a) = \"\") }"
#guard parses "ASK { FILTER(NOW() > ?a) }"
#guard parses "ASK { FILTER(YEAR(?a)+MONTH(?a)+DAY(?a)+HOURS(?a)+MINUTES(?a)+SECONDS(?a) > 0) }"
#guard parses "ASK { FILTER(TIMEZONE(?a) = TZ(?a)) }"
#guard parses "ASK { FILTER(STRDT(\"1\", <http://a/t>) = STRLANG(\"x\",\"en\")) }"
#guard parses "ASK { FILTER(IRI(?a) = URI(?a)) }"
#guard parses "ASK { BIND(BNODE() AS ?b) BIND(BNODE(\"x\") AS ?c) }"
#guard parses "ASK { FILTER(RAND() < 1) }"
#guard parses "ASK { FILTER(UUID() != STRUUID()) }"
#guard parses "ASK { FILTER(EXISTS { ?s ?p ?o }) }"
#guard parses "ASK { FILTER NOT EXISTS { ?s ?p ?o } }"
#guard parses "ASK { FILTER(?a IN (1, 2, 3)) }"
#guard parses "ASK { FILTER(?a NOT IN (1, 2)) }"
#guard parses "ASK { FILTER(<http://a/f>(?a, ?b)) }"
#guard parses "PREFIX f: <http://f/> ASK { FILTER(f:g(?a)) }"
-- An unknown function IRI becomes `Expr.functionCall` (§17.6).
#guard sseOf "ASK { FILTER(<http://a/f>(?x)) }" ==
  "(ask\n  (filter (call http://a/f ?x)\n  (table unit)))"
-- LANGMATCHES has no `Expr` constructor and is modelled the F*'s way.
#guard sseOf "ASK { FILTER(LANGMATCHES(?a, \"en\")) }" ==
  "(ask\n  (filter (call http://www.w3.org/2005/xpath-functions#langMatches ?a \"en\")\n  (table unit)))"
-- [68] Constraint: a builtin call needs no parentheses after FILTER.
#guard parses "ASK { FILTER isIRI(?a) }"
#guard parses "ASK { FILTER regex(?a, \"x\") }"

/-! ## [18]-[27] Solution modifiers -/

#guard parses "SELECT * { ?s ?p ?o } LIMIT 5"
#guard parses "SELECT * { ?s ?p ?o } OFFSET 5"
#guard parses "SELECT * { ?s ?p ?o } LIMIT 5 OFFSET 2"
-- [25] LimitOffsetClauses admits either order.
#guard parses "SELECT * { ?s ?p ?o } OFFSET 2 LIMIT 5"
#guard sseOf "SELECT * { ?s ?p ?o } OFFSET 2 LIMIT 5" ==
       sseOf "SELECT * { ?s ?p ?o } LIMIT 5 OFFSET 2"
#guard parses "SELECT * { ?s ?p ?o } ORDER BY ?s"
#guard parses "SELECT * { ?s ?p ?o } ORDER BY ASC(?s) DESC(?o)"
#guard parses "SELECT * { ?s ?p ?o } ORDER BY STR(?s)"
#guard parses "SELECT ?s (COUNT(?o) AS ?c) { ?s ?p ?o } GROUP BY ?s"
#guard parses "SELECT (COUNT(?o) AS ?c) { ?s ?p ?o } GROUP BY (STR(?s) AS ?k)"
#guard parses "SELECT ?s (COUNT(?o) AS ?c) { ?s ?p ?o } GROUP BY ?s HAVING (COUNT(?o) > 1)"

/-! ## [127] Aggregates -/

#guard parses "SELECT (COUNT(*) AS ?c) { ?s ?p ?o }"
#guard parses "SELECT (COUNT(DISTINCT *) AS ?c) { ?s ?p ?o }"
#guard parses "SELECT (COUNT(DISTINCT ?o) AS ?c) { ?s ?p ?o }"
#guard parses "SELECT (SUM(?o) AS ?x) { ?s ?p ?o }"
#guard parses "SELECT (MIN(?o) AS ?a) (MAX(?o) AS ?b) (AVG(?o) AS ?c) { ?s ?p ?o }"
#guard parses "SELECT (SAMPLE(?o) AS ?x) { ?s ?p ?o }"
#guard parses "SELECT (GROUP_CONCAT(?o) AS ?g) { ?s ?p ?o }"
#guard parses "SELECT (GROUP_CONCAT(DISTINCT ?o ; SEPARATOR=\"-\") AS ?g) { ?s ?p ?o }"

/-! ## SPARQL 1.2 additions — only in `.v12` mode -/

#guard parses "SELECT * { ?s ?p <<( ?a ?b ?c )>> }" .v12
#guard !parses "SELECT * { ?s ?p <<( ?a ?b ?c )>> }" .v11
#guard parses "SELECT * { BIND(TRIPLE(?a,?b,?c) AS ?t) }" .v12
#guard parses "ASK { FILTER(isTRIPLE(?t) && SUBJECT(?t) = PREDICATE(?t) && OBJECT(?t) = ?x) }" .v12
#guard parses "VERSION \"1.2\" SELECT * { ?s ?p ?o }" .v12
#guard !parses "VERSION \"\"\"1.2\"\"\" SELECT * { ?s ?p ?o }" .v12
#guard errMsg "VERSION \"\"\"1.2\"\"\" ASK {}" .v12 ==
  "VERSION requires a plain string literal, not a triple-quoted long string"
#guard parses "ASK { FILTER(hasLANG(?x) && hasLANGDIR(?x) && LANGDIR(?x) = \"ltr\") }" .v12
#guard parses "SELECT * { VALUES ?x { \"a\"@en--rtl } }" .v12

/-! ## Well-formedness rejections

One guard per row of the table in `Parser.lean`'s module header. Some
of the message text is grepped for by tests elsewhere in the repo, so
the strings are the F*'s verbatim. -/

#guard errMsg "SELECT ?x ?x { ?x ?p ?o }" == "duplicate variable in SELECT"
#guard errMsg "SELECT ?x (1 AS ?x) { ?x ?p ?o }" == "duplicate variable in SELECT"
#guard errMsg "SELECT * { ?s ?p ?o } GROUP BY ?s" ==
  "SELECT * not allowed with GROUP BY"
#guard errMsg "SELECT ?p (COUNT(?o) AS ?c) { ?s ?p ?o }" ==
  "SELECT projects ungrouped variable"
#guard errMsg "SELECT ?o (COUNT(?o) AS ?c) { ?s ?p ?o } GROUP BY ?s" ==
  "SELECT projects ungrouped variable"
#guard errMsg "SELECT (1 AS ?o) { ?s ?p ?o }" ==
  "SELECT expression aliases variable already in scope"
#guard errMsg "SELECT * { ?s ?p ?o LATERAL { BIND(1 AS ?o) } }" ==
  "LATERAL: right-hand side reassigns a variable already bound by the left-hand pattern"
#guard errMsg "SELECT * { ?s ?p ?o LATERAL { VALUES ?o { 1 } } }" ==
  "LATERAL: right-hand side reassigns a variable already bound by the left-hand pattern"
#guard errMsg "SELECT * { ?s ?p ?o BIND(1 AS ?o) }" == "BIND variable already in scope"
#guard errMsg "SELECT (COUNT(SUM(?o)) AS ?c) { ?s ?p ?o }" ==
  "nested aggregate in aggregate argument"
#guard errMsg "SELECT (GROUP_CONCAT(SUM(?o)) AS ?c) { ?s ?p ?o }" ==
  "nested aggregate in GROUP_CONCAT argument"
#guard errMsg "SELECT * { VALUES (?a ?a) { (1 2) } }" ==
  "duplicate variable in VALUES clause"
#guard errMsg "SELECT * { VALUES (?a ?b) { (1) } }" ==
  "VALUES row has wrong number of terms"
#guard errMsg "SELECT * { { ?s <http://a/p> _:b } { _:b <http://a/q> ?o } }" ==
  "blank node label reused across nested group scope"
#guard errMsg "SELECT * { { ?s <http://a/p> _:b } UNION { _:b <http://a/q> ?o } }" ==
  "blank node label reused across graph-pattern scope"
#guard errMsg "CONSTRUCT WHERE { ?s ?p ?o FILTER(true) }" ==
  "CONSTRUCT WHERE short form only allows basic graph patterns"
#guard errMsg "DESCRIBE WHERE { ?s ?p ?o }" ==
  "DESCRIBE expects at least one IRI/var or '*'"
#guard errMsg "PREFIX e:x <http://e/> ASK {}" ==
  "invalid PREFIX name (must be prefix: with no local part)"
#guard errMsg "ASK { } ASK { }" == "unexpected tokens after query"
#guard errMsg "SELECT * { ?s ?p ?o } BINDINGS ?x { (1) }" == "unexpected tokens after query"
#guard errMsg "ASK { FILTER(\"\\uD800\") }" ==
  "invalid string escape (surrogate or malformed)"
-- A blank-node label MAY repeat across two BGPs joined in one group,
-- because they become one BGP (`preserves_bgp_scope`).
#guard parses "SELECT * { _:b <http://a/p> ?o . _:b <http://a/q> ?z }"

/-! ## `Query.toSse` snapshots

Twenty representative queries. The expected strings are the port of
`sse_query` / `sse_ggp` / `sse_expr` / `sse_path` applied by hand — see
the file header on why the committed binary could not be the oracle. -/

#guard sseOf "SELECT ?x WHERE { ?x <http://a/p> ?y }" ==
  "(project (?x)\n  (bgp (triple ?x <http://a/p> ?y)))"

#guard sseOf "PREFIX e: <http://e/> SELECT * { e:a a ?t . ?t e:p/e:q ?z }" ==
  "(project *\n  (join (bgp (triple <http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?t))\n  (path ?t (seq <http://e/p> <http://e/q>) ?z)))"

#guard sseOf "ASK { ?s ?p ?o FILTER(?o > 3) }" ==
  "(ask\n  (filter (> ?o 3)\n  (bgp (triple ?s ?p ?o))))"

#guard sseOf "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s" ==
  "(project ((as (agg true) ?c))\n  (bgp (triple ?s ?p ?o)))"

#guard sseOf "SELECT ?s { ?s ?p ?o OPTIONAL { ?s <http://a/x> ?q } }" ==
  "(project (?s)\n  (leftjoin (bgp (triple ?s ?p ?o))\n  (bgp (triple ?s <http://a/x> ?q))\n  true))"

#guard sseOf "CONSTRUCT WHERE { ?s ?p ?o }" ==
  "(construct\n  (bgp (triple ?s ?p ?o)))"

#guard sseOf "SELECT ?x { VALUES (?x ?y) { (1 UNDEF) (2 3) } }" ==
  "(project (?x)\n  (table ?x ?y))"

#guard sseOf "SELECT DISTINCT ?s { { ?s <http://a/p> ?o } UNION { ?s <http://a/q> ?o } } ORDER BY ?s LIMIT 5" ==
  "(project (?s)\n  (union (bgp (triple ?s <http://a/p> ?o))\n  (bgp (triple ?s <http://a/q> ?o)))\n  (order ...)\n  (distinct)\n  (slice _ 5))"

#guard sseOf "SELECT ?s { ?s <http://a/p> ?o . FILTER NOT EXISTS { ?o <http://a/q> ?z } }" ==
  "(project (?s)\n  (filter (notexists (bgp (triple ?o <http://a/q> ?z)))\n  (bgp (triple ?s <http://a/p> ?o))))"

#guard sseOf "SELECT ?s { ?s !(<http://a/p>|^<http://a/q>)* ?o }" ==
  "(project (?s)\n  (path ?s (path* (notoneof <http://a/p> (reverse <http://a/q>))) ?o))"

#guard sseOf "SELECT ?s { GRAPH ?g { ?s ?p ?o } BIND(1 AS ?n) }" ==
  "(project (?s)\n  (extend (?n 1)\n  (graph ?g\n  (bgp (triple ?s ?p ?o)))))"

#guard sseOf "SELECT ?s { SERVICE SILENT <http://x/sparql> { ?s ?p ?o } }" ==
  "(project (?s)\n  (service SILENT <http://x/sparql>\n  (bgp (triple ?s ?p ?o))))"

#guard sseOf "SELECT ?s { ?s ?p ?o MINUS { ?s <http://a/z> ?w } }" ==
  "(project (?s)\n  (minus (bgp (triple ?s ?p ?o))\n  (bgp (triple ?s <http://a/z> ?w))))"

#guard sseOf "SELECT ?s (GROUP_CONCAT(?o ; SEPARATOR=\"-\") AS ?g) { ?s ?p ?o } GROUP BY ?s HAVING (COUNT(?o) > 1)" ==
  "(project (?s (as (agg ?o) ?g))\n  (bgp (triple ?s ?p ?o)))"

#guard sseOf "DESCRIBE <http://a/x>" ==
  "(describe\n  (table unit))"

#guard sseOf "SELECT ?s { ?s <http://a/p> [ <http://a/q> \"v\" ] }" ==
  "(project (?s)\n  (join (bgp (triple ?s <http://a/p> _:_:bnode_6))\n  (bgp (triple _:_:bnode_6 <http://a/q> \"v\"))))"

#guard sseOf "SELECT ?s { ?s <http://a/p> (1 2) }" ==
  "(project (?s)\n  (join (bgp (triple ?s <http://a/p> _:_:bnode_5))\n  (join (bgp (triple _:_:bnode_5 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> \"1\")\n    (triple _:_:bnode_5 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> _:_:bnode_4))\n  (bgp (triple _:_:bnode_4 <http://www.w3.org/1999/02/22-rdf-syntax-ns#first> \"2\")\n    (triple _:_:bnode_4 <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil>)))))"

#guard sseOf "SELECT * { ?s ?p ?o . { SELECT ?o { ?a ?b ?o } LIMIT 2 } }" ==
  "(project *\n  (join (bgp (triple ?s ?p ?o))\n  (project (?o)\n  (bgp (triple ?a ?b ?o))\n  (slice _ 2))))"

#guard sseOf "SELECT ?v { BIND(IF(1 < 2, CONCAT(\"a\",\"b\"), STR(3)) AS ?v) }" ==
  "(project (?v)\n  (extend (?v (if (< 1 2) (concat \"a\" \"b\") (str 3)))\n  (table unit)))"

#guard sseOf "SELECT * { ?s ?p ?o } ORDER BY DESC(?o) OFFSET 2 LIMIT 3" ==
  "(project *\n  (bgp (triple ?s ?p ?o))\n  (order ...)\n  (slice _ 3))"

/-! ## Regressions the W3C corpus caught

Each of these is a real bug this port shipped and the
`l4sparql-probe` run found. Pinned so it cannot come back. -/

-- `aggregates/agg10.rq`: the implicit-grouping check inverted the F*'s
-- `not (for_all p)`, so a BARE projected variable beside an aggregate
-- was not reported ungrouped.
#guard errMsg "PREFIX : <http://www.example.org/>\nSELECT ?P (COUNT(?O) AS ?C)\nWHERE { ?S ?P ?O }" ==
  "SELECT projects ungrouped variable"

-- `syntax-query/syntax-oneof-03.rq`: a relative IRI inside an IN list
-- needs the query's BASE (§4.1.1.1).
#guard parses "BASE <http://a/> SELECT * { ?s ?p ?o FILTER(?o IN(1,<x>)) }"

-- `syntax-query/syntax-BINDscope6.rq` is a NegativeSyntaxTest11: the
-- BIND target is already bound by an earlier triple pattern.
#guard errMsg "PREFIX : <http://www.example.org>\nSELECT *\nWHERE { :s :p ?o . :s :q ?o1 . BIND((1+?o) AS ?o1) }" ==
  "BIND variable already in scope"

-- `syntax-query/syntax-SELECTscope2.rq`, likewise negative: the outer
-- `(1 AS ?X)` aliases a name the sub-SELECT already projects.
#guard errMsg "SELECT (1 AS ?X) { SELECT (2 AS ?X) {} }" ==
  "SELECT expression aliases variable already in scope"

end L4Factoidal.SPARQL
