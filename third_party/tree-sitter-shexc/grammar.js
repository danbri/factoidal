/**
 * @file Grammar for ShEx Compact Syntax (ShExC)
 * @author ericP <eric+github@uu3.org>
 * @license MIT
 *
 * Structured after the ShExC grammar in the ShEx specification
 * (https://shex.io/shex-semantics/#shexc), cross-checked against the
 * LALR grammar shipped with shex.js (packages/shex-parser/lib/ShExJison.jison).
 * Productions are renamed to tree-sitter's snake_case and reorganized to use
 * native repeat()/repeat1()/optional()/prec() instead of synthetic
 * Foo_Star/Foo_Plus/Foo_Opt helper rules and LALR-conflict workarounds.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// ---------------------------------------------------------------------------
// Lexical building blocks (assembled into RegExps; mirrors the character
// classes in the W3C ShExC/Turtle grammars).
// ---------------------------------------------------------------------------

// Includes the supplementary-plane range #x10000-#xEFFFF, which (being
// above the BMP) can only be written as a single character-class member
// using `\u{...}` codepoint escapes -- the regexes assembled from this
// constant must therefore be compiled with the `u` flag.
const PN_CHARS_BASE =
  'A-Za-z' +
  '\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u02FF' +
  '\\u0370-\\u037D\\u037F-\\u1FFF\\u200C-\\u200D' +
  '\\u2070-\\u218F\\u2C00-\\u2FEF\\u3001-\\uD7FF' +
  '\\uF900-\\uFDCF\\uFDF0-\\uFFFD\\u{10000}-\\u{EFFFF}';

const PN_CHARS_U = PN_CHARS_BASE + '_';
const PN_CHARS = PN_CHARS_U + '\\-0-9\\u00B7\\u0300-\\u036F\\u203F-\\u2040';

const HEX = '0-9A-Fa-f';
const UCHAR = '\\\\u[' + HEX + ']{4}|\\\\U[' + HEX + ']{8}';
const PERCENT = '%[' + HEX + ']{2}';
const PN_LOCAL_ESC = "\\\\[_~.\\-!$&'()*+,;=/?#@%]";
const PLX = '(?:' + PERCENT + '|' + PN_LOCAL_ESC + ')';

const PN_PREFIX_SRC =
  '[' + PN_CHARS_BASE + ']' +
  '(?:[' + PN_CHARS + '.]*[' + PN_CHARS + '])?';
const PNAME_NS_SRC = '(?:' + PN_PREFIX_SRC + ')?:';
const PN_LOCAL_SRC =
  '(?:[' + PN_CHARS_U + ':0-9]|' + PLX + ')' +
  '(?:(?:[' + PN_CHARS + '.:]|' + PLX + ')*(?:[' + PN_CHARS + ':]|' + PLX + '))?';
const PNAME_LN_SRC = PNAME_NS_SRC + PN_LOCAL_SRC;

const ECHAR = "\\\\['\"\\\\bfnrt]";
const STRING_LITERAL1_SRC = "'(?:[^'\\\\\\n\\r]|" + ECHAR + '|' + UCHAR + ")*'";
const STRING_LITERAL2_SRC = '"(?:[^"\\\\\\n\\r]|' + ECHAR + '|' + UCHAR + ')*"';
const STRING_LITERAL_LONG1_SRC = "'''(?:(?:'|'')?(?:[^'\\\\]|" + ECHAR + '|' + UCHAR + "))*'''";
const STRING_LITERAL_LONG2_SRC = '"""(?:(?:"|"")?(?:[^"\\\\]|' + ECHAR + '|' + UCHAR + '))*"""';

const LANGTAG_SRC = '@[A-Za-z]+(?:-[0-9A-Za-z]+)*';

const IRIREF_SRC = '<(?:[^\\u0000-\\u0020<>"{}|^`\\\\]|' + UCHAR + ')*>';
const BLANK_NODE_LABEL_SRC =
  '_:(?:[' + PN_CHARS_U + '0-9])' +
  '(?:(?:[' + PN_CHARS + '.])*[' + PN_CHARS + '])?';

const EXPONENT_SRC = '[Ee][+-]?[0-9]+';
const DECIMAL_SRC = '[+-]?[0-9]*\\.[0-9]+';
const DOUBLE_SRC =
  '[+-]?(?:(?:[0-9]+\\.[0-9]*(?:' + EXPONENT_SRC + '))' +
  '|(?:\\.?[0-9]+(?:' + EXPONENT_SRC + ')))';
const INTEGER_SRC = '[+-]?[0-9]+';

const REPEAT_RANGE_SRC = '\\{[0-9]+(?:,(?:[0-9]+|\\*)?)?\\}';

const REGEXP_SRC =
  "/(?:[^/\\\\\\n\\r]|\\\\[nrt\\\\|.?*+(){}$\\u002D\\u005B\\u005D\\u005E/]|" + UCHAR + ')+/[smix]*';

const CODE_SRC = '\\{(?:[^%\\\\]|\\\\[%\\\\]|' + UCHAR + ')*%\\}';

// Case-insensitive ShExC keywords (the BNF spells these e.g. [Bb][Aa][Ss][Ee]).
const ci = word =>
  new RegExp(word.split('').map(c => `[${c.toLowerCase()}${c.toUpperCase()}]`).join(''));

export default grammar({
  name: 'shexc',

  extras: $ => [/[ \t\r\n]/, $.comment],

  rules: {
    // A leading run of directives, optionally followed by the start/shape
    // section. Directives interleaved *after* the first notStartAction or
    // startActions are reachable only via `_statement`, so the grammar
    // isn't ambiguous about which repetition "owns" a given directive.
    shex_doc: $ => seq(
      repeat($._directive),
      optional(seq($._not_start_action_or_start_actions, repeat($._statement)))
    ),

    // -----------------------------------------------------------------
    // Directives
    // -----------------------------------------------------------------

    _directive: $ => choice($.base_decl, $.prefix_decl, $.import_decl),

    base_decl: $ => seq(
      alias(ci('BASE'), $.kw_base),
      field('iri', $.irireference)
    ),

    prefix_decl: $ => seq(
      alias(ci('PREFIX'), $.kw_prefix),
      field('name', $.pname_ns),
      field('iri', $.irireference)
    ),

    import_decl: $ => seq(
      alias(ci('IMPORT'), $.kw_import),
      field('iri', $._iri)
    ),

    _not_start_action_or_start_actions: $ => choice($._not_start_action, $.start_actions),

    _not_start_action: $ => choice($.start, $.shape_expr_decl),

    _statement: $ => choice($._directive, $._not_start_action),

    start: $ => seq(
      alias(ci('START'), $.kw_start),
      '=',
      field('shape_expr', $._shape_expr)
    ),

    // Hand-rolled left-recursive list: `(codeDecl)+` is also how
    // `semantic_actions` is shaped, and tree-sitter collapses
    // structurally-identical `repeat1`/`seq+repeat` expansions into one
    // shared helper symbol -- which then can't tell, deep inside a
    // shapeExprDecl's nested node_constraint, whether it's continuing that
    // shared symbol or finishing this rule's `semantic_actions`. Writing
    // this one as explicit left recursion gives it a distinct shape so the
    // two stay separate symbols.
    start_actions: $ => choice(
      $.code_decl,
      seq($.start_actions, $.code_decl)
    ),

    // -----------------------------------------------------------------
    // Shape expression declarations
    // -----------------------------------------------------------------

    shape_expr_decl: $ => seq(
      optional(alias(ci('ABSTRACT'), $.kw_abstract)),
      field('label', $.shape_expr_label),
      field('restricts', repeat($.restriction)),
      field('shape_expr', choice($._shape_expr, $._shape_external))
    ),

    _shape_external: $ => alias(ci('EXTERNAL'), $.kw_external),

    restriction: $ => seq(
      choice(alias(ci('RESTRICTS'), $.kw_restricts), '-'),
      field('shape', $._shape_or_ref)
    ),

    // -----------------------------------------------------------------
    // Shape expressions.
    //
    // The BNF/Jison grammar layers these as shapeOr > shapeAnd > shapeNot
    // > shapeAtom, each level explicitly excluding the alternatives the
    // level above already handles (e.g. `_shapeExprOrRefNoAndOr`) -- a
    // restructuring forced by LALR(1), called out in the grammar's own
    // "Folded X_Opt back into calling productions to eliminate conflicts"
    // comment. GLR plus explicit `prec`/`prec.left` lets us instead write
    // the natural left-recursive operator chain directly and let the
    // parser sort out precedence/associativity -- the textbook
    // "precedence climbing" idiom for tree-sitter expression grammars.
    // Lower precedence number = looser binding, so OR(1) < AND(2) <
    // NOT/atom(3), matching `shapeOr`/`shapeAnd`/`shapeNot` nesting.
    // -----------------------------------------------------------------

    _shape_expr: $ => choice(
      $.shape_or, $.shape_and, $.shape_not, $.shape_atom
    ),

    shape_or: $ => prec.left(1, seq(
      field('left', $._shape_expr),
      alias(ci('OR'), $.kw_or),
      field('right', $._shape_expr)
    )),

    shape_and: $ => prec.left(2, seq(
      field('left', $._shape_expr),
      alias(ci('AND'), $.kw_and),
      field('right', $._shape_expr)
    )),

    shape_not: $ => prec(3, seq(
      alias(ci('NOT'), $.kw_not),
      field('shape_expr', $._shape_expr)
    )),

    // A non-literal node constraint and a shape definition/reference may
    // sit back to back with no connecting `AND` -- shorthand for their
    // conjunction (`IRI {<p> .}`, `@<Shape1> MinLength 3`, `<#Foo> IRI
    // {...}`); a literal constraint (LITERAL/datatype/values/bare numeric
    // facets) cannot juxtapose and stands alone (literals have no shape).
    // `shape_ref` is reachable only through this juxtaposition (mirroring
    // the source grammar's `shapeOrRef`/`shapeAtom` nesting), not also as
    // a sibling alternative -- that would let `@<label>` reduce two ways
    // and produce a reduce-reduce conflict. Likewise `node_constraint` only
    // appears here, never as a bare `_shape_expr` alternative, so a bare
    // `IRI` doesn't have two derivations.
    // `prec.right` on each juxtaposed form tells the parser to prefer
    // shifting into the optional continuation over reducing early when
    // both are possible on the same lookahead (e.g. in `<S> EXTENDS IRI
    // {<p> .}`, bind the `{...}` to the juxtaposed `IRI` rather than
    // ending the EXTENDS target at `IRI` and starting `<S>`'s own body)
    // -- the GLR analog of an LALR table's natural shift preference.
    shape_atom: $ => choice(
      prec.right(seq(
        field('constraint', $._non_lit_node_constraint),
        optional(field('shape_expr', $._shape_or_ref))
      )),
      $._lit_node_constraint,
      prec.right(seq(
        field('shape_expr', $._shape_or_ref),
        optional(field('constraint', $._non_lit_node_constraint))
      )),
      seq('(', field('shape_expr', $._shape_expr), ')'),
      alias('.', $.shape_any)
    ),

    _shape_or_ref: $ => choice($.shape_definition, $.shape_ref),

    // Inline variants appear inside triple constraints/EXTENDS bodies:
    // same OR/AND/NOT chain over inline shape definitions (no top-level
    // annotations/semantic actions -- those attach to the enclosing
    // tripleConstraint/shapeExprDecl instead).
    inline_shape_expression: $ => $._inline_shape_expr,

    _inline_shape_expr: $ => choice(
      $.inline_shape_or, $.inline_shape_and, $.inline_shape_not,
      $.inline_shape_atom
    ),

    inline_shape_or: $ => prec.left(1, seq(
      field('left', $._inline_shape_expr),
      alias(ci('OR'), $.kw_or),
      field('right', $._inline_shape_expr)
    )),

    inline_shape_and: $ => prec.left(2, seq(
      field('left', $._inline_shape_expr),
      alias(ci('AND'), $.kw_and),
      field('right', $._inline_shape_expr)
    )),

    inline_shape_not: $ => prec(3, seq(
      alias(ci('NOT'), $.kw_not),
      field('shape_expr', $._inline_shape_expr)
    )),

    inline_shape_atom: $ => choice(
      prec.right(seq(
        field('constraint', $._non_lit_node_constraint),
        optional(field('shape_expr', $._inline_shape_or_ref))
      )),
      $._lit_node_constraint,
      prec.right(seq(
        field('shape_expr', $._inline_shape_or_ref),
        optional(field('constraint', $._non_lit_node_constraint))
      )),
      seq('(', field('shape_expr', $._shape_expr), ')'),
      alias('.', $.shape_any)
    ),

    _inline_shape_or_ref: $ => choice($.inline_shape_definition, $.shape_ref),

    // Covers both `@prefix:local` (no intervening whitespace, the lexer's
    // ATPNAME_LN/ATPNAME_NS forms) and `@ <http://...>` / `@ _:b1`
    // (shapeExprLabel can be an iri or blank node either way).
    shape_ref: $ => seq('@', field('label', $.shape_expr_label)),

    // -----------------------------------------------------------------
    // Node constraints (the leaves that constrain literal/non-literal nodes)
    // -----------------------------------------------------------------

    // `node_constraint` comes in two flavors that `shape_atom` must be able
    // to tell apart *before* committing to a parse: only a "non-literal"
    // constraint (an IRI/BNODE/NONLITERAL kind, or bare string facets) may
    // juxtapose with a shape definition/reference to form an implicit AND
    // (`IRI {<p> .}`, `@<Shape1> MinLength 3`) -- a "literal" constraint
    // (LITERAL/datatype/values/bare numeric facets) stands alone. Splitting
    // them into separate rules -- both aliased to the same `node_constraint`
    // node so consumers see one uniform type -- keeps their first-token sets
    // disjoint from each other *and* from a following `shapeExprLabel`
    // (which can start like a `datatype`), so the parser can decide which
    // rule it's in, and when a juxtaposition ends, with one token of
    // lookahead. Facets alone disambiguate literal-vs-non-literal by their
    // flavor: string facets (LENGTH/PATTERN/...) constrain non-literals,
    // numeric facets (MININCLUSIVE/TOTALDIGITS/...) constrain literals --
    // the two flavors cannot mix without an explicit kind/datatype/values.
    _non_lit_node_constraint: $ => alias(prec.right(seq(
      choice(
        seq(field('node_kind', $.node_kind), repeat($.string_facet)),
        repeat1($.string_facet)
      ),
      repeat($.annotation),
      optional($.semantic_actions)
    )), $.node_constraint),

    _lit_node_constraint: $ => alias(prec.right(seq(
      choice(
        seq(alias(ci('LITERAL'), $.kw_literal), repeat($._x_facet)),
        seq(field('datatype', $._iri), repeat($._x_facet)),
        seq(field('values', $.value_set), repeat($._x_facet)),
        repeat1($.numeric_facet)
      ),
      repeat($.annotation),
      optional($.semantic_actions)
    )), $.node_constraint),

    node_kind: $ => choice(
      alias(ci('IRI'), $.kw_iri),
      alias(ci('BNODE'), $.kw_bnode),
      alias(ci('NONLITERAL'), $.kw_nonliteral)
    ),

    _x_facet: $ => choice($.string_facet, $.numeric_facet),

    string_facet: $ => choice(
      seq(field('name', $.string_length_kw), field('value', $.integer)),
      field('pattern', $.regexp)
    ),
    string_length_kw: $ => choice(
      alias(ci('LENGTH'), $.kw_length),
      alias(ci('MINLENGTH'), $.kw_minlength),
      alias(ci('MAXLENGTH'), $.kw_maxlength)
    ),

    numeric_facet: $ => choice(
      seq(field('name', $.numeric_range_kw), field('value', $._raw_numeric)),
      seq(field('name', $.numeric_length_kw), field('value', $.integer))
    ),
    numeric_range_kw: $ => choice(
      alias(ci('MININCLUSIVE'), $.kw_mininclusive),
      alias(ci('MINEXCLUSIVE'), $.kw_minexclusive),
      alias(ci('MAXINCLUSIVE'), $.kw_maxinclusive),
      alias(ci('MAXEXCLUSIVE'), $.kw_maxexclusive)
    ),
    numeric_length_kw: $ => choice(
      alias(ci('TOTALDIGITS'), $.kw_totaldigits),
      alias(ci('FRACTIONDIGITS'), $.kw_fractiondigits)
    ),
    _raw_numeric: $ => choice(
      $.integer, $.decimal, $.double,
      seq(field('value', $.string), '^^', field('datatype', $._iri))
    ),

    // -----------------------------------------------------------------
    // Value sets
    // -----------------------------------------------------------------

    value_set: $ => seq('[', repeat($._value_set_value), ']'),

    _value_set_value: $ => choice(
      $.iri_stem_range, $.literal_stem_range, $.language_stem_range,
      seq('.', $._exclusions)
    ),
    _exclusions: $ => choice(
      repeat1($.iri_exclusion),
      repeat1($.literal_exclusion),
      repeat1($.language_exclusion)
    ),

    iri_stem_range: $ => seq(
      field('stem', $._iri),
      optional(seq('~', repeat(field('exclusion', $.iri_exclusion))))
    ),
    iri_exclusion: $ => seq('-', field('stem', $._iri), optional('~')),

    literal_stem_range: $ => seq(
      field('stem', $.literal),
      optional(seq('~', repeat(field('exclusion', $.literal_exclusion))))
    ),
    literal_exclusion: $ => seq('-', field('stem', $.literal), optional('~')),

    language_stem_range: $ => choice(
      seq(
        field('stem', $.langtag),
        optional(seq('~', repeat(field('exclusion', $.language_exclusion))))
      ),
      seq('@', '~', repeat(field('exclusion', $.language_exclusion)))
    ),
    language_exclusion: $ => seq('-', field('stem', $.langtag), optional('~')),

    // -----------------------------------------------------------------
    // Shape definitions ({ ... } bodies, with EXTENDS/EXTRA/CLOSED prefixes)
    // -----------------------------------------------------------------

    shape_definition: $ => seq(
      $.inline_shape_definition,
      repeat($.annotation),
      optional($.semantic_actions)
    ),

    inline_shape_definition: $ => seq(
      repeat($._shape_definition_modifier),
      '{',
      field('expression', optional($.triple_expression)),
      '}'
    ),

    _shape_definition_modifier: $ => choice($.extension, $.extra_property_set, $._closed_kw),
    _closed_kw: $ => alias(ci('CLOSED'), $.kw_closed),

    // EXTENDS bodies cannot themselves declare EXTENDS/EXTRA/CLOSED or carry
    // annotations/semantic actions, but are otherwise full shape expressions
    // -- the regular OR/AND/NOT chain over inline atoms (which already
    // reaches `shape_ref` via `inline_shape_atom`'s juxtaposition).
    extension: $ => seq(
      choice(alias(ci('EXTENDS'), $.kw_extends), '&'),
      field('shape_expr', $._inline_shape_expr)
    ),

    extra_property_set: $ => seq(
      alias(ci('EXTRA'), $.kw_extra),
      repeat1(field('predicate', $.predicate))
    ),

    // -----------------------------------------------------------------
    // Triple expressions
    // -----------------------------------------------------------------

    triple_expression: $ => $._one_of_triple_expr,

    _one_of_triple_expr: $ => choice($.group_triple_expr, $.one_of),

    one_of: $ => prec.left(seq(
      field('disjunct', $.group_triple_expr),
      repeat1(seq('|', field('disjunct', $.group_triple_expr)))
    )),

    // `element (sep element)* sep?` as a single flattened rule -- the BNF
    // distinguishes a "singleElementGroup" (bare element, no EachOf
    // wrapper) from a "multiElementGroup" (>= 2 elements, wrapped as an
    // EachOf), but expressing those as two alternatives that both start
    // with `unaryTripleExpr (',' | ';')` is ambiguous for an LR parser
    // (which alternative owns that shared prefix can depend on what comes
    // *after* the separator). Folding them into one rule sidesteps the
    // ambiguity entirely; consumers building ShExJ can treat a single
    // `element` capture as a bare expression and >= 2 as an EachOf, same
    // as the semantic action did, just one step later.
    group_triple_expr: $ => seq(
      field('element', $._unary_triple_expr),
      repeat(seq(choice(',', ';'), field('element', $._unary_triple_expr))),
      optional(choice(',', ';'))
    ),

    _unary_triple_expr: $ => choice(
      seq(
        optional(seq('$', field('id', $.triple_expr_label))),
        choice($.triple_constraint, $.bracketed_triple_expr)
      ),
      $.include
    ),

    bracketed_triple_expr: $ => seq(
      '(',
      field('expression', $.triple_expression),
      ')',
      field('cardinality', optional($.cardinality)),
      repeat($.annotation),
      optional($.semantic_actions)
    ),

    triple_constraint: $ => seq(
      field('inverse', optional(alias('^', $.kw_inverse))),
      field('predicate', $.predicate),
      field('value_expr', $.inline_shape_expression),
      field('cardinality', optional($.cardinality)),
      repeat($.annotation),
      optional($.semantic_actions)
    ),

    cardinality: $ => choice(
      alias('*', $.card_star),
      alias('+', $.card_plus),
      alias('?', $.card_opt),
      $.repeat_range
    ),

    include: $ => seq('&', field('label', $.triple_expr_label)),

    // -----------------------------------------------------------------
    // Annotations and semantic actions
    // -----------------------------------------------------------------

    annotation: $ => seq(
      '//',
      field('predicate', $.predicate),
      field('object', choice($._iri, $.literal))
    ),

    // A run of `%name{code%}` blocks is genuinely ambiguous about which
    // enclosing optional `semantic_actions` it belongs to when e.g. a
    // node_constraint and its enclosing tripleConstraint both have one
    // immediately adjacent -- prefer attaching to the closest/innermost
    // (mirrors the greedy-shift behavior an LALR table falls into here).
    semantic_actions: $ => prec.right(repeat1($.code_decl)),

    code_decl: $ => seq(
      '%',
      field('name', $._iri),
      field('code', choice($.code, '%'))
    ),

    // -----------------------------------------------------------------
    // Labels, predicates, IRIs, literals
    // -----------------------------------------------------------------

    shape_expr_label: $ => choice($._iri, $.blank_node),
    triple_expr_label: $ => choice($._iri, $.blank_node),

    predicate: $ => choice($._iri, alias('a', $.kw_a)),
    datatype: $ => $._iri,

    _iri: $ => choice($.irireference, $.prefixed_name),
    irireference: $ => token(new RegExp(IRIREF_SRC)),
    prefixed_name: $ => choice($.pname_ln, $.pname_ns),

    pname_ns: $ => token(new RegExp(PNAME_NS_SRC, 'u')),
    pname_ln: $ => token(new RegExp(PNAME_LN_SRC, 'u')),

    blank_node: $ => token(new RegExp(BLANK_NODE_LABEL_SRC, 'u')),

    literal: $ => choice($.rdf_literal, $.numeric_literal, $.boolean_literal),

    // `"x"@en` is genuinely ambiguous at the grammar level inside a value
    // set: is it one lang-tagged literal, or a plain literal followed by a
    // languageStemRange `@en`? The BNF/Jison lexer resolves this by gluing
    // string+langtag into one LANG_STRING_LITERAL* token whenever they're
    // adjacent (maximal munch), so the parser never sees the ambiguous
    // sequence. `lang_string` mirrors that as a single atomic token --
    // tree-sitter's lexer prefers it (longer match) over `string` followed
    // by a separate `langtag`. Consumers recover the language tag the same
    // way the original parser's unescapeLangString helper does: by
    // trimming the trailing `@...` (matching `langtag`'s pattern) off the
    // token text.
    rdf_literal: $ => choice(
      $.lang_string,
      seq(field('value', $.string), optional(seq('^^', field('datatype', $.datatype))))
    ),

    lang_string: $ => token(choice(
      new RegExp(STRING_LITERAL1_SRC + LANGTAG_SRC),
      new RegExp(STRING_LITERAL2_SRC + LANGTAG_SRC),
      new RegExp(STRING_LITERAL_LONG1_SRC + LANGTAG_SRC),
      new RegExp(STRING_LITERAL_LONG2_SRC + LANGTAG_SRC)
    )),

    numeric_literal: $ => choice($.integer, $.decimal, $.double),
    boolean_literal: $ => choice(
      alias('true', $.kw_true),
      alias('false', $.kw_false)
    ),

    string: $ => choice(
      $.string_literal1, $.string_literal2,
      $.string_literal_long1, $.string_literal_long2
    ),
    string_literal1: $ => token(new RegExp(STRING_LITERAL1_SRC)),
    string_literal2: $ => token(new RegExp(STRING_LITERAL2_SRC)),
    string_literal_long1: $ => token(new RegExp(STRING_LITERAL_LONG1_SRC)),
    string_literal_long2: $ => token(new RegExp(STRING_LITERAL_LONG2_SRC)),

    // NB: the langtag must immediately follow the closing quote (no
    // whitespace) for `rdf_literal` to treat it as a language tag; we rely
    // on tree-sitter's lexer preferring the longer/more-specific match at
    // this position rather than separate LANG_STRING_LITERAL* tokens.
    // Unlike the langtag glued onto `lang_string` (which must immediately
    // follow a string with no intervening whitespace), this standalone
    // form appears in language-stem-range/exclusion value-set entries
    // (`[@fr~ - @fr-be]`) where ordinary whitespace separates it from `-`.
    langtag: $ => token(new RegExp(LANGTAG_SRC)),

    integer: $ => token(new RegExp(INTEGER_SRC)),
    decimal: $ => token(new RegExp(DECIMAL_SRC)),
    double: $ => token(new RegExp(DOUBLE_SRC)),

    repeat_range: $ => token(new RegExp(REPEAT_RANGE_SRC)),
    regexp: $ => token(new RegExp(REGEXP_SRC)),
    code: $ => token(new RegExp(CODE_SRC)),

    comment: $ => token(choice(
      seq('#', /[^\n\r]*/),
      seq('/*', /[^*]*\*+(?:[^/*][^*]*\*+)*/, '/')
    )),
  }
});

