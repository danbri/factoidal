; Comments
(comment) @comment

; Strings and language tags
[
  (string)
  (lang_string)
  (langtag)
] @string

; Numbers
[
  (integer)
  (decimal)
  (double)
] @number

; Literal constants: booleans, IRIs, blank nodes
[
  (boolean_literal)
  (kw_true)
  (kw_false)
  (irireference)
  (prefixed_name)
  (blank_node)
] @constant

; Keywords
[
  (kw_a)
  (kw_abstract)
  (kw_and)
  (kw_base)
  (kw_bnode)
  (kw_closed)
  (kw_extends)
  (kw_external)
  (kw_extra)
  (kw_fractiondigits)
  (kw_import)
  (kw_iri)
  (kw_length)
  (kw_literal)
  (kw_maxexclusive)
  (kw_maxinclusive)
  (kw_maxlength)
  (kw_minexclusive)
  (kw_mininclusive)
  (kw_minlength)
  (kw_nonliteral)
  (kw_not)
  (kw_or)
  (kw_prefix)
  (kw_restricts)
  (kw_start)
  (kw_totaldigits)
  (shape_any)
] @keyword

; Prefixes and datatypes
(prefix_decl name: (_) @type)
(node_constraint [(irireference) (prefixed_name)] @type)

; Predicates
(triple_constraint predicate: (predicate) @property)
(annotation predicate: (_) @property)

; Shape / triple-expression definitions
(shape_expr_decl label: (shape_expr_label) @function)
(group_triple_expr (triple_expr_label) @function)
(include label: (triple_expr_label) @function)

; Shape references (@<Shape>)
(shape_ref label: (shape_expr_label) @variable)

; Semantic actions / embedded code
(code_decl name: (_) @keyword.directive)
(code) @keyword.directive

; Punctuation
["{" "}" "[" "]" "(" ")"] @punctuation.bracket
["," ";"] @punctuation.delimiter

; Operators
[
  "."
  "|"
  "&"
  "@"
  "~"
  "-"
  "="
] @operator
[
  (card_star)
  (card_plus)
  (card_opt)
  (kw_inverse)
] @operator
