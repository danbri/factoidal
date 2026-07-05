module ShEx.Validation

// ============================================================================
// ShEx (Shape Expressions) 2.1 — Stage 2 of the ShEx program
// (docs/designissues/2026-07-05-shex-program-plan.md): NodeConstraint
// dispatch (nodeKind, datatype, values, stem/stemRange, length/pattern/
// numeric facets, totaldigits/fractiondigits) plus a schema-aware
// ShapeAnd/ShapeOr/ShapeNot/shapeExprRef combinator that bottoms out at
// NodeConstraint leaves — NO triple-expression partition matching (Stage 3),
// NO data-graph traversal (a `Shape`'s "expression" is deliberately left
// unsupported here; evaluating it needs the arc-signature/backtracking
// machinery Stage 3 builds), NO recursion/negation-stratification (Stage 5).
//
// Reuse discipline (per the plan's "transliterate the computation, not the
// module" note): this module does NOT `open SHACL.Validation` — ShExJ's AST
// shapes differ from SHACL's RDF-graph-encoded shapes, so the SHACL module's
// constraint-component dispatch isn't directly callable here. It DOES reuse
// the datatype-level arithmetic that both languages need identically, via
// `XSD.Datatypes` (issue #235 slice 1's reusable-foundations module):
// literal_to_scaled/scaled_cmp/literal_ill_formed are the exact SAME
// functions SHACL.Validation.fst now calls, not reimplementations — the one
// place a ShEx-vs-SHACL semantic difference could sneak in via drift.
// `SPARQL11.Algebra.regex_match` (an `assume val` host-engine call-out, rule
// #11's acceptable form) is reused directly for the `pattern` facet, same as
// SHACL's `CC_Pattern`.
//
// `option bool` result convention (mirrors the decode functions' `option`
// idiom rather than inventing a new sum type): `None` means "this
// shapeExpr/fuel budget is outside Stage 2's reach" (a `Shape` with a triple
// expression, `ShapeExternal`, an unresolvable shapeExprRef, or fuel
// exhaustion) — never a silently-wrong verdict. `Some b` is a definite
// pass/fail. `ShapeAnd`/`ShapeOr` are short-circuit-aware: a definite `false`
// wins an AND even if a sibling conjunct is `None`, and a definite `true`
// wins an OR the same way (matches ordinary 3-valued boolean short-circuit
// logic — an AND with one false conjunct is false regardless of whether the
// others could be evaluated).
//
// Facet semantics cross-checked against shex.io/shex-semantics (ShEx 2.1,
// Final CG Report, 2019-10-08), section 5.4.5/5.4.6:
//   - length/minlength/maxlength/pattern apply uniformly to the "lex" of
//     ANY node kind (IRI string, BNode label, or Literal lexical form) —
//     not literals only.
//   - `datatype` requires BOTH the datatype IRI to match AND (for datatypes
//     XSD/SPARQL define a lexical space for) the lexical form to be
//     well-formed in that space — `XSD.Datatypes.literal_ill_formed` already
//     restricts itself to exactly that set and is conservative (never flags
//     datatypes it doesn't recognise), so this holds for arbitrary
//     corpus-custom datatypes (e.g. `focusdatatype.json`'s bloodType) for
//     free: equality alone decides those.
//   - mininclusive/maxinclusive/minexclusive/maxexclusive compare the
//     NUMERIC value only (XPath numeric-type promotion) — unlike SHACL's
//     sh:minInclusive/etc. these ShExJ facets are not extended to
//     xsd:dateTime ordering in the spec's own facet grammar, so this module
//     does not attempt dateTime comparison for them (a documented gap, not
//     silently wrong: comparison returns `None`/fails-closed when either
//     side doesn't parse as a number).
//   - totaldigits/fractiondigits are defined against a literal's "XML Schema
//     canonical form," which is NOT implemented here (no leading-zero
//     stripping, no canonical exponent normalisation) — this module counts
//     digits directly on the RAW lexical form instead (trailing zeros are
//     stripped after the decimal point for fractiondigits, matching the
//     spec's "ignoring trailing zeros" clause, but leading zeros before the
//     decimal point are NOT stripped). Flagged here rather than silently
//     assumed equivalent; revisit if a corpus fixture needs true canonical
//     form.
// ============================================================================

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open ShEx.Schema
open XSD.Datatypes

// Alias, not `open` — SPARQL11.Algebra defines SPARQL-expression machinery
// whose short names would collide with this module's own vocabulary; only
// `regex_match` (an assume val, not re-exported by XSD.Datatypes) is used
// from it directly.
module Alg = SPARQL11.Algebra

// ================================================================
// Small string/char helpers not already provided by XSD.Datatypes /
// RDF.Graph.Executable.
// ================================================================

// Non-strict prefix test (the stem itself counts as a match — "an IRI
// matches an IriStem if the IRI starts with the stem value", and the stem
// value trivially starts with itself). Distinct from RDF.Pretty's
// `starts_with_strict`, which deliberately excludes the equal-length case.
let shex_starts_with (s pfx : string) : bool =
  let pl = String.length pfx in
  let sl = String.length s in
  sl >= pl && String.sub s 0 pl = pfx

// Basic language-range filtering (RFC 4647 §2.1, referenced by the ShEx
// spec for LanguageStem/LanguageStemRange): a range matches a tag if the
// range equals the tag, or is a "-"-bounded prefix of it (so "en" matches
// "en" and "en-US" but not "english").
let lang_range_matches (tag range : string) : bool =
  let tag_l = String.lowercase tag in
  let range_l = String.lowercase range in
  if tag_l = range_l then true
  else
    let rl = String.length range_l in
    let tl = String.length tag_l in
    tl > rl && String.sub tag_l 0 rl = range_l && String.sub tag_l rl 1 = "-"

// The generic "lex" the length/minlength/maxlength/pattern facets operate
// on — defined uniformly over all three RDF node kinds (shex.io-semantics
// §5.4.5), unlike SHACL's term_lexical (which returns None for a BNode).
let shex_lex (t : rdf_term) : string =
  match t with
  | T_IRI i     -> i
  | T_BNode b   -> b
  | T_Literal l -> l.lexical_form

let is_ascii_digit_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

let total_digit_count (s : string) : nat =
  List.Tot.length (List.Tot.filter is_ascii_digit_char (String.list_of_string s))

let rec chars_after_dot (chars : list FStar.Char.char)
  : Tot (option (list FStar.Char.char)) (decreases chars) =
  match chars with
  | [] -> None
  | c :: rest -> if FStar.Char.int_of_char c = 46 (* '.' *) then Some rest else chars_after_dot rest

// Strips trailing '0' characters (fuel-bounded rather than structural: each
// step re-reverses the list, which isn't a subterm of the previous one from
// F*'s termination-checker's point of view, so this uses the same
// fuel-decreasing idiom as the rest of the codebase's non-structural
// recursions). Seed fuel = length of the input list, a safe generous bound
// (at most that many characters can ever be stripped).
let rec strip_trailing_zeros_fuel (chars : list FStar.Char.char) (fuel : nat)
  : Tot (list FStar.Char.char) (decreases fuel) =
  if fuel = 0 then chars
  else
    match List.Tot.rev chars with
    | [] -> []
    | c :: rest ->
      if FStar.Char.int_of_char c = 48 (* '0' *)
      then strip_trailing_zeros_fuel (List.Tot.rev rest) (fuel - 1)
      else chars

let fraction_digit_count (s : string) : nat =
  match chars_after_dot (String.list_of_string s) with
  | None -> 0
  | Some frac ->
    let trimmed = strip_trailing_zeros_fuel frac (List.Tot.length frac) in
    List.Tot.length (List.Tot.filter is_ascii_digit_char trimmed)

// Numeric comparison for the four ShExJ inclusive/exclusive facets. Both
// sides are parsed double-aware (anti-pattern #8: try parse_double_to_scaled
// before a bare-integer parse, or E-notation facet/literal lexemes get
// mis-parsed) via XSD.Datatypes's re-export of
// SPARQL11.Algebra.parse_double_to_scaled. `None` on either side (non-numeric
// lexical form) fails the comparison closed, matching the spec's "v is
// numeric" precondition.
let shex_numeric_le (a b : string) : option bool =
  match parse_double_to_scaled a, parse_double_to_scaled b with
  | Some sa, Some sb -> Some (scaled_cmp sa sb <= 0)
  | _, _ -> None

let shex_numeric_lt (a b : string) : option bool =
  match parse_double_to_scaled a, parse_double_to_scaled b with
  | Some sa, Some sb -> Some (scaled_cmp sa sb < 0)
  | _, _ -> None

// ================================================================
// nodeKind + datatype dispatch.
// ================================================================

let shex_node_kind_ok (nk : shex_node_kind) (t : rdf_term) : bool =
  match nk, t with
  | ShexNK_Iri, T_IRI _        -> true
  | ShexNK_BNode, T_BNode _    -> true
  | ShexNK_NonLiteral, T_IRI _   -> true
  | ShexNK_NonLiteral, T_BNode _ -> true
  | ShexNK_Literal, T_Literal _  -> true
  | _, _ -> false

// `dt` arrives as a plain (unrefined) string from ShEx.Schema's decoder — no
// proof it satisfies `is_iri` was ever available at decode time (it's
// untrusted JSON input). The `if is_iri dt then ...` guard is the same
// idiom SHACL.Validation.fst's `shape_ref_to_term` uses to promote a plain
// string to `wf_iri` inside a branch where the refinement is known to hold;
// outside that branch (a malformed non-IRI "datatype" string in the
// fixture) well-formedness simply isn't checked, which can only ADD
// leniency for a pathological input, never accept something the spec
// requires rejecting via the equality check that already ran.
let shex_datatype_ok (dt : string) (t : rdf_term) : bool =
  match t with
  | T_Literal l ->
    l.datatype = dt &&
    (if is_iri dt then not (literal_ill_formed dt l.lexical_form) else true)
  | _ -> false

// ================================================================
// "values" facet: value_set_value matching, including stems/stemRanges/
// language variants and their exclusion lists. Fuel-bounded on a
// structural size measure (same discipline as ShEx.Schema's JSON decoder)
// since `exclusions` recurses into the same sum type.
// ================================================================

let stem_matches (st : shex_stem) (s : string) : bool =
  match st with
  | ShexStemWildcard  -> true
  | ShexStemPlain pfx -> shex_starts_with s pfx

// Exact ObjectValue match. Absent "type" defaults to xsd:string (no
// language); absent "language" means no language constraint UNLESS the
// ShExJ source set it to the empty string, which is the spec's explicit
// "must not have a language tag" marker — both readings collapse into one
// check here since `l.lang_tag = None` is exactly what "no language" means.
let object_value_matches (ov : shex_object_value) (t : rdf_term) : bool =
  match ov, t with
  | ShexOV_Iri i, T_IRI ti -> i = ti
  | ShexOV_Literal value lang dt, T_Literal l ->
    l.lexical_form = value &&
    (match lang with
     | Some lg ->
       if lg = "" then None? l.lang_tag
       else (match l.lang_tag with Some tlg -> lang_tag_eq lg tlg | None -> false)
     | None ->
       (match dt with
        | Some d -> l.datatype = d && None? l.lang_tag
        | None -> l.datatype = xsd_string && None? l.lang_tag))
  | _, _ -> false

let rec vsv_size (v : shex_value_set_value) : Tot nat (decreases v) =
  match v with
  | VSV_IriStemRange _ excl      -> 1 + vsv_list_size excl
  | VSV_LiteralStemRange _ excl  -> 1 + vsv_list_size excl
  | VSV_LanguageStemRange _ excl -> 1 + vsv_list_size excl
  | _ -> 1
and vsv_list_size (l : list shex_value_set_value) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | hd :: tl -> 1 + vsv_size hd + vsv_list_size tl

let rec vsv_matches (vsv : shex_value_set_value) (t : rdf_term) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let fuel' = fuel - 1 in
    match vsv with
    | VSV_Value ov -> object_value_matches ov t
    | VSV_IriStem st ->
      (match t with T_IRI i -> stem_matches st i | _ -> false)
    | VSV_IriStemRange st excl ->
      (match t with
       | T_IRI i -> stem_matches st i && not (vsv_list_exists excl t fuel')
       | _ -> false)
    | VSV_LiteralStem st ->
      (match t with T_Literal l -> stem_matches st l.lexical_form | _ -> false)
    | VSV_LiteralStemRange st excl ->
      (match t with
       | T_Literal l -> stem_matches st l.lexical_form && not (vsv_list_exists excl t fuel')
       | _ -> false)
    | VSV_Language lt ->
      (match t with
       | T_Literal l -> (match l.lang_tag with Some tag -> lang_tag_eq lt tag | None -> false)
       | _ -> false)
    | VSV_LanguageStem st ->
      (match t with
       | T_Literal l ->
         (match l.lang_tag with
          | Some tag -> (match st with ShexStemWildcard -> true | ShexStemPlain s -> lang_range_matches tag s)
          | None -> false)
       | _ -> false)
    | VSV_LanguageStemRange st excl ->
      (match t with
       | T_Literal l ->
         (match l.lang_tag with
          | Some tag ->
            let base_ok = (match st with ShexStemWildcard -> true | ShexStemPlain s -> lang_range_matches tag s) in
            base_ok && not (vsv_list_exists excl t fuel')
          | None -> false)
       | _ -> false)
// `exists v in items. vsv_matches v t` — reused both for the top-level
// "values" facet (satisfied by any listed value_set_value) and for an
// exclusion list (excluded by any listed value_set_value), matching the
// spec's "there is no x in excls such that nodeIn(n, x)" phrasing directly.
and vsv_list_exists (items : list shex_value_set_value) (t : rdf_term) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match items with
    | [] -> false
    | hd :: tl -> if vsv_matches hd t (fuel - 1) then true else vsv_list_exists tl t (fuel - 1)

let values_ok (values : list shex_value_set_value) (t : rdf_term) : bool =
  if Nil? values then true
  else vsv_list_exists values t (1 + vsv_list_size values)

// ================================================================
// Full NodeConstraint dispatch — conjunction of every present facet.
// Absent facets are vacuously satisfied (`None` in the AST = "not
// constrained"), matching ShExJ's "all present members constrain" reading.
// ================================================================

let node_constraint_matches (nc : shex_node_constraint) (t : rdf_term) : bool =
  let nk_ok = match nc.nc_node_kind with None -> true | Some nk -> shex_node_kind_ok nk t in
  let dt_ok = match nc.nc_datatype with None -> true | Some dt -> shex_datatype_ok dt t in
  let vs_ok = values_ok nc.nc_values t in
  let lex = shex_lex t in
  let length_ok    = match nc.nc_length    with None -> true | Some n -> String.length lex = n in
  let minlength_ok = match nc.nc_minlength with None -> true | Some n -> String.length lex >= n in
  let maxlength_ok = match nc.nc_maxlength with None -> true | Some n -> String.length lex <= n in
  let flags_opt = match nc.nc_flags with Some "" -> None | f -> f in
  let pattern_ok = match nc.nc_pattern with None -> true | Some re -> Alg.regex_match lex re flags_opt in
  // Numeric-only facets: T_IRI/T_BNode never satisfy a present numeric
  // facet (there is no lexical form to parse as a number for them in any
  // useful sense — the spec's "v is numeric" precondition fails closed).
  let num_lex = match t with T_Literal l -> Some l.lexical_form | _ -> None in
  let mininclusive_ok =
    match nc.nc_mininclusive, num_lex with
    | None, _ -> true
    | Some facet, Some nlex -> shex_numeric_le facet nlex = Some true
    | Some _, None -> false in
  let maxinclusive_ok =
    match nc.nc_maxinclusive, num_lex with
    | None, _ -> true
    | Some facet, Some nlex -> shex_numeric_le nlex facet = Some true
    | Some _, None -> false in
  let minexclusive_ok =
    match nc.nc_minexclusive, num_lex with
    | None, _ -> true
    | Some facet, Some nlex -> shex_numeric_lt facet nlex = Some true
    | Some _, None -> false in
  let maxexclusive_ok =
    match nc.nc_maxexclusive, num_lex with
    | None, _ -> true
    | Some facet, Some nlex -> shex_numeric_lt nlex facet = Some true
    | Some _, None -> false in
  let totaldigits_ok =
    match nc.nc_totaldigits, num_lex with
    | None, _ -> true
    | Some n, Some nlex -> total_digit_count nlex <= n
    | Some _, None -> false in
  let fractiondigits_ok =
    match nc.nc_fractiondigits, num_lex with
    | None, _ -> true
    | Some n, Some nlex -> fraction_digit_count nlex <= n
    | Some _, None -> false in
  nk_ok && dt_ok && vs_ok && length_ok && minlength_ok && maxlength_ok && pattern_ok &&
  mininclusive_ok && maxinclusive_ok && minexclusive_ok && maxexclusive_ok &&
  totaldigits_ok && fractiondigits_ok

// ================================================================
// Schema-aware boolean-combinator layer: ShapeAnd/ShapeOr/ShapeNot/
// shapeExprRef over shapeExprs that bottom out at NodeConstraint. Does NOT
// descend into a `Shape`'s "expression" (that's Stage 3's triple-expression
// partition-matching territory, which needs a data graph this function
// never receives) — hitting one returns `None` ("outside Stage 2's reach"),
// same as `ShapeExternal` (SemActs/EXTERNAL scope cut) and an unresolvable
// shapeExprRef label.
// ================================================================

let rec lookup_shape_decl (decls : list shex_shape_decl) (label : string)
  : Tot (option shex_shape_decl) (decreases decls) =
  match decls with
  | [] -> None
  | hd :: tl -> if hd.sd_id = label then Some hd else lookup_shape_decl tl label

// `option bool`: None = outside Stage 2's reach or fuel exhausted; Some b =
// a definite verdict. ShapeAnd/ShapeOr are short-circuit-aware — see the
// file banner comment for why a concrete false/true outranks a sibling
// `None` instead of the whole conjunction/disjunction collapsing to None.
let rec matches_shape_expr (decls : list shex_shape_decl) (se : shex_shape_expr) (t : rdf_term) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match se with
    | SE_NodeConstraint nc -> Some (node_constraint_matches nc t)
    | SE_ShapeAnd ses -> matches_all decls ses t fuel'
    | SE_ShapeOr ses  -> matches_any decls ses t fuel'
    | SE_ShapeNot se' ->
      (match matches_shape_expr decls se' t fuel' with
       | Some b -> Some (not b)
       | None -> None)
    | SE_Ref label ->
      (match lookup_shape_decl decls label with
       | Some sd -> matches_shape_expr decls sd.sd_expr t fuel'
       | None -> None)
    | SE_Shape _ -> None
    | SE_ShapeExternal -> None
and matches_all (decls : list shex_shape_decl) (ses : list shex_shape_expr) (t : rdf_term) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some true
    | hd :: tl ->
      (match matches_shape_expr decls hd t fuel', matches_all decls tl t fuel' with
       | Some false, _ -> Some false
       | _, Some false -> Some false
       | Some true, Some true -> Some true
       | _, _ -> None)
and matches_any (decls : list shex_shape_decl) (ses : list shex_shape_expr) (t : rdf_term) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some false
    | hd :: tl ->
      (match matches_shape_expr decls hd t fuel', matches_any decls tl t fuel' with
       | Some true, _ -> Some true
       | _, Some true -> Some true
       | Some false, Some false -> Some false
       | _, _ -> None)

// Top-level entry point: validate one focus node against a schema, either
// by an explicit shape label (the manifest's `sht:shape`) or the schema's
// own `start` shapeExpr (`sht:shape` absent). Fuel is derived from the
// schema's own shape count (a hop through `SE_Ref` visits at most that many
// distinct decls before repeating, and ShapeAnd/ShapeOr nesting in the
// corpus is shallow) rather than a bare unexplained constant.
let validate_focus (schema : shex_schema) (shape_id : option string) (t : rdf_term) : option bool =
  let fuel = 100 + op_Multiply 20 (List.Tot.length schema.sch_shapes) in
  match shape_id with
  | Some label ->
    (match lookup_shape_decl schema.sch_shapes label with
     | Some sd -> matches_shape_expr schema.sch_shapes sd.sd_expr t fuel
     | None -> None)
  | None ->
    (match schema.sch_start with
     | Some se -> matches_shape_expr schema.sch_shapes se t fuel
     | None -> None)
