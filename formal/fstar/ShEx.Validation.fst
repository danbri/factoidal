module ShEx.Validation

// ============================================================================
// ShEx (Shape Expressions) 2.1 — Stage 2 + Stage 3 of the ShEx program
// (docs/designissues/2026-07-05-shex-program-plan.md).
//
// Stage 2 (unchanged): NodeConstraint dispatch (nodeKind, datatype, values,
// stem/stemRange, length/pattern/numeric facets, totaldigits/fractiondigits)
// plus a schema-aware ShapeAnd/ShapeOr/ShapeNot/shapeExprRef combinator that
// bottoms out at NodeConstraint leaves.
//
// Stage 3 (this revision): triple-expression matching for `Shape` —
// TripleConstraint/EachOf, the plan's "disjoint-predicate fast path only"
// design (see the plan's "Partition-semantics design sketch"). A Shape's
// `expression` is decided by:
//   1. Statically checking `te_fastpath_ok`: the whole tripleExpr tree
//      contains no TE_OneOf, no TE_Ref, and no cardinality-wrapped group
//      (RepeatedGroup/Greedy — `gr_min`/`gr_max` present), AND every EachOf
//      node's children have pairwise-disjoint arc signatures (the set of
//      (inverse, predicate) pairs a subtree can consume). If this check
//      fails anywhere in the tree, the WHOLE shape's expression evaluation
//      is `None` (Stage 4/5 territory) — never a guessed verdict.
//   2. When fast-path-valid, per plan §"Fast path": group the focus node's
//      relevant triples by predicate (no shared-predicate ambiguity possible
//      once disjointness holds) and check each TripleConstraint's
//      [min,max] + valueExpr satisfaction independently.
//   3. `extra`: a predicate present in `sh_extra` tolerates leftover
//      (unmatched-by-count or failing-valueExpr) triples of that predicate
//      REGARDLESS of `closed` — otherwise every candidate triple for a
//      predicate the expression mentions must be part of the matched
//      [min,max] set (see `matches_triple_expr_value`'s `allowed_extra`
//      branch). `closed` (separately, in `matches_shape`) only bounds
//      triples whose predicate is not mentioned by the expression AT ALL —
//      it never relaxes a mentioned predicate's own cardinality. (These are
//      two different clauses of the spec's satisfies(n,Shape,G); conflating
//      them — "not closed" also granting a mentioned predicate's own
//      leftover tolerance — was an actual bug caught by the Stage 3
//      measurement run, see `matches_triple_expr_value`'s doc comment.)
// NO backtracking slow path (TE_OneOf, ambiguous shared-predicate siblings —
// Stage 4), NO recursion/negation-stratification (Stage 5).
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
// idiom rather than inventing a new sum type): `None` means "outside this
// stage's reach" — `ShapeExternal`, an unresolvable shapeExprRef/
// tripleExprRef, a non-fast-path triple expression (TE_OneOf, a
// cardinality-wrapped group, overlapping-signature siblings — Stage 4/5), or
// fuel exhaustion — never a silently-wrong verdict. `Some b` is a definite
// pass/fail. `ShapeAnd`/`ShapeOr` (and the EachOf conjunction below) are
// short-circuit-aware: a definite `false` wins an AND even if a sibling
// conjunct is `None`, and a definite `true` wins an OR the same way (matches
// ordinary 3-valued boolean short-circuit logic — an AND with one false
// conjunct is false regardless of whether the others could be evaluated).
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
//     canonical form": leading zeros before the decimal point and trailing
//     zeros after it are stripped before counting (Stage 3 fix — the Stage 2
//     version counted raw digit characters only, undercounting-safe in the
//     max-bound direction but wrong for `01.2345 TOTALDIGITS 5`-style
//     fixtures the Stage 3 measurement run surfaced). Applicability is now
//     (XSD.Datatypes gap-closure fix, 2026-07-05) gated to xsd:decimal and
//     decimal-derived types ONLY via `digits_lex` above, per XML Schema
//     Part 2 SS4.3.11/4.3.12 and the corpus's own explicit
//     "restricted to decimal-derived datatypes" fixture notes — xsd:float/
//     xsd:double literals fail these two facets closed regardless of digit
//     count, which also retires the earlier "no canonical EXPONENT
//     normalisation for float/double" gap this comment used to disclose:
//     since the facet never applies to float/double at all, no
//     scientific-notation-aware digit counting is needed for them.
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
// "en" and "en-US" but not "english"). The EMPTY range is a special case
// unique to ShEx's `LanguageStem`/`LanguageStemRange` — `{"stem": ""}` is
// the ShExJ encoding of the ShExC `@~` shorthand ("any language tag"),
// distinct from the `{"type":"Wildcard"}` object form `shex_stem` also
// carries (that one is only legal directly inside a *StemRange's own
// "stem" slot, per ShEx.Schema.fst's `decode_stem` doc comment) — an empty
// PLAIN stem string reaching this function is the SAME "any language"
// intent, just spelled as `ShexStemPlain ""` instead of `ShexStemWildcard`.
// Without this case, the "-"-boundary check below rejects every tag
// (`String.sub tag_l 0 1` is never "-"), silently breaking `[@~]` — caught
// by the Stage 3 measurement run (`1val1emptylanguageStem_passLAtfr`, ShExC
// `[@~]` on `"septante"@fr`, expected PASS).
let lang_range_matches (tag range : string) : bool =
  if range = "" then true
  else
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

let rec chars_before_dot (chars : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases chars) =
  match chars with
  | [] -> []
  | c :: rest -> if FStar.Char.int_of_char c = 46 (* '.' *) then [] else c :: chars_before_dot rest

let rec chars_after_dot (chars : list FStar.Char.char)
  : Tot (option (list FStar.Char.char)) (decreases chars) =
  match chars with
  | [] -> None
  | c :: rest -> if FStar.Char.int_of_char c = 46 (* '.' *) then Some rest else chars_after_dot rest

// Strips leading '0' characters — structural (each step consumes the head),
// unlike the trailing-zero stripper below (which needs fuel because
// reversing isn't a visible subterm decrease).
let rec strip_leading_zeros (chars : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases chars) =
  match chars with
  | c :: rest -> if FStar.Char.int_of_char c = 48 (* '0' *) then strip_leading_zeros rest else chars
  | [] -> []

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

// totaldigits counts significant digits per XML Schema's canonical-form
// rule ("leading and trailing zeros are not significant"): strip leading
// zeros from the integer part (before any '.') and trailing zeros from the
// fraction part (after it), then count remaining digit characters in both.
// This is a Stage 3 fix to a documented Stage 2 gap (the file banner used
// to disclose "no leading-zero stripping... revisit if a corpus fixture
// needs true canonical form") — the Stage 3 measurement run surfaced
// exactly such fixtures (e.g. `1literalTotaldigits_pass-decimal-equalLead`,
// TOTALDIGITS 5 against literal `01.2345`: 6 raw digit characters, 5
// significant once the leading zero is stripped).
let total_digit_count (s : string) : nat =
  let chars = String.list_of_string s in
  let before = strip_leading_zeros (chars_before_dot chars) in
  let after = match chars_after_dot chars with
    | None -> []
    | Some frac -> strip_trailing_zeros_fuel frac (List.Tot.length frac) in
  List.Tot.length (List.Tot.filter is_ascii_digit_char before) +
  List.Tot.length (List.Tot.filter is_ascii_digit_char after)

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
  // totaldigits/fractiondigits ONLY (not the four inclusive/exclusive
  // facets above, which the spec's own numeric-value semantics keep
  // applicable to xsd:float/xsd:double): XML Schema Part 2 SS4.3.11/
  // 4.3.12 define totalDigits/fractionDigits as facets of xsd:decimal
  // and its decimal-derived subtypes ONLY — never xsd:float/xsd:double,
  // confirmed against the corpus's own
  // "Note: totalDigits/fractionDigits restricted to decimal-derived
  // datatypes" fixture comments (1literalTotaldigits_fail-float-equal /
  // -double-equal, 1literalFractiondigits_fail-float-equal / -double-equal).
  // `digits_lex` is `Some` only when BOTH hold: the literal's datatype is
  // decimal-derived (`XSD.Datatypes.is_decimal_derived_datatype`) AND its
  // lexical form is well-formed for that datatype
  // (`not (literal_ill_formed ...)`, reusing the SAME conservative check
  // `shex_datatype_ok` already applies for the `datatype` facet — a
  // malformed decimal/integer literal, e.g. "1.23ab"^^xsd:decimal or
  // "1.2345"^^xsd:integer (integer's lexical space forbids '.'), has no
  // well-defined digit count to constrain). Otherwise `None`, which the
  // existing `Some _, None -> false` fail-closed arms below already
  // handle correctly — no new fail-closed logic needed, only this gate
  // on what counts as an applicable input.
  let digits_lex =
    match t with
    | T_Literal l ->
      if is_decimal_derived_datatype l.datatype && not (literal_ill_formed l.datatype l.lexical_form)
      then Some l.lexical_form else None
    | _ -> None in
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
    match nc.nc_totaldigits, digits_lex with
    | None, _ -> true
    | Some n, Some nlex -> total_digit_count nlex <= n
    | Some _, None -> false in
  let fractiondigits_ok =
    match nc.nc_fractiondigits, digits_lex with
    | None, _ -> true
    | Some n, Some nlex -> fraction_digit_count nlex <= n
    | Some _, None -> false in
  nk_ok && dt_ok && vs_ok && length_ok && minlength_ok && maxlength_ok && pattern_ok &&
  mininclusive_ok && maxinclusive_ok && minexclusive_ok && maxexclusive_ok &&
  totaldigits_ok && fractiondigits_ok

// ================================================================
// Stage 3: triple-expression matching — arc signatures + the
// disjoint-predicate fast path. All structural (no `fuel`; a decoded
// `shex_triple_expr` is a genuine finite tree, unlike the JSON decoders that
// needed fuel because `json_val` recursion isn't visibly structural to F*).
// ================================================================

// The set of (inverse, predicate) pairs a triple expression can consume —
// direction-aware per the plan's design sketch, since an `inverse`
// TripleConstraint on predicate `p` draws from a disjoint pool of triples
// (arcsIn) from a non-inverse TripleConstraint on the same `p` (arcsOut), so
// they are never in conflict even though they share a predicate string.
// `None` = "cannot compute a safe signature": a tripleExprRef (unresolved —
// no schema-wide tripleExpr-by-id table exists yet, unlike shapeExprRef's
// `sch_shapes`) or a `OneOf` (ambiguity resolution is Stage 4's backtracking
// slow path, never approximated here).
let rec te_signature (te : shex_triple_expr) : Tot (option (list (bool & string))) (decreases te) =
  match te with
  | TE_Ref _ -> None
  | TE_OneOf _ -> None
  | TE_TripleConstraint tc -> Some [(tc.tc_inverse, tc.tc_predicate)]
  | TE_EachOf grp ->
    // A cardinality-wrapped EachOf (`gr_min`/`gr_max` present — the
    // "RepeatedGroup"/"Greedy" corpus trait) needs the Stage 4 repetition
    // search even when its children are individually disjoint, because a
    // single T splits into k copies of the whole group rather than one
    // partition — signature disjointness alone does not decide it.
    if Some? grp.gr_min || Some? grp.gr_max then None
    else te_signature_list grp.gr_expressions
and te_signature_list (tes : list shex_triple_expr) : Tot (option (list (bool & string))) (decreases tes) =
  match tes with
  | [] -> Some []
  | hd :: tl ->
    (match te_signature hd, te_signature_list tl with
     | Some s1, Some s2 -> Some (List.Tot.append s1 s2)
     | _, _ -> None)

let sig_mem (x : bool & string) (l : list (bool & string)) : bool =
  List.Tot.existsb (fun y -> fst x = fst y && snd x = snd y) l

let rec sig_disjoint (a b : list (bool & string)) : Tot bool (decreases a) =
  match a with
  | [] -> true
  | hd :: tl -> not (sig_mem hd b) && sig_disjoint tl b

// Whole-tree fast-path validity: every node is signature-computable (no
// OneOf/Ref/cardinality-wrapped-group anywhere) AND every EachOf's children
// are pairwise disjoint — checked at every nesting level, so two
// TripleConstraints sharing a predicate are caught at their nearest common
// EachOf ancestor no matter how deep either is nested (the union computed by
// `te_signature` on each side carries the shared predicate up to that
// ancestor's disjointness check).
let rec te_fastpath_ok (te : shex_triple_expr) : Tot bool (decreases te) =
  match te with
  | TE_TripleConstraint _ -> true
  | TE_Ref _ -> false
  | TE_OneOf _ -> false
  | TE_EachOf grp ->
    if Some? grp.gr_min || Some? grp.gr_max then false
    else te_fastpath_ok_list grp.gr_expressions
and te_fastpath_ok_list (tes : list shex_triple_expr) : Tot bool (decreases tes) =
  match tes with
  | [] -> true
  | hd :: tl ->
    te_fastpath_ok hd && te_fastpath_ok_list tl &&
    (match te_signature hd, te_signature_list tl with
     | Some s1, Some s2 -> sig_disjoint s1 s2
     | _, _ -> false)

// Predicates a triple expression definitely claims (non-inverse only — an
// `inverse` TripleConstraint's triples have the FOCUS node as OBJECT, not
// subject, so they never appear in `arcsOut(focus)` and are irrelevant to
// the `closed`/`extra` check below, which is defined over arcsOut only).
// `None` propagates conservatively through TE_Ref/TE_OneOf: since we cannot
// know what predicates an unresolved/ambiguous subtree would ultimately
// claim, a `closed` check must not risk a false "unclaimed" verdict against
// it — see `matches_shape`, which defers (`None`) rather than guessing
// `Some false` whenever `claimed_opt` is `None`.
let rec te_claimed_predicates (te : shex_triple_expr) : Tot (option (list string)) (decreases te) =
  match te with
  | TE_TripleConstraint tc -> Some (if tc.tc_inverse then [] else [tc.tc_predicate])
  | TE_EachOf grp -> te_claimed_predicates_list grp.gr_expressions
  | TE_OneOf _ -> None
  | TE_Ref _ -> None
and te_claimed_predicates_list (tes : list shex_triple_expr) : Tot (option (list string)) (decreases tes) =
  match tes with
  | [] -> Some []
  | hd :: tl ->
    (match te_claimed_predicates hd, te_claimed_predicates_list tl with
     | Some a, Some b -> Some (List.Tot.append a b)
     | _, _ -> None)

// Gathers the "other endpoint" terms of the focus node's arcs relevant to
// one TripleConstraint — arcsOut (focus is subject) for a non-inverse
// constraint, arcsIn (focus is object) for an inverse one. Not part of the
// fuel-threaded mutual group: `find_objects`/`find_subjects` are already
// `Tot` (RDF.Graph.Executable), so this is a plain helper. `tc_predicate`
// arrives as an unrefined `string` from the decoder (untrusted JSON input,
// same situation `shex_datatype_ok` documents) — the `is_iri` guard promotes
// it to `wf_iri` inside the branch where the refinement is known to hold; a
// malformed non-IRI predicate string simply yields zero candidates, which
// can only make the shape LESS likely to match (fails closed), never
// silently accept something the spec requires rejecting.
let shex_gather_candidates (g : rdf_graph) (focus : rdf_term) (inverse : bool) (pred : string)
  : list rdf_term =
  if not (is_iri pred) then []
  else
    if inverse
    then List.Tot.map subject_to_term (find_subjects g pred focus)
    else (match term_to_subject focus with
          | None -> []
          | Some s -> find_objects g s pred)

// All triples with `focus` as subject — the `arcsOut` pool the `closed`
// check is defined over (per the spec's satisfies(n,Shape,G), "outs \ T").
let triples_with_subject (g : rdf_graph) (s : subject) : list triple =
  List.Tot.filter (fun (tr : triple) -> subject_eq tr.s s) g

// ================================================================
// Schema-aware boolean-combinator layer: ShapeAnd/ShapeOr/ShapeNot/
// shapeExprRef/Shape over shapeExprs, now graph-aware (Stage 3's `Shape`
// case needs the data graph to look up the focus node's arcs; Stage 2's
// combinators didn't need one and are otherwise unchanged, just threading
// `g` through). `ShapeExternal` and an unresolvable shapeExprRef still
// return `None`.
// ================================================================

let rec lookup_shape_decl (decls : list shex_shape_decl) (label : string)
  : Tot (option shex_shape_decl) (decreases decls) =
  match decls with
  | [] -> None
  | hd :: tl -> if hd.sd_id = label then Some hd else lookup_shape_decl tl label

// `option bool`: None = outside this stage's reach or fuel exhausted;
// Some b = a definite verdict. ShapeAnd/ShapeOr/EachOf are all
// short-circuit-aware — see the file banner comment for why a concrete
// false/true outranks a sibling `None` instead of the whole
// conjunction/disjunction collapsing to None. This whole group shares one
// fuel-decreasing metric because `matches_shape_expr` (SE_Ref/SE_Shape) and
// `matches_triple_expr_value` (TripleConstraint valueExpr) call each other —
// genuine mutual recursion that isn't visibly structural (a shapeExprRef or
// a NodeConstraint's own recursion depth isn't bounded by any single AST's
// size), same fuel idiom Stage 2 already used.
let rec matches_shape_expr (decls : list shex_shape_decl) (se : shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match se with
    | SE_NodeConstraint nc -> Some (node_constraint_matches nc t)
    | SE_ShapeAnd ses -> matches_all decls ses t g fuel'
    | SE_ShapeOr ses  -> matches_any decls ses t g fuel'
    | SE_ShapeNot se' ->
      (match matches_shape_expr decls se' t g fuel' with
       | Some b -> Some (not b)
       | None -> None)
    | SE_Ref label ->
      (match lookup_shape_decl decls label with
       | Some sd -> matches_shape_expr decls sd.sd_expr t g fuel'
       | None -> None)
    | SE_Shape sh -> matches_shape decls sh t g fuel'
    | SE_ShapeExternal -> None
and matches_all (decls : list shex_shape_decl) (ses : list shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some true
    | hd :: tl ->
      (match matches_shape_expr decls hd t g fuel', matches_all decls tl t g fuel' with
       | Some false, _ -> Some false
       | _, Some false -> Some false
       | Some true, Some true -> Some true
       | _, _ -> None)
and matches_any (decls : list shex_shape_decl) (ses : list shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some false
    | hd :: tl ->
      (match matches_shape_expr decls hd t g fuel', matches_any decls tl t g fuel' with
       | Some true, _ -> Some true
       | _, Some true -> Some true
       | Some false, Some false -> Some false
       | _, _ -> None)
// A `Shape`'s verdict is the AND of its expression result (vacuously true
// when `sh_expression` is absent) and its `closed`/`extra` result (vacuously
// true when `sh_closed` is false) — both computed independently below, then
// combined with the same short-circuit-aware AND as `matches_all`, so a
// definite `closed` violation is `Some false` even if the expression itself
// could not be fully decided (and vice versa).
and matches_shape (decls : list shex_shape_decl) (sh : shex_shape) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  // A shape with a non-empty `extends` (shape inheritance / triple-
  // expression merge, `ShEx.Extends.fst`, Stage 6) cannot be evaluated by
  // looking at `sh_expression` alone — the inherited shape(s)' triple
  // expressions are merged in first. Evaluating just the derived shape's
  // OWN (unmerged) expression would silently accept/reject based on a
  // strictly smaller constraint set than the schema actually specifies —
  // exactly the kind of guessed-wrong verdict this module's `None`
  // discipline exists to prevent. Caught by the Stage 3 measurement run
  // (every `Extends`-tagged manifest entry mismatched before this guard).
  else if not (Nil? sh.sh_extends) then None
  else
    let fuel' = fuel - 1 in
    let arcs_out = match term_to_subject t with
      | None -> []             // a Literal can never be a subject — empty arcsOut
      | Some s -> triples_with_subject g s in
    let expr_result =
      match sh.sh_expression with
      | None -> Some true
      | Some te ->
        if te_fastpath_ok te
        then matches_triple_expr_value decls te t g sh.sh_extra fuel'
        else None in
    let claimed_opt = match sh.sh_expression with
      | None -> Some []
      | Some te -> te_claimed_predicates te in
    let closed_result =
      if not sh.sh_closed then Some true
      else
        match claimed_opt with
        | None -> None
        | Some claimed ->
          Some (List.Tot.for_all
                  (fun (tr : triple) ->
                     List.Tot.mem (tr.p <: string) claimed || List.Tot.mem (tr.p <: string) sh.sh_extra)
                  arcs_out) in
    (match expr_result, closed_result with
     | Some false, _ -> Some false
     | _, Some false -> Some false
     | Some true, Some true -> Some true
     | _, _ -> None)
// One TripleConstraint leaf, or an EachOf's conjunction of children — see
// the file banner + `te_fastpath_ok`'s docs for why every leaf reached here
// is guaranteed a unique (direction, predicate) claim within the whole tree
// (its caller already verified `te_fastpath_ok` for the ENTIRE tree before
// the first call), so each leaf can query the graph directly by predicate
// without tracking a shared "remaining pool" the way an ambiguous OneOf
// search (Stage 4) would need to. `extra` is the enclosing Shape's field,
// threaded down unchanged to every leaf. IMPORTANT: `closed` is deliberately
// NOT consulted here — per the spec's satisfies(n,Shape,G), "closed" only
// bounds triples whose predicate is not mentioned ANYWHERE in the
// expression at all (handled separately in `matches_shape`'s
// `closed_result`); a predicate a TripleConstraint DOES mention must have
// ALL its candidate triples accounted for (either inside the matched
// [min,max] subset, or tolerated as leftover because the predicate is
// explicitly listed in `extra`) regardless of whether the Shape itself is
// closed. Getting this wrong (treating `not closed` as ALSO granting
// leftover tolerance to a mentioned predicate) was caught by the Stage 3
// measurement run: it wrongly PASSED `1dotRef1_overReferrer` (a
// `sht:ValidationFailure` fixture — <n1> has two `p1` arcs against a
// `{p1 @<S2>}` shape with default [1,1] cardinality and no `extra`) because
// the shape isn't `closed`.
//
// A second Stage 3 measurement finding refines what `extra` tolerates:
// `extra` only ever excuses candidates that FAIL `valueExpr` (`bad_count`)
// from counting against `[min,max]` — it does NOT lift the upper bound on
// candidates that DO satisfy `valueExpr` (`good_count`). `1val2IRIREFExtra1_
// fail-iri2` (`EXTRA <p1> {p1 [<o1> <o2>]}` on two `p1` arcs, BOTH values
// in the value set, default max 1) is a `sht:ValidationFailure` — extra
// cannot rescue an over-count of GOOD matches, only tolerate BAD leftovers.
// `1dotExtra1_fail-iri2` (`EXTRA <p1> {p1 .}`, no valueExpr so every
// candidate is vacuously "good", two arcs, max 1) fails the same way — the
// corpus's own `VapidExtra` trait tag names exactly this case. So
// `good_count` is ALWAYS bound by `[min,max]` regardless of `extra`;
// `extra` only relaxes the requirement that `bad_count = 0`.
and matches_triple_expr_value
    (decls : list shex_shape_decl) (te : shex_triple_expr) (focus : rdf_term) (g : rdf_graph)
    (extra : list string) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match te with
    | TE_Ref _ -> None
    | TE_OneOf _ -> None
    | TE_TripleConstraint tc ->
      let others = shex_gather_candidates g focus tc.tc_inverse tc.tc_predicate in
      (match shex_check_others decls others tc.tc_value_expr g fuel' with
       | None -> None
       | Some bools ->
         let n_total = List.Tot.length others in
         let good_count = List.Tot.length (List.Tot.filter (fun b -> b) bools) in
         let bad_count = n_total - good_count in
         let allowed_extra = List.Tot.mem tc.tc_predicate extra in
         let bad_ok = bad_count = 0 || allowed_extra in
         Some (bad_ok && good_count >= tc.tc_min &&
               (tc.tc_max = (-1) || good_count <= tc.tc_max)))
    | TE_EachOf grp -> matches_triple_expr_list decls grp.gr_expressions focus g extra fuel'
and matches_triple_expr_list
    (decls : list shex_shape_decl) (tes : list shex_triple_expr) (focus : rdf_term) (g : rdf_graph)
    (extra : list string) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match tes with
    | [] -> Some true
    | hd :: tl ->
      (match matches_triple_expr_value decls hd focus g extra fuel',
             matches_triple_expr_list decls tl focus g extra fuel' with
       | Some false, _ -> Some false
       | _, Some false -> Some false
       | Some true, Some true -> Some true
       | _, _ -> None)
// Per-candidate valueExpr check (absent valueExpr = vacuously satisfied).
// Any `None` anywhere in the list propagates conservatively — the caller
// cannot safely decide [min,max]/good-vs-bad bookkeeping without a definite
// verdict for every candidate.
and shex_check_others
    (decls : list shex_shape_decl) (others : list rdf_term) (ve : option shex_shape_expr)
    (g : rdf_graph) (fuel : nat)
  : Tot (option (list bool)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match others with
    | [] -> Some []
    | hd :: tl ->
      let this_ok = match ve with
        | None -> Some true
        | Some se -> matches_shape_expr decls se hd g fuel' in
      (match this_ok, shex_check_others decls tl ve g fuel' with
       | Some b, Some rest -> Some (b :: rest)
       | _, _ -> None)

// Top-level entry point: validate one focus node against a schema, either
// by an explicit shape label (the manifest's `sht:shape`) or the schema's
// own `start` shapeExpr (`sht:shape` absent). Fuel is derived from the
// schema's own shape count (a hop through `SE_Ref` visits at most that many
// distinct decls before repeating, and ShapeAnd/ShapeOr nesting in the
// corpus is shallow) rather than a bare unexplained constant.
// Fuel is derived from both the schema's own shape count (a hop through
// `SE_Ref` visits at most that many distinct decls before repeating) AND the
// graph's triple count (Stage 3's `shex_check_others` decrements fuel once
// per candidate triple it value-checks, on top of the AST-recursion steps
// Stage 2 already budgeted for) — a safe generous bound, not a bare
// unexplained constant. Test-suite data graphs are small (plan doc: "a
// handful of triples per focus node"), so this stays cheap in practice.
let validate_focus (schema : shex_schema) (shape_id : option string) (t : rdf_term) (g : rdf_graph) : option bool =
  let fuel = 100 + op_Multiply 20 (List.Tot.length schema.sch_shapes) + op_Multiply 10 (List.Tot.length g) in
  match shape_id with
  | Some label ->
    (match lookup_shape_decl schema.sch_shapes label with
     | Some sd -> matches_shape_expr schema.sch_shapes sd.sd_expr t g fuel
     | None -> None)
  | None ->
    (match schema.sch_start with
     | Some se -> matches_shape_expr schema.sch_shapes se t g fuel
     | None -> None)
