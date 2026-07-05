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

// This function's query is right at the default rlimit boundary (F* itself
// reports "verification condition succeeded after splitting it to localize
// potential errors" even before the bump below) — adding `XSD.Datatypes.
// strip_leading_plus`/`int_lexical_in_range`'s `+`-stripping fix (2026-07-05,
// the `nonPositiveInteger-p1_fail`/`negativeInteger-p0_fail` gap-closure)
// changed that dependency's digest enough to flip this already-marginal
// query from "succeeds after splitting" to "fails outright" at the default
// rlimit. `--z3rlimit_factor 4` (measured: this exact factor recovers a
// clean pass) restores headroom without loosening what is actually proved.
#push-options "--z3rlimit_factor 4"

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
#pop-options

// ================================================================
// Stage 4/5/6 (this revision, 2026-07-05 program-plan follow-up):
// general nondeterministic partition-matching search, replacing Stage 3's
// disjoint-predicate-only fast path; SE_Ref recursion (visited-stack,
// coinductive assume-satisfied-on-reentry); tripleExprRef ("Include")
// resolution via a schema-wide id table; EXTENDS (shape inheritance)
// merge; SemAct dispatch for the shex.io/extensions/Test/ extension.
//
// TERMINATION ARGUMENT (module banner requirement): every function below
// that is mutually recursive with `matches_shape_expr` shares ONE
// `fuel:nat` decreasing metric (the same idiom Stage 2/3 already used for
// shapeExprRef/valueExpr mutual recursion) — EVERY recursive call in the
// group passes `fuel - 1` or less, so F*'s termination checker accepts
// the whole group uniformly. Two recursions are ALSO structurally
// decreasing on their own (the pool list in `tc_choose_acc`, the
// candidate list in `classify_candidates`) but this module does not rely
// on that for termination — `decreases fuel` alone is the proof
// obligation actually discharged, so the fuel budget `validate_focus`
// seeds must be large enough to cover the DEPTH of any single recursive
// chain: schema shape-decl hops (SE_Ref/tripleExprRef chases) PLUS the
// length of the candidate pool a `TripleConstraint`'s subset-enumeration
// walks PLUS EXTENDS-chain depth. Note carefully: the pool-subset search
// is combinatorially BROAD (up to 2^n branches for n ambiguous
// same-predicate candidates — the plan's documented "acceptable now
// because test fixtures are small" tradeoff) but NOT deep — each
// individual branch's fuel-decrease is bounded by the pool length, not by
// 2^n, because every branch gets its OWN `fuel - 1` copy rather than
// sharing one counter across siblings. `validate_focus` sizes fuel off
// the graph's triple count and schema's shape count with a generous
// multiplicative margin (not a bare unexplained constant) — see its own
// comment. This revision's additions (multi-ancestor/diamond EXTENDS —
// `flatten_se_for_extends`'s label-dedup, `matches_chain_shared`'s
// running-intersection + unbounded-member restriction — and Definition
// 4's abstract-descendant witness search, `exists_nonabstract_descendant_
// satisfying`) stay INSIDE this same one-`fuel`-metric discipline: every
// new function passes `fuel - 1` (or less) on every recursive call, never
// its own separate counter, so the termination argument above still
// covers the whole group uniformly — the descendant-witness search adds
// an O(shape-count) breadth (it walks every schema declaration once) on
// top of the existing depth budget, comfortably inside `validate_focus`'s
// existing shape-count-scaled margin (measured: no fixture in the
// reachable corpus hits fuel exhaustion because of it).
//
// RECURSION SEMANTICS: `SE_Ref` carries a `visited : list (string &
// rdf_term)` stack of (shape-label, focus-term) pairs currently being
// checked. Re-entering the SAME pair (`visited_mem`) short-circuits to
// `Some true` — the coinductive "assume satisfied while checking whether
// it's satisfied" reading of shex.io/shex-semantics SS5.7 ("Validation of
// recursive schemas"), sound for POSITIVE recursion (no negation on the
// cycle). This module does NOT implement the spec's full
// stratification/SCC-rejection algorithm for NEGATED cycles (the
// `negativeStructure` corpus testing that rejection, e.g.
// `Cycle1Negation1`, ships ONLY as ShExC fixtures with no ShExJ twin —
// unreachable via this program's ShExJ-only scope per the plan doc's
// scope cut 1 — so there is no reachable test this gap could silently
// mis-score). Every ShapeReference/RecursiveData-tagged fixture in the
// reachable ShExJ corpus is non-negated (a plain reference cycle, e.g.
// `1bnodeRefORRefMinlength.json`'s `S1 -> S1` self-reference via
// ShapeOr/ShapeAnd), so assume-true-on-reentry gives the correct verdict
// for all of them: termination is guaranteed by the visited-stack (a
// repeat pair short-circuits before any further fuel is spent), NOT by
// fuel alone for genuinely-cyclic schemas — fuel remains the backstop for
// non-repeating unbounded chains (e.g. an infinite list-shaped graying
// walk that never actually cycles, which the fuel bound simply reports as
// `None`/deferred rather than looping forever).
//
// EXTENDS (shape inheritance, ShEx 2.1 draft SS)): a `Shape` whose
// `sh_extends` is non-empty has its OWN triple expression (if any) and
// EVERY extended shape's triple expression(s) — resolved recursively
// through `ShapeAnd`/`shapeExprRef` chains via `flatten_se_for_extends`,
// bottoming out at `Shape`/`NodeConstraint`/opaque-shapeExpr leaves —
// merged into ONE combined list and fed through the SAME partition search
// as a plain multi-child `EachOf` (this is what makes counts split
// correctly between an ancestor's inherited share and the derived
// shape's own share — see `ExtendsRepeatedP-pass`'s worked example in the
// design notes: A requires exactly 2 `:p` triples, C's own expression
// requires exactly 1 more, and the search finds the partition that
// gives A its 2 and leaves C 1, out of 3 total). `extra`/`closed` are
// combined by concatenation/OR across the whole chain. Non-`Shape`/
// non-`ShapeAnd` components encountered while flattening (bare
// `NodeConstraint`s, `ShapeOr`, `ShapeNot`) do not contribute triple
// expressions — they become opaque "node checks" verified independently
// against the focus term itself (`ef_checks`, folded in via the existing
// `matches_all` AND-combinator), which is how `AND3G`'s per-ancestor
// regex-pattern `NodeConstraint`s (checked on the focus IRI itself, not
// on any triple) get enforced without being mistaken for triple-claiming
// constraints.
//
// SEMANTIC ACTIONS: this module recognizes exactly one extension IRI,
// `http://shex.io/extensions/Test/` (the shexTest suite's own
// logic-conformance probe — NOT arbitrary code execution). Per the
// plan's scope note, only `print(...)` / `fail(...)` dispatch matters for
// Logic-conformant pass/fail: `print(...)` is a pure no-op (this module
// never needs to actually emit the printed text — Result-conformant
// output matching is out of scope), `fail(...)` unconditionally turns
// whatever construct it's attached to (a `TripleConstraint`, a `Group`,
// a `Shape`, or the schema's own `startActs`) into a failure, REGARDLESS
// of what the underlying structural check would have found. An unknown
// extension IRI is inert (neither print nor fail semantics apply) —
// exactly the "no assume-val" pure-F* extension seam the plan calls for,
// since dispatch is a total function over a closed set of known
// extension IRIs.
// ================================================================

let shex_test_extension_iri : string = "http://shex.io/extensions/Test/"

let rec shex_list_has_prefix (l pfx : list FStar.Char.char) : Tot bool (decreases pfx) =
  match pfx with
  | [] -> true
  | pc :: ptl ->
    (match l with
     | [] -> false
     | lc :: ltl -> pc = lc && shex_list_has_prefix ltl ptl)

let rec shex_list_contains_sub (l sub : list FStar.Char.char) : Tot bool (decreases l) =
  if shex_list_has_prefix l sub then true
  else match l with
       | [] -> false
       | _ :: tl -> shex_list_contains_sub tl sub

let shex_string_contains (s sub : string) : bool =
  shex_list_contains_sub (String.list_of_string s) (String.list_of_string sub)

let semact_says_fail (sa : shex_sem_act) : bool =
  sa.sa_name = shex_test_extension_iri &&
  (match sa.sa_code with
   | Some code -> shex_string_contains code "fail("
   | None -> false)

let rec any_semact_fails (l : list shex_sem_act) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | hd :: tl -> semact_says_fail hd || any_semact_fails tl

// ================================================================
// Recursion: (shape-label, focus-term) visited stack.
// ================================================================

type shex_visited = list (string & rdf_term)

let visited_mem (label : string) (t : rdf_term) (v : shex_visited) : bool =
  List.Tot.existsb (fun (entry : (string & rdf_term)) -> fst entry = label && rdf_term_eq (snd entry) t) v

let rec lookup_shape_decl (decls : list shex_shape_decl) (label : string)
  : Tot (option shex_shape_decl) (decreases decls) =
  match decls with
  | [] -> None
  | hd :: tl -> if hd.sd_id = label then Some hd else lookup_shape_decl tl label

// ================================================================
// tripleExprRef ("Include") resolution: a schema-wide (id -> tripleExpr)
// table, built once per `validate_focus` call by walking every shapeExpr
// reachable from `sch_shapes` (a tripleExpr's "id" can be declared on a
// TripleConstraint or a Group anywhere in the tree, including inside
// another shape's own `expression` — `2EachInclude1.json`'s `S2e` id
// lives on a TripleConstraint inside `S2`'s expression, referenced via a
// bare-string TE_Ref from INSIDE `S1`'s EachOf). Purely structural
// recursion over the AST (no external json_val fuel issue here — this is
// already-decoded F* data), so no `fuel` parameter needed; kept as its
// own small mutual-recursion group, separate from the big fuel-threaded
// group below (it never calls into it).
// ================================================================

let rec se_collect_ids (se : shex_shape_expr) : Tot (list (string & shex_triple_expr)) (decreases se) =
  match se with
  | SE_Ref _ -> []
  | SE_ShapeAnd ses -> se_collect_ids_list ses
  | SE_ShapeOr ses -> se_collect_ids_list ses
  | SE_ShapeNot se' -> se_collect_ids se'
  | SE_NodeConstraint _ -> []
  | SE_ShapeExternal -> []
  | SE_Shape sh ->
    (match sh.sh_expression with
     | None -> []
     | Some te -> te_collect_ids te)
and se_collect_ids_list (ses : list shex_shape_expr) : Tot (list (string & shex_triple_expr)) (decreases ses) =
  match ses with
  | [] -> []
  | hd :: tl -> se_collect_ids hd @ se_collect_ids_list tl
and te_collect_ids (te : shex_triple_expr) : Tot (list (string & shex_triple_expr)) (decreases te) =
  match te with
  | TE_Ref _ -> []
  | TE_TripleConstraint tc ->
    let self = match tc.tc_id with Some id -> [(id, te)] | None -> [] in
    let inner = match tc.tc_value_expr with Some se -> se_collect_ids se | None -> [] in
    self @ inner
  | TE_EachOf grp ->
    let self = match grp.gr_id with Some id -> [(id, te)] | None -> [] in
    self @ te_collect_ids_list grp.gr_expressions
  | TE_OneOf grp ->
    let self = match grp.gr_id with Some id -> [(id, te)] | None -> [] in
    self @ te_collect_ids_list grp.gr_expressions
and te_collect_ids_list (tes : list shex_triple_expr) : Tot (list (string & shex_triple_expr)) (decreases tes) =
  match tes with
  | [] -> []
  | hd :: tl -> te_collect_ids hd @ te_collect_ids_list tl

let rec shape_decl_list_collect_ids (decls : list shex_shape_decl)
  : Tot (list (string & shex_triple_expr)) (decreases decls) =
  match decls with
  | [] -> []
  | hd :: tl -> se_collect_ids hd.sd_expr @ shape_decl_list_collect_ids tl

let rec lookup_te_id (tab : list (string & shex_triple_expr)) (id : string)
  : Tot (option shex_triple_expr) (decreases tab) =
  match tab with
  | [] -> None
  | (k, v) :: tl -> if k = id then Some v else lookup_te_id tl id

// ================================================================
// EXTENDS flattening: resolves a shapeExpr (an `sh_extends` target, or a
// nested ShapeAnd conjunct) down to its contributed triple-expressions,
// extra/closed flags, and opaque node-level checks. Independent of the
// big fuel-threaded matching group below (never calls `matches_shape_expr`
// — it only inspects AST shape, never evaluates against a focus term), so
// kept as its own small fuel-bounded mutual group (fuel bounds the
// extends-chain / ShapeAnd-nesting depth it walks).
//
// DIAMOND DEDUP (multi-ancestor/diamond fix, this revision): a
// `visited : list string` label-set is threaded through all three
// functions (mirrors `shex_visited`'s role for `SE_Ref` recursion, but
// simpler — schema-structural only, no focus term). Whenever a label is
// about to be flattened (via `resolve_extends`'s own `hd`, or a bare
// `SE_Ref label`), it is checked against `visited` first; if already
// present the label contributes `ef_empty` (already counted via some
// OTHER path) instead of being re-flattened. Without this, a diamond —
// e.g. `extends-closed-diamond.shex`'s `BOTTOM EXTENDS @<G0-0> EXTENDS
// @<G0-1>` where BOTH `G0-0` and `G0-1` themselves `EXTENDS @<G0>` — would
// walk `G0` twice (once per path) and fold its own triple-expression into
// the combined list TWICE, silently doubling the count `G0`'s own
// constraint requires (the `two-G0s`/`two-G0-0s`/`two-BOTTOMS` fixtures
// are the NEGATIVE mirror of this: they supply a genuine extra matching
// triple and must still fail — dedup does not change those, only removes
// the SPURIOUS extra requirement `pass-bottom` would otherwise face).
// Every recursive descent adds the just-looked-up label to `visited`
// BEFORE recursing further (also a safety net against a cyclic `extends`
// declaration, which the corpus never exercises but which would
// otherwise only be bounded by `fuel`).
// ================================================================

noeq type extends_flat = {
  ef_tes    : list shex_triple_expr;
  ef_extra  : list string;
  ef_closed : bool;
  ef_checks : list shex_shape_expr;
}

let ef_empty : extends_flat = { ef_tes = []; ef_extra = []; ef_closed = false; ef_checks = [] }

let ef_combine (a b : extends_flat) : extends_flat =
  { ef_tes    = a.ef_tes @ b.ef_tes;
    ef_extra  = a.ef_extra @ b.ef_extra;
    ef_closed = a.ef_closed || b.ef_closed;
    ef_checks = a.ef_checks @ b.ef_checks }

let rec flatten_se_for_extends (decls : list shex_shape_decl) (se : shex_shape_expr) (visited : list string) (fuel : nat)
  : Tot (option (extends_flat & list string)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match se with
    | SE_Shape sh ->
      let own_tes = match sh.sh_expression with Some te -> [te] | None -> [] in
      if Nil? sh.sh_extends then
        Some ({ ef_tes = own_tes; ef_extra = sh.sh_extra; ef_closed = sh.sh_closed; ef_checks = [] }, visited)
      else
        (match resolve_extends decls sh.sh_extends visited fuel' with
         | None -> None
         | Some (parent, visited1) ->
           Some (ef_combine ({ ef_tes = own_tes; ef_extra = sh.sh_extra; ef_closed = sh.sh_closed; ef_checks = [] }) parent, visited1))
    | SE_ShapeAnd ses -> flatten_se_list_for_extends decls ses visited fuel'
    | SE_Ref label ->
      if List.Tot.mem label visited then Some (ef_empty, visited)
      else
        (match lookup_shape_decl decls label with
         | Some sd -> flatten_se_for_extends decls sd.sd_expr (label :: visited) fuel'
         | None -> None)
    | SE_NodeConstraint _ -> Some ({ ef_empty with ef_checks = [se] }, visited)
    | SE_ShapeOr _ -> Some ({ ef_empty with ef_checks = [se] }, visited)
    | SE_ShapeNot _ -> Some ({ ef_empty with ef_checks = [se] }, visited)
    | SE_ShapeExternal -> Some ({ ef_empty with ef_checks = [se] }, visited)
and flatten_se_list_for_extends (decls : list shex_shape_decl) (ses : list shex_shape_expr) (visited : list string) (fuel : nat)
  : Tot (option (extends_flat & list string)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some (ef_empty, visited)
    | hd :: tl ->
      (match flatten_se_for_extends decls hd visited fuel' with
       | None -> None
       | Some (a, visited1) ->
         (match flatten_se_list_for_extends decls tl visited1 fuel' with
          | None -> None
          | Some (b, visited2) -> Some (ef_combine a b, visited2)))
and resolve_extends (decls : list shex_shape_decl) (labels : list string) (visited : list string) (fuel : nat)
  : Tot (option (extends_flat & list string)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match labels with
    | [] -> Some (ef_empty, visited)
    | hd :: tl ->
      if List.Tot.mem hd visited then resolve_extends decls tl visited fuel'
      else
        (match lookup_shape_decl decls hd with
         | None -> None
         | Some sd ->
           (match flatten_se_for_extends decls sd.sd_expr (hd :: visited) fuel' with
            | None -> None
            | Some (a, visited1) ->
              (match resolve_extends decls tl visited1 fuel' with
               | None -> None
               | Some (b, visited2) -> Some (ef_combine a b, visited2))))

// Gathers the "other endpoint" terms of the focus node's arcs relevant to
// one TripleConstraint — arcsOut (focus is subject) for a non-inverse
// constraint, arcsIn (focus is object) for an inverse one. `tc_predicate`
// arrives as an unrefined `string` from the decoder (untrusted JSON
// input) — the `is_iri` guard promotes it to `wf_iri` inside the branch
// where the refinement is known to hold; a malformed non-IRI predicate
// string simply yields zero candidates (fails closed).
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
// Pool plumbing: a "candidate pool" is the list of (inverse, predicate,
// other-endpoint-term) triples relevant to a triple-expression subtree —
// gathered ONCE (per mentioned (inverse,predicate) pair, deduplicated) at
// the point a Shape's expression is evaluated, then threaded through the
// nondeterministic search below. Plain structural recursion, no `fuel`.
// ================================================================

type pool_elem = bool & string & rdf_term
type pool_t = list pool_elem

// Structural equality on one pool candidate — needed by the EXTENDS
// multi-ancestor "shared" joint-coverage check (`matches_chain_shared`'s
// running-intersection accumulator, below) to test whether a specific
// candidate a sibling ancestor's search left as leftover is the SAME
// candidate another sibling's search claimed.
let pool_elem_eq (a b : pool_elem) : bool =
  let (ai, ap, at) = a in
  let (bi, bp, bt) = b in
  ai = bi && ap = bp && rdf_term_eq at bt

let rec pool_intersect (running other : pool_t) : Tot pool_t (decreases running) =
  match running with
  | [] -> []
  | hd :: tl ->
    if List.Tot.existsb (fun (e : pool_elem) -> pool_elem_eq hd e) other
    then hd :: pool_intersect tl other
    else pool_intersect tl other

// Set difference `a \ b` — used by the EXTENDS multi-ancestor "background
// safe" restriction (`restrict_unbounded_completions`, below) to recover
// which candidates an unbounded chain member's completion actually
// claimed (`pool_diff pool leftover`).
let rec pool_diff (a b : pool_t) : Tot pool_t (decreases a) =
  match a with
  | [] -> []
  | hd :: tl ->
    if List.Tot.existsb (fun (e : pool_elem) -> pool_elem_eq hd e) b
    then pool_diff tl b
    else hd :: pool_diff tl b

// Is this triple expression a bare, UNBOUNDED (`+`-cardinality, `max = -1`)
// leaf TripleConstraint? Flags the "background" chain members whose
// contribution to the multi-ancestor shared-closure check
// (`matches_chain_shared`) must be restricted to "background-safe"
// candidates only (see that function's doc comment) — an unbounded
// TripleConstraint has no upper bound, so absent this restriction it can
// gratuitously "claim" ANY good-for-it candidate merely to make the
// closure check pass, even when nothing genuinely requires it to. A
// bounded (`max <> -1`, e.g. exact `[n,n]`) TripleConstraint, or any
// non-leaf triple expression (`EachOf`/`OneOf`/`TE_Ref`), is exempt —
// its own [min,max] accounting already forces genuine, non-gratuitous
// claims (`ExtendAND3G.shex`'s `E`'s own `p:[2]`, `Extend3G.shex`'s `F`'s
// own `p:[3]`/`G`'s own `p:[4]`, all exact-bounded, are NEVER restricted).
let te_is_unbounded_tc (te : shex_triple_expr) : bool =
  match te with
  | TE_TripleConstraint tc -> tc.tc_max = (-1)
  | _ -> false

let pair_mem (x : bool & string) (l : list (bool & string)) : bool =
  List.Tot.existsb (fun (y : bool & string) -> fst x = fst y && snd x = snd y) l

let rec dedup_pairs (l : list (bool & string)) : Tot (list (bool & string)) (decreases l) =
  match l with
  | [] -> []
  | hd :: tl -> if pair_mem hd tl then dedup_pairs tl else hd :: dedup_pairs tl

let rec gather_pool (g : rdf_graph) (focus : rdf_term) (pairs : list (bool & string))
  : Tot pool_t (decreases pairs) =
  match pairs with
  | [] -> []
  | (inv, pred) :: tl ->
    let cands = shex_gather_candidates g focus inv pred in
    List.Tot.map (fun (tm : rdf_term) -> (inv, pred, tm)) cands @ gather_pool g focus tl

// ================================================================
// OneOf branch-result combination: given each branch's own
// `option (list pool_t)` outcome (None = deferred, Some [] = definitely
// no valid completion, Some (_::_) = at least one valid completion), the
// combined verdict for the WHOLE OneOf follows the same "a definite
// success wins over an unresolved sibling" short-circuit discipline the
// rest of this module uses (matches_any's `Some true, _ -> Some true`):
// any branch with a nonempty `Some` makes the combination a definite
// (unioned) success; failing that, any `None` makes the combination
// unresolved; only when EVERY branch is conclusively `Some []` is the
// combination a definite empty result.
// ================================================================

let rec has_any_none (l : list (option (list pool_t))) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | None :: _ -> true
  | Some _ :: tl -> has_any_none tl

let rec has_any_nonempty_some (l : list (option (list pool_t))) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | Some (_ :: _) :: _ -> true
  | _ :: tl -> has_any_nonempty_some tl

let rec collect_nonempty_some (l : list (option (list pool_t))) : Tot (list pool_t) (decreases l) =
  match l with
  | [] -> []
  | Some xs :: tl -> xs @ collect_nonempty_some tl
  | None :: tl -> collect_nonempty_some tl

let combine_oneof (l : list (option (list pool_t))) : option (list pool_t) =
  if has_any_nonempty_some l then Some (collect_nonempty_some l)
  else if has_any_none l then None
  else Some []

// ================================================================
// Ambiguous-pair detection: a (inverse,predicate) pair is "ambiguous"
// when MORE THAN ONE leaf `TripleConstraint` in the combined
// triple-expression list claims it (e.g. `Pstar.json`'s `S1`: two
// TripleConstraints both on predicate `:a`, one requiring `P`-typed
// values and one requiring `T`-typed values — `pt1`/`pt2` satisfy
// BOTH). `eval_expr_list_over_pool` computes this ONCE (from the very
// same undeduped `te_mentioned_pairs_list` multiset it already needs for
// `gather_pool`) and threads it down so `tc_choose_acc` knows, per
// candidate, whether "leave this GOOD candidate unclaimed" is a
// meaningful choice (some OTHER sibling on the SAME pair might claim it
// instead) or a spurious escape hatch. This is what keeps
// `1val2IRIREFExtra1_fail-iri2` correctly rejecting: `S1`'s SOLE
// claimant of `p1` has no sibling to hand an excess good candidate to,
// so leaving one unclaimed is never offered — the full good-count is
// forced through `[min,max]`, and `extra` never gets a chance to
// launder an over-count of GOOD matches (it only ever tolerates BAD
// leftovers, via the "not is_good" branch, which is unconditional
// regardless of ambiguity).
// ================================================================

let rec pair_count (x : bool & string) (l : list (bool & string)) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | hd :: tl -> (if fst x = fst hd && snd x = snd hd then 1 else 0) + pair_count x tl

let rec ambiguous_pairs_of (l : list (bool & string)) : Tot (list (bool & string)) (decreases l) =
  match l with
  | [] -> []
  | hd :: tl -> if pair_count hd tl > 0 then hd :: ambiguous_pairs_of tl else ambiguous_pairs_of tl

// ================================================================
// Repeated-group (RepeatedOneOf/RepeatedGroup/"Greedy" trait) support:
// this corpus's cardinality-wrapped `EachOf`/`OneOf` groups all wrap a
// flat list of plain `TripleConstraint` children on pairwise-distinct
// (inverse,predicate) pairs (verified against every reachable fixture —
// `open3Onedotclosecard2`, `open3Onedotclosecard23`,
// `open4Onedotclosecard23`, `open2Eachdotclosecard25c1dot`,
// `open3Eachdotclosecard23`(+`Annot3Code2`)) — never a same-predicate
// ambiguous repeat. So instead of the general round-based
// unroll-and-search (which the plan's design sketch describes for the
// fully general case), this module uses the cheaper counting shortcut:
// gather each child's own (good, bad) split directly (no cross-child
// ambiguity is possible once the pairs are distinct), then for an
// `EachOf`-repeat require every child's good-count to be the SAME `k`
// (one child-tuple per repetition) with `k` in `[gmin,gmax]`; for a
// `OneOf`-repeat require the SUM of all children's good-counts to be in
// `[gmin,gmax]` (each repetition independently picks any one
// alternative). A repeated group whose children are anything other than
// plain, pairwise-distinct `TripleConstraint`s (not present in the
// reachable corpus) honestly defers (`None`) rather than guessing.
// ================================================================

let rec tc_pairs_of (tes : list shex_triple_expr) : Tot (list (bool & string)) (decreases tes) =
  match tes with
  | [] -> []
  | TE_TripleConstraint tc :: tl -> (tc.tc_inverse, tc.tc_predicate) :: tc_pairs_of tl
  | _ :: tl -> tc_pairs_of tl

let rec all_tc (tes : list shex_triple_expr) : Tot bool (decreases tes) =
  match tes with
  | [] -> true
  | TE_TripleConstraint _ :: tl -> all_tc tl
  | _ -> false

let rec pairs_distinct (l : list (bool & string)) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd :: tl -> not (pair_mem hd tl) && pairs_distinct tl

let distinct_child_pairs (tes : list shex_triple_expr) : bool =
  all_tc tes && pairs_distinct (tc_pairs_of tes)

let rec all_equal_nat (l : list nat) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: tl ->
    (match tl with
     | [] -> true
     | y :: _ -> x = y && all_equal_nat tl)

let rec sum_nat (l : list nat) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | hd :: tl -> hd + sum_nat tl

// ================================================================
// The big mutually-recursive matching group. See the module banner for
// the fuel/termination argument and the `option bool` / `option (list
// pool_t)` conventions (None = outside this module's reach or fuel
// exhausted, never a guessed verdict).
// ================================================================

let rec matches_shape_expr (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (se : shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match se with
    | SE_NodeConstraint nc -> Some (node_constraint_matches nc t)
    | SE_ShapeAnd ses -> matches_all decls idtab visited ses t g fuel'
    | SE_ShapeOr ses -> matches_any decls idtab visited ses t g fuel'
    | SE_ShapeNot se' ->
      (match matches_shape_expr decls idtab visited se' t g fuel' with
       | Some b -> Some (not b)
       | None -> None)
    | SE_Ref label ->
      if visited_mem label t visited then Some true
      else
        (match lookup_shape_decl decls label with
         | Some sd ->
           (match matches_shape_expr decls idtab ((label, t) :: visited) sd.sd_expr t g fuel' with
            | Some true ->
              // ABSTRACT (Definition 4, "Shape Expressions with Inheritance",
              // arxiv 2503.24299): "if z is abstract, there must exist
              // x in desc(z) \ abstract such that G,n,tau |= Sdef(x)" — a
              // node satisfying an abstract shape's OWN structural content
              // is NOT enough; its typing must ALSO be witnessed by some
              // NON-abstract descendant (a shape that itself `extends`,
              // directly or transitively, this label). Only gated when
              // `sd_is_abstract` — every non-abstract `SE_Ref` (the
              // overwhelming common case) skips this entirely, so this can
              // only ever turn a would-be Some true into Some false, never
              // affect a non-abstract reference. `extends-abstract-multi-
              // empty.shex`'s `IssueShape`'s `ex:reportedBy @<PersonShape>`
              // is the fixture this closes: `User2` structurally satisfies
              // ABSTRACT `PersonShape`'s own `(name|(givenName+;familyName));
              // mbox`, but `_user-extraP.ttl`'s `User2` (extra `ex:p`) is
              // witnessed by NEITHER of `PersonShape`'s two non-abstract
              // descendants (`UserShape` — closed, rejects the extra `ex:p`;
              // `EmployeeShape` — requires `foaf:phone`, absent) — Definition
              // 4 fails, so the reference correctly rejects even though the
              // abstract shape's own content alone would have accepted it.
              if sd.sd_is_abstract
              then exists_nonabstract_descendant_satisfying decls idtab visited label t g fuel'
              else Some true
            | other -> other)
         | None -> None)
    | SE_Shape sh -> matches_shape decls idtab visited sh t g fuel'
    | SE_ShapeExternal -> None
// Definition 4's witness search: does SOME non-abstract shape declaration
// that (directly or transitively) `extends` `label` also validate `t`?
// Iterates the WHOLE schema's decl list as the candidate-descendant pool
// (`shape_decl_extends_label` below filters to genuine descendants) —
// short-circuits the same way `matches_any` does (a definite `Some true`
// witness wins over an unresolved sibling; only `Some false` from EVERY
// candidate is a definite `Some false`).
and exists_nonabstract_descendant_satisfying (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (label : string) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    check_descendant_candidates decls idtab visited label decls t g fuel'
and check_descendant_candidates (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (label : string) (candidates : list shex_shape_decl) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match candidates with
    | [] -> Some false
    | cd :: tl ->
      if cd.sd_is_abstract || not (shape_decl_extends_label decls cd label [] fuel')
      then check_descendant_candidates decls idtab visited label tl t g fuel'
      else
        (match matches_shape_expr decls idtab visited cd.sd_expr t g fuel',
               check_descendant_candidates decls idtab visited label tl t g fuel' with
         | Some true, _ -> Some true
         | _, Some true -> Some true
         | Some false, Some false -> Some false
         | _, _ -> None)
// Does declaration `cd` (directly or transitively, through `sh_extends`
// chains and `ShapeAnd`-embedded `extends` sub-shapes alike — the SAME
// two ShExJ encoding idioms `flatten_se_for_extends` already handles) end
// up extending `label`? Purely structural (no focus term involved), so
// — like `flatten_se_for_extends`'s own small mutual group — this needs
// no `fuel` for termination in principle, but shares the caller's `fuel`
// parameter anyway to stay inside the one big mutually-recursive group
// `matches_shape_expr` anchors (simplest way to let it call NOTHING
// outside that group while still being reachable FROM it).
and shape_decl_extends_label (decls : list shex_shape_decl) (cd : shex_shape_decl) (label : string)
    (seen : list string) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else se_extends_label decls cd.sd_expr label seen (fuel - 1)
and se_extends_label (decls : list shex_shape_decl) (se : shex_shape_expr) (label : string)
    (seen : list string) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let fuel' = fuel - 1 in
    match se with
    | SE_Shape sh -> List.Tot.mem label sh.sh_extends || labels_extend_label decls sh.sh_extends label seen fuel'
    | SE_ShapeAnd ses -> se_list_extends_label decls ses label seen fuel'
    | _ -> false
and se_list_extends_label (decls : list shex_shape_decl) (ses : list shex_shape_expr) (label : string)
    (seen : list string) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> false
    | hd :: tl -> se_extends_label decls hd label seen fuel' || se_list_extends_label decls tl label seen fuel'
and labels_extend_label (decls : list shex_shape_decl) (labels : list string) (target : string)
    (seen : list string) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let fuel' = fuel - 1 in
    match labels with
    | [] -> false
    | hd :: tl ->
      if hd = target then true
      else if List.Tot.mem hd seen then labels_extend_label decls tl target seen fuel'
      else
        (match lookup_shape_decl decls hd with
         | Some sd -> se_extends_label decls sd.sd_expr target (hd :: seen) fuel' || labels_extend_label decls tl target seen fuel'
         | None -> labels_extend_label decls tl target seen fuel')
and matches_all (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ses : list shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some true
    | hd :: tl ->
      (match matches_shape_expr decls idtab visited hd t g fuel', matches_all decls idtab visited tl t g fuel' with
       | Some false, _ -> Some false
       | _, Some false -> Some false
       | Some true, Some true -> Some true
       | _, _ -> None)
and matches_any (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ses : list shex_shape_expr) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match ses with
    | [] -> Some false
    | hd :: tl ->
      (match matches_shape_expr decls idtab visited hd t g fuel', matches_any decls idtab visited tl t g fuel' with
       | Some true, _ -> Some true
       | _, Some true -> Some true
       | Some false, Some false -> Some false
       | _, _ -> None)
and matches_shape (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (sh : shex_shape) (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    // EXTENDS: per the "Shape Expressions with Inheritance" formalization
    // (arxiv 2503.24299, Table 3 line 18 — the `M = M' ⊎ ⊎_{x∈anc(X)} M_x`
    // partition rule; Definition 4 for `abstract`, see `flatten_se_for_extends`'s
    // doc comment), this is a TWO-TIER split, not a flat N-way partition:
    //   - `sh.sh_expression` (when the SAME Shape object carries both
    //     `extends` and `expression` together — e.g. `ExtendsRepeatedP`'s
    //     `<C> EXT @<B> { :p }`) is `h`, the derived shape's own NEW
    //     triple-consuming content — it gets a GENUINE DISJOINT share,
    //     exclusive of whatever the ancestor chain consumes (`search_te`
    //     claims it FIRST, in `eval_own_vs_chain`, before the chain tier
    //     ever sees the pool).
    //   - the WHOLE resolved ancestor chain (`resolve_extends`'s `ef_tes` —
    //     one flattened member per DISTINCT ancestor, diamond-deduped, see
    //     `flatten_se_for_extends`'s banner) is `restr`-like: every member
    //     gets to see the SAME leftover pool independently (no
    //     `search_te`-level threading between them — this is what lets an
    //     ancestor's own bound and a plain-ShapeAnd sibling restriction
    //     both be satisfied by the SAME triple, `AND3G`'s A/B/D worked
    //     example), BUT unlike a naive per-member existence check, the
    //     shape-level coverage/closedness obligation (a MENTIONED
    //     predicate's leftover must be `extra`-covered, rule cross-
    //     referenced in `eval_expr_list_over_pool`'s doc comment) is
    //     verified JOINTLY across the WHOLE chain via a running
    //     intersection over one committed completion per member
    //     (`matches_chain_shared`'s doc comment) — an item is "explained"
    //     if ANY chain member's chosen completion actually claims it, not
    //     only if EVERY member happens to. This is what makes BOTH
    //     directions of a multi-ancestor `extends: [X, Y]` array (e.g.
    //     `extends-abstract-multi-empty.shex`'s `EmployeeShape EXTENDS
    //     @<PersonShape> EXTENDS @<RepShape>`, `Extend3G.shex`'s `<G>
    //     EXTENDS @<E> EXTENDS @<F>`) and a genuine diamond (`extends-
    //     closed-diamond.shex`'s `BOTTOM` reaching `G0` via both `G0-0` and
    //     `G0-1`) correctly PARTITION the pool by VALUE-DISJOINTNESS
    //     (each ancestor's own valueExpr only ever claims candidates
    //     nobody else wants) while a plain ShapeAnd restriction chain
    //     (`ExtendsRepeatedP`'s `<B> @<A> AND {...}`, generic no-valueExpr
    //     TripleConstraints all sharing one predicate) correctly ALLOWS
    //     the same candidates to jointly satisfy multiple ancestors'
    //     independent bounds without artificial scarcity — both fall out
    //     of the SAME algorithm because it never forces an EXCLUSIVE
    //     claim, it only requires that SOME member could have claimed
    //     each surviving candidate.
    if Nil? sh.sh_extends then
      let own_te_list = match sh.sh_expression with Some te -> [te] | None -> [] in
      matches_shape_flat decls idtab visited own_te_list sh.sh_extra sh.sh_closed [] sh sh.sh_semacts t g fuel'
    else
      (match resolve_extends decls sh.sh_extends [] fuel' with
       | None -> None
       | Some (chain, _) ->
         let all_extra = sh.sh_extra @ chain.ef_extra in
         let all_closed = sh.sh_closed || chain.ef_closed in
         let node_checks_result =
           if Nil? chain.ef_checks then Some true
           else matches_all decls idtab visited chain.ef_checks t g fuel' in
         let arcs_out = match term_to_subject t with None -> [] | Some s -> triples_with_subject g s in
         let own_pairs_opt = match sh.sh_expression with None -> Some [] | Some te -> te_mentioned_pairs idtab te fuel' in
         let chain_pairs_opt = te_mentioned_pairs_list idtab chain.ef_tes fuel' in
         (match own_pairs_opt, chain_pairs_opt with
          | None, _ -> None
          | _, None -> None
          | Some own_pairs, Some chain_pairs ->
            let all_pairs = own_pairs @ chain_pairs in
            let closed_result =
              if not all_closed then Some true
              else
                let mentioned_preds = List.Tot.map snd (List.Tot.filter (fun (p : bool & string) -> not (fst p)) all_pairs) in
                Some (List.Tot.for_all
                        (fun (tr : triple) -> List.Tot.mem (tr.p <: string) mentioned_preds || List.Tot.mem (tr.p <: string) all_extra)
                        arcs_out)
            in
            let pool0 = gather_pool g t (dedup_pairs all_pairs) in
            let own_chain_ambiguous = ambiguous_pairs_of all_pairs in
            let expr_result = eval_own_vs_chain decls idtab visited own_chain_ambiguous sh.sh_expression chain.ef_tes all_extra pool0 g fuel' in
            let combined =
              match node_checks_result, closed_result, expr_result with
              | Some false, _, _ -> Some false
              | _, Some false, _ -> Some false
              | _, _, Some false -> Some false
              | Some true, Some true, Some true -> Some true
              | _, _, _ -> None
            in
            (match combined with
             | Some true -> Some (not (any_semact_fails sh.sh_semacts))
             | other -> other)))
// Non-EXTENDS Shape evaluation (the Stage 3 behaviour, factored out so
// `matches_shape`'s `sh_extends = []` branch and the EXTENDS branch share
// the SAME closed/extra/node-check plumbing — kept as a single-element
// `own_te_list` plus empty `chain_tes` call into `eval_own_vs_chain`'s
// sibling machinery would also work, but this direct form avoids a
// spurious 2-way split for the overwhelmingly common no-extends case).
and matches_shape_flat (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (own_te_list : list shex_triple_expr) (extra : list string) (closed : bool)
    (node_checks : list shex_shape_expr) (sh : shex_shape) (semacts : list shex_sem_act)
    (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    let node_checks_result = if Nil? node_checks then Some true else matches_all decls idtab visited node_checks t g fuel' in
    let arcs_out = match term_to_subject t with None -> [] | Some s -> triples_with_subject g s in
    let mentioned_opt = te_mentioned_pairs_list idtab own_te_list fuel' in
    let closed_result =
      if not closed then Some true
      else
        match mentioned_opt with
        | None -> None
        | Some pairs ->
          let mentioned_preds = List.Tot.map snd (List.Tot.filter (fun (p : bool & string) -> not (fst p)) pairs) in
          Some (List.Tot.for_all
                  (fun (tr : triple) -> List.Tot.mem (tr.p <: string) mentioned_preds || List.Tot.mem (tr.p <: string) extra)
                  arcs_out)
    in
    let expr_result = eval_expr_list_over_pool decls idtab visited own_te_list extra t g fuel' in
    let combined =
      match node_checks_result, closed_result, expr_result with
      | Some false, _, _ -> Some false
      | _, Some false, _ -> Some false
      | _, _, Some false -> Some false
      | Some true, Some true, Some true -> Some true
      | _, _, _ -> None
    in
    (match combined with
     | Some true -> Some (not (any_semact_fails semacts))
     | other -> other)
// Two-way split between a shape's OWN triple-consuming expression (when
// present — EXCLUSIVE share, disjoint from the chain) and the resolved
// ancestor chain (SHARED amongst its own members — see `matches_shape`'s
// doc comment and `matches_chain_shared`'s below for how "shared" still
// gets a correct joint coverage verdict).
and eval_own_vs_chain (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (own_te_opt : option shex_triple_expr)
    (chain_tes : list shex_triple_expr) (extra : list string) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    let unbounded_tes = List.Tot.filter te_is_unbounded_tc chain_tes in
    match own_te_opt with
    | None -> matches_chain_shared decls idtab visited ambiguous chain_tes unbounded_tes extra pool pool g fuel'
    | Some own_te ->
      (match search_te decls idtab visited ambiguous own_te pool g fuel' with
       | None -> None
       | Some leftovers -> combine_own_vs_chain_results decls idtab visited ambiguous chain_tes unbounded_tes extra leftovers g fuel')
and combine_own_vs_chain_results (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (chain_tes : list shex_triple_expr)
    (unbounded_tes : list shex_triple_expr) (extra : list string) (leftovers : list pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match leftovers with
    | [] -> Some false
    | lo :: tl ->
      (match matches_chain_shared decls idtab visited ambiguous chain_tes unbounded_tes extra lo lo g fuel',
             combine_own_vs_chain_results decls idtab visited ambiguous chain_tes unbounded_tes extra tl g fuel' with
       | Some true, _ -> Some true
       | _, Some true -> Some true
       | Some false, Some false -> Some false
       | _, _ -> None)
// Chain members evaluated SHARED: each independently searches the SAME
// `pool` handed to the chain tier (no consumption threading BETWEEN
// members — `AND3G`'s A/B/D worked example needs an ancestor's own bound
// and a plain-ShapeAnd sibling restriction to both be satisfiable from the
// SAME candidate, which per-member exclusive consumption would break).
//
// What changed from the earlier (wave-A) version: this used to check,
// PER MEMBER, "does SOME completion of just this one TE leave a leftover
// fully covered by `extra`" — correct only when a single ancestor's own
// requirement happens to explain the WHOLE pool by itself. It is wrong
// the moment TWO ancestors each explain a DIFFERENT slice of the pool
// (`extends-abstract-multi-empty.shex`'s `EmployeeShape EXTENDS
// @<PersonShape> EXTENDS @<RepShape>` — Person's own search never touches
// the `foaf:phone` triple RepShape claims, so the old per-member check
// always saw `phone` left over and rejected a fixture the corpus expects
// to PASS) or a diamond re-derives the SAME ancestor's requirement twice
// (`extends-closed-diamond.shex`'s `BOTTOM` reaching `G0` via both `G0-0`
// and `G0-1`, now fixed at the SOURCE by `flatten_se_for_extends`'s
// diamond dedup, but the per-member check was ALSO independently unable
// to tell "explained by a sibling" from "genuinely unexplained").
//
// The fix: `running` is threaded through the whole member list as a
// running INTERSECTION of "candidates not yet explained by anyone's
// committed choice so far". Each member tries EVERY one of its own valid
// completions (`matches_chain_shared_try`, mirroring
// `combine_own_vs_chain_results`'s existing pattern of iterating a
// completion list) — a completion's leftover is intersected into
// `running` (an item drops out of `running`, i.e. becomes "explained",
// the moment SOME member's chosen completion does not list it as
// leftover, i.e. that member actually claimed it). Only after every
// member has committed to ONE completion does `running` become the FINAL
// combined leftover the `extra` clause must fully cover — this is what
// lets `ExtendsRepeatedP`'s `<B> @<A> AND { :p+; :q+ }` reuse the SAME
// triples redundantly across A's and B's own bounds (each intersection
// step only shrinks `running`, never forces a member to avoid a
// candidate another member also wants) while still correctly rejecting
// `extends-closed-diamond`'s `two-G0s` (an EXTRA `G0`-valued triple has
// no OTHER member whose valueExpr accepts it, so it survives every
// intersection regardless of which of `G0`'s own two candidates that
// TripleConstraint's ambiguity-aware search happens to pick).
//
// SECOND fix, this revision (`ExtendAND3G-fail_ExtraP`/`extends-abstract-
// multi-empty_fail-Ref1ExtraP` regression found by measurement): an
// UNBOUNDED (`+`, `max=-1`) chain member has no upper limit, so it can
// gratuitously "choose" to also claim a candidate nothing actually
// requires it to, purely to make the closure check above pass.
// `ExtendAND3G.shex`'s `D` (`p:[0,1,2,3,5,6,7,8,9]+`) tolerates value `3`
// structurally, but `3` must ONLY be excused if some genuinely-bounded
// sibling explicitly pins it (like `Extend3G.shex`'s `F`'s own `p:[3]`,
// an EXACT `[1,1]` claim, unaffected by this restriction) — `D` alone
// gratuitously "absorbing" 3 with no such pin must NOT count, hence
// `ExtendAND3G-fail_ExtraP` (no sibling pins 3) correctly rejects while
// `Extend3G-pass` (its `F` DOES pin 3 exactly) correctly passes, even
// though `D`'s own valueset is identical in both schemas. `search_te`/
// `matches_chain_shared_try` still compute EVERY structurally-valid
// completion for an unbounded member (nothing here changes what makes
// hd's OWN [min,max] bound satisfiable) — `restrict_unbounded_completions`
// only edits which of THOSE claims are trusted to shrink `running`: a
// claimed candidate only stays "explained" if it is `background_safe`
// (good for EVERY OTHER unbounded sibling in the chain too, mirroring
// `Extend3G.shex`'s own `# D: 0 1 5 6 7 8 9+` comment — the INTERSECTION
// of the broad ancestors' valuesets is the unconditional background
// tolerance; anything outside it needs an exact pin). A candidate this
// restriction "gives back" is added back into the completion's own
// leftover — `hd`'s [min,max] bound was already checked against the
// UNRESTRICTED completion by `search_te`, so this can never turn a
// genuinely-required claim into a rejection, only stop a SUPERFLUOUS one
// from being credited to `running`. (An earlier version of this fix used
// `background_safe`'s recursion-base-case `[] -> Some false` for BOTH
// "no unbounded siblings at all" and "reached the end of a non-empty
// list" — collapsing the AND-fold to always-false and spuriously
// rejecting `AND3G-pass`/`ANDAbstract-pass`/`ExtendAND3G-pass`/
// `Extend3G-pass` too; `background_safe`/`background_safe_all` below
// split those two cases apart.)
and matches_chain_shared (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (chain_tes : list shex_triple_expr)
    (unbounded_tes : list shex_triple_expr) (extra : list string) (pool : pool_t) (running : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match chain_tes with
    | [] ->
      Some (List.Tot.for_all (fun (e : pool_elem) -> let (inv, pred, _) = e in inv || List.Tot.mem pred extra) running)
    | hd :: tl ->
      (match search_te decls idtab visited ambiguous hd pool g fuel' with
       | None -> None
       | Some raw_completions ->
         (match restrict_unbounded_completions decls idtab visited hd unbounded_tes pool raw_completions g fuel' with
          | None -> None
          | Some completions ->
            matches_chain_shared_try decls idtab visited ambiguous tl unbounded_tes extra pool running completions g fuel'))
// Tries every completion `hd` (the member just searched by
// `matches_chain_shared`) offers, intersecting each into `running` before
// recursing on the REST of the chain — an `existsb`-style search over
// which one of `hd`'s own valid claims leads to an overall-satisfiable
// group (mirrors `combine_own_vs_chain_results`'s existing shape).
and matches_chain_shared_try (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (rest_tes : list shex_triple_expr)
    (unbounded_tes : list shex_triple_expr) (extra : list string) (pool : pool_t) (running : pool_t)
    (completions : list pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match completions with
    | [] -> Some false
    | c :: crest ->
      (match matches_chain_shared decls idtab visited ambiguous rest_tes unbounded_tes extra pool (pool_intersect running c) g fuel',
             matches_chain_shared_try decls idtab visited ambiguous rest_tes unbounded_tes extra pool running crest g fuel' with
       | Some true, _ -> Some true
       | _, Some true -> Some true
       | Some false, Some false -> Some false
       | _, _ -> None)
// For an UNBOUNDED `hd`, edits every completion in `raw_completions` so a
// claimed-but-not-`background_safe` candidate is added BACK into that
// completion's own leftover (see `matches_chain_shared`'s doc comment) —
// a no-op (`Some raw_completions` unchanged) for a bounded `hd`, whose
// own [min,max] accounting is already non-gratuitous.
and restrict_unbounded_completions (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (hd : shex_triple_expr) (unbounded_tes : list shex_triple_expr)
    (pool : pool_t) (raw_completions : list pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    if not (te_is_unbounded_tc hd) then Some raw_completions
    else
      match raw_completions with
      | [] -> Some []
      | c :: crest ->
        let claimed = pool_diff pool c in
        (match restrict_claimed decls idtab visited unbounded_tes claimed g fuel' with
         | None -> None
         | Some given_back ->
           (match restrict_unbounded_completions decls idtab visited hd unbounded_tes pool crest g fuel' with
            | None -> None
            | Some rest -> Some ((c @ given_back) :: rest)))
// Splits `claimed` (the candidates ONE unbounded member's raw completion
// took) into those that stay "claimed" (dropped — `background_safe`) and
// those handed back into leftover (not `background_safe` — no genuinely-
// bounded sibling pins them, so this member's optional claim on them must
// not count for closure).
and restrict_claimed (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (unbounded_tes : list shex_triple_expr) (claimed : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option pool_t) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match claimed with
    | [] -> Some []
    | e :: tl ->
      (match background_safe decls idtab visited unbounded_tes e g fuel', restrict_claimed decls idtab visited unbounded_tes tl g fuel' with
       | Some true, Some rest -> Some rest
       | Some false, Some rest -> Some (e :: rest)
       | _, _ -> None)
// `item` is "background safe" — tolerated by EVERY unbounded chain member
// unconditionally — iff `unbounded_tes` is non-empty AND `item` is a good
// candidate (or simply not that member's own (inverse,predicate) pair at
// all) for ALL of them (`background_safe_all`). Mirrors `Extend3G.shex`'s
// own `# D: 0 1 5 6 7 8 9+` comment: the INTERSECTION of the broad
// ("+") ancestors' valuesets, computed over their DECLARED goodness (via
// `matches_shape_expr`), not restricted to the actual pool. `[] -> Some
// false` here means "there are no unbounded siblings at all, so nothing
// is unconditionally excused" — a DIFFERENT case from `background_safe_
// all`'s OWN `[] -> Some true` (that one means "every unbounded sibling,
// down to the last one in a non-empty starting list, accepted `item`");
// collapsing these two into one base case was the exact bug an earlier
// version of this fix shipped (see `matches_chain_shared`'s doc comment).
and background_safe (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (unbounded_tes : list shex_triple_expr) (item : pool_elem) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    if Nil? unbounded_tes then Some false
    else background_safe_all decls idtab visited unbounded_tes item g fuel'
and background_safe_all (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (unbounded_tes : list shex_triple_expr) (item : pool_elem) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match unbounded_tes with
    | [] -> Some true
    | hd :: tl ->
      (match item_good_for_unbounded_te decls idtab visited hd item g fuel', background_safe_all decls idtab visited tl item g fuel' with
       | Some a, Some b -> Some (a && b)
       | _, _ -> None)
// Is `item` good for ONE unbounded TripleConstraint's own valueExpr? Used
// only by `background_safe`/`background_safe_all` — never to decide
// `chosen`/`leftover` counts, that remains exclusively `tc_choose_acc`'s
// job.
and item_good_for_unbounded_te (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (te : shex_triple_expr) (item : pool_elem) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match te with
    | TE_TripleConstraint tc ->
      let (inv, pred, tm) = item in
      if not (inv = tc.tc_inverse && pred = tc.tc_predicate) then Some true
      else (match tc.tc_value_expr with
            | None -> Some true
            | Some se -> matches_shape_expr decls idtab visited se tm g fuel')
    | _ -> Some true
// Combined-triple-expression-list evaluator: gathers the pool for every
// (inverse,predicate) pair mentioned anywhere in `tes` (own expression +
// EXTENDS-merged ancestors, see `matches_shape`), runs the general search
// treating `tes` as an implicit EachOf, and accepts if ANY resulting
// leftover has every non-inverse entry's predicate covered by `extra`
// (inverse leftovers never matter here — `closed`/`extra` are defined
// over the focus's OWN outgoing arcs only, per shex.io-semantics; a
// mentioned inverse predicate's OWN [min,max] bound was already enforced
// inside the search itself, same as a non-inverse one).
and eval_expr_list_over_pool (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (tes : list shex_triple_expr) (extra : list string)
    (t : rdf_term) (g : rdf_graph) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    if Nil? tes then Some true
    else
      match te_mentioned_pairs_list idtab tes fuel' with
      | None -> None
      | Some pairs ->
        let pool0 = gather_pool g t (dedup_pairs pairs) in
        let ambiguous = ambiguous_pairs_of pairs in
        (match search_eachof_list decls idtab visited ambiguous tes pool0 g fuel' with
         | None -> None
         | Some leftovers ->
           Some (List.Tot.existsb
                   (fun (lo : pool_t) ->
                      List.Tot.for_all (fun (e : pool_elem) -> let (inv, pred, _) = e in inv || List.Tot.mem pred extra) lo)
                   leftovers))
// The set of (inverse,predicate) pairs a triple expression can consume —
// used both to size the candidate pool (`gather_pool`) and to compute
// which predicates are "mentioned" for the closed-shape check. `None`
// only when a `tripleExprRef` genuinely fails to resolve via `idtab`
// (never for `OneOf`/cardinality — unlike Stage 3's `te_signature`, this
// module handles those directly, so ambiguity is no longer a reason to
// bail out at the signature-computation stage).
and te_mentioned_pairs (idtab : list (string & shex_triple_expr)) (te : shex_triple_expr) (fuel : nat)
  : Tot (option (list (bool & string))) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match te with
    | TE_TripleConstraint tc -> Some [(tc.tc_inverse, tc.tc_predicate)]
    | TE_Ref id ->
      (match lookup_te_id idtab id with
       | Some resolved -> te_mentioned_pairs idtab resolved fuel'
       | None -> None)
    | TE_EachOf grp -> te_mentioned_pairs_list idtab grp.gr_expressions fuel'
    | TE_OneOf grp -> te_mentioned_pairs_list idtab grp.gr_expressions fuel'
and te_mentioned_pairs_list (idtab : list (string & shex_triple_expr)) (tes : list shex_triple_expr) (fuel : nat)
  : Tot (option (list (bool & string))) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match tes with
    | [] -> Some []
    | hd :: tl ->
      (match te_mentioned_pairs idtab hd fuel', te_mentioned_pairs_list idtab tl fuel' with
       | Some a, Some b -> Some (a @ b)
       | _, _ -> None)
// One TripleConstraint claiming a valid sub-selection of `pool` (its own
// (inverse,predicate) candidates only — everything else passes through to
// leftover untouched). Enumerates EVERY way of splitting the CURRENT
// predicate's candidates into "claimed" (must satisfy valueExpr) vs
// "left as leftover" (claimed-but-excess-good, or bad, are both left as
// leftover — see file banner cross-reference to the Stage 3 `extra`/
// `VapidExtra` findings, which this subsumes rather than special-cases),
// keeping only completions whose final claimed count is in
// `[tc_min,tc_max]`. A `fail(...)` Test-extension SemAct on this
// TripleConstraint forces every completion to collapse to "no valid way"
// (`Some []`), regardless of the structural search result.
and tc_choose_acc (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (tc : shex_triple_constraint) (pool : pool_t) (chosen : nat)
    (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match pool with
    | [] ->
      if chosen >= tc.tc_min && (tc.tc_max = (-1) || chosen <= tc.tc_max)
      then Some [[]] else Some []
    | (inv, pred, tm) :: tl ->
      if not (inv = tc.tc_inverse && pred = tc.tc_predicate) then
        (match tc_choose_acc decls idtab visited ambiguous tc tl chosen g fuel' with
         | None -> None
         | Some rests -> Some (List.Tot.map (fun (r : pool_t) -> (inv, pred, tm) :: r) rests))
      else
        let good_opt =
          match tc.tc_value_expr with
          | None -> Some true
          | Some se -> matches_shape_expr decls idtab visited se tm g fuel' in
        (match good_opt with
         | None -> None
         | Some is_good ->
           // A BAD candidate may always be left as leftover (tolerated
           // later via `extra`, or claimable by a sibling constraint on
           // the SAME predicate with a different, more permissive
           // valueExpr). A GOOD candidate may only be "left" (rather
           // than unconditionally counted) when this (inverse,predicate)
           // pair is genuinely ambiguous elsewhere in the combined
           // expression — otherwise every good candidate is forced into
           // the count, so an over-max good-count can never be
           // laundered into leftover-plus-extra (see `1val2IRIREFExtra1_
           // fail-iri2`'s doc comment on `ambiguous_pairs_of`).
           let offer_leave = (not is_good) || pair_mem (inv, pred) ambiguous in
           let leave_opt =
             if offer_leave then
               (match tc_choose_acc decls idtab visited ambiguous tc tl chosen g fuel' with
                | None -> None
                | Some leave_rests -> Some (List.Tot.map (fun (r : pool_t) -> (inv, pred, tm) :: r) leave_rests))
             else Some [] in
           (match leave_opt with
            | None -> None
            | Some leave_opts ->
              if is_good then
                (match tc_choose_acc decls idtab visited ambiguous tc tl (chosen + 1) g fuel' with
                 | None -> None
                 | Some take_rests -> Some (leave_opts @ take_rests))
              else Some leave_opts))
// Classifies a repeated-group child TripleConstraint's own candidate
// sub-pool into (good-count, bad-leftover-list) — no [min,max] bound
// applied here (the repeated group's OWN gmin/gmax governs the total
// across repetitions; see `search_repeated_group`).
and classify_candidates (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ve : option shex_shape_expr) (items : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (nat & pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match items with
    | [] -> Some (0, [])
    | hd :: tl ->
      let (inv, pred, tm) = hd in
      let good_opt = match ve with None -> Some true | Some se -> matches_shape_expr decls idtab visited se tm g fuel' in
      (match good_opt with
       | None -> None
       | Some is_good ->
         (match classify_candidates decls idtab visited ve tl g fuel' with
          | None -> None
          | Some (cnt, badl) -> if is_good then Some (cnt + 1, badl) else Some (cnt, hd :: badl)))
and count_children (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (tes : list shex_triple_expr) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list nat & pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match tes with
    | [] -> Some ([], pool)
    | TE_TripleConstraint tc :: tl ->
      let matching, rest = List.Tot.partition (fun (e : pool_elem) -> let (inv, pred, _) = e in inv = tc.tc_inverse && pred = tc.tc_predicate) pool in
      (match classify_candidates decls idtab visited tc.tc_value_expr matching g fuel' with
       | None -> None
       | Some (good_count, bad_list) ->
         (match count_children decls idtab visited tl rest g fuel' with
          | None -> None
          | Some (counts, leftover) -> Some (good_count :: counts, bad_list @ leftover)))
    | _ -> None
and search_repeated_group (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (grp : shex_group) (pool : pool_t) (g : rdf_graph) (fuel : nat) (is_eachof : bool)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    if not (distinct_child_pairs grp.gr_expressions) then None
    else
      match count_children decls idtab visited grp.gr_expressions pool g fuel' with
      | None -> None
      | Some (counts, leftover) ->
        let gmin = (match grp.gr_min with Some n -> n | None -> 1) in
        let gmax = (match grp.gr_max with Some n -> n | None -> 1) in
        let total_count = sum_nat counts in
        if is_eachof then
          (if not (all_equal_nat counts) then Some []
           else
             (match counts with
              | hd :: _ -> if hd >= gmin && (gmax = (-1) || hd <= gmax) then Some [leftover] else Some []
              | [] -> if 0 >= gmin && (gmax = (-1) || 0 <= gmax) then Some [leftover] else Some []))
        else
          (if total_count >= gmin && (gmax = (-1) || total_count <= gmax) then Some [leftover] else Some [])
// The general search: `te` against `pool`, returning every possible
// leftover-pool after a successful match (empty list = definitely no way
// to match; `None` = outside this module's reach or fuel exhausted).
and search_te (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (te : shex_triple_expr) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match te with
    | TE_TripleConstraint tc ->
      (match tc_choose_acc decls idtab visited ambiguous tc pool 0 g fuel' with
       | None -> None
       | Some results -> if any_semact_fails tc.tc_semacts then Some [] else Some results)
    | TE_Ref id ->
      (match lookup_te_id idtab id with
       | Some resolved -> search_te decls idtab visited ambiguous resolved pool g fuel'
       | None -> None)
    | TE_EachOf grp ->
      let raw =
        if Some? grp.gr_min || Some? grp.gr_max
        then search_repeated_group decls idtab visited grp pool g fuel' true
        else search_eachof_list decls idtab visited ambiguous grp.gr_expressions pool g fuel' in
      (match raw with
       | None -> None
       | Some results -> if any_semact_fails grp.gr_semacts then Some [] else Some results)
    | TE_OneOf grp ->
      let raw =
        if Some? grp.gr_min || Some? grp.gr_max
        then search_repeated_group decls idtab visited grp pool g fuel' false
        else search_oneof_list decls idtab visited ambiguous grp.gr_expressions pool g fuel' in
      (match raw with
       | None -> None
       | Some results -> if any_semact_fails grp.gr_semacts then Some [] else Some results)
// EachOf: sequential thread — each child's leftover states feed the next
// child (this is what makes an ambiguous shared-predicate split between
// TWO DIFFERENT children of the SAME EachOf correct: the first child's
// "leave it for later" branch produces a state the second child can then
// claim from).
and search_eachof_list (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (tes : list shex_triple_expr) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match tes with
    | [] -> Some [pool]
    | hd :: tl ->
      (match search_te decls idtab visited ambiguous hd pool g fuel' with
       | None -> None
       | Some states -> thread_states decls idtab visited ambiguous tl states g fuel')
and thread_states (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (tl : list shex_triple_expr) (states : list pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel' = fuel - 1 in
    match states with
    | [] -> Some []
    | s :: srest ->
      (match search_eachof_list decls idtab visited ambiguous tl s g fuel', thread_states decls idtab visited ambiguous tl srest g fuel' with
       | Some a, Some b -> Some (a @ b)
       | _, _ -> None)
// OneOf: try every child independently against the SAME pool, union the
// definite successes (see `combine_oneof`'s doc comment for why a
// definite success from one branch outranks an unresolved sibling).
and search_oneof_list (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (tes : list shex_triple_expr) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (option (list pool_t)) (decreases fuel) =
  if fuel = 0 then None
  else combine_oneof (search_te_list_map decls idtab visited ambiguous tes pool g (fuel - 1))
and search_te_list_map (decls : list shex_shape_decl) (idtab : list (string & shex_triple_expr))
    (visited : shex_visited) (ambiguous : list (bool & string)) (tes : list shex_triple_expr) (pool : pool_t) (g : rdf_graph) (fuel : nat)
  : Tot (list (option (list pool_t))) (decreases fuel) =
  if fuel = 0 then []
  else
    let fuel' = fuel - 1 in
    match tes with
    | [] -> []
    | hd :: tl -> search_te decls idtab visited ambiguous hd pool g fuel' :: search_te_list_map decls idtab visited ambiguous tl pool g fuel'

// ================================================================
// Top-level entry point (SIGNATURE UNCHANGED from Stage 2/3 — the
// consumer contract `bin/shex-runner/shex_runner.ml` calls this exact
// name/shape and must not be touched here). Schema-level `startActs`
// (`sch_start_acts`) are evaluated once per call, per the corpus's own
// `startCode1fail_abort`/`startCode1startReffail_abort`/
// `startCode3fail_abort` fixtures — a `fail(...)` there aborts the WHOLE
// validation regardless of which shape label is targeted (all three
// fixtures explicitly target shape `S1` via `sht:shape`, not the
// schema's `start` production, confirming startActs fire independent of
// the start-vs-explicit-shape distinction for this suite's Test
// extension). Fuel is sized generously off both the schema's shape count
// (SE_Ref/EXTENDS-chain hop bound) and the graph's triple count squared
// (the general search's subset-enumeration depth is bounded by a single
// predicate's candidate-pool length, which is at most the graph's triple
// count; the extra quadratic term is headroom for deeply-nested
// EachOf/OneOf trees each re-walking a pool of that size, not a
// measured requirement — test-suite data graphs are a handful of
// triples per plan doc, so this stays cheap in practice).
// ================================================================

let validate_focus (schema : shex_schema) (shape_id : option string) (t : rdf_term) (g : rdf_graph) : option bool =
  if any_semact_fails schema.sch_start_acts then Some false
  else
    let idtab = shape_decl_list_collect_ids schema.sch_shapes in
    let n_shapes = List.Tot.length schema.sch_shapes in
    let n_graph = List.Tot.length g in
    let fuel = 300 + op_Multiply 50 n_shapes + op_Multiply 30 n_graph + op_Multiply 5 (op_Multiply n_graph n_graph) in
    match shape_id with
    | Some label ->
      (match lookup_shape_decl schema.sch_shapes label with
       | Some sd -> matches_shape_expr schema.sch_shapes idtab [] sd.sd_expr t g fuel
       | None -> None)
    | None ->
      (match schema.sch_start with
       | Some se -> matches_shape_expr schema.sch_shapes idtab [] se t g fuel
       | None -> None)
