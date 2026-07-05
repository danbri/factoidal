module ShEx.Schema

// ============================================================================
// ShEx (Shape Expressions) 2.1 — ShExJ (JSON syntax) AST + Parser.JSON-based
// decoder. Stage 1 of the ShEx program
// (docs/designissues/2026-07-05-shex-program-plan.md): structural parse of
// the ShExJ document shape only — NO validate() function, NO NodeConstraint
// facet evaluation, NO triple-expression partition matching. Those are later
// stages layered on top of this AST (ShEx.Validation.fst).
//
// Scope (mirrors the plan doc's "Scope cuts"):
//   - ShExJ only. ShExC (the human-readable concrete syntax) is out of scope
//     indefinitely (Stage 9) — this module never sees ShExC text.
//   - The full ShExJ grammar's STRUCTURAL shape is decoded (Schema,
//     ShapeDecl, all shapeExpr variants, all tripleExpr variants, the full
//     NodeConstraint facet set, the full valueSetValue variant set,
//     SemActs, Annotations, extra/closed/extends/imports) so later stages
//     have a complete tree to validate against and Stage 1's own smoke test
//     ("does it parse") is a meaningful signal against the vendored corpus.
//   - shapeExprRef / tripleExprRef: the corpus (third_party/testing/shex)
//     only ever uses the BARE-STRING reference form (a shapeExpr or
//     tripleExpr JSON value that is itself a JString naming another
//     shape's/expression's "id"). The alternative object form
//     {"type":"ShapeRef","reference": IRI} defined in some ShExJ discussions
//     does not appear in the pinned commit (grepped, zero hits) — the
//     bare-string form is what SE_Ref / TE_Ref decode.
//   - Numeric NodeConstraint facets (mininclusive/maxinclusive/minexclusive/
//     maxexclusive) are kept as the VERBATIM JSON number lexeme (a string),
//     not decoded to a scaled/int representation here — same discipline as
//     Parser.JSON's own JNumber and the SHACL/JSON-LD precedent of "keep the
//     lexeme, let the validation-time consumer choose double-aware vs
//     integer parsing" (anti-pattern #8: parse_to_scaled before
//     parse_double_to_scaled). length/minlength/maxlength/totaldigits/
//     fractiondigits and TripleConstraint/group min/max ARE decoded to F-star
//     `int` here, since the ShExJ grammar fixes those as plain JSON integers
//     (no decimal/exponent form ever appears for them in the spec or the
//     corpus).
//   - SemAct "code" bodies are opaque strings (never executed — SemActs are
//     explicitly out of scope per the plan's scope cuts; the AST just keeps
//     them so a future extension point has somewhere to hang).
//
// Reference: shex.io/shex-semantics (ShEx 2.1, Final Community Group Report,
// 2019-10-08) and the ShExJ JSON Schema it defines. Corpus:
// third_party/testing/shex (shexSpec/shexTest, pinned commit 7d0cd92b),
// specifically the schemas/*.json fixtures.
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.JSON
open Parser.IRI

// ================================================================
// Small local integer-lexeme decoder (NOT a JSON parser — Parser.JSON
// already tokenized the number; this only turns that lexeme string into an
// F-star int). Mirrors SPARQL11.Algebra.parse_int_string's exact structure,
// kept local rather than importing SPARQL11.Algebra so ShEx.Schema stays a
// lightweight leaf module (same "dependency-free-of-SPARQL11.Algebra"
// discipline JSONLD.Context.fst documents for itself).
// ================================================================

let shex_char_to_digit (c:FStar.Char.char) : option int =
  let n = FStar.Char.int_of_char c in
  if n >= 48 && n <= 57 then Some (n - 48) else None

let rec shex_parse_int_chars (chars:list FStar.Char.char) (acc:int)
  : Tot (option int) (decreases chars) =
  match chars with
  | [] -> Some acc
  | c :: rest ->
    (match shex_char_to_digit c with
     | Some d -> shex_parse_int_chars rest (op_Multiply acc 10 + d)
     | None -> None)

// Decodes a JSON-number lexeme (as produced by Parser.JSON's JNumber) into
// an int. Only integer lexemes (no '.', no exponent) succeed — exactly the
// shape ShExJ's min/max/length/*digits fields use.
let shex_parse_int_string (s:string) : option int =
  match String.list_of_string s with
  | [] -> None
  | chars ->
    if List.Tot.hd chars = FStar.Char.char_of_int 45 (* '-' *)
    then (match shex_parse_int_chars (List.Tot.tl chars) 0 with
          | Some n -> Some (0 - n)
          | None -> None)
    else shex_parse_int_chars chars 0

// ================================================================
// json_val field-reading conveniences beyond Parser.JSON's own accessors.
// ================================================================

let json_get_number_lexeme (key:string) (obj:json_val) : option string =
  match json_get_field key obj with
  | Some (JNumber s) -> Some s
  | _ -> None

let json_get_int (key:string) (obj:json_val) : option int =
  match json_get_number_lexeme key obj with
  | Some s -> shex_parse_int_string s
  | None -> None

let json_get_int_default (key:string) (obj:json_val) (d:int) : int =
  match json_get_int key obj with
  | Some n -> n
  | None -> d

let json_get_bool_default (key:string) (obj:json_val) (d:bool) : bool =
  match json_get_bool key obj with
  | Some b -> b
  | None -> d

// ================================================================
// AST — leaf types (no mutual recursion with shapeExpr/tripleExpr)
// ================================================================

type shex_node_kind =
  | ShexNK_Iri
  | ShexNK_BNode
  | ShexNK_NonLiteral
  | ShexNK_Literal

// A "stem" value: either a plain IRI/literal-stem string, or the ShExJ
// {"type":"Wildcard"} marker (only legal inside a *StemRange's "stem" slot,
// per the ShExJ grammar — a plain Stem's "stem" is always a bare string).
type shex_stem =
  | ShexStemPlain   : string -> shex_stem
  | ShexStemWildcard : shex_stem

// An exact ObjectValue: either a bare IRI (a plain JSON string in the ShExJ
// source) or a literal value with optional language tag / datatype IRI.
type shex_object_value =
  | ShexOV_Iri     : string -> shex_object_value
  | ShexOV_Literal : value:string -> language:option string -> datatype:option string -> shex_object_value

type shex_sem_act = {
  sa_name : string;
  sa_code : option string;
}

type shex_annotation = {
  an_predicate : string;
  an_object    : shex_object_value;
}

// ================================================================
// value_set_value: NodeConstraint's "values" array element type.
// Not mutually recursive with shapeExpr/tripleExpr, but IS self-recursive
// (StemRange's "exclusions" are themselves value_set_values) — decoded in
// the big fuel-threaded mutual group below alongside shapeExpr/tripleExpr,
// since NodeConstraint (a shapeExpr variant) is the entry point that reaches
// it.
// ================================================================

type shex_value_set_value =
  | VSV_Value            : shex_object_value -> shex_value_set_value
  | VSV_IriStem          : shex_stem -> shex_value_set_value
  | VSV_IriStemRange     : shex_stem -> list shex_value_set_value -> shex_value_set_value
  | VSV_LiteralStem      : shex_stem -> shex_value_set_value
  | VSV_LiteralStemRange : shex_stem -> list shex_value_set_value -> shex_value_set_value
  | VSV_Language         : string -> shex_value_set_value
  | VSV_LanguageStem     : shex_stem -> shex_value_set_value
  | VSV_LanguageStemRange : shex_stem -> list shex_value_set_value -> shex_value_set_value

// A bare JSON string inside a *StemRange's "exclusions" array is NOT always
// an IRI shorthand — the ShExJ grammar types `IriStemRange.exclusions` as
// `(IRI | IriStem) list`, but `LiteralStemRange.exclusions` as
// `(string | LiteralStem) list` (a bare exclusion string = an exact literal
// lexical form) and `LanguageStemRange.exclusions` as
// `(string | LanguageStem) list` (a bare exclusion string = a language
// tag/range). `decode_value_set_value`'s top-level "values"-array JString
// case is correctly IRI-shorthand (per the general value_set_value
// grammar), but reusing it verbatim for exclusions silently mis-decodes
// e.g. `LiteralStemRange.exclusions: ["v1","v2","v3"]` as three IRI
// ObjectValues that can never match a Literal target — the exclusion check
// then vacuously never excludes anything. `decode_value_set_value_list_kind`
// (below) is the context-aware exclusion-list decoder that fixes this.
type shex_vsv_kind = | VSVK_Iri | VSVK_Literal | VSVK_Language

let decode_bare_vsv_string (kind : shex_vsv_kind) (s : string) : shex_value_set_value =
  match kind with
  | VSVK_Iri -> VSV_Value (ShexOV_Iri s)
  | VSVK_Literal -> VSV_Value (ShexOV_Literal s None None)
  | VSVK_Language -> VSV_Language s

type shex_node_constraint = {
  nc_node_kind      : option shex_node_kind;
  nc_datatype       : option string;
  nc_values         : list shex_value_set_value;
  nc_length         : option int;
  nc_minlength      : option int;
  nc_maxlength      : option int;
  nc_pattern        : option string;
  nc_flags          : option string;
  // Numeric facets: verbatim JSON-number lexemes, see banner comment.
  nc_mininclusive   : option string;
  nc_maxinclusive   : option string;
  nc_minexclusive   : option string;
  nc_maxexclusive   : option string;
  nc_totaldigits    : option int;
  nc_fractiondigits : option int;
}

// ================================================================
// shapeExpr / tripleExpr — the mutually recursive core of the AST.
// ================================================================

type shex_shape_expr =
  | SE_Ref           : string -> shex_shape_expr          // shapeExprRef (bare-string form)
  | SE_ShapeAnd      : list shex_shape_expr -> shex_shape_expr
  | SE_ShapeOr       : list shex_shape_expr -> shex_shape_expr
  | SE_ShapeNot      : shex_shape_expr -> shex_shape_expr
  | SE_NodeConstraint : shex_node_constraint -> shex_shape_expr
  | SE_Shape         : shex_shape -> shex_shape_expr
  | SE_ShapeExternal : shex_shape_expr

and shex_shape = {
  sh_closed      : bool;
  sh_extra       : list string;                  // predicates: EXTRA-permitted, unmatched by any TripleConstraint
  sh_expression  : option shex_triple_expr;
  sh_semacts     : list shex_sem_act;
  sh_annotations : list shex_annotation;
  sh_extends     : list string;                  // shapeExprRefs this shape EXTENDS (Stage 6 territory; kept raw here)
}

and shex_triple_expr =
  | TE_Ref              : string -> shex_triple_expr      // tripleExprRef (bare-string form, resolves by "id")
  | TE_TripleConstraint : shex_triple_constraint -> shex_triple_expr
  | TE_EachOf           : shex_group -> shex_triple_expr
  | TE_OneOf            : shex_group -> shex_triple_expr

// EachOf/OneOf. gr_min/gr_max are None for a plain (non-cardinality-wrapped)
// group — the ordinary case — and Some when the group itself carries a
// repeat cardinality (the "RepeatedOneOf"/"RepeatedGroup"/"Greedy" corpus
// trait tags, Stage 4 territory).
and shex_group = {
  gr_id          : option string;
  gr_expressions : list shex_triple_expr;
  gr_min         : option int;
  gr_max         : option int;
  gr_semacts     : list shex_sem_act;
  gr_annotations : list shex_annotation;
}

and shex_triple_constraint = {
  tc_id          : option string;
  tc_inverse     : bool;
  tc_predicate   : string;
  tc_value_expr  : option shex_shape_expr;
  tc_min         : int;                          // default 1 when absent
  tc_max         : int;                          // default 1 when absent; -1 means unbounded
  tc_semacts     : list shex_sem_act;
  tc_annotations : list shex_annotation;
}

type shex_shape_decl = {
  sd_id          : string;
  sd_is_abstract : bool;
  sd_expr        : shex_shape_expr;
}

type shex_schema = {
  sch_start      : option shex_shape_expr;
  sch_start_acts : list shex_sem_act;
  sch_shapes     : list shex_shape_decl;
  sch_imports    : list string;                  // Stage 7 territory; kept raw here
}

// ================================================================
// Leaf decoders (no mutual recursion with the shapeExpr/tripleExpr group).
// ================================================================

let decode_node_kind (s:string) : option shex_node_kind =
  if s = "iri" then Some ShexNK_Iri
  else if s = "bnode" then Some ShexNK_BNode
  else if s = "nonliteral" then Some ShexNK_NonLiteral
  else if s = "literal" then Some ShexNK_Literal
  else None

// Resolves a relative-IRI-shaped string against `base` (RFC 3986 §5.2, via
// Parser.IRI.resolve_iri_v2 — the same resolver Parser.Turtle uses for
// `@base`/`BASE`). A no-op for an already-absolute string (an IRI with a
// scheme resolves to itself regardless of base), so calling this on every
// id/predicate/datatype/value string below is safe for the corpus's
// overwhelmingly-common case of already-absolute ShExJ IRIs; it only
// changes behavior for the handful of `sht:relativeIRI`-trait fixtures
// (validation/1dot-relative.json) whose ShExJ twin keeps its "id"/
// "predicate"/value strings bare, per the ShExJ spec's requirement that a
// schema's relative IRIs resolve against the schema document's own base.
//
// A leading "_:" is a blank-node label (ShapeDecl "id"/shapeExpr-ref
// convention — see bnode1dot.json's `"id": "_:S1"`, decoded verbatim by
// this same code path since ShExJ has no separate "id kind" tag), NOT an
// IRI reference — RFC 3986 has no notion of it, and running it through
// `resolve_iri_v2` would merge it into `base`'s path as if "_:S1" were a
// relative path segment, corrupting the label so it no longer matches the
// runner's `sht:shape _:S1` -> "_:S1" string. Guard it unresolved.
let resolve_against (base:string) (s:string) : string =
  if FStar.String.length s >= 2 && FStar.String.sub s 0 2 = "_:" then s else resolve_iri_v2 base s

let resolve_against_opt (base:string) (o:option string) : option string =
  match o with
  | None -> None
  | Some s -> Some (resolve_against base s)

// A "stem" field's value: a bare string, or {"type":"Wildcard"}. Only an
// `IriStem`'s stem is IRI-shaped — `LiteralStem`/`LanguageStem` stems are
// plain literal-value / language-tag prefixes (e.g. `{"type":
// "LanguageStem","stem":"fr"}`, a language-subtag prefix, not a path
// segment), so `kind` gates whether `resolve_against` applies; resolving
// a LiteralStem/LanguageStem stem against `base` would silently turn a
// literal 2-letter language prefix like "fr" into an absolute IRI merged
// into the schema's own path — wrong per the ShExJ grammar, and the
// regression this fix replaces (caught by the 1val1languageStem*/
// 1val1literalStem* fixtures going MISMATCH when this guard was absent).
let decode_stem (base:string) (kind:shex_vsv_kind) (v:json_val) : option shex_stem =
  match v with
  | JString s -> Some (ShexStemPlain (match kind with VSVK_Iri -> resolve_against base s | _ -> s))
  | JObject _ ->
    (match json_get_string "type" v with
     | Some "Wildcard" -> Some ShexStemWildcard
     | _ -> None)
  | _ -> None

let rec decode_string_list (items:list json_val) : Tot (option (list string)) (decreases items) =
  match items with
  | [] -> Some []
  | JString s :: tl ->
    (match decode_string_list tl with
     | Some rest -> Some (s :: rest)
     | None -> None)
  | _ -> None

let decode_sem_act (v:json_val) : option shex_sem_act =
  match json_get_string "name" v with
  | None -> None
  | Some nm -> Some ({ sa_name = nm; sa_code = json_get_string "code" v })

let rec decode_sem_act_list (items:list json_val) : Tot (option (list shex_sem_act)) (decreases items) =
  match items with
  | [] -> Some []
  | hd :: tl ->
    (match decode_sem_act hd with
     | None -> None
     | Some sa ->
       (match decode_sem_act_list tl with
        | None -> None
        | Some rest -> Some (sa :: rest)))

// An Annotation's "object" is an ObjectValue: a bare IRI string, or an
// object-literal ({"value":..., "language"?, "type"?}).
let decode_object_value (v:json_val) : option shex_object_value =
  match v with
  | JString s -> Some (ShexOV_Iri s)
  | JObject _ ->
    (match json_get_string "value" v with
     | None -> None
     | Some value -> Some (ShexOV_Literal value (json_get_string "language" v) (json_get_string "type" v)))
  | _ -> None

let decode_annotation (v:json_val) : option shex_annotation =
  match json_get_string "predicate" v, json_get_field "object" v with
  | Some p, Some ov ->
    (match decode_object_value ov with
     | Some ovv -> Some ({ an_predicate = p; an_object = ovv })
     | None -> None)
  | _, _ -> None

let rec decode_annotation_list (items:list json_val) : Tot (option (list shex_annotation)) (decreases items) =
  match items with
  | [] -> Some []
  | hd :: tl ->
    (match decode_annotation hd with
     | None -> None
     | Some an ->
       (match decode_annotation_list tl with
        | None -> None
        | Some rest -> Some (an :: rest)))

// ================================================================
// The mutually recursive core: shapeExpr / shape / tripleExpr / group /
// tripleConstraint / nodeConstraint / value_set_value, all threaded through
// one shared `fuel:nat` decreasing metric (no structural-subterm relation is
// available once decoding goes through Parser.JSON's json_get_field/
// json_get_array accessors, so plain fuel-decrease is the termination
// argument — same idiom Parser.JSON itself uses for its own nesting depth,
// and JSONLD.Context uses for its remote-fetch fuel). Each top-level caller
// (decode_shape_decl, decode_schema's "start") seeds `fuel` with
// `json_size` of the specific json_val subtree it is about to decode, which
// is a safe generous upper bound: json_size counts one unit per value plus
// one per array element / object member visited, at least as many units as
// this group's recursion can consume before reaching every leaf.
// ================================================================

let rec decode_shape_expr (base:string) (v:json_val) (fuel:nat) : Tot (option shex_shape_expr) (decreases fuel) =
  if fuel = 0 then None
  else
    match v with
    | JString s -> Some (SE_Ref (resolve_against base s))
    | JObject _ ->
      (match json_get_string "type" v with
       | Some "ShapeAnd" ->
         (match json_get_array "shapeExprs" v with
          | None -> None
          | Some items ->
            (match decode_shape_expr_list base items (fuel - 1) with
             | Some ses -> Some (SE_ShapeAnd ses)
             | None -> None))
       | Some "ShapeOr" ->
         (match json_get_array "shapeExprs" v with
          | None -> None
          | Some items ->
            (match decode_shape_expr_list base items (fuel - 1) with
             | Some ses -> Some (SE_ShapeOr ses)
             | None -> None))
       | Some "ShapeNot" ->
         (match json_get_field "shapeExpr" v with
          | None -> None
          | Some sub ->
            (match decode_shape_expr base sub (fuel - 1) with
             | Some se -> Some (SE_ShapeNot se)
             | None -> None))
       | Some "NodeConstraint" ->
         (match decode_node_constraint base v (fuel - 1) with
          | Some nc -> Some (SE_NodeConstraint nc)
          | None -> None)
       | Some "Shape" ->
         (match decode_shape base v (fuel - 1) with
          | Some sh -> Some (SE_Shape sh)
          | None -> None)
       | Some "ShapeExternal" -> Some SE_ShapeExternal
       | _ -> None)
    | _ -> None

and decode_shape_expr_list (base:string) (items:list json_val) (fuel:nat)
  : Tot (option (list shex_shape_expr)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | hd :: tl ->
      (match decode_shape_expr base hd (fuel - 1) with
       | None -> None
       | Some se ->
         (match decode_shape_expr_list base tl (fuel - 1) with
          | None -> None
          | Some rest -> Some (se :: rest)))

and decode_shape (base:string) (v:json_val) (fuel:nat) : Tot (option shex_shape) (decreases fuel) =
  if fuel = 0 then None
  else
    let expr_ok, expr =
      match json_get_field "expression" v with
      | None -> true, None
      | Some ej ->
        (match decode_triple_expr base ej (fuel - 1) with
         | Some te -> true, Some te
         | None -> false, None) in
    if not expr_ok then None
    else
      let extra_ok, extra =
        match json_get_array "extra" v with
        | None -> true, []
        | Some items ->
          (match decode_string_list items with
           | Some l -> true, l
           | None -> false, []) in
      if not extra_ok then None
      else
        let semacts_ok, semacts =
          match json_get_array "semActs" v with
          | None -> true, []
          | Some items ->
            (match decode_sem_act_list items with
             | Some sa -> true, sa
             | None -> false, []) in
        if not semacts_ok then None
        else
          let annots_ok, annots =
            match json_get_array "annotations" v with
            | None -> true, []
            | Some items ->
              (match decode_annotation_list items with
               | Some an -> true, an
               | None -> false, []) in
          if not annots_ok then None
          else
            let extends_ok, extends =
              match json_get_array "extends" v with
              | None -> true, []
              | Some items ->
                (match decode_string_list items with
                 | Some l -> true, l
                 | None -> false, []) in
            if not extends_ok then None
            else
              Some ({
                sh_closed      = json_get_bool_default "closed" v false;
                sh_extra       = extra;
                sh_expression  = expr;
                sh_semacts     = semacts;
                sh_annotations = annots;
                sh_extends     = extends;
              })

and decode_triple_expr (base:string) (v:json_val) (fuel:nat) : Tot (option shex_triple_expr) (decreases fuel) =
  if fuel = 0 then None
  else
    match v with
    | JString s -> Some (TE_Ref (resolve_against base s))
    | JObject _ ->
      (match json_get_string "type" v with
       | Some "TripleConstraint" ->
         (match decode_triple_constraint base v (fuel - 1) with
          | Some tc -> Some (TE_TripleConstraint tc)
          | None -> None)
       | Some "EachOf" ->
         (match decode_group base v (fuel - 1) with
          | Some g -> Some (TE_EachOf g)
          | None -> None)
       | Some "OneOf" ->
         (match decode_group base v (fuel - 1) with
          | Some g -> Some (TE_OneOf g)
          | None -> None)
       | _ -> None)
    | _ -> None

and decode_triple_expr_list (base:string) (items:list json_val) (fuel:nat)
  : Tot (option (list shex_triple_expr)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | hd :: tl ->
      (match decode_triple_expr base hd (fuel - 1) with
       | None -> None
       | Some te ->
         (match decode_triple_expr_list base tl (fuel - 1) with
          | None -> None
          | Some rest -> Some (te :: rest)))

and decode_group (base:string) (v:json_val) (fuel:nat) : Tot (option shex_group) (decreases fuel) =
  if fuel = 0 then None
  else
    match json_get_array "expressions" v with
    | None -> None
    | Some items ->
      (match decode_triple_expr_list base items (fuel - 1) with
       | None -> None
       | Some exprs ->
         let semacts_ok, semacts =
           match json_get_array "semActs" v with
           | None -> true, []
           | Some sitems ->
             (match decode_sem_act_list sitems with
              | Some sa -> true, sa
              | None -> false, []) in
         if not semacts_ok then None
         else
           let annots_ok, annots =
             match json_get_array "annotations" v with
             | None -> true, []
             | Some aitems ->
               (match decode_annotation_list aitems with
                | Some an -> true, an
                | None -> false, []) in
           if not annots_ok then None
           else
             Some ({
               gr_id          = json_get_string "id" v;
               gr_expressions = exprs;
               gr_min         = json_get_int "min" v;
               gr_max         = json_get_int "max" v;
               gr_semacts     = semacts;
               gr_annotations = annots;
             }))

and decode_triple_constraint (base:string) (v:json_val) (fuel:nat)
  : Tot (option shex_triple_constraint) (decreases fuel) =
  if fuel = 0 then None
  else
    match json_get_string "predicate" v with
    | None -> None
    | Some pred ->
      let ve_ok, ve =
        match json_get_field "valueExpr" v with
        | None -> true, None
        | Some vej ->
          (match decode_shape_expr base vej (fuel - 1) with
           | Some se -> true, Some se
           | None -> false, None) in
      if not ve_ok then None
      else
        let semacts_ok, semacts =
          match json_get_array "semActs" v with
          | None -> true, []
          | Some items ->
            (match decode_sem_act_list items with
             | Some sa -> true, sa
             | None -> false, []) in
        if not semacts_ok then None
        else
          let annots_ok, annots =
            match json_get_array "annotations" v with
            | None -> true, []
            | Some items ->
              (match decode_annotation_list items with
               | Some an -> true, an
               | None -> false, []) in
          if not annots_ok then None
          else
            Some ({
              tc_id          = json_get_string "id" v;
              tc_inverse     = json_get_bool_default "inverse" v false;
              tc_predicate   = resolve_against base pred;
              tc_value_expr  = ve;
              tc_min         = json_get_int_default "min" v 1;
              tc_max         = json_get_int_default "max" v 1;
              tc_semacts     = semacts;
              tc_annotations = annots;
            })

and decode_node_constraint (base:string) (v:json_val) (fuel:nat)
  : Tot (option shex_node_constraint) (decreases fuel) =
  if fuel = 0 then None
  else
    let nk_ok, nk =
      match json_get_string "nodeKind" v with
      | None -> true, None
      | Some s ->
        (match decode_node_kind s with
         | Some k -> true, Some k
         | None -> false, None) in
    if not nk_ok then None
    else
      let values_ok, values =
        match json_get_array "values" v with
        | None -> true, []
        | Some items ->
          (match decode_value_set_value_list base items (fuel - 1) with
           | Some vs -> true, vs
           | None -> false, []) in
      if not values_ok then None
      else
        Some ({
          nc_node_kind      = nk;
          nc_datatype       = resolve_against_opt base (json_get_string "datatype" v);
          nc_values         = values;
          nc_length         = json_get_int "length" v;
          nc_minlength      = json_get_int "minlength" v;
          nc_maxlength      = json_get_int "maxlength" v;
          nc_pattern        = json_get_string "pattern" v;
          nc_flags          = json_get_string "flags" v;
          nc_mininclusive   = json_get_number_lexeme "mininclusive" v;
          nc_maxinclusive   = json_get_number_lexeme "maxinclusive" v;
          nc_minexclusive   = json_get_number_lexeme "minexclusive" v;
          nc_maxexclusive   = json_get_number_lexeme "maxexclusive" v;
          nc_totaldigits    = json_get_int "totaldigits" v;
          nc_fractiondigits = json_get_int "fractiondigits" v;
        })

and decode_value_set_value (base:string) (v:json_val) (fuel:nat)
  : Tot (option shex_value_set_value) (decreases fuel) =
  if fuel = 0 then None
  else
    match v with
    | JString s -> Some (VSV_Value (ShexOV_Iri (resolve_against base s)))
    | JObject _ ->
      (match json_get_string "value" v with
       | Some value ->
         Some (VSV_Value (ShexOV_Literal value (json_get_string "language" v) (json_get_string "type" v)))
       | None ->
         (match json_get_string "type" v with
          | Some "IriStem" ->
            (match json_get_field "stem" v with
             | Some stv -> (match decode_stem base VSVK_Iri stv with Some st -> Some (VSV_IriStem st) | None -> None)
             | None -> None)
          | Some "LiteralStem" ->
            (match json_get_field "stem" v with
             | Some stv -> (match decode_stem base VSVK_Literal stv with Some st -> Some (VSV_LiteralStem st) | None -> None)
             | None -> None)
          | Some "LanguageStem" ->
            (match json_get_field "stem" v with
             | Some stv -> (match decode_stem base VSVK_Language stv with Some st -> Some (VSV_LanguageStem st) | None -> None)
             | None -> None)
          | Some "Language" ->
            (match json_get_string "languageTag" v with
             | Some lt -> Some (VSV_Language lt)
             | None -> None)
          | Some "IriStemRange" ->
            (match decode_stem_range_parts base v VSVK_Iri (fuel - 1) with
             | Some (st, excl) -> Some (VSV_IriStemRange st excl)
             | None -> None)
          | Some "LiteralStemRange" ->
            (match decode_stem_range_parts base v VSVK_Literal (fuel - 1) with
             | Some (st, excl) -> Some (VSV_LiteralStemRange st excl)
             | None -> None)
          | Some "LanguageStemRange" ->
            (match decode_stem_range_parts base v VSVK_Language (fuel - 1) with
             | Some (st, excl) -> Some (VSV_LanguageStemRange st excl)
             | None -> None)
          | _ -> None))
    | _ -> None

and decode_value_set_value_list (base:string) (items:list json_val) (fuel:nat)
  : Tot (option (list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | hd :: tl ->
      (match decode_value_set_value base hd (fuel - 1) with
       | None -> None
       | Some vv ->
         (match decode_value_set_value_list base tl (fuel - 1) with
          | None -> None
          | Some rest -> Some (vv :: rest)))

// Context-aware exclusion-list decoder (see `shex_vsv_kind`'s doc comment):
// a bare JString exclusion element is interpreted per `kind` instead of
// always as an IRI; a JObject exclusion element (an explicit
// IriStem/LiteralStem/LanguageStem, or an object-form Literal) is
// unambiguous regardless of context, so it still goes through the general
// `decode_value_set_value`.
and decode_value_set_value_list_kind (base:string) (items:list json_val) (kind:shex_vsv_kind) (fuel:nat)
  : Tot (option (list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then None
  else
    match items with
    | [] -> Some []
    | JString s :: tl ->
      (match decode_value_set_value_list_kind base tl kind (fuel - 1) with
       | None -> None
       | Some rest -> Some (decode_bare_vsv_string kind s :: rest))
    | hd :: tl ->
      (match decode_value_set_value base hd (fuel - 1) with
       | None -> None
       | Some vv ->
         (match decode_value_set_value_list_kind base tl kind (fuel - 1) with
          | None -> None
          | Some rest -> Some (vv :: rest)))

// Shared (stem, exclusions) decode for IriStemRange/LiteralStemRange/
// LanguageStemRange — identical shape, differing only in which constructor
// the caller wraps the result in (and, per `kind`, how a bare-string
// exclusion element is interpreted). "exclusions" is optional (absent means
// no exclusions, per the ShExJ grammar's "?" on that member).
and decode_stem_range_parts (base:string) (v:json_val) (kind:shex_vsv_kind) (fuel:nat)
  : Tot (option (shex_stem & list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then None
  else
    match json_get_field "stem" v with
    | None -> None
    | Some stv ->
      (match decode_stem base kind stv with
       | None -> None
       | Some st ->
         (match json_get_array "exclusions" v with
          | None -> Some (st, [])
          | Some items ->
            (match decode_value_set_value_list_kind base items kind (fuel - 1) with
             | Some excl -> Some (st, excl)
             | None -> None)))

// ================================================================
// Top level: ShapeDecl / Schema.
// ================================================================

// Two ShExJ ShapeDecl encodings both occur in the vendored corpus (stage 3
// finding, formerly a stage-1 gap): the "generated" form
// {"type":"ShapeDecl","id":..., "shapeExpr": {...}} used throughout
// schemas/*.json, AND the "bare" shorthand ShExJ's own grammar also permits —
// the shapeExpr object's own fields (e.g. {"type":"Shape","expression":...})
// merged directly with "id" at the same JSON-object level, no nested
// "shapeExpr" wrapper — used by several hand-written validation/*.json
// fixtures (1dot-relative.json, Pstar.json, nPlus1.json, etc). Prefer the
// nested "shapeExpr" field when present (unambiguous); otherwise treat `v`
// itself as the shapeExpr (the extra "id"/"abstract" keys are simply ignored
// by decode_shape_expr's field-specific accessors, which only look up the
// keys they recognise).
let decode_shape_decl (base:string) (v:json_val) : option shex_shape_decl =
  match json_get_string "id" v with
  | None -> None
  | Some sid ->
    let sej = match json_get_field "shapeExpr" v with
      | Some nested -> nested
      | None -> v in
    (match decode_shape_expr base sej (json_size sej) with
     | Some se ->
       Some ({
         sd_id          = resolve_against base sid;
         sd_is_abstract = json_get_bool_default "abstract" v false;
         sd_expr        = se;
       })
     | None -> None)

let rec decode_shape_decl_list (base:string) (items:list json_val)
  : Tot (option (list shex_shape_decl)) (decreases items) =
  match items with
  | [] -> Some []
  | hd :: tl ->
    (match decode_shape_decl base hd with
     | None -> None
     | Some sd ->
       (match decode_shape_decl_list base tl with
        | None -> None
        | Some rest -> Some (sd :: rest)))

// Decodes a top-level ShExJ Schema json_val (already parsed by
// Parser.JSON). `base` is the schema document's own absolute IRI (or any
// string RFC-3986-parseable as one) — every relative "id"/"predicate"/
// "datatype"/value-set IRI-shaped string in the document resolves against
// it, per the ShExJ spec's document-relative-IRI rule (see
// `resolve_against`'s doc comment). Passing an empty string / non-IRI
// `base` is safe: `resolve_iri_v2` falls back to returning the reference
// unchanged when `base` doesn't parse as an IRI, so callers that have no
// meaningful base (e.g. a schema with no relative IRIs at all — the
// corpus's overwhelming majority) can pass "" with no behavior change.
// Returns None on any structural mismatch — an honest parse failure,
// never a silently-dropped field.
let decode_schema (base:string) (v:json_val) : option shex_schema =
  match json_get_string "type" v with
  | Some "Schema" ->
    let start_ok, start =
      match json_get_field "start" v with
      | None -> true, None
      | Some sv ->
        (match decode_shape_expr base sv (json_size sv) with
         | Some se -> true, Some se
         | None -> false, None) in
    if not start_ok then None
    else
      let startacts_ok, startacts =
        match json_get_array "startActs" v with
        | None -> true, []
        | Some items ->
          (match decode_sem_act_list items with
           | Some sa -> true, sa
           | None -> false, []) in
      if not startacts_ok then None
      else
        let shapes_ok, shapes =
          match json_get_array "shapes" v with
          | None -> true, []
          | Some items ->
            (match decode_shape_decl_list base items with
             | Some sd -> true, sd
             | None -> false, []) in
        if not shapes_ok then None
        else
          let imports_ok, imports =
            match json_get_array "imports" v with
            | None -> true, []
            | Some items ->
              (match decode_string_list items with
               | Some l -> true, l
               | None -> false, []) in
          if not imports_ok then None
          else
            Some ({
              sch_start      = start;
              sch_start_acts = startacts;
              sch_shapes     = shapes;
              sch_imports    = imports;
            })
  | _ -> None

// Convenience: parse raw ShExJ text straight to the AST in one call,
// resolving relative IRIs against `base` (see `decode_schema`'s doc
// comment — pass "" when the caller has no meaningful document IRI).
let decode_shex_schema (input:string) (base:string) : option shex_schema =
  match parse_json input with
  | None -> None
  | Some v -> decode_schema base v
