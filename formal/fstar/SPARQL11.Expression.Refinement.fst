module SPARQL11.Expression.Refinement

(** ======================================================================== **)
(** G4/M2 -- per-operator semantic lemmas for the SPARQL expression          **)
(** evaluator, `eval_expr_with_base` (SPARQL11.Algebra.fst Part 8, the       **)
(** block relocated during de-vacuation).                                    **)
(**                                                                          **)
(** WHY A NEW MODULE, NOT MORE OF SPARQL11.Algebra.Refinement.fst.           **)
(** That file's Parts 5/6/8/9/12/13 already reason about `E_And`/`E_Not`/    **)
(** filters, but ONLY through the two `irreducible` wrappers                 **)
(** `eval_expr_ebv` / `eval_expr_fwd` treated as UNINTERPRETED (see its      **)
(** own banner: "without any assumption about ... mapping"). Nothing in      **)
(** that file, or anywhere else in the tree (checked by grep before this     **)
(** module was written), states what any single operator of                  **)
(** `eval_expr_with_base` actually COMPUTES against the W3C text. That is    **)
(** this module's job: one operator = one independent spec transcription +   **)
(** one lemma tying the engine's arm to it, the recipe that carried 40+ OWL  **)
(** rules (skills/proof-factory/SKILL.md).                                   **)
(**                                                                          **)
(** IRREDUCIBLE WRAPPERS. `eval_expr_ebv`/`eval_expr_fwd` are marked         **)
(** `irreducible` (SPARQL11.Algebra.fst ~4469-4475) so proofs here go        **)
(** directly against `eval_expr_with_base` + `ebv`, which are NOT            **)
(** irreducible and unfold normally. The two wrappers are used only where a  **)
(** lemma explicitly needs to state something about THEM, via their          **)
(** definitional equation (`eval_expr_ebv base e mu == ebv (eval_expr_with_  **)
(** base base e mu)`), never by unfolding through them implicitly.           **)
(**                                                                          **)
(** WAVE 1 SCOPE (this commit) -- SPARQL 1.1 sections 17.2.2 (EBV), 17.3     **)
(** (logical connectives, error-tolerant And/Or/Not), and the value-         **)
(** comparison path of 17.3's op:numeric-equal / op:equal for SAME-KIND      **)
(** numeric and plain-string classes only:                                   **)
(**   Part 1 -- `ebv_spec`, an independent transcription of the EBV operand- **)
(**             mapping table (17.2.2), and its agreement/divergence         **)
(**             lemmas against the engine's `ebv` (Algebra.fst:878).         **)
(**   Part 2 -- `spec_and`/`spec_or`/`spec_not`, the error-tolerant truth    **)
(**             tables (17.3: And -- false dominates error; Or -- true       **)
(**             dominates error; Not propagates error), and their            **)
(**             agreement/divergence lemmas against the `E_And`/`E_Or`/      **)
(**             `E_Not` arms of `eval_expr_with_base`.                       **)
(**   Part 3 -- `eq_spec_num`/`eq_spec_plain_string`, independent value-      **)
(**             equality specs for two ER_Num operands and two un-language-  **)
(**             tagged xsd:string literals, and their agreement lemmas       **)
(**             against `value_compare`'s `CmpEq`/`CmpNe` arms. Two small    **)
(**             clean-agreement lemmas for the datatype-mismatch and         **)
(**             differing-language-tag edge cases close out the wave.        **)
(**                                                                          **)
(** WHAT REMAINS (future waves, per the G4/M2 brief -- do not read absence   **)
(** here as "not planned"):                                                  **)
(**   - `E_Compare` orderings (CmpLt/CmpGt/CmpLe/CmpGe) and the general      **)
(**     RDFterm-equal relation over IRIs/triple-terms -- tracked against     **)
(**     SR-4 #362 in SPARQL11.Algebra.Refinement.fst.                        **)
(**   - Cross-kind numeric equality (ER_Num vs ER_Dec vs ER_Dbl) and         **)
(**     general (non-reflexive) ER_Dec/ER_Dbl value equality: both need an   **)
(**     independent spec for `parse_to_scaled`/`parse_double_to_scaled`'s    **)
(**     scaled-value semantics, which is arithmetic-promotion work, not      **)
(**     expression-operator work.                                            **)
(**   - String/date builtin functions (STR, SUBSTR, date extraction, etc.)   **)
(**     and XSD casts (`eval_xsd_cast`).                                     **)
(**                                                                          **)
(** EXTRACTION. This module is PROOF-ONLY -- like `RDF.Indexed.StringOrder`  **)
(** (the precedent this wave follows), it states lemmas about already-       **)
(** shipping functions and defines no new executable logic the engine        **)
(** calls. It needs no `build-ocaml.sh` module-list entry and no OCaml       **)
(** extraction wiring.                                                       **)
(** ======================================================================== **)

open FStar.String
open RDF.Term
open RDF.Graph.Executable
open SPARQL11.Algebra

module SO = RDF.Indexed.StringOrder

(** ======================================================================== **)
(** Part 1: Effective Boolean Value -- SPARQL 1.1 section 17.2.2             **)
(**                                                                          **)
(** Spec text (operand mapping table, quoted):                               **)
(**   "Boolean: value of the boolean"                                        **)
(**   "String: (with no language tag) zero-length -> false, else true"       **)
(**   "Numeric: (0/0.0/NaN) -> false, else true"                             **)
(**   "Any other argument -> Type Error"                                     **)
(**                                                                          **)
(** `ebv_spec` below is written from that table directly -- it names its own **)
(** cases and consults the shared xsd:*/is_numeric_datatype vocabulary       **)
(** constants (not the engine's `ebv` match arms) -- and returns `option     **)
(** bool`, `None` standing for the table's "Type Error" row. It intentionally**)
(** does NOT special-case rdf:langString (the table's "String" row is        **)
(** un-language-tagged only), which is exactly where it diverges from the    **)
(** shipping `ebv` -- see the FINDING below.                                 **)
(** ======================================================================== **)

let ebv_spec (v : eval_result) : option bool =
  match v with
  | ER_Bool b -> Some b
  | ER_Num n  -> Some (n <> 0)
  | ER_Dec s  -> Some (s <> "0" && s <> "0.0" && s <> "")
  | ER_Dbl s  -> Some (s <> "0" && s <> "0.0" && s <> "NaN" && s <> "")
  | ER_Term (T_Literal l) ->
    if l.datatype = xsd_boolean then Some (l.lexical_form = "true" || l.lexical_form = "1")
    else if l.datatype = xsd_string then Some (String.length l.lexical_form > 0)
    else if is_numeric_datatype l.datatype
    then Some (l.lexical_form <> "0" && l.lexical_form <> "0.0" && l.lexical_form <> "")
    else None                    // includes rdf:langString / rdf:dirLangString / any other datatype
  | ER_Term (T_IRI _)         -> None    // "any other argument" -> Type Error
  | ER_Term (T_BNode _)       -> None
  | ER_Term (T_TripleTerm _ _ _) -> None
  | ER_Error                  -> None

/// AGREEMENT (the common case): wherever the transcribed table produces a
/// determinate answer, the shipping `ebv` computes the same boolean.
let lemma_ebv_matches_spec_some (v : eval_result) (b : bool)
  : Lemma (requires ebv_spec v == Some b)
          (ensures ebv v == b)
  = match v with
    | ER_Bool _ | ER_Num _ | ER_Dec _ | ER_Dbl _ -> ()
    | ER_Term (T_Literal _) -> ()
    | _ -> ()

/// Classifier mirroring `ebv_spec`'s None arms MINUS the rdf:langString case
/// -- used only to state the "type errors fold to false" agreement below
/// precisely (the langString slice is excluded because it is where the
/// engine and the spec table actually disagree; see the FINDING).
let is_type_error_nonlangstring (v : eval_result) : bool =
  match v with
  | ER_Term (T_IRI _) | ER_Term (T_BNode _) | ER_Term (T_TripleTerm _ _ _) -> true
  | ER_Term (T_Literal l) ->
    l.datatype <> xsd_boolean && l.datatype <> xsd_string &&
    l.datatype <> rdf_lang_string && not (is_numeric_datatype l.datatype)
  | ER_Error -> true
  | _ -> false

/// AGREEMENT (the "harmless divergence" case): outside rdf:langString, every
/// Type-Error class the table identifies is a class the engine folds to
/// `false` -- the engine never raises the error, but it also never claims
/// `true`, so the FILTER-level observable behaviour coincides even though
/// the error itself is silently dropped (see Part 2 for where dropping the
/// error, rather than just its value, becomes observable).
let lemma_ebv_typeerror_folds_false (v : eval_result)
  : Lemma (requires ebv_spec v == None /\ is_type_error_nonlangstring v)
          (ensures ebv v == false)
  = match v with
    | ER_Term (T_IRI _) | ER_Term (T_BNode _) | ER_Term (T_TripleTerm _ _ _) -> ()
    | ER_Term (T_Literal _) -> ()
    | ER_Error -> ()
    | _ -> ()

/// FINDING (EBV-1). The shipping `ebv` treats non-empty rdf:langString
/// literals as SPARQL "string" for EBV purposes (Algebra.fst:889-890),
/// returning `true`/`false` by lexical length exactly as it does for
/// xsd:string. SPARQL 1.1 section 17.2.2's operand-mapping table lists only
/// xsd:boolean, the numeric types, and xsd:string -- a language-tagged
/// literal is "any other argument", i.e. a Type Error, under the table's
/// text. This is a genuine, deliberate extension beyond the strict table
/// (every SPARQL implementation the project has checked treats plain
/// language-tagged literals as truthy-by-length in practice, so this is not
/// flagged as a bug -- but it IS a documented divergence from the letter of
/// 17.2.2, witnessed concretely here rather than asserted).
let lemma_ebv_langstring_finding (s : string) (lang : string)
  : Lemma (requires String.length s > 0)
          (ensures (let l : wf_literal =
                      { lexical_form = s; datatype = rdf_lang_string;
                        lang_tag = Some lang; direction = None } in
                    ebv_spec (ER_Term (T_Literal l)) == None /\      // spec: Type Error
                    ebv (ER_Term (T_Literal l)) == true))            // engine: true (non-empty)
  = ()

(** ======================================================================== **)
(** Part 2: Logical connectives -- SPARQL 1.1 section 17.3, error-tolerant   **)
(** And/Or/Not.                                                              **)
(**                                                                          **)
(** Spec text (section 17.3, "Testing Values", the A-tabular definition):     **)
(**   logical-or(A, B):  A=true -> true;  B=true -> true;                    **)
(**                      A=error,B=error -> error; A=error,B=false -> error; **)
(**                      A=false,B=error -> error; A=false,B=false -> false  **)
(**   logical-and(A, B): A=false -> false; B=false -> false;                 **)
(**                      A=error,B=error -> error; A=error,B=true -> error;  **)
(**                      A=true,B=error -> error; A=true,B=true -> true      **)
(**   fn:not(A): propagates a Type Error argument as a Type Error result.    **)
(**                                                                          **)
(** `spec_and`/`spec_or`/`spec_not` below operate on the same `option bool`  **)
(** shape as `ebv_spec` (`None` = error) and transcribe exactly that table.  **)
(** ======================================================================== **)

let spec_and (a b : option bool) : option bool =
  match a, b with
  | Some false, _ -> Some false
  | _, Some false -> Some false
  | Some true, Some true -> Some true
  | _, _ -> None

let spec_or (a b : option bool) : option bool =
  match a, b with
  | Some true, _ -> Some true
  | _, Some true -> Some true
  | Some false, Some false -> Some false
  | _, _ -> None

let spec_not (a : option bool) : option bool =
  match a with
  | Some b -> Some (not b)
  | None -> None

/// AGREEMENT: whenever both operands' EBVs (per `ebv_spec`) let the table
/// reach a determinate verdict, the engine's boolean-algebra implementation
/// (`ebv v1 && ebv v2`) computes the same value. This covers BOTH dominance
/// rows (one operand false/true) AND the both-determinate row.
let lemma_and_matches_spec_when_no_error (v1 v2 : eval_result) (b : bool)
  : Lemma (requires spec_and (ebv_spec v1) (ebv_spec v2) == Some b)
          (ensures (ebv v1 && ebv v2) == b)
  = match ebv_spec v1, ebv_spec v2 with
    | Some false, _ -> lemma_ebv_matches_spec_some v1 false
    | _, Some false -> lemma_ebv_matches_spec_some v2 false
    | Some true, Some true ->
      lemma_ebv_matches_spec_some v1 true; lemma_ebv_matches_spec_some v2 true
    | _, _ -> ()

let lemma_or_matches_spec_when_no_error (v1 v2 : eval_result) (b : bool)
  : Lemma (requires spec_or (ebv_spec v1) (ebv_spec v2) == Some b)
          (ensures (ebv v1 || ebv v2) == b)
  = match ebv_spec v1, ebv_spec v2 with
    | Some true, _ -> lemma_ebv_matches_spec_some v1 true
    | _, Some true -> lemma_ebv_matches_spec_some v2 true
    | Some false, Some false ->
      lemma_ebv_matches_spec_some v1 false; lemma_ebv_matches_spec_some v2 false
    | _, _ -> ()

let lemma_not_matches_spec_when_no_error (v1 : eval_result) (b : bool)
  : Lemma (requires spec_not (ebv_spec v1) == Some b)
          (ensures (not (ebv v1)) == b)
  = match ebv_spec v1 with
    | Some b1 -> lemma_ebv_matches_spec_some v1 b1
    | None -> ()

/// Expr-level corollaries, tying the abstract-value lemmas above to the
/// actual `E_And`/`E_Or`/`E_Not` arms of `eval_expr_with_base`
/// (SPARQL11.Algebra.fst ~3983-3985). `eval_expr_with_base` is a plain
/// `let rec` (not irreducible), so the equation for a concrete constructor
/// (`E_And e1 e2`, etc.) unfolds under SMT normalization with no extra hint.
let lemma_eval_and_matches_spec
    (base : option wf_iri) (e1 e2 : expr) (mu : solution_mapping) (b : bool)
  : Lemma (requires spec_and (ebv_spec (eval_expr_with_base base e1 mu))
                             (ebv_spec (eval_expr_with_base base e2 mu)) == Some b)
          (ensures eval_expr_with_base base (E_And e1 e2) mu == ER_Bool b)
  = lemma_and_matches_spec_when_no_error
      (eval_expr_with_base base e1 mu) (eval_expr_with_base base e2 mu) b

let lemma_eval_or_matches_spec
    (base : option wf_iri) (e1 e2 : expr) (mu : solution_mapping) (b : bool)
  : Lemma (requires spec_or (ebv_spec (eval_expr_with_base base e1 mu))
                            (ebv_spec (eval_expr_with_base base e2 mu)) == Some b)
          (ensures eval_expr_with_base base (E_Or e1 e2) mu == ER_Bool b)
  = lemma_or_matches_spec_when_no_error
      (eval_expr_with_base base e1 mu) (eval_expr_with_base base e2 mu) b

let lemma_eval_not_matches_spec
    (base : option wf_iri) (e1 : expr) (mu : solution_mapping) (b : bool)
  : Lemma (requires spec_not (ebv_spec (eval_expr_with_base base e1 mu)) == Some b)
          (ensures eval_expr_with_base base (E_Not e1) mu == ER_Bool b)
  = lemma_not_matches_spec_when_no_error (eval_expr_with_base base e1 mu) b

/// FINDING (LOGIC-1, E_And). The table says True AND Error = Error (error
/// propagates once the dominant "false" row is off the table). The shipping
/// `E_And` arm can NEVER produce an error -- `ebv` always returns a plain
/// `bool` (Part 1), so `ER_Bool (ebv v1 && ebv v2)` always returns a
/// definite `ER_Bool`, silently turning "should be Error" into a concrete
/// `false`. Witnessed concretely at the `eval_expr_with_base` level: for any
/// base/mu, `E_And (E_BoolLit true) (E_IRI i)` -- whose second operand is a
/// bare IRI, a Type-Error EBV class -- evaluates to `ER_Bool false`, not to
/// any representation of an error.
let lemma_eval_and_true_error_diverges_finding
    (base : option wf_iri) (i : wf_iri) (mu : solution_mapping)
  : Lemma (ebv_spec (eval_expr_with_base base (E_IRI i) mu) == None /\           // spec: Type Error
           spec_and (Some true) (ebv_spec (eval_expr_with_base base (E_IRI i) mu)) == None /\  // spec: True AND Error = Error
           eval_expr_with_base base (E_And (E_BoolLit true) (E_IRI i)) mu == ER_Bool false)      // engine: a definite False
  = ()

/// FINDING (LOGIC-1, E_Or). Symmetric divergence: the table says False OR
/// Error = Error, but `E_Or (E_BoolLit false) (E_IRI i)` evaluates to
/// `ER_Bool false`, again a definite (wrong) answer rather than an error.
let lemma_eval_or_false_error_diverges_finding
    (base : option wf_iri) (i : wf_iri) (mu : solution_mapping)
  : Lemma (ebv_spec (eval_expr_with_base base (E_IRI i) mu) == None /\
           spec_or (Some false) (ebv_spec (eval_expr_with_base base (E_IRI i) mu)) == None /\   // spec: False OR Error = Error
           eval_expr_with_base base (E_Or (E_BoolLit false) (E_IRI i)) mu == ER_Bool false)       // engine: a definite False
  = ()

/// FINDING (LOGIC-1, E_Not). `fn:not` propagates a Type-Error argument as a
/// Type-Error result. `E_Not (E_IRI i)` instead evaluates to `ER_Bool true`
/// (`not false`, `ebv` having folded the IRI's error to `false` per Part 1).
let lemma_eval_not_error_diverges_finding
    (base : option wf_iri) (i : wf_iri) (mu : solution_mapping)
  : Lemma (ebv_spec (eval_expr_with_base base (E_IRI i) mu) == None /\
           spec_not (ebv_spec (eval_expr_with_base base (E_IRI i) mu)) == None /\   // spec: Not(Error) = Error
           eval_expr_with_base base (E_Not (E_IRI i)) mu == ER_Bool true)            // engine: a definite True
  = ()

(** ======================================================================== **)
(** Part 3: E_Eq / E_Neq on the value-comparison path (`value_compare`,      **)
(** SPARQL11.Algebra.fst:2371) -- SAME-KIND numeric (`ER_Num`/`ER_Num`) and  **)
(** plain-string (un-language-tagged xsd:string) classes only, per wave      **)
(** scope. `value_compare` itself already treats all nine ER_Num/ER_Dec/     **)
(** ER_Dbl pairings uniformly via `numeric_compare` -- the "same-kind"       **)
(** restriction is about what THIS WAVE states a spec for, not about a       **)
(** different engine code path.                                              **)
(** ======================================================================== **)

/// op:numeric-equal on two xsd:integer-denoting operands: mathematical
/// integer equality -- transcribed directly, independent of `numeric_compare`.
let eq_spec_num (a b : int) : bool = (a = b)

/// op:equal (RDFterm-equal, "graph equivalence" leaf case) on two plain
/// (un-language-tagged) xsd:string literals: identical codepoint sequence.
let eq_spec_plain_string (l1 l2 : wf_literal) : bool = (l1.lexical_form = l2.lexical_form)

let lemma_eq_num_matches_spec (a b : int)
  : Lemma (value_compare (ER_Num a) (ER_Num b) CmpEq == Some (eq_spec_num a b) /\
           value_compare (ER_Num a) (ER_Num b) CmpNe == Some (not (eq_spec_num a b)))
  = ()

let lemma_eq_plain_string_matches_spec (l1 l2 : wf_literal)
  : Lemma (requires l1.datatype == xsd_string /\ l2.datatype == xsd_string /\
                     l1.lang_tag == None /\ l2.lang_tag == None)
          (ensures value_compare (ER_Term (T_Literal l1)) (ER_Term (T_Literal l2)) CmpEq
                     == Some (eq_spec_plain_string l1 l2) /\
                   value_compare (ER_Term (T_Literal l1)) (ER_Term (T_Literal l2)) CmpNe
                     == Some (not (eq_spec_plain_string l1 l2)))
  = SO.string_compare_zero_iff_eq l1.lexical_form l2.lexical_form

/// Reflexive same-kind decimal/double equality: the ONLY Dec/Dbl slice this
/// wave proves. General cross-lexical value equality ("1.0" = "1.00") needs
/// an independent spec for `parse_to_scaled`/`parse_double_to_scaled`'s
/// scaled-value semantics -- deferred (see module banner, "what remains").
/// These two lemmas need no such spec: `parse_to_scaled`/`parse_double_to_
/// scaled` are `Tot` functions of the lexical string, so calling either
/// twice on the SAME string trivially returns the same result by
/// referential transparency -- no knowledge of what the parse computes is
/// needed, only that it is a deterministic total function.
let lemma_eq_dec_reflexive (s : string)
  : Lemma (requires Some? (parse_to_scaled s))
          (ensures value_compare (ER_Dec s) (ER_Dec s) CmpEq == Some true)
  = ()

let lemma_eq_dbl_reflexive (s : string)
  : Lemma (requires Some? (parse_double_to_scaled s))
          (ensures value_compare (ER_Dbl s) (ER_Dbl s) CmpEq == Some true)
  = ()

/// AGREEMENT (documented, not surprising): two literals of DIFFERENT
/// datatypes compare as a Type Error under `=`/`!=` unless both are
/// numeric (that combination never reaches this branch of `value_compare`
/// at all -- ER_Num/ER_Dec/ER_Dbl are separate `eval_result` constructors
/// from `ER_Term (T_Literal _)`). Matches the operand-mapping table's
/// general rule that `=` over differently-typed non-numeric literals is a
/// Type Error, not a `false`.
let lemma_eq_literal_different_datatype_typeerror (l1 l2 : wf_literal)
  : Lemma (requires l1.datatype <> l2.datatype)
          (ensures value_compare (ER_Term (T_Literal l1)) (ER_Term (T_Literal l2)) CmpEq == None)
  = ()

/// AGREEMENT (documented, not surprising): two literals of the SAME
/// datatype but DIFFERENT language tags are unequal (not a Type Error) --
/// RDF term identity already distinguishes them by tag, so `=` reports a
/// definite `false` rather than refusing to compare.
let lemma_eq_literal_same_datatype_diff_lang (l1 l2 : wf_literal)
  : Lemma (requires l1.datatype == l2.datatype /\ l1.lang_tag <> l2.lang_tag)
          (ensures value_compare (ER_Term (T_Literal l1)) (ER_Term (T_Literal l2)) CmpEq == Some false /\
                   value_compare (ER_Term (T_Literal l1)) (ER_Term (T_Literal l2)) CmpNe == Some true)
  = ()

/// Expr-level corollary for E_Compare/CmpEq over two `ER_Num`-denoting
/// subexpressions, tying Part 3 to `eval_expr_with_base`'s `E_Compare` arm
/// (SPARQL11.Algebra.fst:3977-3980).
let lemma_eval_eq_num_matches_spec
    (base : option wf_iri) (e1 e2 : expr) (mu : solution_mapping) (a b : int)
  : Lemma (requires eval_expr_with_base base e1 mu == ER_Num a /\
                     eval_expr_with_base base e2 mu == ER_Num b)
          (ensures eval_expr_with_base base (E_Compare CmpEq e1 e2) mu == ER_Bool (eq_spec_num a b))
  = lemma_eq_num_matches_spec a b
