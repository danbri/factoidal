module RDF.Indexed.StringOrder

/// Ordering axioms for `FStar.String.compare` -- acknowledged GAP
/// under iron rule #3(a), tracked by GitHub issue #347, stub entry
/// `minimal_regrettable_glue_code_each_with_an_open_issue/
/// 347_string_compare_ordering_axioms.sh`.
///
/// WHY THIS EXISTS. ulib declares `val compare: string -> string ->
/// Tot int` (FStar.String.fsti line 80) with NO specification and no
/// F* definition -- it is a native primitive, extracted to OCaml
/// `BatString.compare` (ulib/ml/FStar_String.ml line 18), which is
/// byte-lexicographic comparison: a genuine total order. The bucket
/// trees in RDF.Indexed.fsti binary-search by `String.compare`, but
/// build by positional list splits; linking the two (the
/// `bucket_lookup_complete` direction, coverage gap 2, which the
/// rho-df completeness theorem needs) requires exactly the order
/// laws below, and F* cannot prove ANY fact about an unspecified
/// val. Empirically confirmed 2026-08-05: transitivity with no help
/// fails with "Error 19: Could not prove post-condition".
///
/// TRUST SURFACE. Exactly three facts, all true of byte-lexicographic
/// comparison. These belong upstream in ulib (which already states
/// interface axioms such as `concat_injective` in the same
/// proof-free style); until then they live here, in one module, so
/// the assumption is one named place and not scattered.
///
/// DO NOT WIDEN. Add no further axioms here without reopening #347.
/// Anything derivable from these three (totality of the order,
/// irreflexivity of <, sortedness transfer) must be PROVED in a
/// consumer module, not assumed.

/// compare returns zero exactly on equal strings.
val string_compare_zero_iff_eq (a b : string)
  : Lemma (FStar.String.compare a b = 0 <==> a == b)

/// Comparison is antisymmetric in the comparator sense: a before b
/// exactly when b after a.
val string_compare_antisym (a b : string)
  : Lemma (FStar.String.compare a b < 0 <==> FStar.String.compare b a > 0)

/// Strict comparison is transitive.
val string_compare_trans (a b c : string)
  : Lemma (requires FStar.String.compare a b < 0 /\
                    FStar.String.compare b c < 0)
          (ensures  FStar.String.compare a c < 0)
