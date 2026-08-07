#!/bin/bash
# Issue #347 -- ordering axioms for FStar.String.compare.
#
# This stub is DOCUMENTATION-ONLY: no OCaml patch is applied. The
# three assumed lemmas in formal/fstar/RDF.Indexed.StringOrder.fsti
# (zero-iff-equal, antisymmetry, transitivity) erase at extraction --
# there is nothing to realise. What is trusted is a PROPERTY of the
# existing realisation: FStar.String.compare extracts to OCaml
# BatString.compare (ulib/ml/FStar_String.ml), byte-lexicographic
# comparison, which satisfies all three laws.
#
# The gap is that ulib states no specification for `compare`, so the
# laws must be assumed on our side. Proper fix is upstream: a
# specification for String.compare in ulib (which already carries
# interface axioms like concat_injective in the same style). Close
# this stub and #347 together when either (a) upstream ulib gains the
# spec, or (b) the bucket trees move to a verified comparator
# (measured perf decision -- see #347 option 3).
#
# Consumers: RDF.Indexed.KeyInjectivity / OWL.Semantics.MemLemmas
# (bucket_lookup completeness, coverage gap 2 -> rho-df completeness,
# gap 1).
exit 0
