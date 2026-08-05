# Factoidal F* verification Makefile.
#
# `make verify` type-checks EVERY .fst in this directory against z3 4.13.3.
#
# HISTORY — why this file changed (issue #319)
# --------------------------------------------
# Until 2026-07-29 the `verify` target named six modules by hand
# (RDF.Graph.Executable, SPARQL.FullText, SPARQL11.Algebra, Tableau,
# SPARQL.ServiceDescription, SPARQL.GraphStore) while README.md said the
# command "type-checks all F* modules against the SMT solver". A developer
# following the README got a green result having checked about 3% of the
# tree. The target now derives its module list from `$(wildcard *.fst)`, so
# it cannot drift from the corpus again: adding a .fst file adds it to
# `make verify` with no edit here.
#
# It also passes --cache_checked_modules, so the .checked files it writes
# are the same ones ./build-ocaml.sh consumes. Before this change a
# `make verify` run did work the next extract could not reuse, and vice
# versa (proposal P7 in skills/fast-verify-extract/SKILL.md).
#
# The real dependency DAG comes from `fstar.exe --dep full`, regenerated
# into .depend whenever any source changes. That gives make correct
# ordering, so `make -j$(nproc) verify` is safe: make guarantees one
# writer per .checked target and orders writers after their prerequisites
# (concurrency-safety rule 4 in skills/fast-verify-extract/SKILL.md — ad-hoc
# backgrounded fstar.exe fan-out gives neither guarantee and is what
# corrupted the cache on 2026-05-07).
#
# COST. A cold `make verify` re-proves the whole corpus and takes hours;
# see docs/clean-room/ for a measured figure. A warm run over an unchanged
# tree is seconds — every module's .checked is digest-valid and make skips
# it. Use `make verify-smoke` for a fast sanity check of the core modules,
# or `make verify-RDF.Canonical` for one module.

FSTAR_EXE ?= fstar.exe
FSTAR ?= $(FSTAR_EXE) --z3version 4.13.3 --cache_checked_modules
KRML ?= krml
KRML_HOME ?= /tmp/karamel
ROARING_DIR = ../roaring/src

# The corpus. Derived, never hand-maintained — see the header.
ALL_FST  := $(sort $(wildcard *.fst))
ALL_FSTI := $(sort $(wildcard *.fsti))
ALL_CHECKED := $(addsuffix .checked, $(ALL_FST))

# The six modules the old hand-written MODULES list named. Retained as a
# fast smoke target, NOT as the meaning of "verify".
SMOKE_MODULES = RDF.Graph.Executable SPARQL.FullText SPARQL11.Algebra Tableau SPARQL.ServiceDescription SPARQL.GraphStore

DEPEND_FILE = .depend

.PHONY: verify verify-smoke verify-rdf-mt verify-roaring verify-all verify-list clean extract-c depend
.DEFAULT_GOAL := verify

# Whole-corpus verification. This is what README.md describes.
verify: $(ALL_CHECKED)
	@echo "make verify: $(words $(ALL_CHECKED)) F* modules type-checked under z3 4.13.3 (no --lax)."

# Fast core-module sanity check — the pre-#319 behaviour of `make verify`,
# under a name that does not claim whole-corpus coverage.
verify-smoke: $(addsuffix .fst.checked, $(SMOKE_MODULES))
	@echo "make verify-smoke: $(words $(SMOKE_MODULES)) core modules type-checked. This is NOT whole-corpus coverage — run 'make verify' for that."

# Single module: make verify-RDF.Canonical
verify-%: %.fst.checked
	@echo "make verify-$*: verified."

# The model-theoretic verification layer, gated by name (adopted from
# docs/semantics_proposal.md — see the adoption assessment in
# docs/designissues/2026-08-05-semantics-proposal-adoption.md).
# Interpretations, satisfaction, entailment, rule soundness, licensing,
# and the index lemmas they stand on.
RDF_MT_MODULES = \
  RDF.Entailment.Simple.Spec RDF.Entailment.Simple \
  RDF.Entailment.Simple.ModelTheory RDF.Entailment.Simple.Refinement \
  RDF.Entailment.Simple.Boundary \
  RDF.Entailment.RDF.Spec \
  RDF.Entailment.RDFS.Spec RDF.Entailment.RDFS.ModelTheory \
  RDF.Entailment.RDFS.Refinement RDF.Entailment.RDFS.SepFree \
  RDF.Entailment.RDFS.ChainWf \
  RDF.Entailment.RDFS.FixedPoint \
  RDF.Entailment.Regime \
  RDF.Semantics.HypothesisWitness \
  RDF.Indexed.KeyInjectivity \
  OWL.Semantics OWL.Semantics.MemLemmas OWL.Semantics.Soundness \
  OWL.RL.Refinement

verify-rdf-mt: $(addsuffix .fst.checked, $(RDF_MT_MODULES))
	@echo "make verify-rdf-mt: $(words $(RDF_MT_MODULES)) model-theoretic-layer modules type-checked under z3 4.13.3 (no --lax)."

# What the corpus currently is, for anyone auditing coverage claims.
verify-list:
	@echo "$(words $(ALL_FST)) .fst + $(words $(ALL_FSTI)) .fsti in $(CURDIR):"
	@printf '  %s\n' $(ALL_FST)

# Top-level integration hook for the formal/roaring/ tree.
# Verifies Spec, Bits, Container.{Array,Bitmap,Run}, IODemo, Test
# under z3 4.13.3. Uses the Roaring-side Makefile so any future
# modules added there are picked up without editing this file.
verify-roaring:
	$(MAKE) -C $(ROARING_DIR) verify

# Verify the main F* core AND the Roaring tree.
verify-all: verify verify-roaring

# ---------------------------------------------------------------------------
# Dependency graph.
#
# `--dep full` emits make rules for the whole transitive closure, including
# the F* standard library's own .checked files under the opam ulib.checked
# directory. Those are pre-checked and ship with the toolchain; letting make
# see rules for them risks it trying to rewrite files inside the opam switch.
# The filter therefore keeps only rules whose TARGET is a local .checked, and
# strips every prerequisite containing a path separator (all of which are
# ulib). Continuation lines are joined first so the filter sees whole rules.
# ---------------------------------------------------------------------------
depend: $(DEPEND_FILE)

$(DEPEND_FILE): $(ALL_FST) $(ALL_FSTI)
	@echo "  regenerating $(DEPEND_FILE) from fstar.exe --dep full ($(words $(ALL_FST)) modules)..."
	@$(FSTAR) --dep full $(ALL_FST) 2>/dev/null \
	  | awk 'BEGIN{buf=""} { buf = buf $$0; if (buf ~ /\\$$/) { sub(/\\$$/," ",buf); next } print buf; buf="" }' \
	  | grep -E '^[A-Za-z][^:/]*\.fsti?\.checked:' \
	  | sed -E 's#[^ :]*/[^ ]*##g' \
	  > $@.tmp
	@test -s $@.tmp || { echo "ERROR: --dep full produced no local rules; refusing to write an empty $(DEPEND_FILE)" >&2; rm -f $@.tmp; exit 1; }
	@mv $@.tmp $@

# `-include` so a missing .depend triggers the rule above and make restarts
# with real dependency ordering rather than verifying in arbitrary order.
-include $(DEPEND_FILE)

# ---------------------------------------------------------------------------
# The verification rule. F* writes <module>.checked itself when
# --cache_checked_modules is passed AND every dependency already has a valid
# .checked; the .depend ordering above is what guarantees the latter. If the
# file is still absent afterwards, F* emitted Warning 247 and silently
# declined to cache — fail loudly rather than let make loop or report green.
# ---------------------------------------------------------------------------
%.fst.checked: %.fst
	$(FSTAR) $<
	@test -f $@ || { echo "ERROR: $(FSTAR_EXE) did not write $@ (F* Warning 247: a dependency lacks a valid .checked). Run 'make depend' and retry." >&2; exit 1; }

%.fsti.checked: %.fsti
	$(FSTAR) $<
	@test -f $@ || { echo "ERROR: $(FSTAR_EXE) did not write $@ (F* Warning 247: a dependency lacks a valid .checked). Run 'make depend' and retry." >&2; exit 1; }

# Extract verified C from RDF module via KaRaMeL.
#
# Suppressed warnings (see c-output/README.md for details):
#   -9:  Static initializers needed (empty_graph global)
#   -11: Closures/lambdas not in Low* (translated to function pointers)
#   -15: GC types, math integers — extracted C leaks memory without GC
#
# These warnings reflect that the F* source is high-level, not Low*.
# The extracted C is logically correct but not standalone.
# Fix: create RDF.Graph.Impl.fst in Low* subset (Phase 1 of extraction roadmap).
extract-c: c-output/RDF_Graph_Executable.c

c-output/RDF_Graph_Executable.c: RDF.Graph.Executable.fst
	@mkdir -p c-output
	KRML_HOME=$(KRML_HOME) $(KRML) -skip-compilation \
		-warn-error -9-11-15 \
		-add-include '"krml/internal/compat.h"' \
		-tmpdir c-output \
		$<

clean:
	rm -f *.verified $(DEPEND_FILE)
	rm -rf c-output
