FSTAR ?= fstar.exe
KRML ?= krml
KRML_HOME ?= /tmp/karamel

MODULES = RDF.Graph.Executable SPARQL11.Algebra

.PHONY: verify clean extract-c

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

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
	rm -f *.verified
	rm -rf c-output
