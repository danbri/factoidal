FSTAR ?= fstar.exe
KRML ?= krml
KRML_HOME ?= /tmp/karamel
ROARING_DIR = ../roaring/src

MODULES = RDF.Graph.Executable SPARQL11.Algebra Tableau SPARQL.ServiceDescription SPARQL.GraphStore

.PHONY: verify verify-roaring verify-all clean extract-c

verify: $(addsuffix .verified, $(MODULES))

# Top-level integration hook for the formal/roaring/ tree.
# Verifies Spec, Bits, Container.{Array,Bitmap,Run}, IODemo, Test
# under z3 4.13.3. Uses the Roaring-side Makefile so any future
# modules added there are picked up without editing this file.
verify-roaring:
	$(MAKE) -C $(ROARING_DIR) verify

# Verify the main F* core AND the Roaring tree.
verify-all: verify verify-roaring

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
