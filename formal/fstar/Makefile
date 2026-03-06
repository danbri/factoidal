FSTAR ?= fstar.exe
KRML ?= krml
KRML_HOME ?= /tmp/karamel

MODULES = RDF.Graph.Executable SPARQL11.Algebra

.PHONY: verify clean extract-c

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

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
