FSTAR ?= fstar.exe

MODULES = RDF.Graph.Executable SPARQL11.Algebra

.PHONY: verify clean

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

clean:
	rm -f *.verified
