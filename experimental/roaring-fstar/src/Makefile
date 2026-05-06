# Roaring F* — Phase A standalone verification.
#
# Wires up just the Phase A modules (Spec, Container.Array, Test).
# Not yet integrated with formal/fstar/Makefile; that's Phase I.
#
# Usage:
#   eval $(opam env --switch=fstar)
#   make verify
#   make clean

FSTAR ?= fstar.exe

# Order matters: dependencies first.
MODULES = \
	Spec \
	Container.Array \
	Test

.PHONY: verify clean

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

clean:
	rm -f *.verified *.checked *.checked.lax
