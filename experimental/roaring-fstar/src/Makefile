# Roaring F* — Phase A standalone verification + extraction + demo.
#
# Wires up just the Phase A modules (Spec, Container.Array, Test).
# Not yet integrated with formal/fstar/Makefile; that's Phase I.
#
# Usage:
#   eval $(opam env --switch=fstar)
#   make verify         # F* type-check + SMT discharge
#   make extract        # extract verified F* to OCaml
#   make demo           # build native demo binary
#   make run            # run the demo
#   make clean

FSTAR ?= fstar.exe
OCAMLFIND ?= ocamlfind

# Order matters: dependencies first.
MODULES = \
	Spec \
	Container.Array \
	Bits \
	IODemo \
	Test

EXTRACT_MODULES = Spec Container.Array Bits IODemo

.PHONY: verify extract demo run clean

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

# Extract the data-structure modules to OCaml. (Test.fst is verification-
# only; not part of runtime.)
extract: Spec.ml Container_Array.ml Bits.ml IODemo.ml

Spec.ml Container_Array.ml Bits.ml IODemo.ml: Spec.fst Container.Array.fst Bits.fst IODemo.fst
	$(FSTAR) --codegen OCaml --extract '* -FStar' Spec.fst Container.Array.fst Bits.fst IODemo.fst

# Native demo binary linking the extracted code with demo.ml.
demo: extract demo.ml
	$(OCAMLFIND) ocamlopt -package fstar.lib,zarith -linkpkg \
		Spec.ml Container_Array.ml Bits.ml IODemo.ml demo.ml -o demo

run: demo
	./demo

clean:
	rm -f *.verified *.checked *.checked.lax *.cmi *.cmo *.cmx *.o
	rm -f Spec.ml Container_Array.ml Bits.ml IODemo.ml Test.ml demo
