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

FSTAR ?= fstar.exe --z3version 4.13.3
OCAMLFIND ?= ocamlfind

# Order matters: dependencies first.
MODULES = \
	Spec \
	Bits \
	Container.Array \
	Container.Bitmap \
	IODemo \
	Test

EXTRACT_MODULES = Spec Bits Container.Array Container.Bitmap IODemo

.PHONY: verify extract demo run clean

verify: $(addsuffix .verified, $(MODULES))

%.verified: %.fst
	$(FSTAR) $<
	@touch $@

# Extract the data-structure modules to OCaml. (Test.fst is verification-
# only; not part of runtime.)
extract: Spec.ml Bits.ml Container_Array.ml Container_Bitmap.ml IODemo.ml

Spec.ml Bits.ml Container_Array.ml Container_Bitmap.ml IODemo.ml: Spec.fst Bits.fst Container.Array.fst Container.Bitmap.fst IODemo.fst
	$(FSTAR) --codegen OCaml --extract '* -FStar' Spec.fst Bits.fst Container.Array.fst Container.Bitmap.fst IODemo.fst

# Native demo binary linking the extracted code with demo.ml.
demo: extract demo.ml
	$(OCAMLFIND) ocamlopt -package fstar.lib,zarith -linkpkg \
		Spec.ml Bits.ml Container_Array.ml Container_Bitmap.ml IODemo.ml demo.ml -o demo

run: demo
	./demo

clean:
	rm -f *.verified *.checked *.checked.lax *.cmi *.cmo *.cmx *.o
	rm -f Spec.ml Bits.ml Container_Array.ml Container_Bitmap.ml IODemo.ml Test.ml demo
