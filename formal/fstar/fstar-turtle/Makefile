# F* verified streaming Turtle parser - Build system
#
# Prerequisites:
#   - F* compiler (fstar.exe) with z3
#   - KaRaMeL (krml) for C extraction
#   - GCC or Clang for compiling extracted C
#
# Targets:
#   verify    - typecheck all F* modules (proves correctness)
#   extract   - extract to C via KaRaMeL
#   compile   - compile extracted C to binary
#   test      - run tests
#   clean     - remove generated files

FSTAR_HOME ?= $(shell dirname $$(which fstar.exe))/..
FSTAR = fstar.exe
KRML = krml

# F* include paths
FSTAR_INCLUDES = --include src

# KaRaMeL flags
KRML_FLAGS = \
  -tmpdir extract \
  -skip-linking \
  -warn-error -9 \
  -fparentheses

# Source modules in dependency order
MODULES = \
  ByteSource \
  Utf8 \
  Node \
  Sink \
  TurtleReader \
  TurtleReader.Impl

SRC_FILES = $(patsubst %,src/%.fst,$(MODULES))

# F* verification flags
FSTAR_FLAGS = \
  $(FSTAR_INCLUDES) \
  --cache_checked_modules \
  --already_cached 'Prims FStar LowStar'

.PHONY: all verify extract compile test clean

all: verify extract compile

# Verify all F* modules (typechecking + SMT proofs)
verify: $(SRC_FILES)
	@echo "=== Verifying F* modules ==="
	@for f in $(SRC_FILES); do \
		echo "  Checking $$f ..."; \
		$(FSTAR) $(FSTAR_FLAGS) $$f || exit 1; \
	done
	@echo "=== All modules verified ==="

# Extract to C via KaRaMeL
extract: verify
	@echo "=== Extracting to C via KaRaMeL ==="
	@mkdir -p extract
	$(KRML) $(KRML_FLAGS) $(FSTAR_INCLUDES) $(SRC_FILES)
	@echo "=== Extraction complete ==="
	@ls -la extract/*.c extract/*.h 2>/dev/null || echo "  (no C files generated)"

# Compile extracted C
compile: extract
	@echo "=== Compiling extracted C ==="
	@if ls extract/*.c >/dev/null 2>&1; then \
		$(CC) -O2 -Wall -Wextra -I extract \
			-I $(FSTAR_HOME)/lib/fstar \
			-I $(shell $(KRML) -print-include-dir 2>/dev/null || echo /dev/null) \
			extract/*.c \
			test/test_main.c \
			-o test/turtle_test; \
		echo "=== Build complete: test/turtle_test ==="; \
	else \
		echo "  No C files to compile (extraction may have failed)"; \
	fi

# Run tests
test: compile
	@echo "=== Running tests ==="
	@if [ -f test/turtle_test ]; then \
		./test/turtle_test; \
	else \
		echo "  No test binary found"; \
	fi

# Just verify without extraction (faster iteration)
check: $(SRC_FILES)
	@for f in $(SRC_FILES); do \
		echo "Checking $$f ..."; \
		$(FSTAR) $(FSTAR_FLAGS) $$f || exit 1; \
	done

clean:
	rm -rf extract/*.c extract/*.h extract/*.o
	rm -f test/turtle_test
	rm -rf .cache
	rm -f *.checked
