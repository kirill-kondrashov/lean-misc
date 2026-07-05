.PHONY: all build check verify cache auto-build docs question3-report clean

QUESTION3_REPORT_DIR := docs/bronnimann_question_3
QUESTION3_REPORT_TEX := $(QUESTION3_REPORT_DIR)/proof.tex
QUESTION3_REPORT_PDF := $(QUESTION3_REPORT_DIR)/proof.pdf

# Default target
all: check

# Get Mathlib cache.
# Useful when dependencies (lake-manifest.json) change.
cache:
	lake exe cache get

# Build the project
build:
	lake build

# Check axioms
check:
	lake env bash ./scripts/check_axioms.sh

# Verify check output matches README's expected output block
verify:
	./scripts/verify_output.sh

# Fetch cache automatically when dependency metadata changes
.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

# Build/check with automatic cache refresh
auto-build: .cache_marker
	lake build
	lake exe check_axioms

# Build API documentation
docs:
	lake build TaoExercises:docs

# Build the standalone LaTeX report for Bronnimann Question 3
question3-report:
	@if command -v xelatex >/dev/null 2>&1; then \
		xelatex -interaction=nonstopmode -halt-on-error -output-directory $(QUESTION3_REPORT_DIR) $(QUESTION3_REPORT_TEX) && \
		xelatex -interaction=nonstopmode -halt-on-error -output-directory $(QUESTION3_REPORT_DIR) $(QUESTION3_REPORT_TEX); \
	elif command -v lualatex >/dev/null 2>&1; then \
		lualatex -interaction=nonstopmode -halt-on-error -output-directory $(QUESTION3_REPORT_DIR) $(QUESTION3_REPORT_TEX) && \
		lualatex -interaction=nonstopmode -halt-on-error -output-directory $(QUESTION3_REPORT_DIR) $(QUESTION3_REPORT_TEX); \
	else \
		echo "Error: neither xelatex nor lualatex is available." >&2; \
		exit 1; \
	fi
	@echo "Generated $(QUESTION3_REPORT_PDF)"

# Clean local helper artifacts
clean:
	rm -f .cache_marker
	rm -f $(QUESTION3_REPORT_DIR)/proof.aux \
		$(QUESTION3_REPORT_DIR)/proof.log \
		$(QUESTION3_REPORT_DIR)/proof.out \
		$(QUESTION3_REPORT_DIR)/proof.pdf
