.PHONY: all build check cache auto-build docs clean

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
	lake exe check_axioms

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

# Clean local helper artifacts
clean:
	rm -f .cache_marker
