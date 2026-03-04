#!/bin/bash
set -euo pipefail

README="README.md"
EXPECTED="expected.txt"
ACTUAL="output.txt"

# Extract expected output from the first fenced block after "Expected Output:"
# Supports both ``` and ```text / ```bash style openings.
awk '
  /Expected Output:/ { in_section=1; next }
  in_section && /^```/ {
    if (!in_block) { in_block=1; next }
    else { exit }
  }
  in_block { print }
' "$README" > "$EXPECTED"

echo "Re-running make check..."
make check > "$ACTUAL" 2>&1
EXIT_CODE=$?

if [ $EXIT_CODE -ne 0 ]; then
  echo "make check failed with exit code $EXIT_CODE"
  cat "$ACTUAL"
  exit $EXIT_CODE
fi

# Drop wrapper/build noise so README comparison stays stable.
grep -Ev '^(info: \[root\]:|lake exe check_axioms$|make(\[[0-9]+\])?: (Entering|Leaving) directory)' \
  "$ACTUAL" \
  | sed '/^$/d' > actual_cleaned.txt
mv actual_cleaned.txt "$ACTUAL"

cat "$ACTUAL"

if diff -w "$EXPECTED" "$ACTUAL"; then
  echo "Verification successful: Output matches README."
  rm -f "$EXPECTED" "$ACTUAL"
  exit 0
else
  echo "Verification failed: Output differs from README."
  echo "Expected:"
  cat "$EXPECTED"
  echo "Actual:"
  cat "$ACTUAL"
  rm -f "$EXPECTED" "$ACTUAL"
  exit 1
fi
