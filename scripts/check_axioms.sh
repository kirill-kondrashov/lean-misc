#!/bin/bash
set -euo pipefail

BIN=".lake/build/bin/check_axioms"

THEOREMS=(
  "TaoExercises.TaoBook.Chapter2.exercise_2_3"
  "TaoExercises.TaoBook.Chapter2.exercise_2_6"
  "BronnimannQuestion3.positive_answer_of_witness"
  "BronnimannQuestion3.positive_answer"
  "Erdos1.erdos_1.variants.weaker"
  "Erdos1.choose_middle_isEquivalent"
  "Erdos1.erdos_1_solution_axiom"
  "Erdos142.erdos_problem_142_iff_deepmind"
  "Erdos142.erdos_problem_142_explicit_iff_deepmind"
  "Erdos142.erdos_problem_142_solution_axiom"
  "Erdos142.erdos_problem_142_of_mainSplitGap_and_frontier"
)

MODULES=(
  "SimpleExercises.Continuity"
)

run_decl() {
  local decl="$1"
  set +e
  "$BIN" --single "$decl"
  local code=$?
  set -e
  case "$code" in
    0) return 0 ;;
    1) all_ok=0; return 0 ;;
    2) any_temporary=1; return 0 ;;
    *)
      echo "Unexpected exit code $code while checking '$decl'." >&2
      exit "$code"
      ;;
  esac
}

lake build Groups check_axioms >/dev/null

all_ok=1
any_temporary=0

for decl in "${THEOREMS[@]}"; do
  run_decl "$decl"
done

for module_name in "${MODULES[@]}"; do
  case "$module_name" in
    "SimpleExercises.Continuity")
      module_file="SimpleExercises/Continuity.lean"
      ;;
    *)
      echo "No declaration scanner configured for module '$module_name'." >&2
      exit 1
      ;;
  esac
  mapfile -t decls < <(
    grep -E '^(def|theorem|lemma|axiom|opaque)[[:space:]]+[A-Za-z0-9_.]+' "$module_file" \
      | sed -E 's/^(def|theorem|lemma|axiom|opaque)[[:space:]]+([A-Za-z0-9_.]+).*/\2/'
  )
  if [ "${#decls[@]}" -eq 0 ]; then
    echo "✅ The module '$module_name' is included in the checker and currently has no checkable declarations."
  else
    for decl in "${decls[@]}"; do
      run_decl "$decl"
    done
  fi
done

if [ "$all_ok" -eq 1 ]; then
  if [ "$any_temporary" -eq 1 ]; then
    echo "✅ All checked items are free of 'sorry'. Temporary Erdős #1/#142 axiom debt is explicitly allowed."
  else
    echo "✅ All checked solutions are free of 'sorry' and use only base axioms."
  fi
  exit 0
else
  echo "❌ Base-axiom verification failed."
  exit 1
fi
