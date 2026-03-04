import Lake
open Lake DSL

package tao_exercises where
  @[default_target]
  lean_lib TaoExercises

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.27.0"

lean_exe check_axioms where
  root := `check_axioms
