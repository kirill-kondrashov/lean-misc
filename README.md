# Lean Experiments

[![build](https://github.com/kirill-kondrashov/lean-misc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/lean-misc/actions/workflows/lean_action_ci.yml)

Lean formalization experiments and problem-focused developments, using a project structure modeled
after <https://github.com/kirill-kondrashov/yoccos-theorem>.

## At a glance

- Main active fronts:
  [Erdős #1](./docs/readme/erdos_1.md), [Erdős #142](./docs/readme/erdos_142.md), and
  [Brönnimann Question 3](./docs/readme/bronnimann_question_3.md), together with the exploratory
  [hyperbolic residual-finiteness problem](./docs/readme/hyperbolic_residual_finiteness.md)
- Toolchain:
  Lean `v4.27.0`, mathlib `v4.27.0`
- Main entrypoint for the current Erdős #1 frontier:
  [ErdosProblems/Problem1CubeHalfBoundary.lean](./ErdosProblems/Problem1CubeHalfBoundary.lean)
- Main entrypoint for the current Erdős #142 frontier:
  [ErdosProblems/Problem142Gap.lean](./ErdosProblems/Problem142Gap.lean)
- Main entrypoint for the Brönnimann Question 3 formalization:
  [Groups/BronnimannQuestion3.lean](./Groups/BronnimannQuestion3.lean)

## Quick links

- [Repository map](#repository-map)
- [Toolchain](#toolchain-and-dependencies)
- [Common commands](#common-commands)
- [Verification policy](#verification-policy)
- [CI workflow](#ci-workflow-github-actions)
- [Erdős #1](./docs/readme/erdos_1.md)
- [Erdős #142](./docs/readme/erdos_142.md)
- [Brönnimann Question 3](./docs/readme/bronnimann_question_3.md)
- [Hyperbolic residual finiteness](./docs/readme/hyperbolic_residual_finiteness.md)

## Repository map

GitHub renders the old table too narrowly, so this section uses a list instead.

- `Erdos1.erdos_1`
  Statement layer for Erdős Problem #1, sum-distinct variants, and the imported/open literature endpoints.
  Main file: [ErdosProblems/Problem1.lean](./ErdosProblems/Problem1.lean)

- `TaoExercises.TaoBook.Chapter2.exercise_2_3`
  Exercise 2.3: `x^4 + 131 = 3y^4` has no integer solutions.
  Main file: [TaoExercises/TaoBook/Chapter2.lean](./TaoExercises/TaoBook/Chapter2.lean)

- `TaoExercises.TaoBook.Chapter2.exercise_2_6`
  If `k` is odd, then `1^k + 2^k + ··· + n^k` is divisible by `1 + 2 + ··· + n`.
  Main file: [TaoExercises/TaoBook/Chapter2.lean](./TaoExercises/TaoBook/Chapter2.lean)

- `ErdosProblems` (`Erdos142`)
  Erdős #142 statement, explicit-profile strengthening, gap decomposition, and the current frontier packages.
  Main file: [ErdosProblems/Problem142Gap.lean](./ErdosProblems/Problem142Gap.lean)

- `Groups.HeisenbergGroup`
  Formalization work for the discrete Heisenberg group and its geodesic language, following
  Alekseev--Magdiev, "The language of geodesics for the discrete Heisenberg group"
  (<https://arxiv.org/pdf/1905.03226>).
  Main file: [Groups/HeisenbergGroup.lean](./Groups/HeisenbergGroup.lean)

- `Groups.BronnimannQuestion3`
  Statement-level reduction for Brönnimann's Question 3: any explicit witness with solvable word
  problem and irrational geodesic growth yields a positive answer.
  Main file: [Groups/BronnimannQuestion3.lean](./Groups/BronnimannQuestion3.lean)

- `prompts/hyperbolic_residual_finiteness`
  Research prompts and scenario-driven exploration of whether every word-hyperbolic group is
  residually finite. This is an open-problem investigation, not a formalized theorem.

## Toolchain and dependencies

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.27.0` |
| mathlib | `v4.27.0` |
| doc-gen4 | `v4.27.0` |

## Common commands

| Task | Command |
| --- | --- |
| Build everything | `make build` |
| Check axioms | `make check` |
| Verify README checker output | `make verify` |
| Refresh cache + build + check | `make auto-build` |
| Build docs | `make docs` |
| Direct `lake` build | `lake build` |
| Direct checker run | `lake env bash ./scripts/check_axioms.sh` |

## Verification policy

All solved exercises are checked to ensure they:

- do not use `sorry`
- depend only on the base axioms `propext`, `Quot.sound`, and `Classical.choice`
- build the top-level `SimpleExercises` library, including `SimpleExercises.Continuity`
- build the top-level `Groups` library, including `Groups.BronnimannQuestion3`
- build the top-level `ErdosProblems` library, including the `Erdos1` modules
- include the checked `Erdos1` theorems
  (`Erdos1.erdos_1.variants.weaker`, `Erdos1.choose_middle_isEquivalent`,
  and the temporary-axiom wrapper `Erdos1.erdos_1_solution_axiom`)
- include the fully local Brönnimann Question 3 witness-packaging theorem
  (`BronnimannQuestion3.positive_answer_of_witness`) and the unconditional-shape
  Question 3 theorem (`BronnimannQuestion3.positive_answer`), whose axiom
  dependencies are explicitly reported
- include the Problem #142 DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_iff_deepmind`)
- include the strengthened explicit-profile DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_explicit_iff_deepmind`)
- keep checker output explicit about temporary axiom frontier debt where present

The checker now builds the top-level `Groups` library and imports the checked
`SimpleExercises` and `ErdosProblems` proof modules, so `Groups.BronnimannQuestion3`,
`SimpleExercises.Continuity`, and `Erdos1` are built as part of `make check`.
`SimpleExercises.Continuity` contributes the local `RealCont` API, including composition,
affine transformations, sums, products, and polynomial evaluation; these declarations are checked
and currently require no non-base axioms.
It also reports two `Erdos1` theorems that are fully local and base-axiom clean:
`Erdos1.erdos_1.variants.weaker` and `Erdos1.choose_middle_isEquivalent`.
It also reports the fully local Question 3 packaging theorem
`BronnimannQuestion3.positive_answer_of_witness`, which turns any explicit witness with solvable
word problem and irrational geodesic growth into a core-axiom-clean proof of the existential
statement. This theorem is conditional: the witness properties are hypotheses, so the checker sees
no extra axioms beyond the core ones.
It also reports the unconditional-shape Question 3 theorem `BronnimannQuestion3.positive_answer`,
which instantiates the witness-packaging theorem with Bodart's virtually Engel group. Its
axiom dependencies currently include the two remaining internal-facing axioms
`VirtuallyEngel.theorem_4_upper` and `VirtuallyEngel.theorem_4_lower` — the one-sided halves of
Bodart's growth-equivalence `γ(n) ≍ exp(n^(3/5) log n)`, isolating the deep Stoll [Sto98] /
Pansu [Pan83] nilpotent-geometry inputs — together with the compiler-side axioms
`Lean.ofReduceBool` and `Lean.trustCompiler` introduced by the `native_decide` step in the word
problem decision procedure; all of these are treated as temporary allowed axiom debt and are
reported explicitly by the checker. The former internal-facing axioms
`VirtuallyEngel.toCoordGroup_injective` and `VirtuallyEngel.irrationalGeodesicGrowth` have since
been discharged as theorems, and the former single axiom `VirtuallyEngel.theorem_4` is now a
*proved theorem*. Here `≍` is the growth equivalence of geometric group theory
(`LinearRecurrenceGrowth.CoarseGrowth.CoarseEquiv`): each function dominates the other up to a
multiplicative constant on values and a linear rescaling of the argument. The upper half uses the
exponent `exp(n^(3/5) log n)`; the lower half only controls the exponent up to a smaller constant
`exp(κ·n^(3/5) log n)` with `κ ≤ 1`, faithfully mirroring Bodart's §4 estimate. The argument
rescaling of `≍` reconciles the two constants, so `theorem_4` follows from the
two named sub-axioms above; discharging those two Stoll/Pansu-dependent bounds is the remaining
internal work described in `docs/bronnimann_question_3/proof.tex`.
It also reports the open-problem wrapper `Erdos1.erdos_1_solution_axiom`, with the placeholder
axiom `Erdos1.erdos_1` treated as temporary allowed axiom debt in the same style as the current
`Erdos142` frontier checks.
The exact-value theorems proved by `native_decide` are still excluded from this checker because the
current policy treats `Lean.ofReduceBool` / `Lean.trustCompiler` as non-base axioms.


## Research fronts

- [Brönnimann Question 3](./docs/readme/bronnimann_question_3.md)
- [Hyperbolic residual finiteness](./docs/readme/hyperbolic_residual_finiteness.md)
- [Erdős #1](./docs/readme/erdos_1.md)
- [Erdős #142](./docs/readme/erdos_142.md)

## CI workflow (GitHub Actions)

- `.github/workflows/lean_action_ci.yml`
- Pull requests, pushes, and manual runs all execute a single `leanprover/lean-action` build job.
- Docs are not generated/deployed in CI.
- Workflow concurrency is enabled with `cancel-in-progress: true`.
