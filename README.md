# Lean Experiments

Lean formalization experiments and problem-focused developments, using a project structure modeled after:
<https://github.com/kirill-kondrashov/yoccos-theorem>.

## Current contents

- `TaoExercises.TaoBook.Chapter2.exercise_2_3`:
  Terence Tao, *Solving mathematical problems: a personal perspective*, Exercise 2.3
  (`x^4 + 131 = 3y^4` has no integer solutions in integers).

- `TaoExercises.TaoBook.Chapter2.exercise_2_6`:
  Problem 2.6 (Shklarsky et al. 1962, p. 14):
  if `k` is odd, then `1^k + 2^k + · · · + n^k` is divisible by `1 + 2 + · · · + n`.

- `ErdosProblems.erdos_problem_142`:
  Erdős Problem #142 formalization (statement-level):
  define `r_k(N)` as the maximal size of a subset of `{1, ..., N}` avoiding non-trivial
  `k`-term arithmetic progressions, and state the asymptotic-formula goal for fixed `k ≥ 3`.
  Also includes an explicit equivalence theorem with the DeepMind-style formulation:
  `Erdos142.erdos_problem_142_iff_deepmind`.

- `ErdosProblems.erdos_problem_142_explicit`:
  strengthened non-tautological target requiring `r_k` to be `Θ` of an explicit profile class
  (`ErdosProblems.ExplicitProfileClass`), with DeepMind-style equivalence theorem:
  `Erdos142.erdos_problem_142_explicit_iff_deepmind`.

- Plan for solving #142:
  `plan/PLAN_erdos_problem_142.md`

- Active explicit-branch debt-burndown plan:
  `plan/PLAN_erdos_problem_142_explicit_branch_axiom_burndown_2026-03-04.md`

## Toolchain and dependencies

- Lean: `leanprover/lean4:v4.27.0`
- mathlib: `v4.27.0`
- doc-gen4: `v4.27.0`

## Build

```bash
lake build
lake exe check_axioms
```

## Verification

All solved exercises are checked to ensure they:

- do not use `sorry`
- depend only on the base axioms `propext`, `Quot.sound`, and `Classical.choice`
- include the Problem #142 DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_iff_deepmind`)
- include the strengthened explicit-profile DeepMind-equivalence theorem
  (`Erdos142.erdos_problem_142_explicit_iff_deepmind`)
- explicitly track temporary open-problem debt axioms for the roadmap branches:
  - `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom`
  (temporarily allowed so CI stays green, and must eventually be removed)

Run:

```bash
make check
make verify
```

Expected Output:

```text
✅ The proof of 'TaoExercises.TaoBook.Chapter2.exercise_2_3' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'TaoExercises.TaoBook.Chapter2.exercise_2_6' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos142.erdos_problem_142_iff_deepmind' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
✅ The proof of 'Erdos142.erdos_problem_142_explicit_iff_deepmind' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
🟡 The proof of 'Erdos142.erdos_problem_142_solution_axiom' is free of 'sorry' but relies on temporary allowed axiom debt.
Axioms used:
- propext
- Quot.sound
- Classical.choice
- Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom
Temporarily allowed non-base axioms (must be proved later):
- Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom
✅ All checked items are free of 'sorry'. Temporary Erdős #142 axiom debt is explicitly allowed.
```

## Useful Make targets

```bash
make cache      # fetch Mathlib cache
make build      # lake build
make check      # lake exe check_axioms
make verify     # compare make check output with README expected output
make auto-build # cache refresh + build + check
make docs       # build API docs
```

## CI workflow (GitHub Actions)

- `.github/workflows/lean_action_ci.yml`
- Pull requests, pushes, and manual runs all execute a single `leanprover/lean-action` build job.
- Docs are not generated/deployed in CI.
- Workflow concurrency is enabled with `cancel-in-progress: true`.

## Erdős #142: current status and references

- As of March 4, 2026, Problem #142 is still open.
- This repository formalizes the statement and related infrastructure; it does not claim a full
  asymptotic-formula proof.
- A stronger target is now formalized:
  `ErdosProblems.erdos_problem_142_explicit`, where comparison profiles are constrained to explicit
  template classes rather than arbitrary functions.
- A structured theorem outline
  (`Erdos142.erdos_problem_142_solution_axiom`) is tracked in checker output with explicit
  branch debt axioms:
  - `Erdos142.erdos_problem_142_explicit_kge5_profile_witness_axiom`
  The `k = 3` and `k = 4` branches are now routed through imported-assumption interfaces
  (`Erdos142.K3ProfileWitnessImported`, `Erdos142.K4ProfileWitnessImported`) rather than
  temporary checker-allowlisted axioms.
  These are unresolved proof debt that must be removed by real proofs.
- The Erdős Problems page notes that an asymptotic formula remains far out of reach, and cites
  current upper-bound progress by:
  - Kelley-Meka (`k = 3`)
  - Green-Tao (`k = 4`)
  - Leng-Sah-Sawhney (`k ≥ 5`)

References:

- Erdős Problems #142 (status/discussion): <https://www.erdosproblems.com/142>
- Kelley, Z.; Meka, R. (2023), *Strong Bounds for 3-Progressions*:
  <https://arxiv.org/abs/2302.05537>
- Green, B.; Tao, T. (2017), *New bounds for Szemerédi's theorem, III: a polylogarithmic bound
  for r_4(N)* (Mathematika): <https://ora.ox.ac.uk/objects/uuid:1d09eef3-01e2-4ce0-ab9d-2892019812c8>
- Leng, J.; Sah, A.; Sawhney, M. (2024), *Improved bounds for Szemerédi's theorem*:
  <https://arxiv.org/abs/2402.17995>
