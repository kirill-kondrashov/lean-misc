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

- `ErdosProblems` (Erdős #142 family):
  statement, explicit-profile strengthening, and gap decomposition are present under
  `Erdos142` (`erdos_problem_142`, `erdos_problem_142_explicit`, `Problem142Gap`)
  with `erdos_problem_142_iff_deepmind`, `erdos_problem_142_explicit_iff_deepmind`,
  and the current plan series in `plan/` (`PLAN_erdos_problem_142.md` and follow-on files).

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
- keep checker output explicit about temporary axiom frontier debt where present

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
✅ The proof of 'Erdos142.erdos_problem_142_solution_axiom' is free of 'sorry' and uses only base axioms.
Axioms used:
- propext
- Quot.sound
- Classical.choice
🟡 The proof of 'Erdos142.erdos_problem_142_of_mainSplitGap_and_frontier' is free of 'sorry' but relies on temporary allowed axiom debt.
Axioms used:
- propext
- Quot.sound
- Classical.choice
- Erdos142.splitGap_k3_upper_exponent_gt_half_frontier
- Erdos142.splitGap_k4_profile_dominance_frontier
- Erdos142.splitGap_kge5_profile_dominance_frontier
Temporarily allowed non-base axioms (must be proved later):
- Erdos142.splitGap_k3_upper_exponent_gt_half_frontier
- Erdos142.splitGap_k4_profile_dominance_frontier
- Erdos142.splitGap_kge5_profile_dominance_frontier
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

- As of March 7, 2026, Problem #142 remains open; this repository keeps the full matched-profile route behind the temporary frontier axioms `Erdos142.splitGap_k3_upper_exponent_gt_half_frontier`, `Erdos142.splitGap_k4_profile_dominance_frontier`, and `Erdos142.splitGap_kge5_profile_dominance_frontier`, while the strongest honest local `k=3` endpoint is now the source-backed split package `Erdos142.K3SourceBackedSplitGap`, built from Kelley-Meka's explicit `β = 1 / 12` upper witness together with Behrend lower data and the true compatibility direction `k3_behrend_lower_template =O k3_upper_profile`.

The active missing mathematical theorems are now the higher-branch profile-matching statements. For `k = 4`, from split bounds

$$
r_4(N)=O\!\left(\frac{C_u N}{(\log(N+2))^{c_u}}\right),
\qquad
\frac{C_\ell N}{(\log(N+2))^{c_\ell}}=O(r_4(N)),
$$

the missing theorem is

$$
\frac{C_u N}{(\log(N+2))^{c_u}}
=
O\!\left(\frac{C_\ell N}{(\log(N+2))^{c_\ell}}\right).
$$

For each fixed `k \ge 5`, from split bounds

$$
r_k(N)=O\!\left(\frac{C_u(k)\,N}{(\log\log(N+3))^{c_u(k)}}\right),
\qquad
\frac{C_\ell(k)\,N}{(\log\log(N+3))^{c_\ell(k)}}=O(r_k(N)),
$$

the missing theorem is

$$
\frac{C_u(k)\,N}{(\log\log(N+3))^{c_u(k)}}
=
O\!\left(\frac{C_\ell(k)\,N}{(\log\log(N+3))^{c_\ell(k)}}\right)
\qquad (k \ge 5).
$$

These are the exact dominance statements needed to turn the current split upper/lower data into matched `K4ProfileWitness` and `Kge5ProfileWitness` packages.

References:

- Erdős Problems #142 (status/discussion): <https://www.erdosproblems.com/142>
- Kelley, Z.; Meka, R. (2023), *Strong Bounds for 3-Progressions*:
  <https://arxiv.org/abs/2302.05537>
- Green, B.; Tao, T. (2017), *New bounds for Szemerédi's theorem, III: a polylogarithmic bound
  for r_4(N)* (Mathematika): <https://ora.ox.ac.uk/objects/uuid:1d09eef3-01e2-4ce0-ab9d-2892019812c8>
- Leng, J.; Sah, A.; Sawhney, M. (2024), *Improved bounds for Szemerédi's theorem*:
  <https://arxiv.org/abs/2402.17995>
