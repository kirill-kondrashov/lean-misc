# Plan: Erdős Problem #142 (`r_k(N)` asymptotic formula)

## Goal

Formalize and (eventually) solve:

> Let `r_k(N)` be the largest cardinality of a subset of `{1, ..., N}` with no non-trivial
> `k`-term arithmetic progression. Prove an asymptotic formula for `r_k(N)`.

The statement is currently introduced in Lean as:

- `ErdosProblems.erdos_problem_142`

## Current formalization status

- [x] Core definitions are present:
  - `ContainsNontrivialKTermAP`
  - `KTermAPFree`
  - `admissibleSetCardinals`
  - `rk`
  - `HasAsymptoticFormula`
  - `erdos_problem_142`
- [ ] No lower/upper bound machinery formalized yet.
- [ ] No asymptotic formula proof strategy formalized yet.

## Technical milestones

1. Foundation lemmas for `rk`
- Prove basic monotonicity and bounds:
  - `rk k N ≤ N`
  - monotonicity in `N`
  - simple lower bounds (e.g., for small `k`, small `N`)
- Show equivalence between finite-set and function/range formulations where useful.

2. Arithmetic progression API
- Add reusable lemmas for:
  - translating/scaling progressions
  - interval membership (`Icc 1 N`) for progression terms
  - compatibility with `Finset` filtering and images

3. Asymptotic interface refinement
- Decide whether `HasAsymptoticFormula` should use:
  - `Asymptotics.IsEquivalent`, or
  - explicit `Θ`/two-sided `IsBigO` + `IsLittleO` style bounds.
- Add helper lemmas to convert between these formulations.

4. Known benchmark bounds (first formal targets)
- Formalize a nontrivial lower bound family for `rk k N`.
- Formalize a nontrivial upper bound family for at least one fixed `k` (likely `k = 3` first).
- Package results into an eventual "order of magnitude" theorem before full asymptotic formula.

5. Problem decomposition for full statement
- Split `erdos_problem_142` into:
  - fixed-`k` statement
  - `k = 3`, `k = 4`, `k ≥ 5` tracks
- Track dependencies on external deep results; isolate each as explicit assumptions/targets.

## Practical next step

Implement milestone 1 first:
- prove `rk` well-posedness lemmas and monotonicity/bounds,
- then expose a theorem skeleton for `k = 3` as the first concrete subgoal.
