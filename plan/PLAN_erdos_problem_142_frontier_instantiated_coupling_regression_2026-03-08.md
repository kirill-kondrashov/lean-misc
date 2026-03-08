# Plan: Erdős #142 Frontier-Instantiated Coupling Regression

Date: 2026-03-08

## Objective

Make the currently instantiated frontier-to-coupling bridge part of the repository's checked
contract, not just the generic bridge from an abstract frontier package.

That means:

1. add a theorem-level realization surface for the instantiated frontier-to-coupling bridge;
2. check it in `check_axioms.lean`;
3. update the README expected-output block and status narrative;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add a theorem-level realization surface for the instantiated frontier-to-coupling bridge.
   - `splitGapToMainTheoreticalGapAssumptions_exists_of_frontier`

2. `[x]` Add the new instantiated bridge theorem to the checker target list.

3. `[x]` Update the README expected checker output and public status narrative.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The current frontier-debt route is now checker-visible at three debt-carrying layers:
- named frontier package
- instantiated frontier-to-coupling bridge
- frontier-instantiated theorem
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_main_theoretical_gap_assumption_regression_2026-03-08.md`
