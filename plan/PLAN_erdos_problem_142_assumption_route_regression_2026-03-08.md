# Plan: Erdős #142 Assumption-Route Regression

Date: 2026-03-08

## Objective

Make the explicit coupling-assumption route theorem part of the repository's checked contract.

That means:

1. check `erdos_problem_142_of_mainSplitGap_and_assumptions` in `check_axioms.lean`;
2. update the README expected-output block accordingly;
3. clarify in the status docs that the stronger route factors cleanly through the explicit
   coupling-assumption theorem before the named matched-profile frontier specialization;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add the explicit coupling-assumption theorem to the checker target list.
   - `erdos_problem_142_of_mainSplitGap_and_assumptions`

2. `[x]` Update the README expected checker output to include the new checked theorem.

3. `[x]` Update the public status narrative to expose the two-step clean factorization of the
   stronger route.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The stronger off-path route is now checker-visible at three layers:
- explicit coupling assumptions
- named matched-profile frontier package
- current frontier-instantiated theorem
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_frontier_to_coupling_regression_2026-03-08.md`
