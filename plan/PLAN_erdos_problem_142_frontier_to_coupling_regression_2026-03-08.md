# Plan: Erdős #142 Frontier-to-Coupling Regression

Date: 2026-03-08

## Objective

Make the theorem-level bridge from the named matched-profile frontier package to explicit
coupling assumptions part of the repository's checked contract.

That means:

1. add a theorem-level realization surface for the frontier-to-coupling bridge;
2. check it in `check_axioms.lean`;
3. update the README expected-output block and status narrative;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add a theorem-level bridge from `Problem142MatchedProfileFrontier` to
   `SplitGapToMainTheoreticalGapAssumptions`.
   - `SplitGapToMainTheoreticalGapAssumptionsExists`
   - `splitGapToMainTheoreticalGapAssumptions_exists_of_matchedProfileFrontier`

2. `[x]` Add the new frontier-to-coupling bridge theorem to the checker target list.

3. `[x]` Update the README expected checker output and public status narrative.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The stronger off-path route is now checker-visible at four layers:
- frontier-to-coupling bridge
- explicit coupling theorem
- named matched-profile route theorem
- current frontier-instantiated theorem
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_frontier_instantiated_coupling_regression_2026-03-08.md`
