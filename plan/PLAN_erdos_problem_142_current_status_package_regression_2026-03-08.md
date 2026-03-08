# Plan: Erdős #142 Current-Status Package Regression

Date: 2026-03-08

## Objective

Make the canonical current-status package itself part of the repository's checked contract.

That means:

1. add a theorem-level realization surface for `Problem142CurrentResearchStatus`;
2. check that theorem in `check_axioms.lean`;
3. update the README expected-output block;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add a proposition-level realization surface for the current-status package.
   - `CurrentResearchStatusExists`
   - `currentResearchStatus_exists_of_literature_sourceBacked_route`

2. `[x]` Add the new current-status realization theorem to the checker target list.

3. `[x]` Update the README expected checker output to include the new checked theorem.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The repository now checks not only the stabilized negative route but also the full
canonical current-status package as an explicit theorem-level contract surface.
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_frontier_package_regression_2026-03-08.md`
