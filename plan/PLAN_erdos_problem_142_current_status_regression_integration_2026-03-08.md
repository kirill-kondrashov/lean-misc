# Plan: Erdős #142 Current-Status Regression Integration

Date: 2026-03-08

## Objective

Make the stabilized current-status surface part of the repository's regression contract.

That means:

1. check it in `check_axioms.lean`;
2. update the README expected-output block accordingly;
3. rerun the verification pipeline.

## Status

Progress: `██████` `3 / 3`

## Milestones

1. `[x]` Add the stabilized negative-route theorem to the checker target list.
   - `Erdos142.k3_negative_route_stable`

2. `[x]` Update the README expected checker output to include the new checked theorem.

3. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The current-status surface is now part of the repository's checked public contract,
not merely a documented internal package.
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_current_status_package_regression_2026-03-08.md`
