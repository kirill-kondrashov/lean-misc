# Plan: Erdős #142 Frontier-Package Regression

Date: 2026-03-08

## Objective

Make the named off-path matched-profile frontier package part of the repository's checked
contract on its own, rather than only as a field inside the larger current-status package.

That means:

1. add a theorem-level realization surface for `Problem142MatchedProfileFrontier`;
2. check that theorem in `check_axioms.lean`;
3. update the README expected-output block and status narrative;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add a proposition-level realization surface for the matched-profile frontier package.
   - `MatchedProfileFrontierExists`
   - `matchedProfileFrontier_exists`

2. `[x]` Add the new frontier realization theorem to the checker target list.

3. `[x]` Update the README expected checker output and public status text.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
All three components of the current repository status are now individually named and
checker-visible: the practical split route, the stabilized negative `k = 3` route,
and the off-path matched-profile frontier.
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_frontier_route_regression_2026-03-08.md`
