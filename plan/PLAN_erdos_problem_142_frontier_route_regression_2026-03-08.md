# Plan: Erdős #142 Frontier-Route Regression

Date: 2026-03-08

## Objective

Make the clean generic matched-profile route theorem part of the repository's checked contract.

That means:

1. check `erdos_problem_142_of_mainSplitGap_and_matchedProfileFrontier` in `check_axioms.lean`;
2. update the README expected-output block accordingly;
3. clarify in the status docs that this generic route theorem is base-axiom clean, while only the
   current instantiated frontier theorem carries temporary axiom debt;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add the clean generic matched-profile route theorem to the checker target list.
   - `erdos_problem_142_of_mainSplitGap_and_matchedProfileFrontier`

2. `[x]` Update the README expected checker output to include the new checked theorem.

3. `[x]` Update the public status narrative to distinguish the generic route theorem from the
   current frontier-instantiated theorem.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The stronger matched-profile route is now exposed at two checked levels:
- a base-axiom-clean generic theorem
- the current frontier-instantiated theorem carrying the temporary debt
```

## Successor Plan

The next regression-extension cycle is:

- `PLAN_erdos_problem_142_assumption_route_regression_2026-03-08.md`
