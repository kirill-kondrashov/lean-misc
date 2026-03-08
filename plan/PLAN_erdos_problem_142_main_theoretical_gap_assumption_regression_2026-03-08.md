# Plan: Erdős #142 Main-Theoretical-Gap Assumption Regression

Date: 2026-03-08

## Objective

Make the theorem-level realization surface for the full `MainTheoreticalGap` object from explicit
coupling assumptions part of the repository's checked contract.

That means:

1. add a theorem-level realization surface for `MainTheoreticalGap`;
2. check it in `check_axioms.lean`;
3. update the README expected-output block and status narrative;
4. rerun the verification pipeline.

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add a theorem-level realization surface for the full main-gap object from explicit
   coupling assumptions.
   - `MainTheoreticalGapExists`
   - `mainTheoreticalGap_exists_of_mainSplitGap_and_assumptions`

2. `[x]` Add the new main-gap realization theorem to the checker target list.

3. `[x]` Update the README expected checker output and public status narrative.

4. `[x]` Run the verification pipeline.
   - `make verify`

## Current Verdict

```text
The stronger off-path route now exposes the full `MainTheoreticalGap` object as an
explicit checked layer, not just the coupling assumptions and final statement theorem.
```

## Successor Plan

The packaging/regression chain is now considered complete enough for the current debt profile.
The next active plan is a research-program reset:

- `PLAN_erdos_problem_142_revised_research_program_2026-03-08.md`
- `NOTES_problem142_research_program_critique_2026-03-08.md`
