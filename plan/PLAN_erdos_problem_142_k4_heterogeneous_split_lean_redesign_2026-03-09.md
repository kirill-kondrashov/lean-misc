# Plan: Erdős #142 `k = 4` Heterogeneous Split Lean Redesign

Date: 2026-03-09

## Objective

Implement the corrected `k = 4` broader-source route in Lean:
replace the public final `k = 4` polylog-lower split surface by a heterogeneous split package with

- Green--Tao polylogarithmic upper,
- O'Bryant/Rankin `sqrt(log N)`-type lower,
- and no matched-profile coupling claim.

## Status

Progress: `████` `4 / 4`

## Redesign Question

```text
What is the smallest code edit set that makes the public `k = 4` route mathematically honest
without breaking the existing repository structure more than necessary?
```

## Starting Point

- route shape:
  `NOTES_problem142_k4_source_route_shape_2026-03-09.md`
- lower target extraction:
  `NOTES_problem142_k4_lower_shape_extraction_2026-03-09.md`
- integration design:
  `NOTES_problem142_k4_heterogeneous_split_integration_design_2026-03-09.md`

## Milestones

1. `[x]` Freeze the exact redesign target and edit set.

2. `[x]` Add the new `k = 4` lower target and witness/import surfaces.
   - implemented in:
     `Problem142.lean`
     `Problem142Literature.lean`

3. `[x]` Add the corrected heterogeneous split package and gap-layer export.
   - implemented in:
     `Problem142Literature.lean`
     `Problem142Gap.lean`

4. `[x]` Update public status surfaces and verify the build.
   - public status text updated in:
     `README.md`
   - targeted build:
     `lake build ErdosProblems.Problem142 ErdosProblems.Problem142Literature ErdosProblems.Problem142Gap`
   - result:
     passed, with the pre-existing linter suggestion on `Problem142Literature.lean`

## Current Verdict

```text
The first direct code implementation cycle for the corrected `k = 4` route is now complete.

The repository now contains:
  - a new `k = 4` Rankin/O'Bryant lower target,
  - the matching witness/import/source-assumption surfaces,
  - a corrected heterogeneous split package and gap export,
  - and public status text that distinguishes the corrected route from the old placeholder route.

The next remaining `k = 4` task is to cut over the public route surfaces that still depend on the
legacy polylog-lower package.
```

## Successor Cycle

- `PLAN_erdos_problem_142_k4_public_route_cutover_2026-03-09.md`
