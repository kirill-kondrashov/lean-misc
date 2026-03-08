# Plan: `k = 3` Negative-Route Stabilization

Date: 2026-03-08

## Objective

Package the post-critic negative route as a clean repository endpoint rather than leaving it split
across helper lemmas and notes.

The target is to expose the stable conclusion:

```text
the current extracted architecture and its first source-motivated local refinement
both remain off the Behrend scale.
```

## Status

Progress: `██████` `4 / 4`

## Milestones

1. `[x]` Add named theorem-level negative endpoints in Lean for the current extracted architecture.
   - `erdos_142_three_current_architecture_barrier`
   - `erdos_142_three_current_architecture_barrier_true`

2. `[x]` Add named theorem-level negative endpoints in Lean for the first local refinement.
   - `erdos_142_three_one_eighth_refinement_barrier`
   - `erdos_142_three_one_eighth_refinement_barrier_true`

3. `[x]` Add one combined stable negative-route endpoint.
   - `erdos_142_three_negative_route_stable`
   - `erdos_142_three_negative_route_stable_true`

4. `[x]` Link the completed negative/bottleneck program to this stabilized surface.
   - update plan/docs so the post-critic route points to these named endpoints

## Current Verdict

```text
The negative route is no longer only a note-level research stance.
It is now packaged as a named theorem-level endpoint in the repository,
while still remaining explicitly conditional on the extracted architecture template.
```

## Successor Plan

The next public-surface cycle is:

- `PLAN_erdos_problem_142_k3_negative_route_surface_integration_2026-03-08.md`
