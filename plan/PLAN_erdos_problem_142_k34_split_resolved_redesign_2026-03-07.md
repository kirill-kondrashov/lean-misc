# Plan: `k = 3,4` Split-Resolved Redesign

Date: 2026-03-07

## Objective

Adopt the honest downstream surface where

- `k = 3` is resolved only to split strength,
- `k = 4` is resolved only to split strength,
- only `k >= 5` remains a matched-profile coupling frontier.

## Status

Progress: `██████` `6 / 6` milestones

## Milestones

1. `[x]` Define the new split-resolved surface.
   - `MainK34ResolvedSplitGap`

2. `[x]` Add bridge constructors from existing surfaces.
   - from instances,
   - from `MainK3ResolvedSplitGap` plus `K4SourceBackedSplitGap`,
   - from `MainSplitGap` plus both source-backed split witnesses.

3. `[x]` Add compatibility projections.
   - forget to `MainSplitGap`
   - forget to `MainK3ResolvedSplitGap`
   - expose split-gap data

4. `[x]` Add the downstream surface with only `k >= 5` unresolved.
   - `MainK34ResolvedGap`
   - `K34ResolvedSplitGapToMainK34ResolvedGapAssumptions`

5. `[x]` Decide whether this should replace `MainK3ResolvedGap` as the practical target.
   - Yes. On the active redesigned route, `MainK34ResolvedGap` is now the practical target.

6. `[x]` Update top-level docs/status text to name `k >= 5` as the only active coupling frontier on this path.
   - Updated:
     - `README.md`
     - `PLAN_erdos_problem_142_feasibility_reassessment_2026-03-06.md`

## Mathematical Status

On this redesigned route, the active target is:

```text
k = 3:
  source-backed split package only

k = 4:
  source-backed split package only

k >= 5:
  still requires matched-profile coupling
```

So the old obstruction

```text
U_4(N) = O(L_4(N))
```

is no longer on the active downstream path.
It remains a blocked stronger theorem, but it is no longer the next required step for progress
on the redesigned route.

Active follow-up:

- `PLAN_erdos_problem_142_kge5_frontier_elimination_2026-03-07.md`
