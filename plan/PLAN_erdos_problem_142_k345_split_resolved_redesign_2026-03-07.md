# Plan: `k = 3,4,5` Split-Resolved Redesign

Date: 2026-03-07

## Objective

Adopt the honest downstream surface where

- `k = 3` is resolved only to split strength,
- `k = 4` is resolved only to split strength,
- `k = 5` is resolved only to split strength via the new source-backed toy model,
- only `k >= 6` remains a tail coupling frontier.

## Status

Progress: `██████` `6 / 6` milestones

## Milestones

1. `[x]` Define the new split-resolved surface.
   - `MainK345ResolvedSplitGap`

2. `[x]` Add bridge constructors from existing surfaces.
   - from instances,
   - from `MainK34ResolvedSplitGap` plus `K5SourceBackedSplitGap`,
   - from the current literature-side source assumptions.

3. `[x]` Expose branch-local mathematical consequences.
   - all upper variants on the new route,
   - the explicit source-backed `k = 5` split data,
   - the inherited `k >= 6` tail split data.

4. `[x]` Add the downstream surface with only `k >= 6` unresolved.
   - `MainK345ResolvedGap`
   - `K345ResolvedSplitGapToMainK345ResolvedGapAssumptions`

5. `[x]` Decide whether this should replace `MainK34ResolvedGap` as the practical target.
   - Yes. On the active redesigned route, `MainK345ResolvedGap` is now the practical target.

6. `[x]` Update top-level feasibility/status text to name `k >= 6` as the only active coupling frontier on this path.
   - Updated:
     - `PLAN_erdos_problem_142_feasibility_reassessment_2026-03-06.md`
     - `PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md`

## Mathematical Status

On this redesigned route, the active target is:

```text
k = 3:
  source-backed split package only

k = 4:
  source-backed split package only

k = 5:
  source-backed split package only
  with a true comparison theorem
    L5_src(N) = O(U5_src(N))

k >= 6:
  still requires a tail matched-profile coupling theorem
```

So the old obstruction

```text
for all k >= 5,
  force one matched iterated-log profile
```

is no longer on the active downstream path.
The remaining active frontier is only the tail `k >= 6` family.

Active follow-up:

- [PLAN_erdos_problem_142_kge6_source_backed_family_2026-03-07.md](PLAN_erdos_problem_142_kge6_source_backed_family_2026-03-07.md)
