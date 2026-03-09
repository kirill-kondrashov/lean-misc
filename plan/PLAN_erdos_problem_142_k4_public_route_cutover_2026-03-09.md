# Plan: Erdős #142 `k = 4` Public Route Cutover

Date: 2026-03-09

## Objective

Cut the public `k = 4` route surfaces over from the legacy polylog-lower placeholder package to
the corrected heterogeneous split package, wherever that can be done honestly without breaking the
rest of the repository.

## Status

Progress: `████` `4 / 4`

## Cutover Question

```text
Which public theorem and status surfaces should now be redirected to the corrected
`K4HeterogeneousSourceBackedSplit...` route,
and which legacy `k = 4` surfaces must remain only as placeholders?
```

## Starting Point

- completed redesign cycle:
  `PLAN_erdos_problem_142_k4_heterogeneous_split_lean_redesign_2026-03-09.md`
- new corrected surfaces now live in code
- old legacy surfaces still exist

## Milestones

1. `[x]` Freeze the coexistence state:
   corrected route present, legacy route still public in some places.

2. `[x]` Identify the exact public surfaces to cut over.
   - README status claims
   - gap-layer route summaries
   - theorem-level current-status packaging, if affected

3. `[x]` Execute the minimal honest cutover.
   - prefer changing public route surfaces before deleting legacy placeholders

4. `[x]` Verify the cutover build and note any remaining legacy debt explicitly.

## Current Verdict

```text
Track A has now completed public cutover.
The canonical practical route is the heterogeneous `k = 4` route, while the old
polylog-lower all-branches surface remains only as a legacy local placeholder.
```
