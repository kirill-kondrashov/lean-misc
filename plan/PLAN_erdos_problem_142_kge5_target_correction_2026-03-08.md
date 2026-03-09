# Plan: Erdős #142 `k >= 5` Target Correction

Date: 2026-03-08

## Objective

Apply the audit verdict for the `k >= 5` family:
kill the mis-specified iterated-log matched-profile family target as an active debt, and replace it
with an explicitly corrected route statement.

## Status

Progress: `████` `4 / 4`

## Correction Question

```text
How should the repo describe the remaining `k >= 5` debt after the audit showed that the old
iterated-log matched-profile family target is not source-aligned?
```

## Milestones

1. `[x]` Freeze the audit verdict.
   - source: `NOTES_problem142_kge5_matched_profile_debt_audit_2026-03-08.md`
   - verdict: target correction

2. `[x]` Rewrite the active `k >= 5` debt statement so it no longer treats the old iterated-log
   matched-profile family as a live source-backed target.
   - result: the old family theorem is now frozen as a legacy off-path placeholder only

3. `[x]` Identify the corrected remaining debt precisely.
   - either a weaker source-backed split family,
   - or a stronger off-path route with explicitly non-source-backed status
   - result: keep the source-backed `k = 5` split toy-model route live, and treat any stronger
     family matched-profile closure as speculative unless a compatible source appears

4. `[x]` Update the revised research program with the corrected family-debt description.
   - successor cycle: `PLAN_erdos_problem_142_k4_matched_profile_debt_audit_2026-03-09.md`

## Current Verdict

```text
The audit killed the old `k >= 5` iterated-log matched-profile family theorem as an active
source-backed debt.

The corrected repo status is:
  - live source-backed route: the March 7 split pivot (`k = 5` toy model, no family matched
    profile claim),
  - stronger family matched-profile route: explicitly off-path and frozen unless a source-backed
    theorem appears with a compatible scale.

So the next active debt is no longer the old `k >= 5` family theorem.
It is the next ranked live matched-profile debt: `k = 4`.
```

## Correction Note

- `NOTES_problem142_kge5_target_correction_2026-03-09.md`

## Successor Plan

- `PLAN_erdos_problem_142_k4_matched_profile_debt_audit_2026-03-09.md`
