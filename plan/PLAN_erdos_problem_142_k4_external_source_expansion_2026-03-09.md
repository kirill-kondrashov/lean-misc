# Plan: Erdős #142 `k = 4` External Source Expansion

Date: 2026-03-09

## Objective

Run an external source expansion for the `k = 4` branch:
look beyond the current local repository record to see whether any source-backed theorem can

- discharge `import_targets.k4_exponent_order_target`, or
- bypass it by giving a direct dominance theorem strong enough to recover
  `import_targets.split_gap_k4_profile_dominance_target`.

## Status

Progress: `████` `4 / 4`

## Research Question

```text
Is the current `k = 4` matched-profile blocker merely a local-record limitation,
or does the broader source record still stop at split data?
```

## Starting Point

- current blocker note:
  `NOTES_problem142_k4_checked_source_layer_audit_2026-03-09.md`
- current strong targets:
  - `import_targets.k4_exponent_order_target`
  - `import_targets.split_gap_k4_profile_dominance_target`
- current honest endpoint:
  split-only `k = 4`

## Milestones

1. `[x]` Freeze the exact `k = 4` blocker and the current local negative verdict.
   - current verdict:
     local checked source layer stops at split data

2. `[x]` Build the prioritized external source list.
   - include:
     - the exact Green-Tao upper source already cited locally,
     - later `k = 4` quantitative papers, if any,
     - any source giving explicit lower/upper exponent comparison or direct profile dominance
   - note: `NOTES_problem142_k4_external_source_expansion_audit_2026-03-09.md`

3. `[x]` Audit theorem-level statements against the exact blocker.
   - allowed positive outcomes:
     - explicit exponent comparison,
     - direct `U_4 = O(L_4)`-type dominance,
     - or a corrected stronger source-backed target shape
   - outcome:
     corrected stronger source-backed target shape

4. `[x]` Produce a single route verdict.
   - allowed outcomes:
     - positive import target,
     - negative closure note,
     - or target correction
   - outcome: target correction
   - successor cycle:
     `PLAN_erdos_problem_142_k4_source_route_correction_2026-03-09.md`

## Current Verdict

```text
The external source pass is now complete.

No theorem-level exponent comparison or direct polylog-profile dominance source surfaced for
`k = 4`.

Instead, the primary-source record checked in this pass supports:
  - a Green--Tao polylogarithmic upper route,
  - and a Rankin/Behrend-type lower route.

So the correct result of this cycle is not matched-profile reopening.
It is a target correction to a heterogeneous source-backed split route.
```

## Audit Note

- `NOTES_problem142_k4_external_source_expansion_audit_2026-03-09.md`

## Successor Cycle

- `PLAN_erdos_problem_142_k4_source_route_correction_2026-03-09.md`
