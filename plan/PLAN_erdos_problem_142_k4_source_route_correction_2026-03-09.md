# Plan: Erdős #142 `k = 4` Source-Route Correction

Date: 2026-03-09

## Objective

Replace the currently misaligned `k = 4` matched/polylog route by the honest broader-source route:

- Green--Tao upper control on a polylogarithmic scale,
- Rankin/Behrend-type lower control on a subexponential `sqrt(log N)` scale,
- and no claim of a common matched profile.

## Status

Progress: `████` `4 / 4`

## Correction Question

```text
How should the repository re-state the `k = 4` branch now that the broader source record supports
an upper/lower shape mismatch rather than a common polylogarithmic profile?
```

## Starting Point

- external audit:
  `NOTES_problem142_k4_external_source_expansion_audit_2026-03-09.md`
- current misaligned strong targets:
  - `import_targets.k4_exponent_order_target`
  - `import_targets.split_gap_k4_profile_dominance_target`
- current local split placeholder:
  `import_targets.k4_polylog_lower_profile`

## Milestones

1. `[x]` Freeze the external audit verdict.
   - outcome:
     target correction

2. `[x]` State the corrected source-backed `k = 4` route shape precisely.
   - upper:
     Green--Tao polylogarithmic upper
   - lower:
     Rankin/Behrend-type lower
   - route type:
     heterogeneous split, not matched profile
   - note: `NOTES_problem142_k4_source_route_shape_2026-03-09.md`

3. `[x]` Identify the repository consequence.
   - what existing `k = 4` target should be frozen as off-path,
   - and what corrected source-backed surface should replace it
   - note: `NOTES_problem142_k4_repository_consequence_2026-03-09.md`

4. `[x]` Decide whether this corrected route is ready for Lean-side integration
   or needs one more source-shape note first.
   - verdict:
     needs one more source-shape extraction step before Lean redesign
   - successor cycle:
     `PLAN_erdos_problem_142_k4_lower_shape_extraction_2026-03-09.md`

## Current Verdict

```text
The `k = 4` route correction cycle is now complete.

The repository consequence is clear:
the current polylog-lower `k = 4` source-backed surfaces are no longer honest as final endpoints
for the broader-source route.

But the route is still not ready for Lean redesign, because one exact lower-shape extraction step
is needed before replacing those surfaces with a corrected heterogeneous split package.
```

## Consequence Note

- `NOTES_problem142_k4_repository_consequence_2026-03-09.md`

## Successor Cycle

- `PLAN_erdos_problem_142_k4_lower_shape_extraction_2026-03-09.md`
