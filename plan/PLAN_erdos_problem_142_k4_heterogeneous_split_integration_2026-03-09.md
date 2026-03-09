# Plan: Erdős #142 `k = 4` Heterogeneous Split Integration

Date: 2026-03-09

## Objective

Redesign the repository's `k = 4` branch so the final source-backed route matches the corrected
broader-source shape:

- Green--Tao polylogarithmic upper,
- O'Bryant/Rankin `sqrt(log N)`-type lower,
- and no matched-profile coupling claim.

## Status

Progress: `████` `4 / 4`

## Integration Question

```text
How should the existing `k = 4` polylog-lower placeholder surfaces be replaced by a corrected
heterogeneous split package without breaking the honest current repository state?
```

## Starting Point

- route shape:
  `NOTES_problem142_k4_source_route_shape_2026-03-09.md`
- repository consequence:
  `NOTES_problem142_k4_repository_consequence_2026-03-09.md`
- exact lower target:
  `NOTES_problem142_k4_lower_shape_extraction_2026-03-09.md`

## Milestones

1. `[x]` Freeze the corrected upper/lower target shapes.

2. `[x]` Design the replacement `k = 4` source-facing target names and witness surfaces.
   - lower target
   - lower witness
   - split package
   - note: `NOTES_problem142_k4_heterogeneous_split_integration_design_2026-03-09.md`

3. `[x]` Decide how the old polylog-lower `k = 4` surfaces are retained.
   - legacy/off-path placeholder,
   - or deleted/replaced if safe
   - verdict:
     retain temporarily as legacy/local-placeholder surfaces

4. `[x]` Decide the exact Lean edit set for the redesign.
   - note: `NOTES_problem142_k4_heterogeneous_split_integration_design_2026-03-09.md`
   - successor cycle:
     `PLAN_erdos_problem_142_k4_heterogeneous_split_lean_redesign_2026-03-09.md`

## Current Verdict

```text
The integration-design cycle is now complete.

The corrected `k = 4` route now has:
  - a replacement naming scheme,
  - a retention policy for the old placeholder surfaces,
  - and an exact Lean edit set.

The next cycle should therefore edit Lean directly.
```

## Design Note

- `NOTES_problem142_k4_heterogeneous_split_integration_design_2026-03-09.md`

## Successor Cycle

- `PLAN_erdos_problem_142_k4_heterogeneous_split_lean_redesign_2026-03-09.md`
