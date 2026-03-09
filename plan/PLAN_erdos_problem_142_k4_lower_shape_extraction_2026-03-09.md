# Plan: Erdős #142 `k = 4` Lower-Shape Extraction

Date: 2026-03-09

## Objective

Extract one exact formal lower-target template for the corrected `k = 4` source-backed route,
precise enough to support a later Lean redesign.

## Status

Progress: `████` `4 / 4`

## Extraction Question

```text
What exact theorem shape should the repository use for the O'Bryant/Rankin-type `k = 4` lower
benchmark, so that the corrected heterogeneous split route can be integrated cleanly?
```

## Starting Point

- corrected route shape:
  `NOTES_problem142_k4_source_route_shape_2026-03-09.md`
- repository consequence:
  `NOTES_problem142_k4_repository_consequence_2026-03-09.md`
- analogous existing pattern:
  `bound_targets.k5_rankin_obryant_lower_profile`

## Milestones

1. `[x]` Freeze the need for an exact lower-shape extraction before Lean redesign.

2. `[x]` Decide the formal target family for `k = 4`.
   - options to resolve:
     - exact O'Bryant/Rankin general form with `(\log N)^α` and `\log\log N` term,
     - or a coarser Behrend-type specialization if that is all the source pass justifies
   - note: `NOTES_problem142_k4_lower_shape_extraction_2026-03-09.md`
   - outcome:
     specialized O'Bryant/Rankin `sqrt(log N)` lower target with `log log N` correction term

3. `[x]` State the repository-facing design consequence.
   - target name,
   - witness shape,
   - and whether old `k4_polylog_lower_profile` stays only as a local placeholder
   - note: `NOTES_problem142_k4_lower_shape_extraction_2026-03-09.md`

4. `[x]` Decide whether the resulting shape is sufficient to begin Lean-side route redesign.
   - verdict:
     yes
   - successor cycle:
     `PLAN_erdos_problem_142_k4_heterogeneous_split_integration_2026-03-09.md`

## Current Verdict

```text
The lower-shape extraction cycle is now complete.

The corrected `k = 4` lower route should be modeled as a specialized O'Bryant/Rankin
`sqrt(log N)` lower target with a `log log N` correction term, not as a polylog lower profile.

That is precise enough to begin Lean-side redesign of the `k = 4` branch as a heterogeneous split
package.
```

## Extraction Note

- `NOTES_problem142_k4_lower_shape_extraction_2026-03-09.md`

## Successor Cycle

- `PLAN_erdos_problem_142_k4_heterogeneous_split_integration_2026-03-09.md`
