# Plan: Erdős #142 `k = 3` Quantitative Varnavides Import Route

Date: 2026-03-09

## Objective

Turn the extracted quantitative Varnavides reduction into a concrete repository-facing direct
counting route for `k = 3`.

## Status

Progress: `████` `4 / 4`

## Route Question

```text
Can the source-backed quantitative Varnavides reduction be integrated cleanly enough to define one
exact direct-counting theorem chain below the full direct `1 / 8` theorem?
```

## Starting Point

- extraction audit:
  `NOTES_problem142_post_dormancy_trackA_quantitative_varnavides_audit_2026-03-09.md`
- dormant direct-counting endpoint:
  `PLAN_erdos_problem_142_k3_direct_counting_one_eighth_target_2026-03-09.md`

## Milestones

1. `[x]` Freeze the exact extracted reduction theorem.
   - source: Croot--Sisask Lemma 3.1

2. `[x]` Decide the repository-facing layer for this theorem.
   - direct source import target, not gap-layer theorem surface
   - note: `NOTES_problem142_k3_quantitative_varnavides_route_shape_2026-03-09.md`

3. `[x]` Determine the first downstream direct-counting consequence worth targeting.
   - for example: a direct supersaturation theorem driven by existing subscale upper control
   - selected: the extremal transport inequality for `r_3`
   - note: `NOTES_problem142_k3_quantitative_varnavides_route_shape_2026-03-09.md`

4. `[x]` Produce the route verdict.
   - either open one narrower implementation/import chain
   - or close this route if the extracted theorem still does not localize the next debt enough
   - outcome: open the extremal-transport encoding chain
   - successor: `PLAN_erdos_problem_142_k3_varnavides_extremal_transport_encoding_2026-03-09.md`

## Current Verdict

```text
Complete.

The route is now localized:
the first repository-facing Varnavides object is the literature-layer extremal transport target for
`r_3`, rather than the raw progression-count formula.

The active successor cycle is now
`PLAN_erdos_problem_142_k3_varnavides_extremal_transport_encoding_2026-03-09.md`.
```
