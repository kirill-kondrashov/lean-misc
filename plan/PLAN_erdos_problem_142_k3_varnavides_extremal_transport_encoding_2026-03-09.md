# Plan: Erdős #142 `k = 3` Varnavides Extremal-Transport Encoding

Date: 2026-03-09

## Objective

Encode the first repository-facing consequence of the quantitative Varnavides theorem:
the extremal transport inequality for `r_3`.

## Status

Progress: `█---` `1 / 4`

## Encoding Question

```text
Can the literature/import layer expose the Varnavides extremal-transport target cleanly enough to
support one narrower direct-counting consequence, without pulling in a full progression-count API?
```

## Starting Point

- route-shape note:
  `NOTES_problem142_k3_quantitative_varnavides_route_shape_2026-03-09.md`
- quantitative Varnavides route:
  `PLAN_erdos_problem_142_k3_quantitative_varnavides_import_route_2026-03-09.md`

## Milestones

1. `[x]` Freeze the repository-facing layer and first downstream consequence.
   - literature/import layer
   - extremal transport target

2. `[ ]` Encode the import-facing extremal transport target cleanly.
   - avoid introducing a new `T3(A)` API

3. `[ ]` Decide the next narrower direct-counting consequence.
   - likely a conditional direct density transport from subscale upper control

4. `[ ]` Produce the encoding verdict.
   - either keep building this route
   - or close it if even the transport layer remains too coarse

## Current Verdict

```text
The active work is now concrete:
integrate the source-backed transport inequality as the first repo-facing Varnavides object.
```
