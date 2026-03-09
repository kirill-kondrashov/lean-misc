# Plan: Erdős #142 `k = 3` Bootstrap `1 / 8` Placeholder Surface Design

Date: 2026-03-09

## Objective

Design the repository-facing placeholder surfaces for the local `1 / 8` bootstrap lemma debt and
the separate recurrence-closing debt, without presenting either one as a proved theorem.

## Status

Progress: `████` `4 / 4`

## Design Question

```text
What exact placeholder names and layer boundaries should the repository use for:
1. the improved bootstrap lemma target, and
2. the separate recurrence-closing `1 / 8` upper theorem target?
```

## Starting Point

- lemma statement:
  `NOTES_problem142_k3_bootstrap_one_eighth_lemma_statement_2026-03-09.md`
- encoding decision:
  `NOTES_problem142_k3_bootstrap_one_eighth_lemma_encoding_decision_2026-03-09.md`
- scope note:
  `NOTES_problem142_k3_bootstrap_one_eighth_program_scope_2026-03-09.md`

## Milestones

1. `[x]` Freeze the encoding policy: placeholder surface only.

2. `[x]` Propose exact repository-facing names.
   - improved bootstrap lemma target
   - recurrence-closing target
   - optional combined local `1 / 8` debt package
   - note:
     `NOTES_problem142_k3_bootstrap_one_eighth_placeholder_surface_design_2026-03-09.md`

3. `[x]` Place those surfaces in the repo layering.
   - `Problem142.lean` target namespace
   - literature/import layer, if any
   - gap layer, if any

4. `[x]` Decide whether the surface design is clean enough to justify a later Lean encoding cycle.
   - outcome:
     yes
   - successor:
     `PLAN_erdos_problem_142_k3_bootstrap_one_eighth_placeholder_lean_encoding_2026-03-09.md`

## Current Verdict

```text
The surface design is now complete.
The next active question is whether to encode the new local placeholder target in Lean without
creating duplicate or misleading theorem surfaces.
```
