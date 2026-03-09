# Plan: Erdős #142 `k = 3` Bootstrap `1 / 8` Placeholder Lean Encoding

Date: 2026-03-09

## Objective

Encode the approved placeholder-surface design in Lean:
one new local bootstrap-step target, reuse of the existing explicit `1 / 8` upper target, and no
gap-layer export.

## Status

Progress: `████` `4 / 4`

## Encoding Question

```text
Can the repo encode the local bootstrap-step debt cleanly in `Problem142.lean`
without making it look like a realized theorem or duplicating the explicit `1 / 8` upper target?
```

## Starting Point

- design note:
  `NOTES_problem142_k3_bootstrap_one_eighth_placeholder_surface_design_2026-03-09.md`
- encoding decision:
  `NOTES_problem142_k3_bootstrap_one_eighth_lemma_encoding_decision_2026-03-09.md`
- existing explicit upper target:
  `bound_targets.k3_superpolylog_upper_profile_one_eighth`

## Milestones

1. `[x]` Freeze the approved placeholder design.

2. `[x]` Add the new local bootstrap-step placeholder target.
   - `Problem142.lean`
   - local-target namespace
   - clear non-theorem comment

3. `[x]` Reject the optional combined local `1 / 8` debt package as duplicative.
   - reuse `bound_targets.k3_superpolylog_upper_profile_one_eighth`
   - keep the new local debt surface separate

4. `[x]` Verify that the resulting Lean surface is honest and non-duplicative.
   - one new local target only
   - no theorem wrapper
   - no gap-layer export

## Current Verdict

```text
Complete.

`Problem142.lean` now contains exactly one new local theorem-debt placeholder:
`local_targets.k3_bootstrap_one_eighth_step_target`.

The optional combined package was rejected as redundant, because it would only restate the new
local debt together with the already existing explicit upper target
`bound_targets.k3_superpolylog_upper_profile_one_eighth`.

This cycle stayed below the realized theorem surface:
no literature wrapper, no gap export, and no theorem overclaim.
```
