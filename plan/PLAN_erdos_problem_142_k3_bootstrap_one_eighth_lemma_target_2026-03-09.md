# Plan: Erdős #142 `k = 3` Bootstrap `1 / 8` Lemma Target

Date: 2026-03-09

## Objective

Freeze the exact mathematical statement of the improved almost-periodicity -> structured-Bohr-set
bootstrap lemma that would drive the local `1 / 8` route.

## Status

Progress: `████` `4 / 4`

## Target Question

```text
What is the exact lemma statement, as close as possible to the present architecture,
whose proof would deliver the O(L^5) rank increment and exp(-O(dL + L^6)) size-loss step?
```

## Starting Point

- lemma-interface note:
  `NOTES_problem142_k3_bootstrap_one_eighth_lemma_interface_2026-03-09.md`
- theorem-candidate note:
  `NOTES_problem142_k3_bootstrap_one_eighth_theorem_candidate_2026-03-09.md`
- recurrence extraction:
  `NOTES_problem142_k3_upper_recurrence_extraction_2026-03-08.md`

## Milestones

1. `[x]` Freeze the lemma-first narrowing.

2. `[x]` Separate the exact input/output data of the strengthened lemma.
   - ambient regular Bohr set data
   - almost-periodicity hypotheses
   - rank increment bound
   - size-loss bound
   - density increment conclusion
   - note:
     `NOTES_problem142_k3_bootstrap_one_eighth_lemma_statement_2026-03-09.md`

3. `[x]` State the exact boundary between the lemma and the recurrence-closing theorem.
   - what the lemma gives directly
   - what still belongs to the `1 / 8` upper theorem

4. `[x]` Decide whether the lemma target is precise enough to encode as a repository-facing
   theorem or placeholder surface.
   - decision:
     placeholder surface, not theorem surface
   - note:
     `NOTES_problem142_k3_bootstrap_one_eighth_lemma_encoding_decision_2026-03-09.md`
   - successor:
     `PLAN_erdos_problem_142_k3_bootstrap_one_eighth_placeholder_surface_design_2026-03-09.md`

## Current Verdict

```text
The improved bootstrap step is now precise enough to encode, but only as a placeholder surface.
The next active task is to design that surface without overstating theorem progress.
```
