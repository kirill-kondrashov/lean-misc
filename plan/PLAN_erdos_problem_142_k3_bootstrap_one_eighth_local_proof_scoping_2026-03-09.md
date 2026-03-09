# Plan: Erdős #142 `k = 3` Bootstrap `1 / 8` Local-Proof Scoping

Date: 2026-03-09

## Objective

Turn the live local `1 / 8` theorem target into a proof-scoped program by isolating the exact
strengthened lemma interface needed in the almost-periodicity-to-structure step.

## Status

Progress: `████` `4 / 4`

## Scoping Question

```text
What is the exact strengthened lemma, stated close to the present architecture,
whose proof would realize the `O(L^5)` / `exp(-O(d_j L + L^6))` recurrence replacement?
```

## Starting Point

- theorem-candidate note:
  `NOTES_problem142_k3_bootstrap_one_eighth_theorem_candidate_2026-03-09.md`
- scope note:
  `NOTES_problem142_k3_bootstrap_one_eighth_program_scope_2026-03-09.md`
- bottleneck audit:
  `NOTES_problem142_k3_upper_bottleneck_audit_2026-03-08.md`

## Milestones

1. `[x]` Freeze the local-proof-only scope.

2. `[x]` Name the exact strengthened lemma interface.
   - rank increment improvement
   - local size-loss improvement
   - unchanged density increment
   - note:
     `NOTES_problem142_k3_bootstrap_one_eighth_lemma_interface_2026-03-09.md`

3. `[x]` State the minimal Lean-facing consequence of that lemma.
   - which existing `1 / 8` wrappers can be reused directly
   - what new local theorem, if any, would still be needed

4. `[x]` Decide whether the local-proof decomposition is concrete enough to stay active.
   - outcome:
     active
   - successor:
     `PLAN_erdos_problem_142_k3_bootstrap_one_eighth_lemma_target_2026-03-09.md`

## Current Verdict

```text
The route is concrete enough to stay active.
The next honest narrowing is lemma-first:
freeze the exact strengthened bootstrap lemma target before attempting the separate
recurrence-closing `1 / 8` theorem.
```
