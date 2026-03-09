# Plan: Erdős #142 Separated Method-Family Scouting

Date: 2026-03-09

## Objective

Run a quarantined scouting pass for a genuinely new method family, now that the current
theorem-construction family is exhausted.

## Status

Progress: `████` `4 / 4`

## Scouting Question

```text
Can the repository identify one theorem-shaped candidate route that is genuinely outside the
current split / matched-profile / density-increment-Bohr-transfer family?
```

## Starting Point

- fork-gate note:
  `NOTES_problem142_method_family_fork_gate_2026-03-09.md`
- completed route-generation program:
  `PLAN_erdos_problem_142_route_generation_program_2026-03-09.md`

## Milestones

1. `[x]` Launch the scouting branch only after a positive fork verdict.
   - the branch is quarantined and not yet theorem-facing

2. `[x]` Inventory admissible candidate families.
   - exclude all variants that recycle the current architecture
   - note: `NOTES_problem142_method_family_candidate_inventory_2026-03-09.md`

3. `[x]` Select at most one primary fork.
   - only if it yields one theorem-shaped extraction question
   - selected: direct `k = 3` counting / supersaturation bypass
   - note: `NOTES_problem142_method_family_primary_fork_selection_2026-03-09.md`

4. `[x]` Produce the scouting verdict.
   - either promote one candidate to its own theorem-generation chain
   - or close the fork and return to dormant status
   - outcome: promote candidate A
   - successor: `PLAN_erdos_problem_142_k3_direct_counting_route_generation_2026-03-09.md`

## Current Verdict

```text
Complete.

The scouting branch selected exactly one primary fork:
the direct `k = 3` counting / supersaturation bypass.

That candidate survives the fork standard because it is a direct theorem on `A ⊆ [N]`,
not a reformulation of the same recurrence endgame on the terminal structured set.

The active successor cycle is now
`PLAN_erdos_problem_142_k3_direct_counting_route_generation_2026-03-09.md`.
```
