# Plan: Erdős #142 `k = 3` Bottleneck Theorem Generation

Date: 2026-03-09

## Objective

If the `k = 4` external source expansion does not reopen a route, generate one new local
theorem-level target from the `k = 3` bottleneck analysis that would have measurable downstream
effect on the current barrier program.

## Status

Progress: `████` `4 / 4`

## Generation Question

```text
What is the smallest honest theorem statement, extracted from the current `k = 3` bottleneck
analysis, whose proof or source import would actually change the repository's route profile?
```

## Starting Point

- bottleneck note:
  `NOTES_problem142_k3_upper_bottleneck_audit_2026-03-08.md`
- current hold state:
  `NOTES_problem142_k3_matched_profile_hold_2026-03-09.md`
- current honest endpoint:
  the `β = 1 / 12` split route

## Milestones

1. `[x]` Freeze the bottleneck-derived route-generation objective.
   - do not revive the old matched-profile route directly

2. `[x]` Extract one exact theorem candidate from the bottleneck note.
   - examples of acceptable form:
     - sharper almost-periodicity-to-structure theorem,
     - better integer transfer statement,
     - or earlier contradiction/endgame theorem with quantified downstream effect
   - note:
     `NOTES_problem142_k3_bootstrap_one_eighth_theorem_candidate_2026-03-09.md`

3. `[x]` State the measurable repository consequence of that theorem.
   - what barrier claim, split route, or reopen condition would change if proved
   - consequence:
     local `1 / 8` split upgrade becomes live, but matched-profile reopen still does not follow

4. `[x]` Decide whether the candidate is a live theorem-generation program or should be deferred.
   - outcome:
     live, but only as a scoped local `1 / 8` theorem-generation program
   - successor:
     `PLAN_erdos_problem_142_k3_bootstrap_one_eighth_theorem_program_2026-03-09.md`

## Current Verdict

```text
Track B is now active in a scoped form.
The exact live target is a sharper `k = 3` bootstrapping theorem that propagates `1/9` to `1/8`,
without reviving the old matched-profile route.
```
