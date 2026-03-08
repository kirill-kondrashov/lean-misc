# Plan: `k = 3` Post-Behrend Pivot

Date: 2026-03-08

## Objective

Replace the no-longer-active Behrend-scale upper-bound route by an honest follow-up route.

The new active alternatives are:

1. prove an explicit improved upper bound of the form

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/8}\bigr),
```

along the present Kelley--Meka / Bloom--Sisask architecture; or

2. prove a negative/bottleneck statement showing that the present architecture cannot by itself
approach Behrend scale.

## Status

Progress: `██████` `6 / 6`

## Rationale

The strict Behrend-scale plan established:

```text
current architecture -> explicit recurrence -> current exponent 1/9
source-motivated local improvement -> propagated exponent 1/8
```

Therefore the present architecture is no longer treated as a live route to exponent `1/2`.

## Milestones

1. `[x]` Fix the pivot target: no longer `1/2`, now either explicit `1/8` or a negative theorem.
2. `[x]` State the exact `1/8`-type upper theorem target in repository notation.
   - Lean target: `bound_targets.k3_superpolylog_upper_profile_one_eighth`
3. `[x]` State the exact negative/bottleneck theorem target in mathematical notation.
   - note: `NOTES_problem142_k3_negative_bottleneck_target_2026-03-08.md`
4. `[x]` Decide which of the two targets is more realistic from the current source evidence.
   - verdict: the explicit `1/8` target is the more realistic positive theorem target, because the source explicitly indicates this omitted refinement
5. `[x]` Record the chosen target as the active `k = 3` route.
   - active positive route: explicit `1/8` theorem
   - parallel meta route: negative/bottleneck theorem
6. `[x]` Start implementing that route in notes/Lean scaffolding.
   - Lean scaffolding added in `Problem142.lean` and `Problem142Literature.lean` for the `β = 1/8` target

## Current Verdict

```text
The live question is no longer “can this architecture prove Behrend scale?”.
It is “what is the strongest honest theorem this architecture can plausibly support next?”.
```

## Post-Audit Update

The follow-up audit in
`PLAN_erdos_problem_142_k3_one_eighth_positive_route_2026-03-08.md`
and
`NOTES_problem142_k3_one_eighth_source_audit_2026-03-08.md`
found no audited published `1/8` theorem. So the positive `1/8` route remains conjectural
scaffolding, while the primary active theorem program pivots to the negative/bottleneck route.

Active follow-up plan:

- `PLAN_erdos_problem_142_k3_negative_bottleneck_program_2026-03-08.md`
- `NOTES_problem142_k3_negative_template_escape_critic_2026-03-08.md`

Program reset after the packaging/regression chain:

- `PLAN_erdos_problem_142_revised_research_program_2026-03-08.md`
- `NOTES_problem142_research_program_critique_2026-03-08.md`
