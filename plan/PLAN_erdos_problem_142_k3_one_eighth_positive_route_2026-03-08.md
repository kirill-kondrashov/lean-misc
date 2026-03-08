# Plan: `k = 3` Explicit `1/8` Positive Route

Date: 2026-03-08

## Objective

Treat the explicit `1/8` upper theorem as the active positive `k = 3` target after the
post-Behrend pivot.

Target theorem:

```math
\exists c>0,\ \exists C>0,\quad
r_3(N)=O\!\left(C\,N\exp\!\bigl(-c(\log(N+2))^{1/8}\bigr)\right).
```

## Status

Progress: `██████` `6 / 6`

## Milestones

1. `[x]` State the exact `1/8` target in Lean.
   - `bound_targets.k3_superpolylog_upper_profile_one_eighth`

2. `[x]` Add the literature-side wrapper and extracted witness.
   - `LiteratureK3OneEighthSourceAssumptions`
   - imported witness at `β = 1/8`

3. `[x]` Add a theorem-level branch endpoint for the `1/8` route.
   - `erdos_142_three_source_backed_split_one_eighth`
   - `erdos_142_three_source_backed_split_one_eighth_of_literatureK3OneEighthSourceAssumptions`

4. `[x]` Audit whether an actual published `1/8` theorem exists, or whether it remains only a
   source-suggested omitted optimization.
   - note: `NOTES_problem142_k3_one_eighth_source_audit_2026-03-08.md`
   - verdict: no audited published `1/8` theorem found; current evidence is only an omitted
     optimization remark around the Bloom--Sisask `1/9` paper

5. `[x]` Decide whether the active positive route is an import route or only a conjectural target.
   - verdict: conjectural/import-only target

6. `[x]` If the `1/8` theorem is not source-backed, pivot to the negative/bottleneck route as the
   primary active theorem program.
   - primary follow-up: `NOTES_problem142_k3_negative_bottleneck_target_2026-03-08.md`
   - Lean consequence: keep the `1/8` objects only as optional scaffolding; do not treat them as
     active source-backed closure machinery

## Current Verdict

```text
The repository is structurally ready for an explicit `1/8` import if one is ever source-backed.
As of 2026-03-08, that theorem is not supported by the audited published sources checked here.
Therefore the `1/8` route remains conjectural scaffolding, and the primary active theorem program
should pivot to the negative/bottleneck route.
```
