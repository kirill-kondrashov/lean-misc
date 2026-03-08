# Plan: Erdős #142 `k >= 5` Matched-Profile Debt Audit

Date: 2026-03-08

## Objective

Run the first source-first audit selected by the revised research program:
determine whether the current `k >= 5` matched-profile family debt is a real missing theorem or a
mis-specified target.

## Status

Progress: `████` `4 / 4`

## Audit Question

```text
Does the current literature support a family matched-profile target of iterated-log type for
fixed `k >= 5`, or does the source evidence instead force a different target shape?
```

## Candidate Outcomes

1. audited positive:
   - a real source-backed family target exists and should replace the current off-path debt

2. audited negative:
   - no such family target is source-backed, and the current debt should be killed explicitly

3. target correction:
   - the right family target exists, but it has a different scale from the current one

## Milestones

1. `[x]` Freeze the exact debt to audit.
   - current target family:
     `import_targets.kge5_exponent_order_target`
     and
     `import_targets.split_gap_kge5_profile_dominance_target`

2. `[x]` Re-audit the source-backed upper family scale for fixed `k >= 5`.
   - source verdict: the publication-backed family upper theorem is stretched-exponential in
     `log log N`, not iterated-log power type

3. `[x]` Compare that scale against the current matched-profile target family used in the repo.
   - verdict: the current family target is mis-specified as an active source-backed debt

4. `[x]` Record a decisive verdict:
   - salvage,
   - kill,
   - or target correction
   - current outcome: target correction with route kill for the old iterated-log matched-profile
     family target

## Current Verdict

```text
The audit result is not "missing proof of the current family target".
It is "the current `k >= 5` matched-profile family target is mis-specified relative to the
publication-backed upper scale".

So the correct next step is:
  kill the old iterated-log matched-profile family target as an active debt,
  and replace it by an explicitly corrected route statement.
```

## Audit Note

- `NOTES_problem142_kge5_matched_profile_debt_audit_2026-03-08.md`

## Successor Plan

- `PLAN_erdos_problem_142_kge5_target_correction_2026-03-08.md`
