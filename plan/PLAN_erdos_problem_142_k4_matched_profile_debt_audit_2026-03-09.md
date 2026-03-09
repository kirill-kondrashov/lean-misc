# Plan: Erdős #142 `k = 4` Matched-Profile Debt Audit

Date: 2026-03-09

## Objective

Run the next source-first audit on the highest-leverage remaining matched-profile debt:
decide whether the current `k = 4` exponent-order / profile-dominance target is

- an honest source-backed missing theorem,
- an audited negative route,
- or a mis-specified target.

## Status

Progress: `████` `4 / 4`

## Audit Question

```text
After separating the source-backed split package from the stronger matched-profile closure,
what is the honest mathematical status of
  `import_targets.k4_exponent_order_target`
and
  `import_targets.split_gap_k4_profile_dominance_target`?
```

## Starting Point

- prior local audit: `NOTES_problem142_k4_source_audit_2026-03-07.md`
- prior pivot: `PLAN_erdos_problem_142_k4_source_backed_pivot_2026-03-07.md`
- revised-program reason for this cycle:
  the `k >= 5` family target has now been corrected away as an active source-backed debt

## Milestones

1. `[x]` Freeze the exact debt and the prior local negative verdict.
   - exact targets:
     - `import_targets.k4_exponent_order_target`
     - `import_targets.split_gap_k4_profile_dominance_target`
   - prior local verdict:
     split route live, matched-profile route not source-backed

2. `[x]` Reconstruct the exact `k = 4` source-facing theorem target.
   - distinguish:
     - source-backed split data already present,
     - exponent-order / profile-dominance still missing
   - note: `NOTES_problem142_k4_matched_profile_target_reconstruction_2026-03-09.md`

3. `[x]` Audit whether the checked source layer supports the minimal sufficient comparison.
   - target shape:
     `cL <= cU`
   - acceptable substitute:
     any equivalent comparison strong enough to discharge
     `import_targets.k4_exponent_order_target`
   - note: `NOTES_problem142_k4_checked_source_layer_audit_2026-03-09.md`

4. `[x]` Produce a single verdict and repoint the revised program.
   - allowed outcomes:
     - audited positive import target,
     - audited negative verdict keeping the split-only route,
     - or target correction if the current matched-profile statement is itself wrong
   - outcome: audited negative verdict
   - successor cycle: `PLAN_erdos_problem_142_k3_matched_profile_hold_2026-03-09.md`

## Current Verdict

```text
The checked source layer confirms the March 7 local verdict.

`LiteratureLowerImportAssumptions` supplies enough to build the honest split package, but the
matched-profile closure still sits behind the extra debt-carrying class
`LiteratureK4ExponentOrderAssumptions`.

No theorem in the checked source layer derives that exponent-order assumption from the sourced
upper and lower inputs already present.

So the audit result is negative:
the active honest `k = 4` endpoint remains split strength, not matched-profile closure.
```

## Audit Note

- `NOTES_problem142_k4_checked_source_layer_audit_2026-03-09.md`

## Successor Plan

- `PLAN_erdos_problem_142_k3_matched_profile_hold_2026-03-09.md`
