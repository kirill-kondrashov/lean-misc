# Notes: `k >= 5` Target Correction

Date: 2026-03-09

## Objective

Replace the mis-specified active `k >= 5` family debt with the corrected statement forced by the
March 8 audit and the March 7 source-backed pivot.

## Old Active Debt To Kill

The following targets should no longer be treated as live source-backed missing theorems:

- `import_targets.kge5_exponent_order_target`
- `import_targets.split_gap_kge5_profile_dominance_target`

Reason:

```text
the current target compares iterated-log family templates,
but the publication-backed upper family scale is stretched-exponential in log log N.
```

So the issue is not merely "proof missing". The active family target itself is mis-specified.

## Corrected `k >= 5` Status

### A. What remains live and source-backed

The honest positive route is still the March 7 split pivot:

- `PLAN_erdos_problem_142_kge5_source_backed_pivot_2026-03-07.md`

That route already did the mathematically correct thing:

- treat `k = 5` as the live source-backed toy-model branch;
- use the stretched-exponential upper scale and Rankin-type lower scale exactly as split data;
- avoid claiming a common matched profile for the whole fixed-`k >= 5` family.

### B. What remains off-path

The old iterated-log matched-profile family route can remain in the repository only as a legacy,
explicitly non-source-backed placeholder.

It may be reopened only if a source-backed theorem appears with a genuinely compatible family
shape. Without that, it should not be counted as a live active debt in the revised program.

## Program Consequence

After this correction, the `k >= 5` family debt is no longer the next active source-first audit
target.

The next ranked live debt is:

```text
`k = 4` matched-profile / exponent-order debt
```

That is now the right place to spend the next audit cycle.

## Verdict

```text
Outcome: target corrected.

The `k >= 5` family matched-profile theorem is no longer an active source-backed missing target.
The active honest route is split-only; the stronger family matched-profile route is frozen as
speculative unless new compatible source input appears.
```
