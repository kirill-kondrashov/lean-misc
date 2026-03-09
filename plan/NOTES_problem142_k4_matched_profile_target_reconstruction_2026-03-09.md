# Notes: `k = 4` Matched-Profile Target Reconstruction

Date: 2026-03-09

## Objective

Freeze the exact theorem boundary for the new `k = 4` audit:
separate what is already source-backed at split strength from what still needs a genuine
matched-profile comparison theorem.

## Exact Strong Target Under Audit

The strong `k = 4` route in the repository is:

- `import_targets.k4_exponent_order_target`
- `import_targets.split_gap_k4_profile_dominance_target`

with the analytic bridge:

- `import_targets.k4_polylog_template_dominance_of_exponent_le`
- `import_targets.split_gap_k4_profile_dominance_target_of_exponent_order`

So the strong route is not "any upper/lower polylog control for `k = 4`".
It is specifically the comparison layer that turns split data into matched-profile dominance.

## Minimal Missing Comparison

The current sufficient input is the exponent-order statement

```text
`cL <= cU`
```

as packaged by `import_targets.k4_exponent_order_target`.

Any source-backed substitute used in this audit must be mathematically strong enough to discharge
that same comparison step.

## What Is Already Source-Backed At Split Strength

The repository already has an honest split package for `k = 4`:

- `K4SourceBackedSplitWitness`
- `k4SourceBackedSplitWitness_of_literatureLowerImportAssumptions`
- `K4SourceBackedSplitGap`
- `k4_split_data_of_literatureLowerImportAssumptions`

This means the audit is not re-deciding whether the branch has usable upper/lower profile data.
It already does.

## Audit Boundary

The source-first question is now sharply defined:

```text
Does any checked source-backed route actually justify the exponent comparison needed to pass from
the existing split package to
`import_targets.split_gap_k4_profile_dominance_target`?
```

If yes, the stronger matched-profile branch can be revived honestly.
If not, the honest endpoint remains the split package already present.

## Reconstruction Verdict

```text
The live `k = 4` debt is not missing split data.
It is missing a source-backed comparison theorem connecting the existing split data to the
matched-profile dominance target.
```
