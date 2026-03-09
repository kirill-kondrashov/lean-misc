# Notes: `k = 4` Checked Source-Layer Audit

Date: 2026-03-09

## Objective

Decide whether the currently checked source-facing layer really supports the minimal comparison
needed to close the strong `k = 4` matched-profile target.

## Exact Strong Target

The strong route under audit is:

- `import_targets.k4_exponent_order_target`
- `import_targets.split_gap_k4_profile_dominance_target`

This is the extra comparison layer turning split upper/lower data into one matched-profile
dominance theorem.

## Checked Source-Layer Facts

### A. What the checked sourced layer does provide

The checked literature layer contains:

- sourced upper-side input through `LiteratureAssumptions.k4_upper_green_tao`
- sourced rate-side upper packaging through `LiteratureRateAssumptions.k4_polylog_upper_profile`
- lower split-side input only through the import-facing layer
  `LiteratureLowerImportAssumptions.k4_polylog_lower_profile`

From that, the repository already builds the honest split route:

- `k4SourceBackedSplitWitness_of_literatureLowerImportAssumptions`
- `K4SourceBackedSplitGap`
- `k4_split_data_of_literatureLowerImportAssumptions`

So the branch already has:

```text
L_4(N) = O(r_4(N))
r_4(N) = O(U_4(N)).
```

### B. What the checked sourced layer does not provide

The matched-profile closure still needs the exponent-comparison target

```text
`cL <= cU`
```

as packaged by `import_targets.k4_exponent_order_target`.

But the repository records that comparison only in the stronger extra class

- `LiteratureK4ExponentOrderAssumptions`

which strictly extends `LiteratureLowerImportAssumptions`.

Theorems such as

- `k4_exponent_order_target_of_literatureK4ExponentOrderAssumptions`
- `split_gap_k4_profile_dominance_target_of_literatureK4ExponentOrderAssumptions`

show that the extra class is sufficient.
They do not show that it is source-backed from the already checked layer.

## Audit Verdict

```text
Outcome: audited negative verdict.

The checked source-facing layer supports the split package for `k = 4`,
but it does not support the exponent-comparison step needed for
`import_targets.split_gap_k4_profile_dominance_target`.
```

So the honest mathematical status remains:

```text
proved:   split data
missing:  matched-profile dominance
blocked:  no checked source-backed route to `import_targets.k4_exponent_order_target`
```

## Program Consequence

The `k = 4` matched-profile branch should stay classified as blocked, not live positive progress.

The next research-program action should therefore follow the debt-ledger recommendation for rank 3:

```text
put the `k = 3` strengthening route on explicit hold unless genuinely new source evidence appears
```
