# Notes: Erdős #142 `k = 3` Varnavides Scale Benchmark Verdict

Date: 2026-03-09

## Objective

Decide the exact repository-facing target shape, choose the first benchmark subscale input, and
determine whether the conditional density-transport route actually opens a new theorem debt.

## Repository-Facing Target Shape

The next honest target is **not** another abstract wrapper theorem.

Reason:

- `import_targets.k3_varnavides_extremal_transport_target` already records the generic reduction;
- introducing one more generic "`δ(M)`-transport" wrapper would only rename the same inequality;
- the real remaining mathematical content is now the scale benchmark:

```text
what concrete upper input at scale M produces a genuinely smaller debt at scale N?
```

So the correct repository-facing shape for this cycle is:

```text
a benchmark-specialized conditional density-transport verdict note,
not a new public theorem surface and not a new generic import wrapper.
```

## First Benchmark Input

The first benchmark input should be the existing explicit local scaffold

```text
bound_targets.k3_superpolylog_upper_profile_one_eighth.
```

This is the right first benchmark because it is already the sharpest explicit `k = 3` upper-profile
shape present in the repository, even though it remains conjectural/import-only.

For comparison, the checked source-backed benchmark

```text
bound_targets.k3_superpolylog_upper_profile_one_twelfth
```

has the same transport geometry, only with exponent `1 / 12` instead of `1 / 8`.

## Scale Calculation

Assume the benchmark input has the explicit form

```text
r3(M) ≤ C M exp(-c (log M)^(1 / 8)).
```

Then the imported Varnavides transport gives

```text
r3(N) ≤ (C exp(-c (log M)^(1 / 8)) + 1 / M) N
```

for `1 ≤ M ≤ N`, up to the obvious cast formatting.

Now choose a proper subscale

```text
M = exp((log N)^θ),   0 < θ < 1.
```

Then the transported bound becomes

```text
r3(N) ≤ N (C exp(-c (log N)^(θ / 8)) + exp(-(log N)^θ)).
```

So the decisive transported exponent is

```text
θ / 8.
```

The same computation with the source-backed `1 / 12` benchmark gives transported exponent

```text
θ / 12.
```

## Consequence

This benchmark calculation has one clean conclusion:

- any proper subscale choice strictly degrades the exponent;
- preserving exponent `1 / 8` forces `θ = 1`, which means `M` is essentially on the original
  scale `N`;
- that same-scale choice does not create a smaller theorem debt than the benchmark upper theorem
  itself.

So the conditional density-transport route is mathematically correct, but under the currently
available benchmark inputs it does **not** open a new direct theorem route.

## Verdict

```text
Close the current conditional density-transport cycle.

Keep the imported Varnavides extremal transport as a valid reduction object, but do not open a new
implementation chain from it under the current benchmark set.
```
