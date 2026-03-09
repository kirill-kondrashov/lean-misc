# Notes: `k = 4` Lower-Shape Extraction

Date: 2026-03-09

## Objective

Freeze one exact formal lower-target template for the corrected `k = 4` source-backed route.

## Source Basis

Primary lower source:

- O'Bryant, *Sets of integers that do not contain long arithmetic progressions*,
  Electron. J. Combin. 18 (2011), P59.
  - journal page:
    https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p59

The abstract and statement summary on the journal page give a general lower family depending on

```text
n = ceil(log_2 k).
```

For `k = 4`, this specializes to

```text
n = 2.
```

Inference:
the lower side can be specialized to a `sqrt(log N)`-scale Rankin/O'Bryant shape with an
additional `log log N` correction term.

## Exact Formal Shape To Use

The repository should model the corrected `k = 4` lower source target on the same style already
used for `k = 5`, but specialized to the `k = 4` exponent:

```text
∃ A B C : ℝ, 0 < A ∧ 0 < C ∧
  (fun N =>
    C * N * exp(-A * sqrt(log(N+2)) + B * log(log(N+2))))
    =O(r 4 N).
```

This is more precise than a coarse Behrend-only placeholder and still compatible with the existing
repository pattern for O'Bryant-type lower routes.

## Why This Shape, Not The Old Polylog Placeholder

The old `k4_polylog_lower_profile` placeholder has the wrong asymptotic family for the broader
source-backed route.

The O'Bryant-specialized `k = 4` lower side is:

- subexponential on the `sqrt(log N)` scale,
- not polylogarithmic,
- and naturally expressed with an additional `log log N` term.

So the right replacement is a specialized Rankin/O'Bryant lower target, not an exponent-order
comparison inside the old polylog family.

## Repository-Facing Design Consequence

The natural next design is:

- add a new source target such as `bound_targets.k4_rankin_obryant_lower_profile`,
- add the matching witness / imported-witness surfaces,
- keep `import_targets.k4_polylog_lower_profile` only as a local placeholder or legacy surface,
- and rebuild the `k = 4` branch as a heterogeneous split package.

## Sufficiency Verdict

```text
This lower-shape extraction is precise enough to begin Lean-side redesign.

The remaining work is no longer source-shape extraction.
It is repository integration.
```
