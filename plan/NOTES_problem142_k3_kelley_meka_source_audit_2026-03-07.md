# Notes: Erdős #142 `k=3` Kelley-Meka Source Audit (2026-03-07)

## Objective

Determine whether the current Kelley-Meka source can justify the strengthened source-facing target
`bound_targets.k3_superpolylog_upper_profile_gt_half`, which would be enough to remove the
remaining `k=3` non-base frontier item.

## Source Used

- Kelley, Z.; Meka, R., *Strong Bounds for 3-Progressions*, arXiv:2302.05537
  - abstract page: <https://arxiv.org/abs/2302.05537>
  - source downloaded locally from arXiv `e-print`

## Relevant Statements From The Source

1. Abstract and Theorem `3-progs`
   - the paper states only that there is some absolute constant exponent `β > 0` such that
     progression-free sets have density at most `2^{-Ω((log N)^β)}`.
   - This does not provide any support for `β > 1 / 2`.

2. Theorem `many-3-progs`
   - if `A ⊆ [N]` has density at least `2^{-d}`, then the number of triples
     `(x, y, z) ∈ A^3` with `x + y = 2z` is at least `2^{-O(d^12)} N^2`.

## Derived Quantitative Consequence

To force a nontrivial 3-progression from `many-3-progs`, it is enough that

```text
2^{-O(d^12)} N^2 > N,
```

since there are at most `N` trivial progressions.

Equivalently, for sufficiently small absolute `c > 0`, it suffices that

```text
d <= c * (log N)^(1/12).
```

So the current source-backed upper-profile consequence has the shape

```text
|A| >= N * 2^{-O((log N)^(1/12))}.
```

This corresponds to an explicit source-backed exponent regime

```text
β = 1 / 12.
```

## Verdict

- Source-backed and compatible with the current weaker target:
  - `bound_targets.k3_superpolylog_upper_profile`
- Not source-backed by the current Kelley-Meka extraction:
  - `bound_targets.k3_superpolylog_upper_profile_gt_half`

Therefore the current `k=3` frontier-elimination route that requires `β > 1 / 2` cannot be
closed from the presently extracted Kelley-Meka theorem shape.

## Consequence For The Lean Plan

The `β > 1 / 2` comparison route is now audited to failure for the current source extraction:

- the Lean-side coupling/comparison machinery is complete;
- the missing issue is no longer “find the right source statement”;
- the actual source-backed exponent visible from the paper is too weak for that route.

So the next honest research direction is not to keep chasing
`splitGap_k3_upper_exponent_gt_half_frontier` from Kelley-Meka.
It is to redesign the `k=3` frontier around a source-backed exponent regime such as `β = 1/12`,
or to find a different coupling argument that does not require `β > 1 / 2`.
