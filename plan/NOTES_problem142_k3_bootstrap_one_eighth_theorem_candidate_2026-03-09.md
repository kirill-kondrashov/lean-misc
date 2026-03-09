# Notes: Erdős #142 `k = 3` Bootstrap `1 / 8` Theorem Candidate

Date: 2026-03-09

## Objective

Extract one exact theorem-shaped candidate from the existing `k = 3` bottleneck notes and state
its measurable repository consequence.

## Candidate Theorem

The smallest exact local target currently supported by the notes is:

```text
Sharpen the almost-period-set -> structured-Bohr-set bootstrapping step in the
Kelley--Meka / Bloom--Sisask integer-case iteration so that, with
L := log(2 / α),

  d_{j+1} ≤ d_j + O(L^5)

and

  |B_{j+1}| ≥ exp(-O(d_j L + L^6)) |B_j|,

while keeping the same multiplicative density increment

  α_{j+1} ≥ (1 + c) α_j.
```

This is the exact theorem-shaped replacement identified in:

- `NOTES_problem142_k3_upper_bottleneck_audit_2026-03-08.md`
- `NOTES_problem142_k3_upper_local_replacement_candidate_2026-03-08.md`

## Quantitative Consequence

Plugging that candidate into the extracted recurrence gives:

```text
d_m = O(L^6)
|B_m| ≥ exp(-O(L^8)) N
```

and therefore the upper bound

```math
r_3(N) \ll N \exp(-c (\log N)^{1/8}).
```

So the exact measurable effect is:

```text
improve the current propagated exponent from 1/9 to 1/8.
```

## Repository Consequence

If proved or honestly imported, this theorem would:

1. turn the current conjectural/import-only `1 / 8` surface into a live local theorem target;
2. justify a scoped upgrade of the active `k = 3` split route from the audited `β = 1 / 12`
   endpoint toward an explicit `β = 1 / 8` endpoint;
3. show that the present architecture still has one step of quantified local headroom.

It would **not** by itself:

1. satisfy the hold-note reopen condition for the matched-profile route;
2. recover `β > 1 / 2`;
3. make the Behrend-scale program credible inside the current architecture.

## Verdict

```text
This is a live theorem-generation target, but only as a scoped local split-improvement program.
It is not a direct reopen of the old matched-profile route.
```
