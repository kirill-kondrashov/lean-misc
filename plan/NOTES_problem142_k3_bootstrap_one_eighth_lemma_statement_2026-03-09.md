# Notes: Erdős #142 `k = 3` Bootstrap `1 / 8` Lemma Statement

Date: 2026-03-09

## Objective

State the strengthened bootstrap lemma as an exact input/output target and separate it from the
later recurrence-closing theorem.

## Exact Input/Output Shape

The improved lemma should be stated at one density-increment step.

### Input

- a regular ambient Bohr set `B` of rank `d`
- a subset `A ⊆ B` of relative density `α`
- the same almost-periodicity / few-progressions hypotheses currently used in the modern
  Kelley--Meka / Bloom--Sisask integer-case step
- the derived scale parameter

```text
L := log(2 / α)
```

### Output

- a successor regular Bohr set `B'`
- a densified translate/restriction `A' ⊆ B'`

with quantitative conclusions

```text
rk(B') ≤ d + C1 L^5
|B'| ≥ exp(-C2 (d L + L^6)) |B|
density(A' in B') ≥ (1 + c) α
```

for absolute positive constants `C1`, `C2`, `c`.

## Boundary With The Recurrence-Closing Theorem

### The lemma gives directly

- one improved structural step
- one improved rank increment bound
- one improved local size-loss bound
- one unchanged multiplicative density increment

### The lemma does not give directly

- the full `O(L)`-step recurrence solution
- the final estimate `|B_m| ≥ exp(-O(L^8)) N`
- the explicit upper theorem

```math
r_3(N) \ll N \exp(-c (\log N)^{1/8})
```

Those belong to the separate recurrence-closing theorem.

## Lemma-First Verdict

```text
The lemma target is now mathematically separable from the recurrence-closing theorem.
So the `1 / 8` route can continue in lemma-first form without conflating the two debts.
```
