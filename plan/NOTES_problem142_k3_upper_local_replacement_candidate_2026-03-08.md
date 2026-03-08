# Notes: `k = 3` Local Replacement Candidate For The Modern Upper-Bound Line (2026-03-08)

## Objective

State one exact local replacement theorem candidate for the modern Kelley--Meka / Bloom--Sisask
upper-bound architecture, and compute the final exponent it would imply when inserted into the
recurrence extracted in

- `NOTES_problem142_k3_upper_recurrence_extraction_2026-03-08.md`

## Recurrence Baseline

From the extracted current recurrence, with

```math
L := \log(2/\alpha),
```

the present integer-case argument has the coarse step sizes

```math
d_{j+1} \le d_j + O(L^6),
```

and

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^7)\bigr)|B_j|,
```

with `O(L)` density-increment steps.

This yields cumulative size loss

```math
|B_m| \ge \exp(-O(L^9))N,
```

hence final exponent `1/9`.

## Source-Motivated Replacement Candidate

Bloom--Sisask explain that their refined bootstrapping exploits additional structure to improve a
key finite-field quantity from an `\alpha^4`-type loss to an `\alpha^3`-type loss, and they also
remark that a more careful treatment of the same step could recover an omitted `1/8`-type
improvement.

The clean repository-level mathematical interpretation is:

```text
Candidate local theorem:
replace the current almost-period-set -> structured-Bohr-set bootstrapping lemma
by one whose rank-growth cost drops by one power of L,
and whose pure local size-loss term drops by the same one power of L.
```

Concretely, the candidate replacement recurrence is:

### Rank increment

```math
d_{j+1} \le d_j + O(L^5)
```

instead of

```math
d_{j+1} \le d_j + O(L^6).
```

### Size loss

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^6)\bigr)|B_j|
```

instead of

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^7)\bigr)|B_j|.
```

### Density increment

Keep the same multiplicative increment:

```math
\alpha_{j+1} \ge (1+c)\alpha_j,
```

so the number of steps remains

```math
m = O(L).
```

## Exponent Propagation For The Candidate

With the candidate recurrence:

```math
d_j = O(jL^5),
```

hence after `m = O(L)` steps,

```math
d_m = O(L^6).
```

The cumulative size loss becomes

```math
\sum_{j < m} d_j L = O\!\left(\sum_{j < m} jL^6\right)=O(m^2L^6)=O(L^8),
```

while the pure local term contributes only

```math
\sum_{j < m} L^6 = O(L^7),
```

which is lower-order.

So the final ambient-size lower bound becomes

```math
|B_m| \ge \exp(-O(L^8))N.
```

Running the same terminal contradiction as before gives

```math
\exp(-O(L^8))N \ll 1,
```

hence

```math
L^8 \gg \log N,
```

so

```math
\alpha \le \exp\!\bigl(-c(\log N)^{1/8}\bigr).
```

Therefore the candidate replacement theorem would imply the upper bound

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/8}\bigr).
```

## Verdict

This computation has two consequences.

### A. The candidate local theorem is mathematically meaningful

It does improve the final exponent, from

```math
1/9 \quad \text{to} \quad 1/8.
```

So the source-mentioned omitted refinement is quantitatively coherent.

### B. It does not make the Behrend-scale target viable

The desired Behrend-scale theorem would require exponent

```math
1/2,
```

whereas this localized improvement yields only

```math
1/8.
```

So this exact local replacement theorem is not enough to justify continuing the current program
as a credible route to

```math
r_3(N)\ll N\exp(-c\sqrt{\log N}).
```

## Consequence For The Active Plan

The strict plan should therefore record the following judgment:

```text
The current architecture admits a meaningful local-improvement theorem candidate,
but the resulting propagated exponent is still far from Behrend scale.
Therefore the Behrend-scale target should no longer be treated as the active live theorem target
for this architecture.
```

The honest next targets are instead:

1. an explicit `1/8`-type theorem along the present architecture; or
2. a negative result stating that this architecture cannot by itself approach exponent `1/2`.
