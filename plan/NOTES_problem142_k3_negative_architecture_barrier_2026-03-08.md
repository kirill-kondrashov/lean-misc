# Notes: `k = 3` Generic Architecture Barrier For The Negative Route (2026-03-08)

## Objective

Turn the negative/bottleneck route into an explicit recurrence calculation rather than a slogan.

The goal is to compute, for the architecture class isolated in the March 8 notes, the exact final
exponent forced by the recurrence parameters.

## Architecture Template

Let

```math
\alpha := |A|/N,
\qquad
L := \log(2/\alpha).
```

Assume an upper-bound argument iterates over structured sets `B_j` with ranks `d_j` and satisfies:

```math
d_{j+1} \le d_j + O(L^a),
```

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^b)\bigr)|B_j|,
```

```math
\alpha_{j+1} \ge (1+c)\alpha_j,
```

for some absolute `c > 0`, with at most `m = O(L)` iterations.

This is the exact class abstracted from the current Kelley--Meka / Bloom--Sisask recurrence notes.

## Generic Propagation Calculation

### Rank growth

Starting from `d_0 = 0`, after `j` steps:

```math
d_j = O(jL^a).
```

Hence after `m = O(L)` steps:

```math
d_m = O(L^{a+1}).
```

### Cumulative size loss

The rank-dependent contribution is

```math
\sum_{j < m} d_j L
= O\!\left(\sum_{j < m} jL^{a+1}\right)
= O(m^2 L^{a+1})
= O(L^{a+3}).
```

The pure local contribution is

```math
\sum_{j < m} L^b = O(L^{b+1}).
```

Therefore the total loss exponent is

```math
\gamma(a,b) := \max(a+3,\, b+1),
```

and the terminal structured set satisfies

```math
|B_m| \ge \exp\!\bigl(-O(L^{\gamma(a,b)})\bigr)N.
```

### Final upper-bound exponent

Running the usual terminal contradiction

```math
|B_m| \ll 1
```

gives

```math
\exp\!\bigl(-O(L^{\gamma(a,b)})\bigr)N \ll 1,
```

so

```math
L^{\gamma(a,b)} \gg \log N.
```

Equivalently,

```math
L \gg (\log N)^{1/\gamma(a,b)},
```

and therefore

```math
\alpha \le \exp\!\bigl(-c(\log N)^{\theta(a,b)}\bigr),
\qquad
\theta(a,b) := \frac{1}{\gamma(a,b)} = \frac{1}{\max(a+3,\, b+1)}.
```

So the architecture class forces the upper bound

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{\theta(a,b)}\bigr).
```

## Consistency Checks

### Current published recurrence

For

```math
a = 6,
\qquad
b = 7,
```

we get

```math
\gamma(6,7) = \max(9,8) = 9,
\qquad
\theta(6,7) = 1/9.
```

This matches the extracted Bloom--Sisask exponent.

### Source-motivated local improvement

For

```math
a = 5,
\qquad
b = 6,
```

we get

```math
\gamma(5,6) = \max(8,7) = 8,
\qquad
\theta(5,6) = 1/8.
```

This matches the propagated omitted-improvement calculation.

## Barrier To Behrend Scale

To reach Behrend scale inside this template, one would need

```math
\theta(a,b) = 1/2,
```

equivalently

```math
\gamma(a,b) = 2.
```

But

```math
\gamma(a,b) = \max(a+3,\, b+1) = 2
```

forces

```math
a \le -1,
\qquad
b \le 1.
```

So any architecture of the above form with nonnegative polynomial loss exponents

```math
a \ge 0,
\qquad
b \ge 0
```

cannot yield Behrend scale. In particular, the current source-backed regime and the first
source-motivated local improvement are both far outside the range needed for exponent `1/2`.

## Practical Consequence

This note gives the exact negative-route justification:

```text
within the extracted architecture class, the propagated exponent is controlled by
theta(a,b) = 1 / max(a+3, b+1),
so the present route and its first local refinement can reach 1/9 and 1/8 respectively,
but not 1/2.
```

That is the honest mathematical reason the active theorem program should pivot away from treating
the Behrend-scale upper bound as a live target for the current architecture.

## Lean Surface

The corresponding repository-level schema now lives in `ErdosProblems/Problem142.lean` as:

- `K3ArchitectureBarrierParams`
- `K3ArchitectureBarrierParams.lossExponent`
- `K3ArchitectureBarrierParams.propagatedExponent`
- `K3ArchitectureBarrierParams.not_behrendScaleViable`
- `k3CurrentArchitectureBarrierParams`
- `k3OneEighthArchitectureBarrierParams`
- `erdos_142_three_current_architecture_barrier`
- `erdos_142_three_one_eighth_refinement_barrier`
- `erdos_142_three_negative_route_stable`
