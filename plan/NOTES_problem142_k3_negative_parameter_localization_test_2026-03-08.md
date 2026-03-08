# Notes: `k = 3` Negative-Route Parameter-Localization Test (2026-03-08)

## Objective

Run the first live test from the `Template-Escape Critic`:

```text
is the negative-route barrier only an artifact of freezing one global
L = log(2/α),
or does the same exponent order survive if the iteration is written with
L_j = log(2/α_j)?
```

## Localized Template

Let

```math
\alpha_0 = \alpha,
\qquad
L_j := \log(2/\alpha_j).
```

Assume the same multiplicative density increment as in the existing notes:

```math
\alpha_{j+1} \ge (1+c)\alpha_j
```

for some absolute `c > 0`.

Then

```math
L_{j+1} \le L_j - \log(1+c),
```

so with

```math
\kappa := \log(1+c) > 0
```

we have

```math
L_j \le L_0 - \kappa j = L - \kappa j.
```

In particular:

```math
m \le L/\kappa + O(1) = O(L),
```

and for all `j < m`,

```math
0 \le L_j \le L.
```

## Localized Recurrence

Now replace the global-template recurrence by its localized form:

```math
d_{j+1} \le d_j + O(L_j^a),
```

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L_j + L_j^b)\bigr)|B_j|.
```

The critic question is whether this change can improve the exponent order beyond the current

```math
\theta(a,b) = 1 / \max(a+3, b+1).
```

## Rank Growth With Local Parameters

From `L_j ≤ L`,

```math
d_j \le \sum_{t<j} O(L_t^a) \le \sum_{t<j} O(L^a) = O(jL^a),
```

so still

```math
d_j = O(jL^a),
\qquad
d_m = O(L^{a+1}).
```

This is the same coarse order as in the frozen-`L` template.

## Cumulative Size Loss

### Rank-dependent term

Using the bound above,

```math
\sum_{j<m} d_j L_j
\le \left(\sup_{j<m} d_j\right)\sum_{j<m} L_j.
```

Now

```math
\sup_{j<m} d_j = O(L^{a+1}),
```

and because `L_j` decreases at least linearly to `0`,

```math
\sum_{j<m} L_j = O(L^2).
```

Therefore

```math
\sum_{j<m} d_j L_j = O(L^{a+3}).
```

### Pure local term

Also,

```math
\sum_{j<m} L_j^b \le m L^b = O(L^{b+1}).
```

So the same total loss exponent survives:

```math
\gamma(a,b) = \max(a+3, b+1).
```

## Critic Verdict For This Escape Route

Within the same recurrence architecture, replacing the frozen parameter `L` by localized
parameters `L_j` does **not** improve the exponent order of the barrier calculation.

The reason is:

```text
localization makes later steps cheaper,
but not enough to change the dominant orders
sup d_j = O(L^{a+1})
and
sum L_j = O(L^2),
whose product still gives O(L^{a+3}).
```

So the `parameter-localization escape` does **not** currently break the negative-route template.

## Scope Of This Verdict

This is not yet a critic-proof theorem about the papers themselves. It is a verdict only for the
following move:

```text
replace frozen L by local L_j while keeping the same basic recurrence architecture.
```

The remaining live critic questions are still:

1. whether the endgame `|B_m| << 1` is too crude;
2. whether the integer-case Bohr loss is avoidable by a different transport route.
