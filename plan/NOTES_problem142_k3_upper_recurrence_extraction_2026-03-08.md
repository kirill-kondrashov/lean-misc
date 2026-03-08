# Notes: `k = 3` Upper-Bound Recurrence Extraction (2026-03-08)

## Objective

Extract the quantitative recurrence underlying the modern integer-case `k = 3` upper bound

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/9}\bigr),
```

using the Bloom--Sisask improvement note and its summary of the Kelley--Meka iteration.

## Source

Primary source:
- Bloom, T. F.; Sisask, O., *An improvement to the Kelley-Meka bounds on three-term arithmetic progressions*, arXiv:2309.02353
  - PDF: <https://arxiv.org/pdf/2309.02353>

Relevant extracted statements:
- Proposition 10: PDF lines 555--581
- iteration summary for Theorem 1: PDF lines 538--553

## Notation

Let

```math
\alpha := |A|/N
```

be the initial density of a `3`-AP-free set `A \subseteq \{1,\dots,N\}`.

Write

```math
L := L(\alpha) := \log(2/\alpha).
```

The Kelley--Meka / Bloom--Sisask density-increment argument iterates over regular Bohr sets

```math
B_0 \supseteq B_1 \supseteq B_2 \supseteq \cdots
```

with corresponding relative densities

```math
\alpha_j := |A_j|/|B_j|,
```

where each `A_j` is a translate/restriction of `A` inside `B_j`.

Let

```math
d_j := \operatorname{rk}(B_j)
```

be the Bohr-set rank.

## Source-Extracted Increment Step

Bloom--Sisask Proposition 10 states, in the regime relevant for the final integer-case theorem,
that when there are too few three-term progressions one may take

```math
\varepsilon \asymp 1,
\qquad
p \asymp L,
```

and obtain a density increment on a new Bohr set `B_{j+1}` with:

### Rank increment

From Proposition 10,

```math
d_{j+1} \le d_j + O_\varepsilon(L(\alpha)^4 p^2).
```

Substituting `p \asymp L` and `\varepsilon \asymp 1` gives the coarse recurrence

```math
d_{j+1} \le d_j + O(L^6).
```

### Density increment

The conclusion of Proposition 10 gives

```math
\|\mu_{B_{j+1}} * \mu_{A_j}\|_\infty \ge (1+c)\mu(B_j)^{-1}
```

for an absolute `c>0`, so after translating to the densest translate this yields a multiplicative
increment of the form

```math
\alpha_{j+1} \ge (1+c)\alpha_j.
```

Hence the number of iterations is at most

```math
m = O(L),
```

since density cannot exceed `1`.

### Size loss

Again from Proposition 10,

```math
|B_{j+1}| \ge \exp\!\bigl(-O_\varepsilon(d_j L(\alpha) + L(\alpha)^5 p^2)\bigr)|B_j|.
```

Substituting `p \asymp L` gives

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^7)\bigr)|B_j|.
```

Equivalently,

```math
\log \frac{|B_j|}{|B_{j+1}|} \le O(d_j L + L^7).
```

## Solving The Recurrence

### Rank growth

Starting from the trivial Bohr set

```math
d_0 = 0,
```

and iterating `m = O(L)` times,

```math
d_m \le \sum_{j < m} O(L^6) = O(L^7).
```

This matches the paper's summary

```math
d \ll L(\alpha)^7
```

at PDF lines 542--543.

### Size loss

At stage `j`, we have the coarse bound

```math
d_j = O(jL^6).
```

Therefore

```math
\sum_{j < m} d_j L = O\!\left(\sum_{j < m} jL^7\right)=O(m^2L^7)=O(L^9),
```

since `m = O(L)`.

Also,

```math
\sum_{j < m} L^7 = O(L^8),
```

which is lower-order than `O(L^9)`.

So the cumulative size loss satisfies

```math
|B_m| \ge \exp(-O(L^9))|B_0|.
```

With `|B_0| \asymp N`, this becomes

```math
|B_m| \ge \exp(-O(L^9))N.
```

This matches the source summary at PDF lines 544--545.

## Re-Deriving The Final Exponent `1/9`

At the end of the iteration, the paper states that one reaches a Bohr set `B_m` on which the
restricted set has the expected number of three-term progressions. Since the original set is
`3`-AP-free, only trivial progressions remain, forcing

```math
|B_m| \ll 1.
```

Combining this with the lower bound above gives

```math
\exp(-O(L^9))N \ll 1.
```

Equivalently,

```math
L^9 \gg \log N.
```

Hence

```math
L = \log(2/\alpha) \gg (\log N)^{1/9},
```

which rearranges to

```math
\alpha \le \exp\!\bigl(-c(\log N)^{1/9}\bigr)
```

for some `c>0`.

Since `|A| = \alpha N`, this is exactly

```math
r_3(N)\ll N\exp\!\bigl(-c(\log N)^{1/9}\bigr).
```

## Mathematical Consequence

The exponent `1/9` is now traced to the following quantitative chain:

```text
rank increment per step:     O(L^6)
number of steps:             O(L)
rank after iteration:        O(L^7)
size loss per step:          exp(-O(d_j L + L^7))
cumulative size loss:        exp(-O(L^9))
terminal contradiction:      exp(-O(L^9)) N << 1
final exponent:              1/9
```

This is the exact reason the strict plan insists on recurrence extraction before discussing local
improvements.

## What Must Be Improved To Beat `1/9`

To improve the final exponent, one must improve at least one of the quantities in the chain above.
The source-backed bottleneck note indicates the most plausible local target is:

```text
replace the current almost-period-set -> Bohr-set bootstrapping step by one with better
rank/size parameters.
```

But now that claim can be tested quantitatively: any proposed replacement theorem must be plugged
back into the recurrence above, and the resulting final exponent must be recomputed.
