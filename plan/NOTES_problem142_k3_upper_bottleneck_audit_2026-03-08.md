# Notes: `k = 3` Upper-Bound Bottleneck Audit (2026-03-08)

## Objective

Audit the modern Kelley--Meka / Bloom--Sisask upper-bound architecture to identify a concrete
local bottleneck relevant to the stronger target

```math
\texttt{bound\_targets.k3\_behrend\_scale\_upper\_profile},
```

namely

```math
r_3(N)=O\!\left(N\exp(-c\sqrt{\log N})\right).
```

## Primary Sources Consulted

1. Kelley, Z.; Meka, R., *Strong Bounds for 3-Progressions*, arXiv:2302.05537
   - abstract page: <https://arxiv.org/abs/2302.05537>

2. Bloom, T. F.; Sisask, O., *An improvement to the Kelley-Meka bounds on three-term arithmetic progressions*, arXiv:2309.02353
   - abstract page: <https://arxiv.org/abs/2309.02353>
   - ar5iv HTML used for section structure and proof outline: <https://ar5iv.labs.arxiv.org/html/2309.02353>

3. Bloom, T. F.; Sisask, O., *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*, arXiv:2007.03528
   - abstract page: <https://arxiv.org/abs/2007.03528>

## Source-Backed Facts

### A. Current published upper range is still far from Behrend scale

Kelley--Meka prove only an upper bound of the shape

```math
r_3(N)\le N\exp\!\bigl(-c(\log N)^\beta\bigr)
```

for some `\beta > 0`; see the abstract of arXiv:2302.05537.

Bloom--Sisask improve this to the explicit bound

```math
r_3(N)\le N\exp\!\bigl(-c(\log N)^{1/9}\bigr);
```

see the abstract of arXiv:2309.02353.

This is still far from the desired Behrend-scale target

```math
r_3(N)\le N\exp\!\bigl(-c\sqrt{\log N}\bigr).
```

### B. The improvement paper explicitly identifies the local modified step

Bloom--Sisask write that their contribution is a

```text
quantitatively improved bootstrapping of almost-periodicity
```

and that this is the point inserted into the Kelley--Meka argument to obtain the `1/9` bound.
See ar5iv lines 40--41 and 58--60.

### C. The concrete bottleneck is the almost-period-set -> structured-object conversion

In the model finite-field setting, the paper explains that the critical bootstrapping step replaces
an arbitrary set of almost-periods by a structured subspace, and that the crude estimate of a key
Fourier quantity forces a worse parameter choice. See ar5iv lines 69--76.

The same source then states that exploiting additional structure improves the key term from an
`\alpha^4`-type quantity to an `\alpha^3`-type quantity in the Kelley--Meka application; see ar5iv
lines 73--75.

Inference from the source:

```text
the main quantitative loss is not spread uniformly through the whole proof;
it is concentrated in the bootstrapping step that turns almost-periodicity into algebraic structure.
```

### D. There is an explicit integer-case loss beyond the finite-field model

For the general integer case, Bloom--Sisask state that there is an additional loss in the size of
the Bohr set, and that

```text
it is ultimately this which is responsible for losing two logs between the F_p^n and the integer case.
```

See ar5iv lines 134--135.

Inference from the source:

```text
even if the finite-field bootstrapping step were sharp enough, the integer-to-Bohr-set conversion
still introduces a separate quantitative obstruction.
```

### E. The authors themselves indicate a local stronger theorem direction

After the proof of Lemma 6, Bloom--Sisask state that a more careful treatment of the same step can
push the exponent further to `1/8`, but they omit the technical optimization because they expect
future ideas to make such optimization redundant; see ar5iv lines 17--18 and 114--120.

This is direct evidence that the active bottleneck is local and quantitative, not merely global.

## Bottleneck Verdict

The current best source-backed diagnosis is:

```text
Primary bottleneck:
  improved bootstrapping of almost-periodicity
  (turning a set of almost-periods into a structured subspace/Bohr set)

Secondary integer-case bottleneck:
  extra Bohr-set size/rank loss in the passage from the model finite-field setting
  to the integers
```

This is the exact place where the current modern upper-bound line should be attacked first.

## Local Stronger-Theorem Candidate

A realistic next theorem target is not yet the full Behrend-scale upper bound. It is a sharper
bootstrapping theorem replacing the current crude bound in the almost-periodicity-to-structure step.

In repository-language, the useful local theorem would have the form:

```text
Given the Kelley--Meka/Bloom--Sisask almost-periodicity hypotheses,
produce a structured set of almost-periods (subspace/Bohr set)
with strictly better codimension/rank growth than the present bootstrapping lemma.
```

A concrete success criterion would be:

```text
recover at least the omitted 1/8-type exponent improvement source-mentioned by Bloom--Sisask,
thereby proving the architecture still has nontrivial headroom.
```

## Consequence For The Plan

The active `k = 3` Behrend-scale plan should not try to jump directly from `1/9` to `1/2`.
The honest next move is:

1. isolate the bootstrapping lemma as the primary local theorem debt;
2. test whether the source-mentioned `1/8` refinement can be formalized as a concrete research
   target;
3. if not, pivot to the negative/bottleneck program rather than continue blind optimization.

## Bottom Line

```text
There is now a concrete source-backed bottleneck.
It is the almost-periodicity bootstrapping step, with an additional integer-case Bohr loss.
This makes Program 1 mathematically meaningful, but only in a localized form.
The next reasonable target is a sharper local bootstrapping theorem, not the full Behrend-scale
upper bound in one jump.
```
