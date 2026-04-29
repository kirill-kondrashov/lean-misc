# Note: Erdős #1 Against The Current Literature

Last literature refresh: **April 24, 2026**. That refresh still found the original integer Erdős
distinct subset sums problem listed as open on the Erdős problems site:

```math
N \gg 2^n.
```

The best **published** lower bound for the original problem remains

```math
N \ge \binom{n}{\lfloor n/2\rfloor}
\sim \sqrt{\frac{2}{\pi}}\,\frac{2^n}{\sqrt n}.
```

## Published Frontier

The conservative external baseline from the April 24, 2026 literature refresh is:

- Erdős problems page, last edited **April 6, 2026**:
  <https://www.erdosproblems.com/1>
  It still marks the problem open and states that the current record is the constant
  `sqrt(2/pi)`, with Dubroff–Fox–Xu proving the exact middle-binomial bound.
- Dubroff–Fox–Xu (2021):
  <https://dblp.org/rec/journals/siamdm/DubroffFX21.html>
  This is the established exact theorem
  ```math
  N \ge \binom{n}{\lfloor n/2\rfloor}.
  ```
- Steinerberger (2023):
  <https://doi.org/10.1142/S1793042123500860>
  This gives another proof / reformulation of the same benchmark, not a stronger bound.
- The problem page itself now explicitly says the current record `sqrt(2/pi)` is achieved by
  Dubroff–Fox–Xu, who also prove the exact bound
  ```math
  N \ge \binom{n}{\lfloor n/2\rfloor}.
  ```

So the published all-`n` state of the art for the original problem is still the
middle-binomial scale.

## New Or Related Results That Do Not Change The Baseline

These are relevant for context, but they do not improve the accepted frontier for the original
integer problem.

- Dutta, *The Greedy Algorithm for Dissociated Sets* (arXiv, 2026):
  <https://arxiv.org/abs/2601.07068>
  This is the most relevant new item in the search. It proves refined bounds for dissociated sets
  on a positive-density set of cutoffs and studies the greedy algorithm. It is useful context for
  the equivalent dissociated-set formulation, but it does **not** replace the uniform all-`n`
  Dubroff-Fox-Xu lower bound used as the original-problem benchmark.
- Cambie–Gao–Kim–Liu, modular variant:
  <https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/217/4/115883/the-erdos-distinct-subset-sums-problem-in-a-modular-setting>
- Costa–Della Fiore–Dalai, *Variants of the Erdős distinct sums problem and variance method*
  (Discrete Applied Mathematics, 2025):
  <https://doi.org/10.1016/j.dam.2025.03.003>
  This explicitly treats variants and records the best known original-problem bound as still being
  of order `2^n / sqrt(n)`.
- Other 2025–2026 variants, subset-product analogues, and higher-dimensional generalisations may be
  relevant nearby, but they do not currently change the accepted frontier for the original
  one-dimensional problem.

## Preprints And Unestablished Claims

There is at least one public 2025 preprint claim of a full resolution:

- Bado, *On Erdős's distinct subset sums conjecture via the circle method*:
  <https://zenodo.org/records/16117091>

This should currently be treated as **unestablished** for the purposes of this repo:

- the Erdős problems page still lists the problem as open;
- the standard published benchmark has not been displaced in the sources above;
- the GitHub/database status pages checked in this search do not indicate that the published
  frontier has changed.

So preprints can be tracked, but they should not redefine the repo's claimed baseline unless the
broader literature clearly accepts them.

There is also at least one nearby 2025 preprint in a generalized setting:

- Gu, *A Generalisation on Erdős Distinct Subset Sums Problem*:
  <https://arxiv.org/abs/2510.06032>

This is relevant background, but it is not a new published bound for the original one-dimensional
problem.

## GitHub And Database Status

The most useful GitHub-facing status source found in this search is:

- the community database repo behind `erdosproblems.com`:
  <https://github.com/teorth/erdosproblems>

That repo is useful as a status tracker, but not as proof authority. The problem page itself is
still the cleanest public summary:

- problem `#1` is open;
- it is marked as formalised;
- it still points to the Dubroff–Fox–Xu / Steinerberger benchmark for the original problem.

The formalisation link on the problem page points to Google DeepMind's `formal-conjectures`
repository:

- <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1.lean>

This is a useful statement-level reference, but not a proof repository changing the bound.

I did not find a GitHub repository that changes the accepted original-problem frontier beyond that.
The fresh GitHub search turned up only:

- the `erdosproblems` database repo;
- unrelated repositories mentioning “distinct subset sums” in other contexts;
- no codebase or manuscript repository that has clearly displaced the published baseline.

## What This Branch Has Actually Achieved

This branch has **not** yet proved a stronger unconditional lower bound than

```math
\binom{n}{\lfloor n/2\rfloor}.
```

So it is not yet a literature-level improvement.

What it has done is reduce the proof search to a much sharper form:

- exact route:
  one explicit two-layer bottleneck
  ```math
  \left|\partial^+\!\left(\left(\binom{[n]}{m}\setminus V\right)\cup U\right)\right|
  \ge
  \left|\binom{[n]}{m}\setminus V\right|;
  ```
- stronger route:
  one explicit approximation target
  ```math
  N \ge \binom{n}{\lfloor n/2\rfloor} + \left\lfloor \frac{n-1}{2} \right\rfloor,
  ```
  now reformulated as a restricted half-cube Hamming-ball stability problem.

## Bottom Line

Relative to the current literature:

- the accepted original-problem baseline is still
  ```math
  N \ge \binom{n}{\lfloor n/2\rfloor};
  ```
- preprints may claim more, but they are not yet the accepted frontier;
- GitHub/database status is consistent with that published picture;
- this repo's realistic near-term goal is therefore a first additive/stability improvement over the
  established approximation, not a claim of a full solution of Erdős #1.
