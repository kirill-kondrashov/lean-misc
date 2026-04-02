# Note: Erdős #1 Position Against Current Literature

As of **March 31, 2026**, the original integer Erdős distinct subset sums problem is still open in
the literature. The current published benchmark for the original problem remains

```math
N \ge \binom{n}{\lfloor n/2\rfloor}
\sim \sqrt{\frac{2}{\pi}}\,\frac{2^n}{\sqrt n},
```

while the conjectural target is still

```math
N \gg 2^n.
```

References:

- Erdős problem page: <https://www.erdosproblems.com/sources_bib/Er82e/yes>
- Dubroff–Fox–Xu (2021): <https://dblp.org/rec/journals/siamdm/DubroffFX21.html>
- Steinerberger (2023): <https://doi.org/10.1142/S1793042123500860>
- Cambie–Gao–Kim–Liu (2025, modular variant only): <https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/online/115883/the-erdos-distinct-subset-sums-problem-in-a-modular-setting>

## What This Branch Has Done

This branch has **not** yet proved a stronger unconditional lower bound than

```math
\binom{n}{\lfloor n/2\rfloor}.
```

So it is not yet a literature-level improvement.

What it *has* done is reduce the proof search to a much sharper form:

1. The broad prism/half-cube route has been formalized and normalized.
2. The exact middle-binomial endpoint is now funneled to one explicit two-layer bottleneck:

```math
\left|\partial^+\!\left(\left(\binom{[n]}{m}\setminus V\right)\cup U\right)\right|
\ge
\left|\binom{[n]}{m}\setminus V\right|.
```

3. A stronger-than-literature program has been isolated:

```math
|\partial^+F| \ge |C| + \Gamma(F),
```

with the goal of proving a positive gap away from the equality templates and then showing the
transported sum-distinct families cannot realize those templates.

## Why This Is Real Progress

The repo is no longer in the state “many possible approaches, unclear bottleneck.” It is now in
the state:

- one exact theorem would recover the current literature-level benchmark through the formal route;
- one explicit stability/gap program is the natural next step beyond that benchmark.

That is substantial proof-architecture progress, even though it is not yet a new theorem.

## Current Structural Evidence

The strongest exact evidence on the stronger branch is now:

- in the shifted world, equality appears only in two templates:
  - the full lower layer,
  - the principal-star two-layer family;
- the first strict shifted gap is:
  - `2` in `n = 5`,
  - `3` in `n = 7`;
- the shell-envelope symmetry is now exact in shifted `n = 7, 9, 11`:
  for the `full_lower` and `principal_star` strands, the shell-by-shell gap interval agrees at
  every computed shell distance;
- the principal-star strand dominates multiplicity of near-extremizers, even when the shell gap
  envelope matches the full-lower strand.

So the stronger branch is now naturally split into two subproblems:

1. a distance-only shell-envelope theorem;
2. a template-attribution / multiplicity theorem.

## What Still Separates Us From A New Result

Two gaps remain.

First, the exact bottleneck theorem itself is still open:

```math
\left|\partial^+\!\left(\left(\binom{[n]}{m}\setminus V\right)\cup U\right)\right|
\ge
\left|\binom{[n]}{m}\setminus V\right|.
```

Second, even once that is proved, a literature-level advance needs more:

- prove a positive gap off the equality templates;
- prove that transported sum-distinct families cannot lie in the equality-template neighborhoods;
- convert that gap into

```math
N \ge \binom{n}{\lfloor n/2\rfloor} + g(n)
```

for some explicit positive function `g(n)`.

## Bottom Line

Relative to the literature:

- no new unconditional bound yet;
- but a large reduction in proof debt;
- and a much sharper picture of the exact and stability theorems that would matter for a real
  advance on Erdős #1.
