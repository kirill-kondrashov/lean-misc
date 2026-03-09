# Notes: Erdős #142 Post-Dormancy Track A Quantitative Varnavides Audit

Date: 2026-03-09

## Objective

Run the first post-dormancy exact-debt extraction audit on the direct counting /
supersaturation cluster.

## Source Hit

The audit found an exact source-backed candidate in:

- Croot--Sisask, *A new proof of Roth's theorem on arithmetic progressions*,
  Lemma 3.1
- provenance note inside that paper: the averaging argument is said to be essentially contained in
  Croot's earlier work and is a quantitative version of Varnavides's theorem

## Exact Extracted Statement

For integers `1 <= M <= N` and every set `A ⊆ [N]`, the paper proves a direct lower bound of the
shape

```text
T3(A) > ((|A|/N - (r3(M) + 1)/M) / M^4) * N^2,
```

where `T3(A)` counts nontrivial 3-term arithmetic progressions in `A`.

Equivalently:

```text
if |A|/N > (r3(M) + 1)/M,
then A already contains quantitatively many 3-term arithmetic progressions,
with an explicit polynomial loss in M.
```

## Why This Qualifies

This extracted statement satisfies the restart admissibility rule:

1. it is one exact theorem-shaped statement;
2. it is strictly smaller than the full direct `1 / 8` theorem on `A ⊆ [N]`;
3. it lies outside the exhausted family because it is a direct counting theorem on `A ⊆ [N]`,
   not a split-coupling theorem and not the current almost-periodicity/Bohr recurrence;
4. it has a clear downstream consequence for the repository.

## Why It Is Smaller Than The Full Direct `1 / 8` Theorem

The extracted theorem does **not** itself assert

```text
r3(N) = O(N exp(-c (log N)^(1/8))).
```

Instead, it converts subscale extremal information at length `M` into a direct global progression
count on length `N`.

So it is a local direct-counting reduction theorem, not the final upper theorem.

## Repository Consequence

This creates a new honest successor route:

```text
import / encode the quantitative Varnavides reduction,
then ask what existing or future subscale bound is enough to drive a direct counting theorem at the
`1 / 8` scale.
```

This is stronger and cleaner than the previously closed direct-counting branch, because the missing
local debt is no longer vague:
it is exactly the source-backed quantitative reduction theorem above.

## Audit Verdict

```text
Positive extraction.
```

Track A succeeds:
the post-dormancy program has found one exact smaller theorem debt outside the exhausted family.

## Successor

Open the direct-counting import/reduction chain:

```text
PLAN_erdos_problem_142_k3_quantitative_varnavides_import_route_2026-03-09.md
```
