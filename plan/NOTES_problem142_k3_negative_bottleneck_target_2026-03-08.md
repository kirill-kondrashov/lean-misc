# Notes: `k = 3` Negative/Bottleneck Target After The Behrend Pivot (2026-03-08)

## Objective

Record the exact mathematical shape of the negative theorem suggested by the completed strict
post-Behrend audit.

## Informal Statement

The intended negative theorem is:

```text
The present Kelley--Meka / Bloom--Sisask density-increment architecture,
with its current almost-periodicity-to-structure conversion costs,
cannot by itself yield a Behrend-scale upper bound
r_3(N) << N exp(-c sqrt(log N)).
```

## Mathematical Template

Let

```math
\alpha := |A|/N,
\qquad
L := \log(2/\alpha).
```

Suppose an upper-bound argument proceeds by iterating density increments over structured sets
`B_j` with ranks `d_j` and satisfies the current-architecture-type bounds

```math
d_{j+1} \le d_j + O(L^a),
```

```math
|B_{j+1}| \ge \exp\!\bigl(-O(d_j L + L^b)\bigr)|B_j|,
```

and

```math
\alpha_{j+1} \ge (1+c)\alpha_j,
```

for absolute `c>0`, with `O(L)` iterations.

The strict-plan analysis shows:

- current explicit architecture corresponds to roughly
  ```math
  a = 6, \quad b = 7,
  ```
  giving exponent `1/9`;
- the first source-motivated local improvement corresponds to
  ```math
  a = 5, \quad b = 6,
  ```
  giving exponent `1/8`.

So a negative theorem target can be phrased schematically as:

```math
\text{Under this architecture class, the propagated exponent }\theta(a,b)
\text{ remains strictly below }1/2.
```

In particular, for the currently source-motivated local improvement,

```math
\theta = 1/8 < 1/2.
```

## Practical Role

This is not yet a formal Lean theorem target. It is a meta-level mathematical research target.
Its purpose is:

1. certify that the Behrend-scale route is misaligned with the present architecture;
2. justify pivoting to either an explicit `1/8` theorem or a broader new architecture.

## Follow-Up

The generic propagation formula for this architecture class is now written out in

- `NOTES_problem142_k3_negative_architecture_barrier_2026-03-08.md`

and the active repository follow-up plan is

- `PLAN_erdos_problem_142_k3_negative_bottleneck_program_2026-03-08.md`.
